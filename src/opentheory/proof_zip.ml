(* Proof-trace zip archive -- new format.
   Entries:
     _storage/<key>   -- one zip entry per storage key (const defs, etc.)
     <name>.entry     -- minidag encoding of a theory's consts + thm sequents

   Format of the "theory" root minidag node:
     int n_param_consts  refs[n] to "ce" nodes
     int n_param_thms    refs[n] to seq nodes
     int n_consts        refs[n] to "ce" nodes
     int n_thms          refs[n] to seq nodes

   "ce" (const entry) node:
     string name
     ref    ty_expr
     string "ar" | "vs"
     int    n
     refs   (ty_var exprs if "vs")
*)

open Common_
module Storage = Trustee_core.Storage
module LP = K.Linear_proof
module Enc = Trustee_minidag.Encode
module Dec = Trustee_minidag.Decode

(* ---- Constants ------------------------------------------------------------ *)

let entry_suffix = ".entry"
let storage_prefix = "_storage/"

(* ---- Tracked storage ------------------------------------------------------ *)

(** Wraps an in-memory storage and records every (key, bytes) stored into it,
    so they can later be written to the zip. *)
type tracked_storage = {
  ts_inner: Storage.t;
  mutable ts_entries: (string * string) list;
}

let make_tracked_storage ?(size = 1024) () : tracked_storage =
  let ts_inner = Storage.in_memory ~size () in
  { ts_inner; ts_entries = [] }

let tracked_as_storage (ts : tracked_storage) : Storage.t =
  let (module Inner) = ts.ts_inner in
  let module M = struct
    let get ~key = Inner.get ~key
    let mem ~key = Inner.mem ~key

    let store ~key ?(erase = false) s =
      if erase || not (Inner.mem ~key) then (
        Inner.store ~key ~erase s;
        ts.ts_entries <- (key, s) :: ts.ts_entries
      )
  end in
  (module M)

(* ---- Zip handle ----------------------------------------------------------- *)

(* Note: the minidag encode/decode caches (expr↔offset) remain plain
   Hashtbl.t because that is the type required by the kernel's mg_enc_*/
   mg_dec_* API.  We cannot substitute a named module without touching
   the kernel. *)

module Theory_lru = Lru.M.Make
    (struct
      type t = string
      let equal = String.equal
      let hash = Hashtbl.hash
    end)
    (struct
      (* theory, proof-section offset (-1 = absent), raw entry bytes,
         expr cache built during theory decode (reused for proof decode) *)
      type t = K.Theory.t * int * string * (int, K.expr) Hashtbl.t
      let weight _ = 1
    end)

type zip_handle = {
  zf: Zip.in_file;
  entries: Zip.entry list;
  (* cache: name -> (theory, proof_offset, raw_entry_bytes, expr_cache) *)
  theory_cache: Theory_lru.t;
}

let open_zip (path : string) : zip_handle =
  let zf = Zip.open_in path in
  let entries = Zip.entries zf in
  { zf; entries; theory_cache = Theory_lru.create 8 }

let close_zip (zh : zip_handle) : unit = Zip.close_in zh.zf

let theory_names (zh : zip_handle) : string list =
  let suf_len = String.length entry_suffix in
  List.filter_map
    (fun entry ->
      let name = entry.Zip.filename in
      let nlen = String.length name in
      if nlen > suf_len
         && String.sub name (nlen - suf_len) suf_len = entry_suffix then
        Some (String.sub name 0 (nlen - suf_len))
      else
        None)
    zh.entries

(* ---- Storage restore ------------------------------------------------------ *)

let restore_storage (zh : zip_handle) (ctx : K.ctx) : unit =
  let storage = K.Ctx.storage ctx in
  let pfx_len = String.length storage_prefix in
  List.iter
    (fun entry ->
      let name = entry.Zip.filename in
      let nlen = String.length name in
      if nlen > pfx_len && String.sub name 0 pfx_len = storage_prefix then (
        let key = String.sub name pfx_len (nlen - pfx_len) in
        let data = Zip.read_entry zh.zf entry in
        Storage.store storage ~erase:false ~key data
      ))
    zh.entries

(* ---- Encode a theory ------------------------------------------------------ *)

(* Encode a standalone const as a "ce" node. *)
let enc_const_ (cache : (K.expr, int) Hashtbl.t) enc (c : K.Const.t) : int =
  let ty_off = K.Expr.mg_enc_expr cache enc (K.Const.ty c) in
  (* Pre-encode var nodes BEFORE starting the "ce" write_node, so their
     bytes don't appear inside the node's arg stream. *)
  let args_enc = match K.Const.args c with
    | K.Const.C_arity n -> `Ar n
    | K.Const.C_ty_vars vs ->
      let v_offs = List.map (K.Expr.mg_enc_var cache enc) vs in
      `Vs (List.length vs, v_offs)
  in
  Enc.write_node enc "ce" (fun nd ->
    Enc.string nd (K.Const.name c);
    Enc.ref nd ty_off;
    match args_enc with
    | `Ar n -> Enc.string nd "ar"; Enc.int nd n
    | `Vs (n, v_offs) ->
      Enc.string nd "vs";
      Enc.int nd n;
      List.iter (Enc.ref nd) v_offs)

(* Encode LP proof args and steps, sharing the expr cache with the theory encoder.
   Returns the offset of the "lp" root node. *)
let enc_lp_ (cache : (K.expr, int) Hashtbl.t) enc (lp : K.Linear_proof.t) : int =
  let enc_arg = function
    | K.Proof.Pr_expr e ->
      let e' = K.Expr.mg_enc_expr cache enc e in
      Enc.write_node enc "pe" (fun nd -> Enc.ref nd e')
    | K.Proof.Pr_subst pairs ->
      let pair_offs =
        List.map
          (fun (v, e) ->
            (K.Expr.mg_enc_var cache enc v, K.Expr.mg_enc_expr cache enc e))
          pairs
      in
      Enc.write_node enc "ps" (fun nd ->
          List.iter (fun (v', e') -> Enc.ref nd v'; Enc.ref nd e') pair_offs)
  in
  let enc_step (step : K.Linear_proof.step) =
    let { K.Linear_proof.concl; rule; args; parents } = step in
    let concl' = K.Expr.mg_enc_seq cache enc concl in
    let arg_offs = List.map enc_arg args in
    Enc.write_node enc "step" (fun nd ->
        Enc.ref nd concl';
        Enc.string nd rule;
        Enc.int nd (List.length parents);
        List.iter (Enc.int nd) parents;
        List.iter (Enc.ref nd) arg_offs)
  in
  let step_offs =
    K.Linear_proof.steps lp
    |> Iter.map (fun (_i, step) -> enc_step step)
    |> Iter.to_list
  in
  Enc.write_node enc "lp" (fun nd ->
      Enc.int nd (List.length step_offs);
      List.iter (Enc.ref nd) step_offs)

(** Footer size and magic. *)
let footer_size = 16
let footer_magic = 0x504F4F462E454E54L  (* "POOF.ENT" *)

(** Write a 16-byte footer:
    [last_node_size as LE int64][magic as LE int64]
    where [last_node_size] is the byte-length of the "theory" root node.  This
    lets the decoder find the root in O(1) by jumping backward. *)
let write_footer buf ~last_node_size =
  let b = Bytes.create footer_size in
  Bytes.set_int64_le b 0 (Int64.of_int last_node_size);
  Bytes.set_int64_le b 8 footer_magic;
  Buffer.add_bytes buf b

(** Read the footer from [data].  Returns the byte-length of the last minidag
    node, or [-1] if the footer is absent (old format / no proofs). *)
let read_footer data : int =
  let total = String.length data in
  if total < footer_size then
    -1
  else (
    let magic = String.get_int64_le data (total - 8) in
    if magic <> footer_magic then
      -1
    else (
      let n = String.get_int64_le data (total - footer_size) in
      Int64.to_int n
    )
  )

(* Encode a theory into a minidag string.

   Layout:
     [const/seq minidag nodes]
     [pe/ps/step/lp/"proofs" nodes]    <- proof section (may be empty)
     ["theory" root node]               <- last minidag node; refs into all above
     [16-byte footer: last_node_size LE int64 + magic LE int64]

   The "theory" root node's last field is:
     - Ref(proofs_node_off)  when proofs are present
     - Null                  when no proofs

   To decode without reading proofs:
     1. Read footer → last_node_size.
     2. theory_root_off = total_len - footer_size - last_node_size.
     3. Dec.read_node at theory_root_off → decode consts/seqs; save the
        proofs Ref (or Null) as the last field without following it.

   Old entries without a valid footer fall back to full iter_nodes scan
   (no proof section available). *)
let encode_theory ?(proofs : K.Linear_proof.t list option) (theory : K.Theory.t) : string =
  let buf = Buffer.create 4096 in
  let out =
    object
      method write b o l = Buffer.add_subbytes buf b o l
    end
  in
  let enc = Enc.create ~out () in
  let cache : (K.expr, int) Hashtbl.t = Hashtbl.create 128 in
  let enc_c c = enc_const_ cache enc c in
  let enc_thm_seq th = K.Expr.mg_enc_seq cache enc (K.Thm.sequent th) in
  let param_consts = K.Theory.param_consts theory in
  let param_thms = K.Theory.param_theorems theory in
  let consts = K.Theory.consts theory in
  let thms = K.Theory.theorems theory in
  let pc_offs = List.map enc_c param_consts in
  let pt_offs = List.map enc_thm_seq param_thms in
  let c_offs = List.map enc_c consts in
  let t_offs = List.map enc_thm_seq thms in
  (* Encode proof nodes before the theory root (refs must be backward). *)
  let proof_node_off : int option =
    match proofs with
    | None -> None
    | Some lps ->
      let lp_offs = List.map (enc_lp_ cache enc) lps in
      let off = Enc.write_node enc "proofs" (fun nd ->
          Enc.int nd (List.length lp_offs);
          List.iter (Enc.ref nd) lp_offs) in
      Some off
  in
  (* Theory root is the last minidag node. Record its start offset. *)
  Enc.flush enc;
  let theory_root_start = Enc.current_offset enc in
  let _root =
    Enc.write_node enc "theory" (fun nd ->
        Enc.int nd (List.length pc_offs);
        List.iter (Enc.ref nd) pc_offs;
        Enc.int nd (List.length pt_offs);
        List.iter (Enc.ref nd) pt_offs;
        Enc.int nd (List.length c_offs);
        List.iter (Enc.ref nd) c_offs;
        Enc.int nd (List.length t_offs);
        List.iter (Enc.ref nd) t_offs;
        match proof_node_off with
        | None -> Enc.null nd
        | Some off -> Enc.ref nd off)
  in
  Enc.flush enc;
  let theory_root_end = Enc.current_offset enc in
  let last_node_size = theory_root_end - theory_root_start in
  (* Append footer. *)
  write_footer buf ~last_node_size;
  Buffer.contents buf

(* ---- Decode a theory ------------------------------------------------------ *)

let read_int_ nd =
  match Dec.read nd with
  | Dec.Int64 i -> Int64.to_int i
  | _ -> failwith "proof_zip.read_int_: expected int"

(* Decode a "ce" node into a K.Const.t. *)
let dec_const_ (ctx : K.ctx) dec (cache : (int, K.expr) Hashtbl.t) off :
    K.Const.t =
  Dec.read_node dec off (fun nd _cmd ->
      let name = Dec.read_string_exn nd in
      let ty_off = Dec.read_ref_exn nd in
      let ty = K.Expr.mg_dec_expr ctx dec cache ty_off in
      let args_kind = Dec.read_string_exn nd in
      let n = read_int_ nd in
      let c_args =
        match args_kind with
        | "ar" -> K.Const.C_arity n
        | "vs" ->
          let vs =
            List.init n (fun _ ->
                let v_off = Dec.read_ref_exn nd in
                K.Expr.mg_dec_var ctx dec cache v_off)
          in
          K.Const.C_ty_vars vs
        | s -> failwith ("proof_zip.dec_const_: unknown args_kind " ^ s)
      in
      K.Const.make_from_parts ~name ~ty ~args:c_args)

(* Decode LP arg from a node at [off]. *)
let dec_lp_arg_ (ctx : K.ctx) dec (cache : (int, K.expr) Hashtbl.t) off : K.Proof.arg =
  Dec.read_node dec off (fun nd cmd ->
      match cmd with
      | "pe" ->
        let e = K.Expr.mg_dec_expr ctx dec cache (Dec.read_ref_exn nd) in
        K.Proof.Pr_expr e
      | "ps" ->
        let acc = ref [] in
        let go = ref true in
        while !go do
          match Dec.read nd with
          | Dec.Ref v_off ->
            let v = K.Expr.mg_dec_var ctx dec cache v_off in
            let e_off = Dec.read_ref_exn nd in
            let e = K.Expr.mg_dec_expr ctx dec cache e_off in
            acc := (v, e) :: !acc
          | Dec.Stop -> go := false
          | _ -> failwith "proof_zip.dec_lp_arg_: ps: expected Ref or Stop"
        done;
        K.Proof.Pr_subst (List.rev !acc)
      | c -> failwith ("proof_zip.dec_lp_arg_: unknown arg cmd " ^ c))

(* Decode a single "lp" node at [off]. *)
let dec_lp_ (ctx : K.ctx) dec (cache : (int, K.expr) Hashtbl.t) off : K.Linear_proof.t =
  Dec.read_node dec off (fun nd _cmd ->
      let n = read_int_ nd in
      let step_offs = Array.init n (fun _ -> Dec.read_ref_exn nd) in
      let dec_step s_off =
        Dec.read_node dec s_off (fun nd _cmd ->
            let concl = K.Expr.mg_dec_seq ctx dec cache (Dec.read_ref_exn nd) in
            let rule = Dec.read_string_exn nd in
            let n_parents = read_int_ nd in
            let parents = List.init n_parents (fun _ -> read_int_ nd) in
            let arg_offs = ref [] in
            let go = ref true in
            while !go do
              match Dec.read nd with
              | Dec.Ref r -> arg_offs := r :: !arg_offs
              | Dec.Stop -> go := false
              | _ -> failwith "proof_zip.dec_lp_: expected Ref or Stop for args"
            done;
            let args = List.rev_map (dec_lp_arg_ ctx dec cache) (List.rev !arg_offs) in
            ({ K.Linear_proof.concl; rule; parents; args } : K.Linear_proof.step))
      in
      K.Linear_proof.make_from_steps (Array.map dec_step step_offs))

(* Find the theory root offset from [data].
   Uses the footer (O(1)) if present; falls back to iter_nodes scan otherwise. *)
let find_theory_root_off (data : string) : int =
  let total = String.length data in
  let last_node_size = read_footer data in
  if last_node_size > 0 then
    (* O(1) jump: theory root starts this many bytes before the footer. *)
    total - footer_size - last_node_size
  else (
    (* Old format or no footer: scan all nodes, take the last one. *)
    let dec = Dec.create data in
    let root_off = ref 0 in
    Dec.iter_nodes dec (fun off _cmd _args -> root_off := off);
    !root_off
  )

(* Decode a theory from minidag bytes.
   Returns the theory and the byte offset of the "proofs" node (-1 = no proofs). *)
let decode_theory (ctx : K.ctx) (name : string) (data : string) : K.Theory.t * int * (int, K.expr) Hashtbl.t =
  let dec = Dec.create data in
  let cache : (int, K.expr) Hashtbl.t = Hashtbl.create 128 in
  let root_off = find_theory_root_off data in
  Dec.read_node dec root_off (fun nd _cmd ->
      let n_pc = read_int_ nd in
      let pc_offs = Array.init n_pc (fun _ -> Dec.read_ref_exn nd) in
      let n_pt = read_int_ nd in
      let pt_offs = Array.init n_pt (fun _ -> Dec.read_ref_exn nd) in
      let n_c = read_int_ nd in
      let c_offs = Array.init n_c (fun _ -> Dec.read_ref_exn nd) in
      let n_t = read_int_ nd in
      let t_offs = Array.init n_t (fun _ -> Dec.read_ref_exn nd) in
      (* Last field: Ref to "proofs" node, or Null (no proofs), or Stop (old format). *)
      let proof_node_off =
        match Dec.read nd with
        | Dec.Ref r -> r
        | Dec.Null | Dec.Stop -> -1
        | _ -> -1
      in
      let dec_c off = dec_const_ ctx dec cache off in
      let dec_seq off = K.Expr.mg_dec_seq ctx dec cache off in
      let param_consts = Array.to_list (Array.map dec_c pc_offs) in
      let param_seqs = Array.to_list (Array.map dec_seq pt_offs) in
      let consts = Array.to_list (Array.map dec_c c_offs) in
      let thm_seqs = Array.to_list (Array.map dec_seq t_offs) in
      let th =
        K.Theory.with_ ctx ~name (fun th ->
            List.iter (K.Theory.add_assumption_const th) param_consts;
            List.iter
              (fun seq ->
                let thm = K.Thm.assume_box ctx seq in
                K.Theory.add_param_theorem th thm)
              param_seqs;
            List.iter (K.Theory.add_const th) consts;
            List.iter
              (fun seq ->
                let thm = K.Thm.assume_box ctx seq in
                K.Theory.add_theorem th thm)
              thm_seqs)
      in
      (th, proof_node_off, cache))

(* ---- Load theory from zip ------------------------------------------------- *)

let find_entry (zh : zip_handle) (filename : string) : Zip.entry option =
  List.find_opt (fun e -> e.Zip.filename = filename) zh.entries

let load_theory (zh : zip_handle) ~(ctx : K.ctx) (name : string) :
    K.Theory.t option =
  match Theory_lru.find name zh.theory_cache with
  | Some (th, _proof_off, _data, _ecache) ->
    Theory_lru.promote name zh.theory_cache;
    Some th
  | None ->
    let entry_name = name ^ entry_suffix in
    (match find_entry zh entry_name with
    | None -> None
    | Some entry ->
      (try
         let data = Zip.read_entry zh.zf entry in
         let (th, proof_off, ecache) = decode_theory ctx name data in
         Theory_lru.add name (th, proof_off, data, ecache) zh.theory_cache;
         Theory_lru.trim zh.theory_cache;
         Some th
       with e ->
         Printf.eprintf "proof_zip.load_theory: decode error for %s: %s\n%!"
           name (Printexc.to_string e);
         None))

(** Load the proof terms for an already-loaded theory on demand.
    Returns [None] if proofs are not present in the entry or if the theory
    has not been loaded yet via [load_theory]. *)
let load_proofs (zh : zip_handle) ~(ctx : K.ctx) (name : string) :
    K.Linear_proof.t list option =
  match Theory_lru.find name zh.theory_cache with
  | None -> None
  | Some (_th, proof_off, data, ecache) ->
    Theory_lru.promote name zh.theory_cache;
    if proof_off < 0 then
      None
    else (
      try
        let dec = Dec.create data in
        (* Reuse the expr cache from theory decoding so proof nodes can
           reference const/var/expr nodes encoded in the theory section. *)
        Some (
          Dec.read_node dec proof_off (fun nd _cmd ->
              let n = read_int_ nd in
              let lp_offs = Array.init n (fun _ -> Dec.read_ref_exn nd) in
              Array.to_list (Array.map (dec_lp_ ctx dec ecache) lp_offs)))
      with e ->
        Printf.eprintf "proof_zip.load_proofs: decode error for %s: %s\n%!"
          name (Printexc.to_string e);
        None
    )

(* ---- Build zip ------------------------------------------------------------ *)

let build ~output ~(eval : Eval.state) ~(ts : tracked_storage)
    ~(names : string Iter.t) : unit =
  let zf = Zip.open_out output in
  let n_theories = ref 0 in
  Iter.iter
    (fun name ->
      match Eval.eval_theory eval name with
      | Error e ->
        Format.eprintf "build-zip: error in %s: %a@." name
          Trustee_core.Error.pp e
      | Ok (theory, _info) ->
        (try
           (* Collect linear proofs from theorems (if store_proofs was enabled) *)
           let proofs =
             try
               let thms = K.Theory.theorems theory in
               let lps = List.map K.Linear_proof.of_thm_proof thms in
               Some lps
             with _ -> None
           in
           let data = encode_theory ?proofs theory in
           Zip.add_entry data zf (name ^ entry_suffix);
           incr n_theories
         with e ->
           Format.eprintf "build-zip: encode error in %s: %s@." name
             (Printexc.to_string e)))
    names;
  (* Write storage entries (const defs, etc.) collected during evaluation *)
  let storage_entries =
    List.sort_uniq (fun (k1, _) (k2, _) -> String.compare k1 k2)
      ts.ts_entries
  in
  List.iter
    (fun (key, data) -> Zip.add_entry data zf (storage_prefix ^ key))
    storage_entries;
  Zip.close_out zf;
  Printf.printf
    "wrote %d theory entries + %d storage entries to %s\n%!"
    !n_theories (List.length storage_entries) output

(* ---- Legacy API ----------------------------------------------------------- *)

let zip_entry_name name = name ^ ".lp"

let encode_proof_list (proofs : LP.t list) : string =
  let buf = Buffer.create 1024 in
  let out =
    object
      method write b o l = Buffer.add_subbytes buf b o l
    end
  in
  let enc = Enc.create ~out () in
  let cache : (K.expr, int) Hashtbl.t = Hashtbl.create 64 in
  let enc_arg = function
    | K.Proof.Pr_expr e ->
      let e' = K.Expr.mg_enc_expr cache enc e in
      Enc.write_node enc "pe" (fun nd -> Enc.ref nd e')
    | K.Proof.Pr_subst pairs ->
      let pair_offs =
        List.map
          (fun (v, e) ->
            (K.Expr.mg_enc_var cache enc v, K.Expr.mg_enc_expr cache enc e))
          pairs
      in
      Enc.write_node enc "ps" (fun nd ->
          List.iter (fun (v', e') -> Enc.ref nd v'; Enc.ref nd e') pair_offs)
  in
  let enc_step step =
    let { LP.concl; rule; args; parents } = step in
    let concl' = K.Expr.mg_enc_seq cache enc concl in
    let arg_offs = List.map enc_arg args in
    Enc.write_node enc "step" (fun nd ->
        Enc.ref nd concl';
        Enc.string nd rule;
        Enc.int nd (List.length parents);
        List.iter (Enc.int nd) parents;
        List.iter (Enc.ref nd) arg_offs)
  in
  let enc_lp lp =
    let step_offs =
      LP.steps lp |> Iter.map (fun (_i, step) -> enc_step step) |> Iter.to_list
    in
    Enc.write_node enc "lp" (fun nd ->
        Enc.int nd (List.length step_offs);
        List.iter (Enc.ref nd) step_offs)
  in
  let proof_offs = List.map enc_lp proofs in
  let _root =
    Enc.write_node enc "thms" (fun nd ->
        Enc.int nd (List.length proof_offs);
        List.iter (Enc.ref nd) proof_offs)
  in
  Enc.flush enc;
  Buffer.contents buf

let decode_proof_list (ctx : K.ctx) (s : string) : LP.t list =
  let dec = Dec.create s in
  let cache : (int, K.expr) Hashtbl.t = Hashtbl.create 64 in
  let root_off = ref 0 in
  Dec.iter_nodes dec (fun off _cmd _args -> root_off := off);
  let dec_arg_node off =
    Dec.read_node dec off (fun nd cmd ->
        match cmd with
        | "pe" ->
          let e = K.Expr.mg_dec_expr ctx dec cache (Dec.read_ref_exn nd) in
          K.Proof.Pr_expr e
        | "ps" ->
          let acc = ref [] in
          let go = ref true in
          while !go do
            match Dec.read nd with
            | Dec.Ref v_off ->
              let v = K.Expr.mg_dec_var ctx dec cache v_off in
              let e_off = Dec.read_ref_exn nd in
              let e = K.Expr.mg_dec_expr ctx dec cache e_off in
              acc := (v, e) :: !acc
            | Dec.Stop -> go := false
            | _ -> failwith "proof_zip.decode: ps: expected Ref or Stop"
          done;
          K.Proof.Pr_subst (List.rev !acc)
        | c -> failwith ("proof_zip.decode: unknown arg cmd " ^ c))
  in
  let dec_step off =
    Dec.read_node dec off (fun nd _cmd ->
        let concl = K.Expr.mg_dec_seq ctx dec cache (Dec.read_ref_exn nd) in
        let rule = Dec.read_string_exn nd in
        let n_parents =
          match Dec.read nd with
          | Dec.Int64 i -> Int64.to_int i
          | _ -> failwith "proof_zip.decode: expected n_parents"
        in
        let parents =
          List.init n_parents (fun _ ->
              match Dec.read nd with
              | Dec.Int64 i -> Int64.to_int i
              | _ -> failwith "proof_zip.decode: expected parent idx")
        in
        let arg_offs = ref [] in
        let go = ref true in
        while !go do
          match Dec.read nd with
          | Dec.Ref r -> arg_offs := r :: !arg_offs
          | Dec.Stop -> go := false
          | _ -> failwith "proof_zip.decode: expected Ref or Stop for args"
        done;
        let args = List.rev_map dec_arg_node (List.rev !arg_offs) in
        ({ LP.concl; rule; parents; args } : LP.step))
  in
  let dec_lp off =
    Dec.read_node dec off (fun nd _cmd ->
        let n =
          match Dec.read nd with
          | Dec.Int64 i -> Int64.to_int i
          | _ -> failwith "proof_zip.decode: expected step count"
        in
        let step_offs = Array.init n (fun _ -> Dec.read_ref_exn nd) in
        let steps_arr = Array.map dec_step step_offs in
        LP.make_from_steps steps_arr)
  in
  Dec.read_node dec !root_off (fun nd _cmd ->
      let n =
        match Dec.read nd with
        | Dec.Int64 i -> Int64.to_int i
        | _ -> failwith "proof_zip.decode: expected proof count"
      in
      let lp_offs = Array.init n (fun _ -> Dec.read_ref_exn nd) in
      Array.to_list (Array.map dec_lp lp_offs))

let load (path : string) : string Str_tbl.t =
  let tbl = Str_tbl.create 64 in
  let zf = Zip.open_in path in
  List.iter
    (fun entry ->
      let name = entry.Zip.filename in
      let data = Zip.read_entry zf entry in
      Str_tbl.replace tbl name data)
    (Zip.entries zf);
  Zip.close_in zf;
  tbl

let lookup_theory ~cache:(cache : string Str_tbl.t) ~(ctx : K.ctx) name
    : K.Linear_proof.t list option =
  let entry = zip_entry_name name in
  match Str_tbl.get cache entry with
  | None -> None
  | Some data ->
    (try Some (decode_proof_list ctx data)
     with e ->
       Printf.eprintf "proof_zip.lookup_theory: decode error for %s: %s\n%!"
         name (Printexc.to_string e);
       None)
