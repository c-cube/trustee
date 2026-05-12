(* Proof-trace zip archive.
   One entry per theory named "<theory-name>.lp".
   Each entry is a minidag encoding of a list of Linear_proof.t values,
   one per theorem defined by that theory.
   Root node: "thms", refs to each "lp" node (one per theorem). *)

open Common_

module LP = K.Linear_proof
module Enc = Trustee_minidag.Encode
module Dec = Trustee_minidag.Decode

let zip_entry_name name = name ^ ".lp"

(* ── Encoding a list of linear proofs into one minidag ────────────────────── *)

let encode_proof_list (proofs : LP.t list) : string =
  let buf = Buffer.create 1024 in
  let out =
    object
      method write b o l = Buffer.add_subbytes buf b o l
    end
  in
  let enc = Enc.create ~out () in
  (* Shared expr cache across all proofs for space efficiency *)
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
              let v =
                match K.Expr.view (K.Expr.mg_dec_expr ctx dec cache v_off) with
                | K.Expr.E_var v -> v
                | _ -> failwith "proof_zip.decode: ps: expected var"
              in
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

(* ── Build zip ────────────────────────────────────────────────────────────── *)

let build ~output ~(eval : Eval.state) ~(names : string Iter.t) : unit =
  let zf = Zip.open_out output in
  Iter.iter
    (fun name ->
      match Eval.eval_theory eval name with
      | Error e ->
        Format.eprintf "build-zip: error in %s: %a@." name
          Trustee_core.Error.pp e
      | Ok (theory, _info) ->
        let thms = K.Theory.theorems theory in
        let proofs =
          List.filter_map
            (fun thm ->
              try Some (LP.of_thm_proof thm) with _ -> None)
            thms
        in
        if proofs <> [] then (
          let data = encode_proof_list proofs in
          Zip.add_entry data zf (zip_entry_name name)
        ))
    names;
  Zip.close_out zf

(* ── Load zip ─────────────────────────────────────────────────────────────── *)

let load (path : string) : (string, string) Hashtbl.t =
  let tbl = Hashtbl.create 64 in
  let zf = Zip.open_in path in
  List.iter
    (fun entry ->
      let name = entry.Zip.filename in
      let data = Zip.read_entry zf entry in
      Hashtbl.replace tbl name data)
    (Zip.entries zf);
  Zip.close_in zf;
  tbl

(* ── Lookup ───────────────────────────────────────────────────────────────── *)

let lookup_theory ~cache ~(ctx : K.ctx) name : K.Linear_proof.t list option =
  let entry = zip_entry_name name in
  match Hashtbl.find_opt cache entry with
  | None -> None
  | Some data ->
    (try Some (decode_proof_list ctx data)
     with e ->
       Printf.eprintf "proof_zip.lookup_theory: decode error for %s: %s\n%!"
         name (Printexc.to_string e);
       None)
