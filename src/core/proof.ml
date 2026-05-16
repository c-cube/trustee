open Types
open Sigs

type t = proof =
  | Pr_dummy
  | Pr_main of proof
  | Pr_step of {
      rule: string;
      args: proof_arg list;
      parents: thm list;
    }

type arg = proof_arg =
  | Pr_expr of expr
  | Pr_subst of (var * expr) list

let a_expr e : arg = Pr_expr e
let a_subst (s : subst) : arg = Pr_subst (Subst.to_list s)
let dummy : t = Pr_dummy
let main self : t = Pr_main self

let step ?(args = []) ?(parents = []) (rule : string) : t =
  Pr_step { rule; args; parents }

let is_main = function
  | Pr_main _ -> true
  | _ -> false

let is_main_or_dummy = function
  | Pr_dummy | Pr_main _ -> true
  | Pr_step _ -> false

module Linear_proof = struct
  type arg = proof_arg =
    | Pr_expr of expr
    | Pr_subst of (var * expr) list

  type step = {
    concl: sequent;
    rule: string;
    args: arg list;
    parents: int list;
  }

  type t = { steps: step Vec.t }

  let steps (self : t) : _ Iter.t =
   fun k -> Vec.iteri (fun i s -> k (i, s)) self.steps

  let make_from_steps (steps_arr : step array) : t =
    let v = Vec.create () in
    Array.iter (Vec.push v) steps_arr;
    { steps = v }

  module Sequent_tbl = CCHashtbl.Make (Sequent)

  let of_thm_proof (th0 : thm) : t =
    let steps = Vec.create () in
    let idx = ref 0 in
    let seen = Sequent_tbl.create 8 in

    let add_step ?(args = []) ?(parents = []) (seqt : sequent) (rule : string) :
        int =
      let i = !idx in
      incr idx;
      Vec.push steps { concl = seqt; rule; args; parents };
      i
    in

    let rec traverse seqt pr : int =
      match Sequent_tbl.find_opt seen seqt with
      | Some i -> i
      | None ->
        let i =
          match pr with
          | Pr_main pr' when seqt == th0.th_seq -> emit_step seqt pr'
          | _ -> emit_step seqt pr
        in
        Sequent_tbl.add seen seqt i;
        i
    and emit_step (seqt : sequent) (pr : proof) : int =
      match pr with
      | Pr_main _ -> add_step seqt "lemma" ~args:[]
      | Pr_dummy -> add_step seqt "<dummy>" ~args:[]
      | Pr_step { rule; args; parents } ->
        let parents =
          List.map (fun th' -> traverse th'.th_seq th'.th_proof) parents
        in
        add_step seqt rule ~args ~parents
    in

    ignore (traverse th0.th_seq th0.th_proof : int);
    { steps }
end

(** Minidag encode/decode for [Linear_proof.t]. Lives here (not in expr.ml) to
    avoid a circular dependency: proof.ml depends on expr.ml, and
    [Expr.mg_enc_expr] etc. are the bridging helpers. *)
module Linear_proof_mg = struct
  module Enc = Trustee_minidag.Encode
  module Dec = Trustee_minidag.Decode

  let encode (lp : Linear_proof.t) : string =
    let buf = Buffer.create 512 in
    let out =
      object
        method write b o l = Buffer.add_subbytes buf b o l
      end
    in
    let enc = Enc.create ~out () in
    let cache : int Expr.Tbl.t = Expr.Tbl.create 32 in
    let enc_arg = function
      | Pr_expr e ->
        let e' = Expr.mg_enc_expr cache enc e in
        Enc.write_node enc "pe" (fun nd -> Enc.ref nd e')
      | Pr_subst pairs ->
        let pair_offs =
          List.map
            (fun (v, e) ->
              Expr.mg_enc_var cache enc v, Expr.mg_enc_expr cache enc e)
            pairs
        in
        Enc.write_node enc "ps" (fun nd ->
            List.iter
              (fun (v', e') ->
                Enc.ref nd v';
                Enc.ref nd e')
              pair_offs)
    in
    let enc_step (step : Linear_proof.step) =
      let concl' = Expr.mg_enc_seq cache enc step.concl in
      let arg_offs = List.map enc_arg step.args in
      Enc.write_node enc "step" (fun nd ->
          Enc.ref nd concl';
          Enc.string nd step.rule;
          Enc.int nd (List.length step.parents);
          List.iter (Enc.int nd) step.parents;
          List.iter (Enc.ref nd) arg_offs)
    in
    let step_offs =
      Vec.to_iter lp.Linear_proof.steps |> Iter.map enc_step |> Iter.to_list
    in
    let _root =
      Enc.write_node enc "lp" (fun nd ->
          Enc.int nd (List.length step_offs);
          List.iter (Enc.ref nd) step_offs)
    in
    Enc.flush enc;
    Buffer.contents buf

  let decode (ctx : ctx) (s : string) : Linear_proof.t =
    let dec = Dec.create s in
    let cache : expr Int_tbl.t = Int_tbl.create 32 in
    let root_off = ref 0 in
    Dec.iter_nodes dec (fun off _cmd _args -> root_off := off);
    let dec_arg_node off =
      Dec.read_node dec off (fun nd cmd ->
          match cmd with
          | "pe" ->
            let e = Expr.mg_dec_expr ctx dec cache (Dec.read_ref_exn nd) in
            Pr_expr e
          | "ps" ->
            let acc = ref [] in
            let go = ref true in
            while !go do
              match Dec.read nd with
              | Dec.Ref v_off ->
                let v = Expr.mg_dec_var ctx dec cache v_off in
                let e_off = Dec.read_ref_exn nd in
                let e = Expr.mg_dec_expr ctx dec cache e_off in
                acc := (v, e) :: !acc
              | Dec.Stop -> go := false
              | _ -> failwith "Linear_proof_mg.decode: ps: expected Ref or Stop"
            done;
            Pr_subst (List.rev !acc)
          | c -> failwith ("Linear_proof_mg.decode: unknown arg cmd " ^ c))
    in
    let dec_step off =
      Dec.read_node dec off (fun nd _cmd ->
          let concl = Expr.mg_dec_seq ctx dec cache (Dec.read_ref_exn nd) in
          let rule = Dec.read_string_exn nd in
          let n_parents =
            match Dec.read nd with
            | Dec.Int64 i -> Int64.to_int i
            | _ -> failwith "Linear_proof_mg.decode: expected n_parents"
          in
          let parents =
            List.init n_parents (fun _ ->
                match Dec.read nd with
                | Dec.Int64 i -> Int64.to_int i
                | _ -> failwith "Linear_proof_mg.decode: expected parent idx")
          in
          let arg_offs = ref [] in
          let go = ref true in
          while !go do
            match Dec.read nd with
            | Dec.Ref r -> arg_offs := r :: !arg_offs
            | Dec.Stop -> go := false
            | _ ->
              failwith "Linear_proof_mg.decode: expected Ref or Stop for args"
          done;
          let args = List.rev_map dec_arg_node (List.rev !arg_offs) in
          { Linear_proof.concl; rule; parents; args })
    in
    Dec.read_node dec !root_off (fun nd _cmd ->
        let n =
          match Dec.read nd with
          | Dec.Int64 i -> Int64.to_int i
          | _ -> failwith "Linear_proof_mg.decode: expected step count"
        in
        let step_offs = Array.init n (fun _ -> Dec.read_ref_exn nd) in
        let steps_arr = Array.map dec_step step_offs in
        let v = Vec.create () in
        Array.iter (Vec.push v) steps_arr;
        { Linear_proof.steps = v })
end
