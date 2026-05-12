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
