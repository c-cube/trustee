
open Sigs
module K = Kernel
module E = K.Expr

(** Result of a rewriting operation *)
type rw_result =
  | Same
  | Rw_step of K.thm
    (** A theorem [A |- a=b] where [a] is the initial term, and [b] the result. *)

type conv = K.ctx -> K.expr -> rw_result
(** Converter: takes a term and returns a possible rewrite theorem for it *)

let thm_res_eqn thm : E.t * E.t =
  match E.unfold_eq (K.Thm.concl thm) with
  | None -> errorf (fun k->k"rw: theorem %a should be an equation" K.Thm.pp thm)
  | Some pair -> pair

let[@inline] thm_res_rhs th : E.t = snd (thm_res_eqn th)
let[@inline] thm_res_lhs th : E.t = fst (thm_res_eqn th)

let bottom_up ctx (conv:conv) (e0:K.expr) : rw_result =
  (* normalize [e] *)
  let rec loop e : rw_result =
    match E.view e with
    | E.E_kind | E.E_type | E.E_arrow _ -> Same
    | E.E_app (f, x) ->
      let r_f = loop f in
      let r_x = loop x in
      let res, e' =
        match r_f, r_x with
        | Same, Same -> Same, e
        | Same, Rw_step th_x ->
          let th = K.Thm.congr ctx (K.Thm.refl ctx f) th_x in
          Rw_step th, thm_res_rhs th
        | Rw_step th_f, Same ->
          let th = K.Thm.congr ctx th_f (K.Thm.refl ctx x) in
          Rw_step th, thm_res_rhs th
        | Rw_step th_f, Rw_step th_x ->
          let th = K.Thm.congr ctx th_f th_x in
          Rw_step th, thm_res_rhs th
      in
      try_conv res e'
    | E.E_lam _ ->
      (* TODO: introduce variable, apply it, rewrite body *)
      try_conv Same e
    | E.E_var _ | E.E_bound_var _ | E.E_const _ -> try_conv Same e

  and try_conv step1 e : rw_result =
    match conv ctx e with
    | Same -> step1
    | Rw_step th2 as step2 ->
      let step, e' =
        match step1 with
        | Same -> step2, thm_res_rhs th2
        | Rw_step th1 ->
          let th = K.Thm.trans ctx th1 th2 in
          Rw_step th, thm_res_rhs th
      in
      try_conv step e' (* fixpoint here *)
  in
  loop e0

(** {2 Rewrite rules} *)
module Rule = struct
  type t = {
    lhs: K.expr;
    th: K.thm; (* lhs = rhs *)
  }
  (** A rewrite rule, i.e. an equation *)

  let pp out (self:t) = Fmt.fprintf out "(@[rw.rule@ %a@])" K.Thm.pp_quoted self.th

  let to_conv (self:t) : conv = fun ctx e ->
    match Unif.match_ self.lhs e with
    | None -> Same
    | Some subst ->
      let th2 = K.Thm.subst ~recursive:false ctx self.th subst in
      assert (E.equal e (thm_res_lhs th2));
      Rw_step th2
end

(** {2 A set of rewrite rules} *)
module RuleSet = struct
  type t = Rule.t list

  let empty : t = []
  let size = List.length

  let of_list l : t = l
  let to_iter = Iter.of_list

  exception Step of K.thm

  let to_conv (self:t) : conv = fun ctx e ->
    try
      List.iter
        (fun rule ->
           match Rule.to_conv rule ctx e with
           | Same -> ()
           | Rw_step th -> raise_notrace (Step th))
        self;
      Same
    with Step th -> Rw_step th
end
