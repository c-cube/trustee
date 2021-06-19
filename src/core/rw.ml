
open Sigs
module K = Kernel
module E = K.Expr

type conv = Conv.t
type rw_step = Conv.rw_step = Same | Rw_step of K.thm

let thm_res_eqn thm : E.t * E.t =
  match E.unfold_eq (K.Thm.concl thm) with
  | None -> errorf (fun k->k"rw: theorem %a should be an equation" K.Thm.pp thm)
  | Some pair -> pair

let[@inline] thm_res_rhs th : E.t = snd (thm_res_eqn th)
let[@inline] thm_res_lhs th : E.t = fst (thm_res_eqn th)

let bottom_up (conv:conv) : conv =
  fun ctx (e0 : E.t) : rw_step ->
  (* normalize [e] *)
  let rec loop e : Conv.rw_step =
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

  and try_conv step1 e : rw_step =
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

module Conv = struct
end

module Rule = struct
  type t = {
    lhs: K.expr;
    rhs: rhs;
  }
  and rhs =
    | Basic of {
        th: K.thm;
      }
    | Dynamic of {
        mk_rhs: (K.ctx -> K.expr -> K.Subst.t -> K.thm option);
      }

  let mk_rule lhs th : t = {lhs; rhs=Basic {th}}
  let mk_dynamic lhs mk_rhs : t = {lhs; rhs=Dynamic {mk_rhs}}

  let pp out (self:t) =
    match self.rhs with
    | Basic {th;_} ->
      Fmt.fprintf out "(@[rw.rule@ %a@])" K.Thm.pp_quoted th
    | Dynamic _ ->
      Fmt.fprintf out "(@[rw.dyn-rule@ :lhs %a@])" K.Expr.pp self.lhs

  let to_conv (self:t) : conv = fun ctx e ->
    match Unif.match_ self.lhs e with
    | None -> Same
    | Some subst ->
      begin match self.rhs with
        | Basic {th} ->
          let th2 = K.Thm.subst ~recursive:false ctx th subst in
          assert (E.equal e (thm_res_lhs th2));
          Rw_step th2
        | Dynamic {mk_rhs} ->
          begin match mk_rhs ctx self.lhs subst with
            | None -> Same
            | Some th2 ->
              assert (E.equal e (thm_res_lhs th2));
              Rw_step th2
          end
      end
end

module RuleSet = struct
  type t = Rule.t list

  let empty : t = []
  let size = List.length

  let of_list l : t = l
  let to_iter = Iter.of_list

  exception Step of K.thm

  (* TODO: some form of indexing on [lhs], so that this scales at least a bit.
     Perhaps a limited-depth discrimination tree? *)

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

module AC_rule = struct
  type t = {
    f: K.expr;
    (** A binary AC function *)

    assoc: K.thm;
    (** Theorem [|- f (f x y) z = f x (f y z)] *)

    comm: K.thm;
    (** Theorem [|- f x y = f y x] *)

    rw_assoc: Rule.t; (* built from assoc *)
    rw_comm: Rule.t; (* built from comm *)
  }

  let make ~f ~assoc ~comm () : t =
    (* TODO: check the shape of assoc/comm? *)
    (* TODO: polymorphism? *)
    let rw_assoc = Rule.mk_rule (thm_res_lhs assoc) assoc in
    let rw_comm = Rule.mk_rule (thm_res_lhs comm) comm in
    {f; assoc; comm; rw_assoc; rw_comm}

  let pp out self = Fmt.fprintf out "(@[ac-rw@ :f %a@])" K.Expr.pp self.f

  let to_conv self : conv = fun ctx e ->
    match Rule.to_conv self.rw_assoc ctx e with
    | Rw_step _ as r -> r
    | Same ->
      match Rule.to_conv self.rw_comm ctx e with
      | Rw_step th as r when KBO.gt (thm_res_lhs th) (thm_res_rhs th) ->
        (* rewrite, but only in a decreasing way *)
        r
      | _ -> Same

end
