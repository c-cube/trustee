
open Sigs
module K = Kernel
module E = K.Expr

type conv = Conv.t
type rw_step = Conv.rw_step = Same | Rw_step of K.thm

let unfold_eqn_ e =
  match E.unfold_eq e with
  | None -> errorf (fun k->k"rw: %a should be an equation" K.Expr.pp e)
  | Some pair -> pair
let thm_res_eqn thm : E.t * E.t =
  unfold_eqn_ (K.Thm.concl thm)

let[@inline] arg_n i e =
  let _, args = K.Expr.unfold_app e in
  if i<List.length args then List.nth args i
  else errorf (fun k->k"`%a` does not have %d args" K.Expr.pp e (i+1))
let arg0 = arg_n 0
let arg1 = arg_n 1
let[@inline] eq_lhs e = fst (unfold_eqn_ e)
let[@inline] eq_rhs e = snd (unfold_eqn_ e)
let[@inline] thm_res_rhs th : E.t = snd (thm_res_eqn th)
let[@inline] thm_res_lhs th : E.t = fst (thm_res_eqn th)

let bottom_up (conv:conv) : conv =
  fun ctx (e0 : E.t) : rw_step ->
  (* cache, to normalize as a DAG *)
  let tbl = E.Tbl.create 8 in
  (* normalize [e] *)
  let rec loop e : Conv.rw_step =
    match E.view e with
    | E.E_kind | E.E_type | E.E_arrow _ -> Same
    | _ ->
      match E.Tbl.get tbl e with
      | Some step -> step
      | None ->
        let step = loop_uncached e in
        E.Tbl.add tbl e step;
        step

  and loop_uncached e : rw_step =
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
      (* call [loop] again, to get to a fixpoint *)
      let step' = loop (thm_res_rhs th2) in
      Conv.(chain_res ctx step1 (chain_res ctx step2 step'))
  in
  loop e0

let bottom_up_apply conv ctx e =
  Conv.apply (bottom_up conv) ctx e

module Pos = struct
  type t =
    | Root
    | App0 of t
    | App1 of t
    (* | App_n of int * t *)
    | Lam_body of t

  let rec pp out = function
    | Root -> Fmt.fprintf out "@<1>ε"
    | App0 p -> Fmt.fprintf out "left.%a" pp p
    | App1 p -> Fmt.fprintf out "right.%a" pp p
    (*     | App_n (i,p) -> Fmt.fprintf out "%d.%a" i pp p *)
    | Lam_body p -> Fmt.fprintf out "body.%a" pp p

  let root = Root
  let app0 p = App0 p
  let app1 p = App1 p
(*   let app_n i p = App_n (i,p) *)
  let eqn0 p = app0 @@ app1 p
  let eqn1 p = app1 p
  let lam_body p = Lam_body p
end

let under (p:Pos.t) (conv:Conv.t) : Conv.t =
  fun ctx e ->
  let module Th = (val K.make_thm ctx) in
  let rec loop_ p e =
    match p, E.view e with
    | Pos.Root, _ -> conv ctx e
    | Pos.App0 p, E.E_app (f, a) ->
      begin match loop_ p f with
        | Same -> Same
        | Rw_step th -> Rw_step (Th.congr th (Th.refl a))
      end
    | Pos.App1 p, E.E_app (f, a) ->
      begin match loop_ p a with
        | Same -> Same
        | Rw_step th -> Rw_step (Th.congr (Th.refl f) th)
      end
    | Lam_body p, E.E_lam _ ->
      let v, bod = E.open_lambda_exn ctx e in
      begin match loop_ p bod with
        | Same -> Same
        | Rw_step th ->
          Rw_step (Th.abs v th)
      end
      (*TODO
    | Pos.App_n (i, p), _ ->
      let f, args = E.unfold_app e in
      if i < List.length args then (
        begin match loop_ p bod with
          | Same -> Same
          | Rw_step th ->
            Rw_step (Th.abs v th)
        end

      ) else Same
        *)
    | _ -> Same
  in
  loop_ p e

let under_apply p conv ctx e =
  Conv.apply (under p conv) ctx e

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

  let mk_rule th : t =
    let lhs = thm_res_lhs th in
    {lhs; rhs=Basic {th}}

  let mk_dynamic lhs mk_rhs : t = {lhs; rhs=Dynamic {mk_rhs}}

  let mk_non_oriented th : t =
    let lhs = thm_res_lhs th in
    mk_dynamic lhs
      (fun ctx _lhs subst ->
         let th = K.Thm.subst ctx ~recursive:false th subst in
         let lhs, rhs = thm_res_eqn th in
         if KBO.gt lhs rhs then Some th else None)

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
  type ordered = bool
  type t = {
    f: K.expr;
    (** A binary AC function *)

    assoc: K.thm;
    (** Theorem [|- f (f x y) z = f x (f y z)] *)

    comm: K.thm;
    (** Theorem [|- f x y = f y x] *)

    rules: (Rule.t * ordered) list;
    (** List of rules, with a flag stating whether they are already
        oriented left-to-right or not. *)
  }

  let make ctx ~f ~assoc ~comm () : t =
    let module E = (val K.make_expr ctx) in
    let module Th = (val K.make_thm ctx) in
    (* TODO: polymorphism? *)

    let tau = E.ty_exn f |> E.return_ty in
    let x = E.var_name "x" tau in
    let y = E.var_name "y" tau in
    let z = E.var_name "z" tau in
    let assoc_shape =
      E.(app_eq (app_l f [app_l f [x; y]; z]) (app_l f [x; app_l f [y;z]]))
    and comm_shape =
      E.(app_eq (app_l f [x; y]) (app_l f [y; x]))
    in

    if not (Unif.is_alpha_equiv assoc_shape (Th.concl assoc)) then (
      errorf (fun k->k"wrong shape for associativity theorem:@ expected `%a`@ got %a"
                 E.pp assoc_shape E.pp (Th.concl assoc))
    );
    if not (Unif.is_alpha_equiv comm_shape (Th.concl comm)) then (
      errorf (fun k->k"wrong shape for commutativity theorem:@ expected `%a`@ got %a"
                 E.pp comm_shape E.pp (Th.concl comm))
    );

    let rule_assoc = Rule.mk_rule assoc in
    let rule_comm = Rule.mk_rule comm in

    let rw_with rule e : Th.t =
      Conv.apply (Rule.to_conv rule) ctx e
    in
    let rw_at pos rule e : Th.t =
      under_apply pos (Rule.to_conv rule) ctx e
    in

    let assoc' = Th.sym assoc in

    (* from "E: a brainiac theorem prover", the ground complete system
       is an extension of AC:
       [f (f x y) z = f x (f y z)] (assoc)
       [f x y = f y x] (comm)
       [f x (f y z) = f z (f x y)] (r1)
       [f x (f y z) = f y (f x z)] (r2)
       [f x (f y z) = f z (f y x)] (r3)
    *)
    let r1 =
      let r1' = rw_at Pos.(eqn1 root) rule_comm (Th.concl assoc') in
      Th.bool_eq assoc' r1'
    and r2 =
      (*
         [f x (f y z) = f (f x y) z] (assoc')
         have: [f (f x y) z = f (f y x) z]
         trans: [f x (f y z) = f (f y x) z]
         assoc: [f x (f y z) = f y (f x z)]
      *)
      let r1 = rw_at Pos.(eqn1 @@ app0 @@ app1 @@ root) rule_comm
          (Th.concl assoc') in
      let r2 = Th.bool_eq assoc' r1 in
      let r3 = rw_with rule_assoc (thm_res_rhs r2) in
      Th.trans r2 r3
    and r3 =
      (*
         [f x (f y z) = f (f x y) z] (assoc')
         comm: [f (f x y) z = f z (f x y)]
         comm: [f x (f y z) = f z (f y x)]
      *)
      let r1 = rw_at Pos.(eqn1 root) rule_comm (Th.concl assoc') in
      let r2 = Th.bool_eq assoc' r1 in
      let r3 = rw_at Pos.(eqn1 @@ app1 root) rule_comm (Th.concl r2) in
      Th.bool_eq r2 r3
    in
    let rules = [
      rule_assoc, true;
      rule_comm, false;
      Rule.mk_rule r1, false;
      Rule.mk_rule r2, false;
      Rule.mk_rule r3, false;
    ] in
    {f; assoc; comm; rules; }

  let pp out self = Fmt.fprintf out "(@[ac-rw@ :f %a@])" K.Expr.pp self.f

  let to_conv self : conv = fun ctx e ->
    (* try rules one by one *)
    let rec loop_ = function
      | [] -> Same
      | (rule, ordered) :: tl ->
        match Rule.to_conv rule ctx e with
        | Rw_step _ as r when ordered -> r
        | Rw_step th as r when KBO.gt (thm_res_lhs th) (thm_res_rhs th) ->
          (* rewrite, but only in a decreasing way *)
          r
        | _ -> loop_ tl
    in
    loop_ self.rules
end
