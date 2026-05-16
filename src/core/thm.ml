open Types
open Sigs
module H = CCHash

type t = thm

let[@inline] concl self = self.th_seq.concl
let[@inline] sequent self = self.th_seq
let[@inline] hyps_ self = self.th_seq.hyps
let[@inline] hyps_iter self k = Expr_set.iter k self.th_seq.hyps
let[@inline] hyps_l self = Expr_set.to_list self.th_seq.hyps
let hyps_sorted_l = hyps_l
let iter_exprs self = Sequent.iter_exprs self.th_seq
let[@inline] has_hyps self = not (Expr_set.is_empty self.th_seq.hyps)
let n_hyps self = Expr_set.size self.th_seq.hyps

let is_fully_concrete self =
  Const.expr_is_concrete_ (concl self)
  && Iter.for_all Const.expr_is_concrete_ (hyps_iter self)

let rec chash_proof_ ctx =
  let open Chash in
  function
  | Pr_main p ->
    string ctx "m";
    chash_proof_ ctx p
  | Pr_dummy -> string ctx "d"
  | Pr_step { rule; args = _; parents } ->
    string ctx "s";
    string ctx rule;
    List.iter (fun th -> Expr.Util_chash_.hasher_seq_ ctx th.th_seq) parents

let chash self =
  let open Chash in
  let ctx = create () in
  Expr.Util_chash_.hasher_seq_ ctx self.th_seq;
  chash_proof_ ctx self.th_proof;
  finalize ctx

let proof self = self.th_proof

let make_main_proof self =
  if not (Proof.is_main_or_dummy self.th_proof) then
    self.th_proof <- Pr_main self.th_proof

(** Release the proof DAG, replacing it with [Pr_dummy]. Call this after the
    proof has been serialised to reclaim memory. *)
let drop_proof self = self.th_proof <- Pr_dummy

let[@inline] equal a b = Sequent.equal a.th_seq b.th_seq
let hash (self : t) = Sequent.hash self.th_seq

module Tbl = CCHashtbl.Make (struct
  type t = thm

  let equal = equal
  let hash = hash
end)

type 'a with_ctx = ctx -> 'a

let pp_depth ~max_depth out (th : t) =
  let pp_t = Expr.pp_depth ~max_depth in
  if has_hyps th then
    Fmt.fprintf out "@[<hv1>%a@;<1 -1>|-@ %a@]" (pp_list ~sep:", " pp_t)
      (hyps_l th) pp_t (concl th)
  else
    Fmt.fprintf out "@[<1>|-@ %a@]" pp_t (concl th)

let pp = pp_depth ~max_depth:max_int
let to_string = Fmt.to_string pp
let pp_quoted = Fmt.within "`" "`" pp

let is_proof_of self (g : Sequent.t) : bool =
  Expr.equal self.th_seq.concl (Sequent.concl g)
  && Expr_set.subset self.th_seq.hyps (Sequent.hyps g)

let make_seq_ ctx seq proof th_theory : t =
  let th_flags = ctx.ctx_uid in
  let proof =
    if ctx.ctx_store_proofs then
      proof ()
    else
      Proof.dummy
  in
  { th_flags; th_seq = seq; th_proof = proof; th_theory }

let make_for_zip ctx seq proof = make_seq_ ctx seq (fun () -> proof) None

let make_ ctx hyps concl proof th : t =
  let th_seq = Sequent.make hyps concl in
  make_seq_ ctx th_seq proof th

let is_bool_ ctx e : bool =
  let ty = Expr.ty_exn e in
  Expr.equal (Expr.bool ctx) ty

let assume ctx (e : Expr.t) : t =
  let@ () =
    Error.guard (fun err -> Error.wrapf "in assume `@[%a@]`:" Expr.pp e err)
  in
  ctx_check_e_uid ctx e;
  if not (is_bool_ ctx e) then Error.fail "assume takes a boolean";
  let proof () = Proof.(step "assume" ~args:[ a_expr e ]) in
  make_ ctx (Expr_set.singleton e) e proof None

let axiom ctx hyps e : t =
  let@ () =
    Error.guard (fun err ->
        let g = Sequent.make_l hyps e in
        Error.wrapf "in axiom `@[%a@]`:" Sequent.pp g err)
  in
  ctx_check_e_uid ctx e;
  if not ctx.ctx_axioms_allowed then
    Error.fail
      "the context does not accept new axioms, see `pledge_no_more_axioms`";
  if not (is_bool_ ctx e && List.for_all (is_bool_ ctx) hyps) then
    Error.fail "axiom takes a boolean";
  let proof () = Proof.(step "axiom" ~args:[ a_expr e ]) in
  make_ ctx (Expr_set.of_list hyps) e proof None

let merge_hyps_ = Expr_set.union

let merge_theory_ a b =
  match a, b with
  | None, a -> a
  | a, None -> a
  | (Some a as res), Some b ->
    if a != b then Error.fail "cannot use theorems from distinct theories";
    res

let cut ctx th1 th2 : t =
  let@ () =
    Error.guard (fun e ->
        Error.wrapf "@[<2>in cut@ th1=`@[%a@]`@ th2=`@[%a@]`@]:" pp th1 pp th2 e)
  in
  ctx_check_th_uid ctx th1;
  ctx_check_th_uid ctx th2;
  let b = concl th1 in
  let hyps = merge_hyps_ (hyps_ th1) (Expr_set.remove b (hyps_ th2)) in
  let proof () = Proof.(step "cut" ~parents:[ th1; th2 ]) in
  let th = merge_theory_ th1.th_theory th2.th_theory in
  make_ ctx hyps (concl th2) proof th

let refl ctx e : t =
  ctx_check_e_uid ctx e;
  let proof () = Proof.(step "refl" ~args:[ a_expr e ]) in
  make_ ctx Expr_set.empty (Expr.app_eq ctx e e) proof None

let congr ctx th1 th2 : t =
  let@ () =
    Error.guard (fun err ->
        Error.wrapf "@[<2>in congr@ th1=`@[%a@]`@ th2=`@[%a@]`@]:" pp th1 pp th2
          err)
  in
  ctx_check_th_uid ctx th1;
  ctx_check_th_uid ctx th2;
  match Expr.unfold_eq (concl th1), Expr.unfold_eq (concl th2) with
  | None, _ -> Error.fail "th1 is non equational"
  | _, None -> Error.fail "th2 is non equational"
  | Some (f, g), Some (t, u) ->
    let t1 = Expr.app ctx f t in
    let t2 = Expr.app ctx g u in
    let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
    let proof () = Proof.(step "congr" ~parents:[ th1; th2 ]) in
    let th = merge_theory_ th1.th_theory th2.th_theory in
    make_ ctx hyps (Expr.app_eq ctx t1 t2) proof th

exception E_subst_non_closed of var * expr

let subst ~recursive ctx th s : t =
  (try
     Var.Map.iter
       (fun v t ->
         if not (Expr.is_closed t) then
           raise_notrace (E_subst_non_closed (v, t)))
       s.m
   with E_subst_non_closed (v, t) ->
     Error.failf (fun k ->
         k "subst: variable %a@ is bound to non-closed term %a" Var.pp v Expr.pp
           t));
  let hyps =
    hyps_ th |> Expr_set.map (fun e -> Expr.subst ~recursive ctx e s)
  in
  let concl = Expr.subst ~recursive ctx (concl th) s in
  let proof () = Proof.(step "subst" ~args:[ a_subst s ] ~parents:[ th ]) in
  make_ ctx hyps concl proof th.th_theory

let sym ctx th : t =
  let@ () =
    Error.guard (fun err -> Error.wrapf "@[<2>in sym@ `@[%a@]`@]:" pp th err)
  in
  ctx_check_th_uid ctx th;
  match Expr.unfold_eq (concl th) with
  | None ->
    Error.failf (fun k -> k "sym: concl of %a@ should be an equation" pp th)
  | Some (t, u) ->
    let proof () = Proof.(step "sym" ~parents:[ th ]) in
    make_ ctx (hyps_ th) (Expr.app_eq ctx u t) proof th.th_theory

let trans ctx th1 th2 : t =
  let@ () =
    Error.guard (fun err ->
        Error.wrapf "@[<2>in trans@ %a@ %a@]:" pp_quoted th1 pp_quoted th2 err)
  in
  ctx_check_th_uid ctx th1;
  ctx_check_th_uid ctx th2;
  match Expr.unfold_eq (concl th1), Expr.unfold_eq (concl th2) with
  | None, _ ->
    Error.failf (fun k -> k "trans: concl of %a@ should be an equation" pp th1)
  | _, None ->
    Error.failf (fun k -> k "trans: concl of %a@ should be an equation" pp th2)
  | Some (t, u), Some (u', v) ->
    if not (Expr.equal u u') then
      Error.failf (fun k ->
          k "@[<2>kernel: trans: conclusions@ of %a@ and %a@ do not match@]" pp
            th1 pp th2);
    let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
    let proof () = Proof.(step "trans" ~parents:[ th1; th2 ]) in
    let th = merge_theory_ th1.th_theory th2.th_theory in
    make_ ctx hyps (Expr.app_eq ctx t v) proof th

let bool_eq ctx th1 th2 : t =
  let@ () =
    Error.guard (fun err ->
        Error.wrapf "@[<hv2>in bool_eq@ th1=%a@ th2=%a@]:" pp_quoted th1
          pp_quoted th2 err)
  in
  ctx_check_th_uid ctx th1;
  ctx_check_th_uid ctx th2;
  match Expr.unfold_eq (concl th2) with
  | None ->
    Error.failf (fun k ->
        k "bool-eq should have a boolean equality as conclusion in %a" pp th2)
  | Some (t, u) ->
    if Expr.equal t (concl th1) then (
      let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
      let proof () = Proof.(step "bool_eq" ~parents:[ th1; th2 ]) in
      let th = merge_theory_ th1.th_theory th2.th_theory in
      make_ ctx hyps u proof th
    ) else
      Error.failf (fun k ->
          k
            "bool-eq: mismatch,@ conclusion of %a@ does not match LHS of %a@ \
             (lhs is: `@[%a@]`)"
            pp_quoted th1 pp_quoted th2 Expr.pp t)

let bool_eq_intro ctx th1 th2 : t =
  let@ () =
    Error.guard (fun err ->
        Error.wrapf "@[<2>in bool_eq_intro@ th1=`@[%a@]`@ th2=`@[%a@]`@]:" pp
          th1 pp th2 err)
  in
  ctx_check_th_uid ctx th1;
  ctx_check_th_uid ctx th2;
  let e1 = concl th1 in
  let e2 = concl th2 in
  let hyps =
    merge_hyps_
      (Expr_set.remove e1 (hyps_ th2))
      (Expr_set.remove e2 (hyps_ th1))
  in
  let proof () = Proof.(step "bool_eq_intro" ~parents:[ th1; th2 ]) in
  let th = merge_theory_ th1.th_theory th2.th_theory in
  make_ ctx hyps (Expr.app_eq ctx e1 e2) proof th

let beta_conv ctx e : t =
  let@ () =
    Error.guard (fun err ->
        Error.wrapf "@[<2>in beta-conv `@[%a@]`:" Expr.pp e err)
  in
  ctx_check_e_uid ctx e;
  match Expr.view e with
  | E_app (f, a) ->
    (match Expr.view f with
    | E_lam (_, ty_v, body) ->
      assert (Expr.equal ty_v (Expr.ty_exn a));
      let rhs = Expr.subst_db_0 ctx body ~by:a in
      let proof () = Proof.(step "beta_conv" ~args:[ a_expr e ]) in
      make_ ctx Expr_set.empty (Expr.app_eq ctx e rhs) proof None
    | _ ->
      Error.failf (fun k ->
          k "not a redex: function %a is not a lambda" Expr.pp f))
  | _ -> Error.failf (fun k -> k "not a redex: %a not an application" Expr.pp e)

let abs ctx v th : t =
  let@ () =
    Error.guard (fun err ->
        Error.wrapf "@[<2>in abs :var %a `@[%a@]`:" Var.pp v pp th err)
  in
  ctx_check_th_uid ctx th;
  ctx_check_e_uid ctx v.v_ty;
  match Expr.unfold_eq th.th_seq.concl with
  | Some (a, b) ->
    let is_in_hyp hyp = Iter.mem ~eq:Var.equal v (Expr.free_vars_iter hyp) in
    if Expr_set.exists is_in_hyp th.th_seq.hyps then
      Error.failf (fun k ->
          k "variable `%a` occurs in an hypothesis@ of %a" Var.pp v pp th);
    let proof () = Proof.(step "abs" ~parents:[ th ]) in
    make_ ctx th.th_seq.hyps
      (Expr.app_eq ctx (Expr.lambda ctx v a) (Expr.lambda ctx v b))
      proof th.th_theory
  | None ->
    Error.failf (fun k -> k "conclusion of `%a`@ is not an equation" pp th)

let new_basic_definition ctx (e : expr) : t * const =
  let@ () =
    Error.guard (fun err ->
        Error.wrapf "@[<2>in new-basic-def@ `@[%a@]`@]:" Expr.pp e err)
  in
  ctx_check_e_uid ctx e;
  match Expr.unfold_eq e with
  | None ->
    Error.failf (fun k ->
        k "new-basic-def: expect an equation `x=rhs`,@ got %a" Expr.pp e)
  | Some (x, rhs) ->
    if Expr.contains rhs ~sub:x then
      Error.failf (fun k ->
          k "RHS %a@ contains variable %a" Expr.pp rhs Expr.pp x);
    if not (Expr.is_closed rhs) then
      Error.failf (fun k -> k "RHS %a@ is not closed" Expr.pp rhs);
    let x_var =
      match Expr.view x with
      | E_var v -> v
      | _ ->
        Error.failf (fun k -> k "LHS must be a variable,@ but got %a" Expr.pp x)
    in

    let fvars = Expr.free_vars rhs in
    let ty_vars_l = Var.Set.to_list fvars in
    (match List.find (fun v -> not (Expr.is_eq_to_type v.v_ty)) ty_vars_l with
    | v ->
      Error.failf (fun k ->
          k
            "RHS contains free variable `@[%a : %a@]`@ which is not a type \
             variable"
            Var.pp v Expr.pp v.v_ty)
    | exception Not_found -> ());

    let c =
      Const.new_const ctx
        ~def:(C_def_expr { vars = ty_vars_l; rhs })
        (Var.name x_var) ty_vars_l (Var.ty x_var)
    in
    let c_e = Expr.const ctx c (List.map (Expr.var ctx) ty_vars_l) in
    let proof () = Proof.(step "new_def" ~args:[ a_expr e ]) in
    let th = make_ ctx Expr_set.empty (Expr.app_eq ctx c_e rhs) proof None in
    th, c

let new_basic_type_definition ctx ?ty_vars:provided_ty_vars ~name ~abs ~repr
    ~thm_inhabited () : New_ty_def.t =
  Error.guard (fun err ->
      Error.wrapf "@[<2>in new-basic-ty-def :name %s@ :thm `@[%a@]`@]:" name pp
        thm_inhabited err)
  @@ fun () ->
  ctx_check_th_uid ctx thm_inhabited;
  if has_hyps thm_inhabited then
    Error.failf (fun k ->
        k "theorem %a must not have any hypothesis" pp thm_inhabited);
  let phi, witness =
    match Expr.view (concl thm_inhabited) with
    | E_app (phi, w) -> phi, w
    | _ ->
      Error.failf (fun k ->
          k "expected conclusion of theorem %a@ to be an application" pp
            thm_inhabited)
  in
  let ty = Expr.ty_exn witness in
  let fvars_phi = Expr.free_vars phi in
  let all_ty_fvars =
    Expr.free_vars_iter witness
    |> Iter.filter (fun v -> Expr.is_eq_to_type v.v_ty)
    |> Var.Set.add_iter fvars_phi
  in
  (match
     Var.Set.find_first (fun v -> not (Expr.is_eq_to_type (Var.ty v))) fvars_phi
   with
  | v ->
    Error.failf (fun k ->
        k
          "free variable %a@ occurs in Phi (in `|- Phi t`)@ and it is not a \
           type variable"
          Var.pp_with_ty v)
  | exception Not_found -> ());

  let ty_vars_l =
    match provided_ty_vars with
    | None -> Var.Set.to_list all_ty_fvars
    | Some l ->
      if not (Var.Set.equal all_ty_fvars (Var.Set.of_list l)) then
        Error.failf (fun k ->
            k
              "list of type variables (%a) in new-basic-ty-def@ does not match \
               %a"
              (Fmt.Dump.list Var.pp)
              (Var.Set.to_list all_ty_fvars)
              (Fmt.Dump.list Var.pp) l);
      l
  in
  let ty_vars_expr_l = ty_vars_l |> CCList.map (Expr.var ctx) in

  Log.debugf 5 (fun k ->
      k
        "(@[new-basic-ty-def@ :name `%s`@ :phi %a@ :ty-vars %a@ :repr `%s`@ \
         :abs `%s`@])"
        name pp_quoted thm_inhabited (Fmt.Dump.list Var.pp) ty_vars_l repr abs);

  let arity = List.length ty_vars_l in

  let tau = Const.new_ty_const ~def:(C_def_ty { arity; phi }) ctx name arity in
  let tau_vars = Expr.const ctx tau ty_vars_expr_l in

  let c_abs =
    let ty = Expr.arrow ctx ty tau_vars in
    Const.new_const ~def:(C_def_ty_abs { arity; phi }) ctx abs ty_vars_l ty
  in
  let c_repr =
    let ty = Expr.arrow ctx tau_vars ty in
    Const.new_const ~def:(C_def_ty_repr { arity; phi }) ctx repr ty_vars_l ty
  in

  let proof () = Proof.(step "new_ty" ~args:[ a_expr phi ]) in

  let abs_x = Var.make "x" tau_vars in
  let abs_thm =
    let abs_x = Expr.var ctx abs_x in
    let repr = Expr.const ctx c_repr ty_vars_expr_l in
    let t = Expr.app ctx repr abs_x in
    let abs = Expr.const ctx c_abs ty_vars_expr_l in
    let abs_t = Expr.app ctx abs t in
    let eqn = Expr.app_eq ctx abs_t abs_x in
    make_ ctx Expr_set.empty eqn proof None
  in

  let repr_x = Var.make "x" ty in
  let repr_thm =
    let repr_x = Expr.var ctx repr_x in
    let abs = Expr.const ctx c_abs ty_vars_expr_l in
    let t1 = Expr.app ctx abs repr_x in
    let repr = Expr.const ctx c_repr ty_vars_expr_l in
    let t2 = Expr.app ctx repr t1 in
    let eq_t2_x = Expr.app_eq ctx t2 repr_x in
    let phi_x = Expr.app ctx phi repr_x in
    make_ ctx Expr_set.empty (Expr.app_eq ctx phi_x eq_t2_x) proof None
  in

  {
    New_ty_def.tau;
    c_repr;
    c_abs;
    fvars = ty_vars_l;
    repr_x;
    repr_thm;
    abs_x;
    abs_thm;
  }

let box ctx (th : t) : t =
  let box = Expr.box ctx th.th_seq in
  let proof () = Proof.(step "box" ~parents:[ th ]) in
  make_ ctx Expr_set.empty box proof th.th_theory

let assume_box ctx (seq : sequent) : t =
  let box = Expr.box ctx seq in
  let seq' = { seq with hyps = Expr_set.add box seq.hyps } in
  let proof () = Proof.(step "assume-box") in
  make_seq_ ctx seq' proof None
