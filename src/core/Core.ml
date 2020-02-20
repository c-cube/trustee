(** {1 Core functions to manipulate Terms and Theorems} *)

module Fmt = CCFormat

module type S = sig
  module KoT : Trustee_kot.S
  open KoT

  type var = Expr.var
  type term = Expr.t
  type thm = Thm.t
  type subst = Expr.Subst.t

  (** {2 Term manipulation} *)

  val unfold_lambda_exn : term -> var * term
  (** [unfold_lambda_exn (λx. t)] is [(x,t)].
      @raise Error if the term is not a lambda. *)

  val unfold_arrow : term -> term list * term
  (** [unfold_arrow (a -> b -> c)] is [[a;b], c] *)

  val free_vars : term -> Expr.Var.Set.t
  (** Free variables of the term *)

  val free_vars_l : term -> var list
  (** Free variables of the term *)

  val pi_l : var list -> term -> term
  (** [pi_l [x1;…;xn] t] is [pi x1. pi x2… pi xn. t] *)

  val lambda_l : var list -> term -> term
  (** [lambda_l [x1;…;xn] t] is [λ x1. λ x2… λ xn. t] *)

  exception Unif_fail of term * term * subst
  (** Error during unification of the given
      pair of subterms, with given partial solution *)

  val unify_exn : ?subst:subst -> term -> term -> subst
  (** [unify_exn t1 t2] tries to unify [t1] and [t2], assuming they
      share no variables.
      @raise Unif_fail if the unification fails. *)

  val unify : ?subst:subst -> term -> term -> (subst, term*term*subst) result
  (** Safe version of {!unify_exn} *)

  (** {2 Rules} *)

  val new_poly_def : string -> term -> thm * term * var list
  (** [new_poly_def c rhs] defines [c := rhs], but starts by closing [rhs]'s
      over its type variables. *)

  val app1_term : term -> thm -> thm
  (** [app1_term f (F |- t=u)] is [F |- (f t)=(f u)] *)

  val app2_term : term -> thm -> thm
  (** [app2_term x (F |- f=g)] is [F |- (f x)=(g x)] *)

  val cut' : thm -> thm -> thm
  (** [cut (F1 |- b) (F2, b |- c)] is [F1, F2 |- c].
      We reimplement it here to show it's redundant. *)

  val eq_trans : term -> term -> term -> thm

  val sym : thm -> thm
  (** [sym (F |- t=u)] is [F |- u=t] *)

  val eq_sym : term -> term -> thm
  (** [eq_sym t u] is [t=u |- u=t] *)

  val eq_reflect : thm -> thm
  (** [eq_reflect (F, a=a, b=b |- t)] is [F |- t].
      Trivial equations in hypothesis are removed. *)

  val cong_fol : term -> term list -> term list -> thm
  (** [cong_fol f l1 l2] is [l1 = l2 |- f l1 = f l2] *)
end

module Make(KoT : Trustee_kot.S)
    : S with module KoT = KoT
= struct
  module KoT = KoT
  open KoT

  module T = Expr
  module Subst = T.Subst

  type var = Expr.var
  type term = Expr.t
  type thm = Thm.t
  type subst = Expr.Subst.t

  (* === TERMS === *)

  let unfold_lambda_exn t = match T.view t with
    | Lambda (x, u) -> x, u
    | _ -> errorf_ (fun k->k"%a is not a lambda" T.pp t)

  let rec unfold_arrow t = match T.view t with
    | Arrow (a, b) -> let args, ty = unfold_arrow b in a::args, ty
    | _ -> [], t

  let iter_immediate ~f t : unit =
    match T.view t with
    | T.Var _ | T.Const _ | T.Type | T.Kind -> ()
    | T.App (a,b) -> f a; f b
    | T.Pi (_, t) | T.Lambda (_,t) -> f t
    | T.Arrow (a,b) -> f a; f b

  let iter ~f t : unit =
    let rec aux t =
      f t;
      CCOpt.iter f (T.ty t);
      iter_immediate ~f:aux t
    in
    aux t

  let free_vars (t:term) : T.Var.Set.t =
    let res = ref T.Var.Set.empty in
    let rec aux bound t =
      CCOpt.iter (aux bound) (T.ty t);
      match T.view t with
      | T.Type | T.Kind | T.Const _ -> ()
      | T.Var vc ->
        let v = T.var_of_c vc in
        if not @@ T.Var.Set.mem v bound then (
          res := T.Var.Set.add v !res
        )
      | T.Pi (v, u) | T.Lambda (v,u) ->
        aux (T.Var.Set.add v bound) u
      | T.App (a,b) | T.Arrow (a,b) -> aux bound a; aux bound b
    in
    aux T.Var.Set.empty t;
    !res

  let free_vars_l t = T.Var.Set.elements @@ free_vars t

  let lambda_l vs body : term = List.fold_right T.lambda vs body

  let pi_l vars t = List.fold_right T.pi vars t

  let app1_term f th : Thm.t = Thm.congr (Thm.refl f) th

  let app2_term x th = Thm.congr th (Thm.refl x)

  let[@inline] eq_lhs t = fst @@ T.unfold_eq_exn t
  let[@inline] eq_rhs t = snd @@ T.unfold_eq_exn t

  exception Unif_fail of term * term * subst

  module T2_tbl = CCHashtbl.Make(struct
      type t = term*term
      let equal (a1,b1) (a2,b2) = T.equal a1 a2 && T.equal b1 b2
      let hash (a,b) = CCHash.combine3 10 (T.hash a) (T.hash b)
      end)

  let unify_exn ?(subst=Subst.empty) t1 t2 : subst =
    let solved = T2_tbl.create 8 in
    let subst = ref subst in
    (* dereference variables following [subst] *)
    let rec deref t = match T.view t with
      | T.Var v ->
        begin match Subst.find !subst (T.var_of_c v) with
          | None -> t
          | Some u -> deref u
        end
      | _ -> t
    in
    let rec occur_check (v:var) t =
      let t = deref t in
      CCOpt.exists (occur_check v) (T.ty t) ||
      begin match T.view t with
        | T.Var v' -> T.Var.equal v (T.var_of_c v')
        | T.App (a,b) | T.Arrow (a,b) -> occur_check v a || occur_check v b
        | T.Type | T.Kind | T.Const _ -> false
        | T.Lambda (v',bod) | T.Pi (v', bod) ->
          not (T.Var.equal v v') && occur_check v bod
    end
    in
    let rec aux t1 t2 : unit =
      if T.equal t1 t2 then ()
      else if T2_tbl.mem solved (t1,t2) then ()
      else (
        T2_tbl.add solved (t1,t2) ();
        (* unify types *)
        begin match T.ty t1, T.ty t2 with
          | None, None -> ()
          | Some ty1, Some ty2 -> aux ty1 ty2
          | Some _, None | None, Some _ -> raise (Unif_fail (t1,t2,!subst))
        end;
        match T.view t1, T.view t2 with
        | (T.Type | T.Kind | T.Const _), _ ->
          raise (Unif_fail (t1,t2,!subst)) (* would be equal *)
        | T.Var v, _ ->
          let v = T.var_of_c v in
          if occur_check v t2 then (
            raise (Unif_fail (t1,t2,!subst))
          );
          subst := Subst.add v t2 !subst;
        | _, T.Var v ->
          let v = T.var_of_c v in
          if occur_check v t2 then (
            raise (Unif_fail (t1,t2,!subst))
          );
          subst := Subst.add v t2 !subst;
        | App (a1,b1), App (a2,b2)
        | Arrow (a1,b1), Arrow (a2,b2) ->
          aux a1 a2; aux b1 b2
        | Pi (v1, bod1), Pi (v2,bod2)
        | Lambda (v1, bod1), Lambda (v2,bod2) ->
          aux (T.Var.ty v1) (T.Var.ty v2);
          (* locally bind [v1 := v2] *)
          if not (T.Var.equal v1 v2) then (
            subst := Subst.add v1 (T.var v2) !subst;
          );
          aux bod1 bod2;
          subst := Subst.remove v1 !subst;
        | (App _ | Lambda _ | Pi _ | Arrow _), _ ->
          raise (Unif_fail (t1,t2,!subst))
      )
    in
    aux t1 t2;
    !subst

  let unify ?subst t1 t2 =
    try Ok (unify_exn ?subst t1 t2)
    with Unif_fail (a,b,s) -> Error (a,b,s)

  let new_poly_def (c:string) (rhs:term) : _ * _ * _ =
    (* make a definition [c := rhs] *)
    let ty = T.ty_exn rhs in
    let vars = free_vars_l ty in
    (* check that we only close over type vars *)
    if not @@ List.for_all (fun v -> T.Var.has_ty v T.type_) vars then (
      errorf_
        (fun k->k"cannot make a polymorphic definition of %s@ using rhs %a@ \
                  the RHS contains non-type free variables"
            c T.pp rhs);
    );
    let ty_closed = pi_l vars ty in
    let rhs_closed = lambda_l vars rhs in
    let eqn =
      T.eq (T.new_var' c ty_closed) rhs_closed
    in
    let thm, c = Thm.new_basic_definition eqn in
    thm, c, vars

  (* === RULES === *)

  let cut' th1 th2 =
    let c1 = Thm.concl th1 in
    if T.Set.mem c1 (Thm.hyps th2) then (
      (* [F1,F2 |- b=c] *)
      let th_bc = Thm.bool_eq_intro th1 th2 in
      (* booleq with [F1 |- b] to get [F1,F2 |- c] *)
      Thm.bool_eq ~eq:th_bc th1
    ) else (
      errorf_
        (fun k->k"cut: conclusion of %a@ does not appear in hypothesis of %a"
            Thm.pp th1 Thm.pp th2)
    )

  let eq_trans a b c =
    Thm.trans (Thm.assume (T.eq a b)) (Thm.assume (T.eq b c))

  let sym (th:Thm.t) : Thm.t =
    try
      (* start with [F |- t=u].
         now by left-congruence with [refl(=)], [F |- ((=) t) = ((=) u)].
         by right-congruence with [refl(t)], [F |- (((=) t) t) = (((=) u) t)].
         in other words, [F |- (t=t)=(u=t)].
         Just do bool_eq_elim with [|- t=t] (refl(t)) and we're done. *)
      let t, u = T.unfold_eq_exn (Thm.concl th) in
      let refl_t = Thm.refl t in
      let th_tequ_eq_ueqt =
        Thm.congr
          (Thm.congr (Thm.refl @@ T.app T.eq_const (T.ty_exn u)) th)
          refl_t
      in
      Thm.bool_eq ~eq:th_tequ_eq_ueqt refl_t
    with Error msg ->
      error_wrapf_ msg (fun k->k"(@[in@ sym %a])" Thm.pp th)

  let eq_sym a b = sym (Thm.assume (T.eq a b))
  (* from [a=b] we get [(a=b) = (a=b)] *)

  (*
    let p =
      let x = T.new_var "x" (T.ty_exn a) in
      T.lambda x (T.eq (T.var x) a)
    in
    Thm.eq_leibniz a b ~p |> Thm.cut (Thm.refl a)
     *)

  let eq_reflect thm =
    let as_trivial_eq t =
      match T.unfold_eq_exn t with
      | t, u when T.equal t u -> Some t
      | _ -> None
      | exception Error _ -> None
    in
    (* find all the [t] such that [(t=t) \in thm.hyps] *)
    let trivial_eqn_members =
      T.Set.fold
        (fun t l -> match as_trivial_eq t with Some x -> T.Set.add x l | None -> l)
        (Thm.hyps thm) T.Set.empty
    in
    (*Format.printf "trivial: %a@." Fmt.Dump.(list T.pp) (T.Set.elements trivial_eqn_members); *)
    if T.Set.is_empty trivial_eqn_members then (
      thm
    ) else (
      T.Set.fold
        (fun t thm -> Thm.cut (Thm.refl t) ~lemma:thm) trivial_eqn_members thm
    )

  let cong_fol f l1 l2 =
    if List.length l1 <> List.length l2 then (
      errorf_ (fun k->k "cong_fol: arity mismatch")
    );
    let rec aux thm l1 l2 = match l1, l2 with
      | [], [] -> thm
      | [], _ | _, [] -> assert false
      | x :: l1', y :: l2' ->
        let thm = Thm.congr thm (Thm.assume @@ T.eq x y) in
        aux thm l1' l2'
    in
    aux (Thm.refl f) l1 l2

  let eq_proof _ _ = assert false (* TODO *)

  (* TODO
  let cong_t f g x y : t =
    instantiate cong_ax (Expr.Subst.of_list [f,
  *)
end
