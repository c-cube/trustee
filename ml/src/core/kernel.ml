
(** {1 Kernel of trust} *)

open Sigs
module H = CCHash

let ctx_id_bits = 5
let ctx_id_mask = (1 lsl ctx_id_bits) - 1

type fixity = Fixity.t

type expr_view =
  | E_kind
  | E_type
  | E_var of var
  | E_bound_var of bvar
  | E_const of const
  | E_app of expr * expr
  | E_lam of expr * expr
  | E_pi of expr * expr

and expr = {
  e_view: expr_view;
  e_ty: expr option lazy_t;
  mutable e_id: int;
  mutable e_flags: int; (* ̵contains: [higher DB var | ctx uid] *)
}

and var = {
  v_name: string;
  v_ty: ty;
}

and bvar = {
  bv_idx: int;
  bv_ty: ty;
}

and ty = expr

and const = {
  c_name: ID.t;
  c_ty: ty;
  mutable c_fixity: fixity;
}

let[@inline] expr_eq (e1:expr) e2 : bool = e1 == e2
let[@inline] expr_hash (e:expr) = H.int e.e_id
let[@inline] expr_compare (e1:expr) e2 : int = CCInt.compare e1.e_id e2.e_id
let[@inline] expr_db_depth e = e.e_flags lsr ctx_id_bits
let[@inline] expr_ctx_uid e : int = e.e_flags land ctx_id_mask

let[@inline] var_eq v1 v2 = v1.v_name = v2.v_name && expr_eq v1.v_ty v2.v_ty
let[@inline] var_hash v1 = H.combine3 5 (H.string v1.v_name) (expr_hash v1.v_ty)
let[@inline] var_pp out v1 = Fmt.string out v1.v_name

module Expr_set = CCSet.Make(struct
    type t = expr
    let compare = expr_compare
    end)

type thm = {
  th_concl: expr;
  th_hyps: Expr_set.t;
  mutable th_flags: int; (* [bool flags|ctx uid] *)
}

let[@inline] thm_ctx_uid th : int = th.th_flags land ctx_id_mask

(* open an application *)
let unfold_app (e:expr) : expr * expr list =
  let rec aux acc e =
    match e.e_view with
    | E_app (f, a) -> aux (a::acc) f
    | _ -> e, acc
  in
  aux [] e

(* debug printer *)
let expr_pp_ out (e:expr) : unit =
  let rec aux k out e =
    let pp = aux k in
    match e.e_view with
    | E_kind -> Fmt.string out "kind"
    | E_type -> Fmt.string out "type"
    | E_var v -> Fmt.string out v.v_name
    | E_bound_var v -> Fmt.fprintf out "x_%d" (k-v.bv_idx-1)
    | E_const c -> ID.pp out c.c_name
    | E_app _ ->
      let f, args = unfold_app e in
      Fmt.fprintf out "(@[%a@ %a@])" pp f (pp_list pp) args
    | E_lam (_ty, bod) ->
      Fmt.fprintf out "(@[\\x_%d:@[%a@].@ %a@])" k pp _ty (aux (k+1)) bod
    | E_pi (ty, bod) ->
      if expr_db_depth bod = 0 then (
        Fmt.fprintf out "(@[%a@ -> %a@])" pp ty (aux (k+1)) bod
      ) else (
        Fmt.fprintf out "(@[@<1>Π x_%d:%a.@ %a@])" k pp ty (aux (k+1)) bod
      )
  in
  aux 0 out e

module Expr_hashcons = Hashcons.Make(struct
    type t = expr

    let equal a b =
      begin match a.e_view, b.e_view with
        | E_kind, E_kind
        | E_type, E_type -> true
        | E_const c1, E_const c2 -> ID.equal c1.c_name c2.c_name
        | E_var v1, E_var v2 -> var_eq v1 v2
        | E_bound_var v1, E_bound_var v2 ->
          v1.bv_idx = v2.bv_idx && expr_eq v1.bv_ty v2.bv_ty
        | E_app (f1,a1), E_app (f2,a2) ->
          expr_eq f1 f2 && expr_eq a1 a2
        | E_lam (ty1,bod1), E_lam (ty2,bod2)
        | E_pi (ty1,bod1), E_pi (ty2,bod2) ->
          expr_eq ty1 ty2 && expr_eq bod1 bod2
        | (E_kind | E_type | E_const _ | E_var _ | E_bound_var _
          | E_app _ | E_lam _ | E_pi _), _ -> false
      end

    let hash e : int =
      match e.e_view with
      | E_kind -> 11
      | E_type -> 12
      | E_const c -> H.combine3 20 (ID.hash c.c_name) (expr_hash c.c_ty)
      | E_var v -> H.combine2 30 (var_hash v)
      | E_bound_var v -> H.combine3 40 (H.int v.bv_idx) (expr_hash v.bv_ty)
      | E_app (f,a) -> H.combine3 50 (expr_hash f) (expr_hash a)
      | E_lam (ty,bod) ->
        H.combine3 60 (expr_hash ty) (expr_hash bod)
      | E_pi (ty,bod) ->
        H.combine3 70 (expr_hash ty) (expr_hash bod)

    let set_id t id =
      assert (t.e_id == -1);
      t.e_id <- id

    let on_new e = ignore (Lazy.force e.e_ty : _ option)
    end)

type ctx = {
  ctx_uid: int;
  ctx_exprs: Expr_hashcons.t;
  ctx_named_thm: thm Str_tbl.t;
  ctx_named_const: const Str_tbl.t;
  ctx_kind: expr lazy_t;
  ctx_type: expr lazy_t;
  ctx_bool: expr lazy_t;
  ctx_bool_c: const lazy_t;
  ctx_eq: expr lazy_t;
  ctx_eq_c: const lazy_t;
  mutable ctx_axioms: thm list;
  mutable ctx_axioms_allowed: bool;
}
(* TODO: derived rules and named rules/theorems *)

let[@inline] ctx_check_e_uid ctx (e:expr) = assert (ctx.ctx_uid == expr_ctx_uid e)
let[@inline] ctx_check_th_uid ctx (th:thm) = assert (ctx.ctx_uid == thm_ctx_uid th)

module Const = struct
  type t = const
  let pp out c = ID.pp out c.c_name
  let[@inline] fixity c = c.c_fixity
  let[@inline] set_fixity c f = c.c_fixity <- f
end

module Var = struct
  type t = var

  let[@inline] name v = v.v_name
  let[@inline] ty v = v.v_ty
  let make v_name v_ty : t = {v_name; v_ty}
  let equal = var_eq
  let hash = var_hash
  let pp = var_pp
  let to_string = Fmt.to_string pp
  let compare a b : int =
    if expr_eq a.v_ty b.v_ty
    then String.compare a.v_name b.v_name
    else expr_compare a.v_ty b.v_ty

  module AsKey = struct
    type nonrec t = t
    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make(AsKey)
  module Set = CCSet.Make(AsKey)
  module Tbl = CCHashtbl.Make(AsKey)
end

module BVar = struct
  type t = bvar
  let make i ty : t = {bv_idx=i; bv_ty=ty}
  let pp out v = Fmt.fprintf out "db_%d" v.bv_idx
  let to_string = Fmt.to_string pp
end

let id_bool = ID.make "bool"
let id_eq = ID.make "="

module Subst = struct
  type t = expr Var.Map.t

  let is_empty = Var.Map.is_empty

  let pp out (s:t) : unit =
    if is_empty s then Fmt.string out "{}"
    else (
      let pp_b out (v,t) =
        Fmt.fprintf out "(@[%a := %a@])" Var.pp v expr_pp_ t
      in
      Fmt.fprintf out "@[<hv>{@,%a@,}@]"
        (pp_iter ~sep:" " pp_b) (Var.Map.to_iter s)
    )

  let to_string = Fmt.to_string pp

  let empty = Var.Map.empty
  let[@inline] bind x t s : t = Var.Map.add x t s
  let size = Var.Map.cardinal
end

module Expr = struct
  type t = expr

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const
    | E_app of t * t
    | E_lam of t * t
    | E_pi of t * t

  let equal = expr_eq
  let hash = expr_hash
  let pp = expr_pp_
  let to_string = Fmt.to_string pp
  let compare = expr_compare
  let db_depth = expr_db_depth
  let[@inline] ty e = Lazy.force e.e_ty
  let[@inline] view e = e.e_view
  let[@inline] ty_exn e = match e.e_ty with
    | lazy None -> assert false
    | lazy (Some ty) -> ty

  let[@inline] is_closed e : bool = db_depth e == 0

  let compute_db_depth_ e : int =
    let d1 = match ty e with
      | None -> 0
      | Some d -> db_depth d
    in
    let d2 = match view e with
      | E_kind | E_type | E_const _ | E_var _ -> 0
      | E_bound_var v -> v.bv_idx
      | E_app (f,g) -> max (db_depth f) (db_depth g)
      | E_lam (ty,bod) | E_pi (ty,bod) ->
        max (db_depth ty) (max 0 (db_depth bod - 1))
    in
    max d1 d2

  (* hashconsing + computing metadata *)
  let make_ (ctx:ctx) view ty : t =
    let e = { e_view=view; e_ty=ty; e_id= -1; e_flags=0 } in
    let e_h = Expr_hashcons.hashcons ctx.ctx_exprs e in
    if e == e_h then (
      (* new term, compute metadata *)
      assert ((ctx.ctx_uid land ctx_id_mask) == ctx.ctx_uid);
      e_h.e_flags <-
        ((compute_db_depth_ e) lsl ctx_id_bits)
        lor ctx.ctx_uid;
    );
    e_h

  let kind ctx = Lazy.force ctx.ctx_kind
  let type_ ctx = Lazy.force ctx.ctx_type

  let[@inline] is_eq_to_kind e = match view e with E_kind -> true | _ -> false
  let[@inline] is_eq_to_type e = match view e with | E_type -> true | _ -> false
  let[@inline] is_a_type e = is_eq_to_type (ty_exn e)
  let is_eq_to_bool e =
    match view e with E_const c -> ID.equal c.c_name id_bool | _ -> false
  let is_a_bool e = is_eq_to_bool (ty_exn e)

  let bool ctx = Lazy.force ctx.ctx_bool
  let eq ctx = Lazy.force ctx.ctx_eq

  let var ctx v : t =
    ctx_check_e_uid ctx v.v_ty;
    make_ ctx (E_var v) (Lazy.from_val (Some v.v_ty))

  let var_name ctx s ty : t = var ctx {v_name=s; v_ty=ty}

  let const ctx c : t =
    ctx_check_e_uid ctx c.c_ty;
    if not (is_closed c.c_ty) then (
      errorf
        (fun k->k"cannot declare constant %a@ with non-closed type %a"
            ID.pp c.c_name pp c.c_ty);
    );
    make_ ctx (E_const c) (Lazy.from_val (Some c.c_ty))

  let new_const ctx name ty : t =
    let id = ID.make name in
    let c = {c_name=id; c_ty=ty; c_fixity=F_normal; } in
    let tc = const ctx c in
    Str_tbl.replace ctx.ctx_named_const name c;
    tc

  let new_ty_const ctx name : ty =
    new_const ctx name (type_ ctx)

  let bvar ctx i ty : t =
    assert (i>=0);
    ctx_check_e_uid ctx ty;
    make_ ctx (E_bound_var {bv_idx=i; bv_ty=ty}) (Lazy.from_val (Some ty))

  (* map immediate subterms *)
  let map ctx ~f (e:t) : t =
    match view e with
    | E_kind | E_type | E_const _ -> e
    | _ ->
      let ty = lazy (
        match ty e with
        | None -> None
        | Some ty -> Some (f false ty)
      ) in
      let view = match view e with
        | E_kind | E_type | E_const _ -> assert false
        | E_var v -> E_var {v with v_ty=f false v.v_ty}
        | E_bound_var v -> E_bound_var {v with bv_ty=f false v.bv_ty}
        | E_app (hd,a) -> E_app (f false hd, f false a)
        | E_lam (tyv, bod) -> E_lam (f false tyv, f true bod)
        | E_pi (tyv, bod) -> E_pi (f false tyv, f true bod)
      in
      make_ ctx view ty

  let iter ~f (e:t) : unit =
    match view e with
    | E_kind | E_type | E_const _ -> ()
    | _ ->
      CCOpt.iter (f false) (ty e);
      match view e with
      | E_kind | E_type | E_const _ -> assert false
      | E_var v -> f false v.v_ty
      | E_bound_var v -> f false v.bv_ty
      | E_app (hd,a) -> f false hd; f false a
      | E_lam (tyv, bod) | E_pi (tyv, bod) -> f false tyv; f true bod

  exception IsSub

  let contains e ~sub : bool =
    let rec aux e =
      if equal e sub then raise_notrace IsSub;
      iter e ~f:(fun _ u -> aux u)
    in
    try aux e; false with IsSub -> true

  let free_vars e : Var.Set.t =
    let set = ref Var.Set.empty in
    let rec aux e =
      match view e with
      | E_var v ->
        set := Var.Set.add v !set;
        aux (Var.ty v)
      | _ ->
        iter e ~f:(fun _ u -> aux u)
    in
    aux e;
    !set

  let db_shift ctx (e:t) (n:int) =
    ctx_check_e_uid ctx e;
    let rec aux e k : t =
      if is_closed e then e
      else (
        match view e with
        | E_bound_var bv ->
          let ty = aux bv.bv_ty k in
          if bv.bv_idx >= k
          then bvar ctx (bv.bv_idx + n) ty
          else bvar ctx bv.bv_idx ty
        | _ ->
          map ctx e ~f:(fun inbind u -> aux u (if inbind then k+1 else k))
      )
    in
    if n = 0 then e else aux e 0

  let subst ctx e (subst:t Var.Map.t) : t =
    let rec aux e k =
      match view e with
      | E_var v ->
        begin match Var.Map.find v subst with
          | u -> db_shift ctx u k
          | exception Not_found -> e
        end
      | _ ->
        map ctx e ~f:(fun inb u -> aux u (if inb then k+1 else k))
    in
    aux e 0

  let abs_on_ ctx (v:var) (e:t) : t =
    ctx_check_e_uid ctx v.v_ty;
    ctx_check_e_uid ctx e;
    if not (is_closed v.v_ty) then (
      errorf (fun k->k"cannot abstract on variable with non closed type %a" pp v.v_ty)
    );
    let db0 = bvar ctx 0 v.v_ty in
    let body = db_shift ctx e 1 in
    subst ctx body (Var.Map.singleton v db0)

  (* replace DB0 in [e] with [u] *)
  let subst_db_0 ctx e ~by:u : t =
    ctx_check_e_uid ctx e;
    ctx_check_e_uid ctx u;
    let rec aux e k : t =
      match view e with
      | E_bound_var bv when bv.bv_idx = k ->
        (* replace here *)
        db_shift ctx u k
      | _ ->
        map ctx e ~f:(fun inb u -> aux u (if inb then k+1 else k))
    in
    if is_closed e then e else aux e 0

  let ty_app_ ctx f a =
    let ty_f = ty_exn f in
    match view ty_f with
    | E_pi (ty_v, body) ->
      let tya = ty_exn a in
      if not (equal ty_v tya) then (
        errorf (fun k->k"cannot apply f (= `@[%a@]`)@ to a (= `@[%a@]`)@ \
                f expects argument of type %a, but a has type %a"
          pp f pp a pp ty_v pp tya)
      );
      let ty2 = subst_db_0 ctx body ~by:tya in
      ty2
    | _ ->
      errorf (fun k->k"cannot apply `@[%a@]`@ of type %a"
        pp f pp ty_f)

  let app ctx f a : t =
    ctx_check_e_uid ctx f;
    ctx_check_e_uid ctx a;
    let ty = lazy (Some (ty_app_ ctx f a)) in
    make_ ctx (E_app (f,a)) ty

  let rec app_l ctx f l = match l with
    | [] -> f
    | x :: l' ->
      let f = app ctx f x in
      app_l ctx f l'

  let app_eq ctx a b =
    let f = eq ctx in
    let f = app ctx f (ty_exn a) in
    let f = app ctx f a in
    let f = app ctx f b in
    f

  let pi_db ctx ~ty_v bod : t =
    ctx_check_e_uid ctx ty_v;
    ctx_check_e_uid ctx bod;
    if not (is_eq_to_type ty_v) && not (is_a_type ty_v) then (
      errorf (fun k->k"pi: variable must be a type of have type Type, not %a"
                 pp ty_v);
    );
    if not (is_eq_to_type (ty_exn bod)) && not (is_eq_to_kind (ty_exn bod)) then (
      errorf (fun k->k"pi: body must be a type of have type Type,@ not %a"
                 pp (ty_exn bod))
    );
    let ty = Lazy.from_val (Some (type_ ctx)) in
    make_ ctx (E_pi (ty_v, bod)) ty

  let arrow ctx a b : t =
    pi_db ctx ~ty_v:a (db_shift ctx b 1)

  let arrow_l ctx l ret : t = CCList.fold_right (arrow ctx) l ret

  let lambda_db ctx ~ty_v bod : t =
    ctx_check_e_uid ctx ty_v;
    ctx_check_e_uid ctx bod;
    let ty = lazy (
      (* type of [λx:a. t] is [Πx:a. typeof(b)]. *)
      Some (pi_db ctx ~ty_v (ty_exn bod))
    ) in
    make_ ctx (E_lam (ty_v, bod)) ty

  let lambda ctx v bod =
    let bod = abs_on_ ctx v bod in
    lambda_db ctx ~ty_v:v.v_ty bod

  let lambda_l ctx = CCList.fold_right (lambda ctx)

  let pi ctx v bod =
    let bod = abs_on_ ctx v bod in
    pi_db ctx ~ty_v:v.v_ty bod

  let pi_l ctx = CCList.fold_right (pi ctx)

  let unfold_app = unfold_app

  let unfold_eq e =
    let f, l = unfold_app e in
    match view f, l with
    | E_const {c_name;_}, [_;a;b] when ID.equal c_name id_eq -> Some(a,b)
    | _ -> None

  let[@inline] as_const e = match e.e_view with
    | E_const c -> Some c
    | _ -> None

  let[@inline] as_const_exn e = match e.e_view with
    | E_const c -> c
    | _ -> errorf (fun k->k"%a is not a constant" pp e)

  module AsKey = struct
    type nonrec t = t
    let equal = equal
    let compare = compare
    let hash = hash
  end

  module Map = CCMap.Make(AsKey)
  module Set = Expr_set
  module Tbl = CCHashtbl.Make(AsKey)
end

(** {2 Context}

    The context is storing the term state, list of axioms,
    and other parameters.
    Terms from distinct contexts must never be mixed. *)
module Ctx = struct
  type t = ctx

  let uid_ = ref 0

  let create () : t =
    let ctx_uid = !uid_ land ctx_id_mask in
    incr uid_;
    let rec ctx = {
      ctx_uid;
      ctx_exprs=Expr_hashcons.create ~size:2_048 ();
      ctx_named_thm=Str_tbl.create 32;
      ctx_named_const=Str_tbl.create 32;
      ctx_axioms=[];
      ctx_axioms_allowed=true;
      ctx_kind=lazy (Expr.make_ ctx E_kind (Lazy.from_val None));
      ctx_type=lazy (
        let kind = Expr.kind ctx in
        Expr.make_ ctx E_type (Lazy.from_val (Some kind))
      );
      ctx_bool_c=lazy (
        let typ = Expr.type_ ctx in
        {c_name=id_bool; c_ty=typ; c_fixity=F_normal; }
      );
      ctx_bool=lazy (
        Expr.const ctx (Lazy.force ctx.ctx_bool_c)
      );
      ctx_eq_c=lazy (
        let typ = Expr.(
            let type_ = type_ ctx in
            let db0 = bvar ctx 0 type_ in
            pi_db ctx ~ty_v:type_ @@ arrow ctx db0 @@ arrow ctx db0 @@ bool ctx
          ) in
        {c_name=id_eq; c_ty=typ; c_fixity=F_normal; }
      );
      ctx_eq=lazy (
        Expr.const ctx (Lazy.force ctx.ctx_eq_c)
      );
    } in
    ctx

  let pledge_no_more_axioms self =
    if self.ctx_axioms_allowed then (
      Log.debugf 5 (fun k->k "pledge no more axioms");
      self.ctx_axioms_allowed <- false;
    )

  let axioms self k = List.iter k self.ctx_axioms

  let find_const_by_name self s : const option =
    Str_tbl.get self.ctx_named_const s
end

module New_ty_def = struct
  type t = {
    tau: expr;
    (** the new type constructor *)
    fvars: var list;
    c_abs: expr;
    (** Function from the general type to `tau` *)
    c_repr: expr;
    (** Function from `tau` back to the general type *)
    abs_thm: thm;
    (** `abs_thm` is `|- abs (repr x) = x` *)
    abs_x: var;
    repr_thm: thm;
    (** `repr_thm` is `|- Phi x <=> repr (abs x) = x` *)
    repr_x: var;
  }
end

module Thm = struct
  type t = thm

  let[@inline] concl self = self.th_concl
  let[@inline] hyps_ self = self.th_hyps
  let[@inline] hyps_iter self k = Expr_set.iter k self.th_hyps
  let[@inline] hyps_l self = Expr_set.elements self.th_hyps
  let[@inline] has_hyps self = Expr_set.is_empty self.th_hyps
  let n_hyps self = Expr_set.cardinal self.th_hyps

  let pp out (th:t) =
    if has_hyps th then (
      Fmt.fprintf out "@[<hv1>%a@ |-@ %a@]" (pp_list Expr.pp) (hyps_l th)
        Expr.pp (concl th)
    ) else (
      Fmt.fprintf out "@[<1>|-@ %a@]" Expr.pp (concl th)
    )

  let to_string = Fmt.to_string pp

  (** {3 Deduction rules} *)

  let make_ ctx hyps concl : t =
    let th_flags = ctx.ctx_uid in
    { th_flags; th_concl=concl; th_hyps=hyps; }

  let is_bool_ ctx e : bool =
    let ty = Expr.ty_exn e in
    Expr.equal (Expr.bool ctx) ty

  let[@inline] wrap_exn k f =
    try f()
    with e ->
      errorf ~src:e k

  let assume ctx (e:Expr.t) : t =
    wrap_exn (fun k->k"in assume `@[%a@]`" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    if not (is_bool_ ctx e) then (
      error "assume takes a boolean"
    );
    make_ ctx (Expr.Set.singleton e) e

  let axiom ctx e : t =
    wrap_exn (fun k->k"in axiom `@[%a@]`" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    if not ctx.ctx_axioms_allowed then (
      error "the context does not accept new axioms, see `pledge_no_more_axioms`"
    );
    if not (is_bool_ ctx e) then (
      error "axiom takes a boolean"
    );
    make_ ctx Expr.Set.empty e

  let merge_hyps_ = Expr.Set.union

  let cut ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in cut@ th1=`@[%a@]`@ th2=`@[%a@]`@]" pp th1 pp th2)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    let b = concl th1 in
    let hyps = merge_hyps_ (hyps_ th1) (Expr.Set.remove b (hyps_ th2)) in
    make_ ctx hyps (concl th2)

  let refl ctx e : t =
    ctx_check_e_uid ctx e;
    make_ ctx Expr.Set.empty (Expr.app_eq ctx e e)

  let congr ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in congr@ th1=`@[%a@]`@ th2=`@[%a@]`@]" pp th1 pp th2)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th1), Expr.unfold_eq (concl th2) with
    | None, _ -> error "th1 is non equational"
    | _, None -> error "th2 is non equational"
    | Some (f,g), Some (t,u) ->
      let t1 = Expr.app ctx f t in
      let t2 = Expr.app ctx g u in
      let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
      make_ ctx hyps (Expr.app_eq ctx t1 t2)

  let congr_ty ctx th ty : t =
    wrap_exn (fun k->k"@[<2>in congr_ty@ th=`@[%a@]`@ ty=%a@]" pp th Expr.pp ty)
    @@ fun () ->
    ctx_check_th_uid ctx th;
    ctx_check_e_uid ctx ty;
    if not (Expr.is_a_type ty) then (
      errorf (fun k->k"congr_ty: argument %a should be a type" Expr.pp ty);
    );
    match Expr.unfold_eq (concl th) with
    | None ->
      errorf (fun k->k"congr_ty: conclusion of %a@ should be an equation" pp th)
    | Some (t, u) ->
      let c = Expr.app_eq ctx (Expr.app ctx t ty) (Expr.app ctx u ty) in
      make_ ctx (hyps_ th) c

  exception E_subst_non_closed of var * expr

  let subst ctx th s : t =
    begin try
        Var.Map.iter (fun v t ->
            if not (Expr.is_closed t) then raise_notrace (E_subst_non_closed (v,t)))
          s
      with
      | E_subst_non_closed (v,t) ->
        errorf(fun k->k"subst: variable %a@ is bound to non-closed term %a"
                  Var.pp v Expr.pp t)
    end;
    let hyps = hyps_ th |> Expr.Set.map (fun e -> Expr.subst ctx e s) in
    let concl = Expr.subst ctx (concl th) s in
    make_ ctx hyps concl

  let sym ctx th : t =
    wrap_exn (fun k->k"@[<2>in sym@ `@[%a@]`@]" pp th) @@ fun () ->
    ctx_check_th_uid ctx th;
    match Expr.unfold_eq (concl th) with
    | None -> errorf (fun k->k"sym: concl of %a@ should be an equation" pp th)
    | Some (t,u) ->
      make_ ctx (hyps_ th) (Expr.app_eq ctx u t)

  let bool_eq ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in bool_eq@ th1=`@[%a@]`@ th2=`@[%a@]`@]"
                 pp th1 pp th2) @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th2) with
    | None ->
      errorf (fun k->k"bool-eq should have a boolean equality as conclusion in %a"
                 pp th2)
    | Some (t, u) ->
      if Expr.equal t (concl th1) then (
        let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
        make_ ctx hyps u
      ) else (
        errorf (fun k->k"bool-eq: mismatch,@ conclusion of %a@ does not match LHS of %a"
                   pp th1 pp th2)
      )

  let bool_eq_intro ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in bool_eq_intro@ th1=`@[%a@]`@ th2=`@[%a@]`@]"
                 pp th1 pp th2) @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    let e1 = concl th1 in
    let e2 = concl th2 in
    let hyps =
      merge_hyps_
        (Expr.Set.remove e1 (hyps_ th2))
        (Expr.Set.remove e2 (hyps_ th1))
    in
    make_ ctx hyps (Expr.app_eq ctx e1 e2)

  let beta_conv ctx e : t =
    wrap_exn (fun k->k"@[<2>in beta-conv `@[%a@]`" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    match Expr.view e with
    | E_app (f, a) ->
      (match Expr.view f with
       | E_lam (ty_v, body) ->
         assert (Expr.equal ty_v (Expr.ty_exn e));
         let rhs = Expr.subst_db_0 ctx body ~by:a in
         make_ ctx Expr.Set.empty (Expr.app_eq ctx e rhs)
       | _ ->
         errorf (fun k->k"not a redex: function %a is not a lambda" Expr.pp f)
      )
    | _ ->
      errorf (fun k->k"not a redex: %a not an application" Expr.pp e)

  let new_basic_definition ctx (e:expr) : t * expr =
    wrap_exn (fun k->k"@[<2>in new-basic-def `@[%a@]`@]" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    match Expr.unfold_eq e with
    | None ->
      errorf (fun k->k"new-basic-def: expect an equation `x=rhs`,@ got %a" Expr.pp e)
    | Some (x, rhs) ->
      if Expr.contains rhs ~sub:x then (
        errorf (fun k->k"RHS %a@ contains variable %a" Expr.pp rhs Expr.pp x)
      );
      if not (Expr.is_closed rhs) then (
        errorf (fun k->k"RHS %a@ is not closed" Expr.pp rhs);
      );
      let x_var = match Expr.view x with
        | E_var v -> v
        | _ ->
          errorf (fun k-> k "LHS must be a variable,@ but got %a" Expr.pp x)
      in
      let c = Expr.new_const ctx (Var.name x_var) (Var.ty x_var) in
      let th = make_ ctx Expr.Set.empty (Expr.app_eq ctx c rhs) in
      th, c

  let new_basic_type_definition ctx
      ~name ~abs ~repr ~thm_inhabited () : New_ty_def.t =
    wrap_exn (fun k->k"@[<2>in new-basic-ty-def %s `@[%a@]`@]"
                 name pp thm_inhabited) @@ fun () ->
    ctx_check_th_uid ctx thm_inhabited;
    if has_hyps thm_inhabited then (
      errorf (fun k->k"theorem %a must not have any hypothesis" pp thm_inhabited);
    );
    let phi, witness = match Expr.view (concl thm_inhabited) with
      | E_app (phi,w) -> phi, w
      | _ ->
        errorf (fun k->k"expected conclusion of theorem %a@ to be an application"
                   pp thm_inhabited);
    in
    (* the concrete type *)
    let ty = Expr.ty_exn witness in
    (* check that all free variables are type variables *)
    let fvars = Expr.free_vars (concl thm_inhabited) in
    begin match
        Var.Set.find_first (fun v -> not (Expr.is_eq_to_type (Var.ty v))) fvars
      with
      | v -> errorf (fun k->k"free variable %a is not a type variable" Var.pp v)
      | exception Not_found -> ()
    end;

    let fvars_l = Var.Set.to_list fvars in
    let fvars_expr = fvars_l |> List.rev_map (Expr.var ctx) in

    (* construct new type and mapping functions *)
    let tau = Expr.new_const ctx name (Expr.pi_l ctx fvars_l (Expr.type_ ctx)) in
    let tau_vars = Expr.app_l ctx tau fvars_expr in

    let c_abs =
      let ty = Expr.pi_l ctx fvars_l @@ Expr.arrow ctx ty tau_vars in
      Expr.new_const ctx abs ty
    in
    let c_repr =
      let ty = Expr.pi_l ctx fvars_l @@ Expr.arrow ctx tau_vars ty in
      Expr.new_const ctx repr ty
    in

    let abs_x = Var.make "x" tau_vars in
    (* `|- abs (repr x) = x` *)
    let abs_thm =
      let abs_x = Expr.var ctx abs_x in
      let repr = Expr.app_l ctx c_repr fvars_expr in
      let t = Expr.app ctx repr abs_x in
      let abs = Expr.app_l ctx c_abs fvars_expr in
      let abs_t = Expr.app ctx abs t in
      let eqn = Expr.app_eq ctx abs_t abs_x in
      make_ ctx Expr.Set.empty eqn
    in

    let repr_x = Var.make "x" ty in
    (* `|- Phi x <=> repr (abs x) = x` *)
    let repr_thm =
      let repr_x = Expr.var ctx repr_x in
      let abs = Expr.app_l ctx c_abs fvars_expr in
      let t1 = Expr.app ctx abs repr_x in
      let repr = Expr.app_l ctx c_repr fvars_expr in
      let t2 = Expr.app ctx repr t1 in
      let eq_t2_x = Expr.app_eq ctx t2 repr_x in
      let phi_x = Expr.app ctx phi repr_x in
      make_ ctx Expr.Set.empty (Expr.app_eq ctx phi_x eq_t2_x)
    in

    {New_ty_def.
      tau; c_repr; c_abs; fvars=fvars_l; repr_x;
      repr_thm; abs_x; abs_thm}

end

