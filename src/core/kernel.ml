
(** {1 Kernel of trust} *)

open Sigs
module H = CCHash

let ctx_id_bits = 5
let ctx_id_mask = (1 lsl ctx_id_bits) - 1

type fixity = Fixity.t
type location = Loc.t

type expr_view =
  | E_kind
  | E_type
  | E_var of var
  | E_bound_var of bvar
  | E_const of const * expr list
  | E_app of expr * expr
  | E_lam of expr * expr
  | E_arrow of expr * expr

and expr = {
  e_view: expr_view;
  e_ty: expr option lazy_t;
  mutable e_id: int;
  mutable e_flags: int; (* ̵contains: [higher DB var | 5:ctx uid] *)
}

and var = {
  v_name: string;
  v_ty: ty;
}
and ty_var = var

and bvar = {
  bv_idx: int;
  bv_ty: ty;
}

and ty = expr

and const = {
  c_name: ID.t;
  c_args: const_args;
  c_ty: ty; (* free vars = c_ty_vars *)
  c_def_loc: location option;
  mutable c_fixity: fixity;
}
and ty_const = const

and const_args =
  | C_ty_vars of ty_var list
  | C_arity of int (* for type constants *)

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
(* TODO:
   - store set of axioms used
   *)

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
    let pp' = aux' k in
    match e.e_view with
    | E_kind -> Fmt.string out "kind"
    | E_type -> Fmt.string out "type"
    | E_var v -> Fmt.string out v.v_name
    | E_bound_var v ->
      let idx = v.bv_idx in
      if idx<k then Fmt.fprintf out "x_%d" (k-idx-1)
      else Fmt.fprintf out "%%db_%d" (idx-k)
    | E_const (c,[]) -> ID.pp out c.c_name
    | E_const (c,args) ->
      Fmt.fprintf out "(@[%a@ %a@])" ID.pp c.c_name (pp_list pp') args
    | E_app _ ->
      let f, args = unfold_app e in
      begin match f.e_view, args with
        | E_const (c, [_]), [a;b] when ID.name c.c_name = "=" ->
          Fmt.fprintf out "@[%a@ = %a@]" pp' a pp' b
        | _ ->
          Fmt.fprintf out "@[%a@ %a@]" pp' f (pp_list pp') args
      end
    | E_lam (_ty, bod) ->
      Fmt.fprintf out "(@[\\x_%d:@[%a@].@ %a@])" k pp' _ty (aux (k+1)) bod
    | E_arrow(a,b) ->
      Fmt.fprintf out "@[%a@ -> %a@]" pp' a pp b

  and aux' k out e = match e.e_view with
    | E_kind | E_type | E_var _ | E_const (_, []) -> aux k out e
    | _ -> Fmt.fprintf out "(%a)" (aux k) e
  in
  aux 0 out e

module Expr_hashcons = Hashcons.Make(struct
    type t = expr

    let equal a b =
      begin match a.e_view, b.e_view with
        | E_kind, E_kind
        | E_type, E_type -> true
        | E_const (c1,l1), E_const (c2,l2) ->
          ID.equal c1.c_name c2.c_name && CCList.equal expr_eq l1 l2
        | E_var v1, E_var v2 -> var_eq v1 v2
        | E_bound_var v1, E_bound_var v2 ->
          v1.bv_idx = v2.bv_idx && expr_eq v1.bv_ty v2.bv_ty
        | E_app (f1,a1), E_app (f2,a2) ->
          expr_eq f1 f2 && expr_eq a1 a2
        | E_lam (ty1,bod1), E_lam (ty2,bod2) ->
          expr_eq ty1 ty2 && expr_eq bod1 bod2
        | E_arrow(a1,b1), E_arrow(a2,b2) ->
          expr_eq a1 a2 && expr_eq b1 b2
        | (E_kind | E_type | E_const _ | E_var _ | E_bound_var _
          | E_app _ | E_lam _ | E_arrow _), _ -> false
      end

    let hash e : int =
      match e.e_view with
      | E_kind -> 11
      | E_type -> 12
      | E_const (c,l) ->
        H.combine4 20 (ID.hash c.c_name) (expr_hash c.c_ty) (H.list expr_hash l)
      | E_var v -> H.combine2 30 (var_hash v)
      | E_bound_var v -> H.combine3 40 (H.int v.bv_idx) (expr_hash v.bv_ty)
      | E_app (f,a) -> H.combine3 50 (expr_hash f) (expr_hash a)
      | E_lam (ty,bod) ->
        H.combine3 60 (expr_hash ty) (expr_hash bod)
      | E_arrow (a,b) -> H.combine3 80 (expr_hash a) (expr_hash b)

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
  ctx_eq_c: const lazy_t;
  mutable ctx_axioms: thm list;
  mutable ctx_axioms_allowed: bool;
}
(* TODO: derived rules and named rules/theorems *)

let[@inline] ctx_check_e_uid ctx (e:expr) = assert (ctx.ctx_uid == expr_ctx_uid e)
let[@inline] ctx_check_th_uid ctx (th:thm) = assert (ctx.ctx_uid == thm_ctx_uid th)

let id_bool = ID.make "bool"
let id_eq = ID.make "="

module Const = struct
  type t = const
  let pp out c = ID.pp out c.c_name
  let to_string = Fmt.to_string pp
  let def_loc c = c.c_def_loc
  let[@inline] fixity c = c.c_fixity
  let[@inline] set_fixity c f = c.c_fixity <- f
  let[@inline] equal c1 c2 = ID.equal c1.c_name c2.c_name

  type args = const_args =
    | C_ty_vars of ty_var list
    | C_arity of int
  let[@inline] args c = c.c_args
  let[@inline] ty c = c.c_ty

  let pp_args out = function
    | C_arity n -> Fmt.fprintf out "arity %d" n
    | C_ty_vars vs -> Fmt.fprintf out "ty_vars %a" (Fmt.Dump.list var_pp) vs

  let[@inline] eq ctx = Lazy.force ctx.ctx_eq_c
  let[@inline] bool ctx = Lazy.force ctx.ctx_bool_c
  let is_eq_to_bool c = ID.equal c.c_name id_bool
  let is_eq_to_eq c = ID.equal c.c_name id_bool
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
  let[@inline] bind' s x t : t = Var.Map.add x t s
  let size = Var.Map.cardinal
end

module Expr = struct
  type t = expr

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const * expr list
    | E_app of t * t
    | E_lam of t * t
    | E_arrow of t * t

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
      | E_bound_var v -> v.bv_idx+1
      | E_app (a,b) | E_arrow (a,b) -> max (db_depth a) (db_depth b)
      | E_lam (ty,bod) ->
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
      ctx_check_e_uid ctx e_h;
    );
    e_h

  let kind ctx = Lazy.force ctx.ctx_kind
  let type_ ctx = Lazy.force ctx.ctx_type

  let[@inline] is_eq_to_type e = match view e with | E_type -> true | _ -> false
  let[@inline] is_a_type e = is_eq_to_type (ty_exn e)
  let is_eq_to_bool e =
    match view e with E_const (c,[]) -> ID.equal c.c_name id_bool | _ -> false
  let is_a_bool e = is_eq_to_bool (ty_exn e)

  let bool ctx = Lazy.force ctx.ctx_bool

  let var ctx v : t =
    ctx_check_e_uid ctx v.v_ty;
    make_ ctx (E_var v) (Lazy.from_val (Some v.v_ty))

  let var_name ctx s ty : t = var ctx {v_name=s; v_ty=ty}

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
        | E_arrow (a,b) -> E_arrow (f false a, f false b)
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
      | E_lam (tyv, bod) -> f false tyv; f true bod
      | E_arrow (a,b) -> f false a; f false b

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

  let new_const_ ctx ?def_loc name args ty : const =
    let id = ID.make name in
    let c = {
      c_name=id; c_ty=ty; c_args=args;
      c_def_loc=def_loc; c_fixity=F_normal;
    } in
    Str_tbl.replace ctx.ctx_named_const name c;
    c

  let new_const ctx ?def_loc name ty_vars ty : const =
    let fvars = free_vars ty in
    if not (Var.Set.equal fvars (Var.Set.of_list ty_vars)) then (
      errorf
        (fun k->k
            "Kernel.new_const: type variables should be [@[%a@]],@ \
             but RHS has free type variables %a"
            (Fmt.Dump.list Var.pp) ty_vars Var.Set.(pp Var.pp) fvars)
    );
    new_const_ ctx ?def_loc name (C_ty_vars ty_vars) ty

  let new_ty_const ctx ?def_loc name n : ty_const =
    new_const_ ctx name ?def_loc (C_arity n) (type_ ctx)

  let db_shift ctx (e:t) (n:int) =
    ctx_check_e_uid ctx e;
    let is_closed_ty e = match e.e_ty with
      | lazy None -> true
      | lazy (Some ty) -> is_closed ty
    in
    let rec aux e k : t =
      if is_closed e && is_closed_ty e then e
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
    assert (n >= 0);
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

  let const ctx c args : t =
    ctx_check_e_uid ctx c.c_ty;
    let ty =
      match c.c_args with
      | C_arity n ->
        if List.length args <> n then (
          errorf
            (fun k->k"constant %a requires %d arguments, but is applied to %d"
                ID.pp c.c_name
                n (List.length args));
        );
        Lazy.from_val (Some c.c_ty)
      | C_ty_vars ty_vars ->
        if List.length args <> List.length ty_vars then (
          errorf
            (fun k->k"constant %a requires %d arguments, but is applied to %d"
                ID.pp c.c_name
                (List.length ty_vars) (List.length args));
        );
        lazy (
          let sigma = List.fold_left2 Subst.bind' Subst.empty ty_vars args in
          Some (subst ctx c.c_ty sigma)
        )
    in
    make_ ctx (E_const (c,args)) ty

  let eq ctx ty =
    let eq = Lazy.force ctx.ctx_eq_c in
    const ctx eq [ty]

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

  let ty_app_ f a =
    let ty_f = ty_exn f in
    let tya = ty_exn a in
    match view ty_f with
    | E_arrow (ty1, ty2) ->
      if not (equal tya ty1) then (
        errorf
          (fun k->
             k"@[<2>kernel: cannot apply function@ `@[%a@]`@ \
               to argument `@[%a@]`@]@];@ \
               @[function expects argument of type@ `@[%a@]`,@ \
               but arg has type `@[%a@]`@]"
          pp f pp a pp ty1 pp tya)
      );
      ty2
    | _ ->
      errorf
        (fun k->k
            "@[kernel: cannot apply `@[%a@]`@ of type %a;@ it is not a function@]"
            pp f pp ty_f)

  let app ctx f a : t =
    ctx_check_e_uid ctx f;
    ctx_check_e_uid ctx a;
    let ty = lazy (Some (ty_app_ f a)) in
    let e = make_ ctx (E_app (f,a)) ty in
    ignore (Lazy.force e.e_ty);
    e

  let rec app_l ctx f l = match l with
    | [] -> f
    | x :: l' ->
      let f = app ctx f x in
      app_l ctx f l'

  let app_eq ctx a b =
    let f = eq ctx (ty_exn a) in
    let f = app ctx f a in
    let f = app ctx f b in
    f

  let arrow ctx a b : t =
    if not (is_a_type a) || not (is_a_type b) then (
      errorf (fun k->k"arrow: both arguments must be types");
    );
    let ty = Lazy.from_val (Some (type_ ctx)) in
    make_ ctx (E_arrow (a,b)) ty

  let arrow_l ctx l ret : t = CCList.fold_right (arrow ctx) l ret

  let lambda_db ctx ~ty_v bod : t =
    ctx_check_e_uid ctx ty_v;
    ctx_check_e_uid ctx bod;
    if not (is_a_type ty_v) then (
      errorf (fun k->k"lambda: variable must have a type as type, not %a"
                 pp ty_v);
    );
    let ty = lazy (
      (* type of [λx:a. t] is [a -> typeof(t)] if [a] is a type *)
      Some (arrow ctx ty_v (ty_exn bod))
    ) in
    make_ ctx (E_lam (ty_v, bod)) ty

  let lambda ctx v bod =
    let bod = abs_on_ ctx v bod in
    lambda_db ctx ~ty_v:v.v_ty bod

  let lambda_l ctx = CCList.fold_right (lambda ctx)

  let unfold_app = unfold_app

  let unfold_eq e =
    let f, l = unfold_app e in
    match view f, l with
    | E_const ({c_name;_}, [_]), [a;b] when ID.equal c_name id_eq -> Some(a,b)
    | _ -> None

  let[@inline] as_const e = match e.e_view with
    | E_const (c,args) -> Some (c,args)
    | _ -> None

  let[@inline] as_const_exn e = match e.e_view with
    | E_const (c,args) -> c, args
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

(*$inject
  let ctx = Ctx.create ()
  let bool = Expr.bool ctx
  let type_ = Expr.type_ ctx
  let tau = Expr.const ctx (Expr.new_ty_const ctx "tau" 0) []
  let lambda v t = Expr.lambda ctx v t
  let v' s ty = Var.make s ty
  let v x = Expr.var ctx x
  let (@->) a b = Expr.arrow ctx a b
  let (@@) a b = Expr.app ctx a b
  let a = Expr.const ctx (Expr.new_const ctx "a0" [] tau) []
  let b = Expr.const ctx (Expr.new_const ctx "b0" [] tau) []
  let c = Expr.const ctx (Expr.new_const ctx "c0" [] tau) []
  let f1: const = Expr.new_const ctx "f1" [] (tau @-> tau)
  let eq = Expr.app_eq ctx

  let must_fail f = try ignore (f()); false with _ -> true
*)

(*$T
  must_fail (fun() -> a @-> b)
  Expr.equal (tau @-> bool) (tau @-> bool)
*)


(** {2 Toplevel goals} *)
module Goal = struct
  type t = {
    hyps: Expr.Set.t;
    concl: Expr.t;
  }

  let make hyps concl : t = {hyps; concl}
  let make_l h c = make (Expr.Set.of_list h) c
  let make_nohyps c : t = make Expr.Set.empty c

  let[@inline] concl g = g.concl
  let[@inline] hyps g = g.hyps
  let[@inline] hyps_iter g = Expr.Set.to_iter g.hyps

  let pp out (self:t) : unit =
    if Expr.Set.is_empty self.hyps then (
      Fmt.fprintf out "@[?-@ %a@]" Expr.pp self.concl
    ) else (
      Fmt.fprintf out "@[<hv>%a@ ?-@ %a@]"
        (pp_iter ~sep:", " Expr.pp) (hyps_iter self)
        Expr.pp self.concl
    )
  let to_string = Fmt.to_string pp
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
        {c_name=id_bool; c_ty=typ; c_def_loc=None;
         c_fixity=F_normal; c_args=C_arity 0; }
      );
      ctx_bool=lazy (
        Expr.const ctx (Lazy.force ctx.ctx_bool_c) []
      );
      ctx_eq_c=lazy (
        let type_ = Expr.type_ ctx in
        let a_ = Var.make "a" type_ in
        let ea = Expr.var ctx a_ in
        let typ = Expr.(arrow ctx ea @@ arrow ctx ea @@ bool ctx) in
        {c_name=id_eq; c_args=C_ty_vars [a_]; c_ty=typ;
         c_def_loc=None; c_fixity=F_normal; }
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
    tau: ty_const;
    (** the new type constructor *)
    fvars: var list;
    c_abs: const;
    (** Function from the general type to `tau` *)
    c_repr: const;
    (** Function from `tau` back to the general type *)
    abs_thm: thm;
    (** `abs_thm` is `|- abs (repr x) = x` *)
    abs_x: var;
    repr_thm: thm;
    (** `repr_thm` is `|- Phi x <=> repr (abs x) = x` *)
    repr_x: var;
  }
end

(** {2 Theorems and Deduction Rules} *)
module Thm = struct
  type t = thm

  let[@inline] concl self = self.th_concl
  let[@inline] hyps_ self = self.th_hyps
  let[@inline] hyps_iter self k = Expr_set.iter k self.th_hyps
  let[@inline] hyps_l self = Expr_set.elements self.th_hyps
  let[@inline] has_hyps self = not (Expr_set.is_empty self.th_hyps)
  let n_hyps self = Expr_set.cardinal self.th_hyps

  let pp out (th:t) =
    if has_hyps th then (
      Fmt.fprintf out "@[<hv1>%a@ |-@ %a@]" (pp_list Expr.pp) (hyps_l th)
        Expr.pp (concl th)
    ) else (
      Fmt.fprintf out "@[<1>|-@ %a@]" Expr.pp (concl th)
    )

  let to_string = Fmt.to_string pp
  let pp_quoted = Fmt.within "`" "`" pp

  let is_proof_of self (g:Goal.t) : bool =
    Expr.equal self.th_concl (Goal.concl g) &&
    Expr_set.subset self.th_hyps (Goal.hyps g)

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

  let new_basic_definition ctx ?def_loc (e:expr) : t * const =
    Log.debugf 5 (fun k->k"new-basic-def %a" Expr.pp e);
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
      let ty_vars = Expr.free_vars rhs |> Var.Set.to_list in
      begin match List.find (fun v -> not (Expr.is_eq_to_type v.v_ty)) ty_vars with
        | v ->
          errorf
            (fun k->k"RHS contains free variable `@[%a : %a@]`@ which is not a type variable"
                Var.pp v Expr.pp v.v_ty)
        | exception Not_found -> ()
      end;
      let c = Expr.new_const ctx ?def_loc (Var.name x_var) ty_vars (Var.ty x_var) in
      let c_e = Expr.const ctx c (List.map (Expr.var ctx) ty_vars) in
      let th = make_ ctx Expr.Set.empty (Expr.app_eq ctx c_e rhs) in
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

    let ty_vars_l = Var.Set.to_list fvars in
    let ty_vars_expr_l = ty_vars_l |> List.rev_map (Expr.var ctx) in

    (* construct new type and mapping functions *)
    let tau = Expr.new_ty_const ctx name (List.length ty_vars_l) in
    let tau_vars = Expr.const ctx tau ty_vars_expr_l in

    let c_abs =
      let ty = Expr.arrow ctx ty tau_vars in
      Expr.new_const ctx abs ty_vars_l ty
    in
    let c_repr =
      let ty = Expr.arrow ctx tau_vars ty in
      Expr.new_const ctx repr ty_vars_l ty
    in

    let abs_x = Var.make "x" tau_vars in
    (* `|- abs (repr x) = x` *)
    let abs_thm =
      let abs_x = Expr.var ctx abs_x in
      let repr = Expr.const ctx c_repr ty_vars_expr_l in
      let t = Expr.app ctx repr abs_x in
      let abs = Expr.const ctx c_abs ty_vars_expr_l in
      let abs_t = Expr.app ctx abs t in
      let eqn = Expr.app_eq ctx abs_t abs_x in
      make_ ctx Expr.Set.empty eqn
    in

    let repr_x = Var.make "x" ty in
    (* `|- Phi x <=> repr (abs x) = x` *)
    let repr_thm =
      let repr_x = Expr.var ctx repr_x in
      let abs = Expr.const ctx c_abs ty_vars_expr_l in
      let t1 = Expr.app ctx abs repr_x in
      let repr = Expr.const ctx c_repr ty_vars_expr_l in
      let t2 = Expr.app ctx repr t1 in
      let eq_t2_x = Expr.app_eq ctx t2 repr_x in
      let phi_x = Expr.app ctx phi repr_x in
      make_ ctx Expr.Set.empty (Expr.app_eq ctx phi_x eq_t2_x)
    in

    {New_ty_def.
      tau; c_repr; c_abs; fvars=ty_vars_l; repr_x;
      repr_thm; abs_x; abs_thm}

end

(* ok def *)
(*$R
  let a_ = v' "a" type_ in
  let ok_def, _thm =
    Thm.new_basic_definition ctx
      (let thevar = v (v' "body" (v a_ @-> v a_)) in
       let x = v' "x" (v a_) in
       eq thevar (lambda x (v x)))
  in
  ()
*)

