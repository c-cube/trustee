
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
  | E_const of const * expr list
  | E_app of expr * expr
  | E_lam of var * expr
  | E_arrow of expr * expr

and expr = {
  e_view: expr_view;
  e_ty: expr option lazy_t;
  mutable e_id: int;
  mutable e_flags: int; (* ̵contains: [alpha-equiv hash | 5:ctx uid] *)
}

and var = {
  v_name: string;
  v_ty: ty;
}
and ty_var = var

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
let[@inline] expr_ctx_uid e : int = e.e_flags land ctx_id_mask
let[@inline] expr_hash_mod_alpha e : int = e.e_flags lsr ctx_id_bits

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
  let rec pp out e =
    match e.e_view with
    | E_kind -> Fmt.string out "kind"
    | E_type -> Fmt.string out "type"
    | E_var v -> Fmt.string out v.v_name
    (* | E_var v -> Fmt.fprintf out "(@[%s : %a@])" v.v_name pp v.v_ty *)
    | E_const (c,[]) -> ID.pp out c.c_name
    | E_const (c,args) ->
      Fmt.fprintf out "%a@ %a" ID.pp c.c_name (pp_list pp') args
    | E_app _ ->
      let f, args = unfold_app e in
      begin match f.e_view, args with
        | E_const (c, [_]), [a;b] when ID.name c.c_name = "=" ->
          Fmt.fprintf out "@[%a@ = %a@]" pp' a pp' b
        | _ ->
          Fmt.fprintf out "@[%a@ %a@]" pp' f (pp_list pp') args
      end
    | E_lam (v, bod) ->
      Fmt.fprintf out "(@[\\%s:@[%a@].@ %a@])" v.v_name pp v.v_ty pp bod
    | E_arrow(a,b) ->
      Fmt.fprintf out "@[%a@ -> %a@]" pp' a pp b

  and pp' out e = match e.e_view with
    | E_app _ | E_arrow _ | E_const (_,_::_) -> Fmt.fprintf out "(@[%a@])" pp e
    | _ -> pp out e
  in
  pp out e

let[@inline] var_eq v1 v2 = v1.v_name = v2.v_name && expr_eq v1.v_ty v2.v_ty
let[@inline] var_hash v1 = H.combine3 5 (H.string v1.v_name) (expr_hash v1.v_ty)
let[@inline] var_pp out v1 = Fmt.string out v1.v_name

let[@inline] const_equal_ c1 c2 = ID.equal c1.c_name c2.c_name

(** {2 Variables} *)
module Var = struct
  type t = var

  let[@inline] name v = v.v_name
  let[@inline] ty v = v.v_ty
  let[@inline] make v_name v_ty : t = {v_name; v_ty}
  let makef fmt ty = Fmt.kasprintf (fun s->make s ty) fmt
  let[@inline] map_ty ~f v = {v with v_ty=f v.v_ty}
  let equal = var_eq
  let hash = var_hash
  let pp = var_pp
  let pp_with_ty out v = Fmt.fprintf out "(@[%s :@ %a@])" v.v_name expr_pp_ v.v_ty
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

(* are [e1] and [e2] alpha-equivalent? *)
let expr_alpha_equiv_ e1 e2 : bool =
  let bnd_count_ = ref 0 in
  let rec loop bnd1 bnd2 e1 e2 : bool =
    if e1 == e2 then true
    else if expr_hash_mod_alpha e1 <> expr_hash_mod_alpha e2 then false
    else (
    (* compare types first *)
      begin match e1.e_ty, e2.e_ty with
        | lazy (Some ty1), lazy (Some ty2) -> expr_eq ty1 ty2
        | _ -> true
      end
      &&
      match e1.e_view, e2.e_view with
      | E_var v1, _ when Var.Map.mem v1 bnd1 ->
        begin match e2.e_view with
          | E_var v2 ->
            (try Var.Map.find v1 bnd1 = Var.Map.find v2 bnd2
             with Not_found -> false)
          | _ -> false
        end
      | _, E_var v when Var.Map.mem v bnd2 -> false
      | E_app (f1,a1), E_app (f2,a2)
      | E_arrow (f1,a1), E_arrow (f2,a2) ->
        loop bnd1 bnd2 f1 f2 && loop bnd1 bnd2 a1 a2
      | E_const (c1,[]), E_const (c2,[]) when const_equal_ c1 c2 -> true
      | E_const (c1,l1), E_const (c2,l2) when const_equal_ c1 c2 ->
        (* compare arguments pairwise *)
        assert (List.length l1=List.length l2);
        List.for_all2 (loop bnd1 bnd2) l1 l2
      | E_lam (v1,bod1), E_lam (v2,bod2) ->
        loop bnd1 bnd2 v1.v_ty v2.v_ty &&
        begin
          let n = !bnd_count_ in
          incr bnd_count_;
          let bnd1 = Var.Map.add v1 n bnd1 in
          let bnd2 = Var.Map.add v2 n bnd2 in
          loop bnd1 bnd2 bod1 bod2
        end
      | (E_type | E_kind | E_var _ | E_const _
        | E_app _ | E_arrow _ | E_lam _), _
        -> false
    )
  in
  loop Var.Map.empty Var.Map.empty e1 e2

let expr_compare_mod_alpha e1 e2 : int =
  if expr_alpha_equiv_ e1 e2 then 0
  else expr_compare e1 e2 (* no need for this to be stable modulo alpha *)

(* Set of expressions, modulo alpha *)
module Expr_set_alpha = CCSet.Make(struct
    type t = expr
    let compare = expr_compare_mod_alpha
    end)

type thm = {
  th_concl: expr;
  th_hyps: Expr_set_alpha.t;
  mutable th_flags: int; (* [bool flags|ctx uid] *)
}
(* TODO:
   - store set of axioms used
   *)

let[@inline] thm_ctx_uid th : int = th.th_flags land ctx_id_mask

(* parametrized hash for exprs *)
let expr_hash_param_ ~h_var ~h_sub e : int =
  match e.e_view with
  | E_kind -> 11
  | E_type -> 12
  | E_const (c,l) ->
    H.combine4 20 (ID.hash c.c_name) (h_sub c.c_ty) (H.list h_sub l)
  | E_var v -> h_var v
  | E_app (f,a) -> H.combine3 50 (h_sub f) (h_sub a)
  | E_lam (v,bod) ->
    H.combine3 60 (h_var v) (h_sub bod)
  | E_arrow (a,b) -> H.combine3 80 (h_sub a) (h_sub b)

module Expr_hashcons = Hashcons.Make(struct
    type t = expr

    let equal a b =
      begin match a.e_view, b.e_view with
        | E_kind, E_kind
        | E_type, E_type -> true
        | E_const (c1,l1), E_const (c2,l2) ->
          ID.equal c1.c_name c2.c_name && CCList.equal expr_eq l1 l2
        | E_var v1, E_var v2 -> var_eq v1 v2
        | E_app (f1,a1), E_app (f2,a2) ->
          expr_eq f1 f2 && expr_eq a1 a2
        | E_lam (v1,bod1), E_lam (v2,bod2) ->
          String.equal v1.v_name v2.v_name &&
          expr_eq v1.v_ty v2.v_ty && expr_eq bod1 bod2
        | E_arrow(a1,b1), E_arrow(a2,b2) ->
          expr_eq a1 a2 && expr_eq b1 b2
        | (E_kind | E_type | E_const _ | E_var _
          | E_app _ | E_lam _ | E_arrow _), _ -> false
      end

    let hash e : int =
      expr_hash_param_ e
        ~h_var:(fun v -> H.combine2 (H.string v.v_name) (expr_hash v.v_ty))
        ~h_sub:expr_hash

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
  ctx_select_c : const lazy_t;
  mutable ctx_axioms: thm list;
  mutable ctx_axioms_allowed: bool;
}
(* TODO: derived rules and named rules/theorems *)

let[@inline] ctx_check_e_uid ctx (e:expr) = assert (ctx.ctx_uid == expr_ctx_uid e)
let[@inline] ctx_check_th_uid ctx (th:thm) = assert (ctx.ctx_uid == thm_ctx_uid th)

let id_bool = ID.make "bool"
let id_eq = ID.make "="
let id_select = ID.make "select"

module Const = struct
  type t = const
  let pp out c = ID.pp out c.c_name
  let to_string = Fmt.to_string pp
  let def_loc c = c.c_def_loc
  let[@inline] fixity c = c.c_fixity
  let[@inline] set_fixity c f = c.c_fixity <- f
  let equal = const_equal_

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
  let[@inline] select ctx = Lazy.force ctx.ctx_select_c
  let is_eq_to_bool c = ID.equal c.c_name id_bool
  let is_eq_to_eq c = ID.equal c.c_name id_bool
end

type subst = {
  m: expr Var.Map.t;
  codom: Var.Set.t lazy_t;
}

module Expr = struct
  type t = expr

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_const of const * t list
    | E_app of t * t
    | E_lam of var * t
    | E_arrow of expr * expr

  let[@inline] ty e = Lazy.force e.e_ty
  let[@inline] view e = e.e_view
  let[@inline] ty_exn e = match e.e_ty with
    | lazy None -> assert false
    | lazy (Some ty) -> ty

  let equal = expr_eq
  let hash = expr_hash
  let pp = expr_pp_
  let to_string = Fmt.to_string pp
  let compare = expr_compare
  let alpha_equiv = expr_alpha_equiv_

  let[@inline] iter ~f ~bind b_acc (e:t) : unit =
    match view e with
    | E_kind | E_type | E_const _ -> ()
    | _ ->
      CCOpt.iter (f b_acc) (ty e);
      match view e with
      | E_kind | E_type | E_const _ -> assert false
      | E_var v -> f b_acc v.v_ty
      | E_app (hd,a) -> f b_acc hd; f b_acc a
      | E_lam (v, bod) ->
        f b_acc v.v_ty;
        let b_acc = bind b_acc v in
        f b_acc bod
      | E_arrow (a,b) -> f b_acc a; f b_acc b

  exception E_exit

  let[@inline] exists ~f ~bind b_acc e : bool =
    try
      iter b_acc e ~bind
        ~f:(fun b x -> if f b x then raise_notrace E_exit); false
    with E_exit -> true

  let[@inline] for_all ~f ~bind b_acc e : bool =
    try
      iter b_acc e ~bind
        ~f:(fun b x -> if not (f b x) then raise_notrace E_exit); true
    with E_exit -> false

  (* hash that is compatible modulo alpha *)
  let compute_hash_mod_alpha_ e : int =
    expr_hash_param_ e ~h_sub:expr_hash_mod_alpha
      ~h_var:(fun v -> expr_hash_mod_alpha v.v_ty)

  (* hashconsing + computing metadata *)
  let make_ (ctx:ctx) view ty : t =
    let e = { e_view=view; e_ty=ty; e_id= -1; e_flags=0 } in
    let e_h = Expr_hashcons.hashcons ctx.ctx_exprs e in
    if e == e_h then (
      (* new term, compute metadata *)
      assert ((ctx.ctx_uid land ctx_id_mask) == ctx.ctx_uid);
      e_h.e_flags <-
        ((compute_hash_mod_alpha_ e) lsl ctx_id_bits)
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

  (* map immediate subterms *)
  let[@inline] map ctx ~f ~bind b_acc (e:t) : t =
    match view e with
    | E_kind | E_type | E_const (_,[]) -> e
    | _ ->
      let ty = lazy (
        match e.e_ty with
        | lazy None -> None
        | lazy (Some ty) -> Some (f b_acc ty)
      ) in
      begin match view e with
        | E_var v ->
          let v_ty = f b_acc v.v_ty in
          if v_ty == v.v_ty then e
          else make_ ctx (E_var {v with v_ty}) ty
        | E_app (hd,a) ->
          let hd' =  f b_acc hd in
          let a' =  f b_acc a in
          if a==a' && hd==hd' then e
          else make_ ctx (E_app (f b_acc hd, f b_acc a)) ty
        | E_lam (v, bod) ->
          let v' = {v with v_ty=f b_acc v.v_ty} in
          let b_acc = bind b_acc v in
          let bod' = f b_acc bod in
          if var_eq v v' && expr_eq bod bod'
          then e (* fast path *)
          else make_ ctx (E_lam (v', bod')) ty
        | E_arrow (a,b) ->
          let a' = f b_acc a in
          let b' = f b_acc b in
          if a==a' && b==b' then e (* fast path *)
          else make_ ctx (E_arrow (a', b')) ty
        | E_const (c, l) ->
          let l' = List.map (f b_acc) l in
          if List.for_all2 expr_eq l l'
          then e (* fast path *)
          else make_ ctx (E_const (c, l')) ty
        | E_kind | E_type -> assert false
      end

  exception IsSub

  let contains e ~sub : bool =
    let rec aux e =
      if equal e sub then raise_notrace IsSub;
      iter () e ~bind:(fun () _ -> ()) ~f:(fun _ u -> aux u)
    in
    try aux e; false with IsSub -> true

  let free_vars_iter e : var Iter.t =
    fun yield ->
      let rec aux bnd e =
        match view e with
        | E_var v when Var.Set.mem v bnd -> () (* captured *)
        | E_var v -> yield v; aux bnd (Var.ty v)
        | E_const (_, args) -> List.iter (aux bnd) args
        | _ ->
          iter bnd e ~f:aux ~bind:(fun bnd v -> Var.Set.add v bnd)
      in
      aux Var.Set.empty e

  let free_vars ?(init=Var.Set.empty) e : Var.Set.t =
    let set = ref init in
    free_vars_iter e (fun v -> set := Var.Set.add v !set);
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
    let diff = Var.Set.diff fvars (Var.Set.of_list ty_vars) in
    begin match Var.Set.choose_opt diff with
      | None -> ()
      | Some v ->
        errorf
          (fun k->k
              "Kernel.new_const: type variable %a@ \
               occurs in type of the constant `%s`,@ \
               but not in the type variables %a"
              Var.pp v name (Fmt.Dump.list Var.pp) ty_vars);
    end;
    new_const_ ctx ?def_loc name (C_ty_vars ty_vars) ty

  let new_ty_const ctx ?def_loc name n : ty_const =
    new_const_ ctx name ?def_loc (C_arity n) (type_ ctx)

  let mk_const_ ctx c args ty : t =
    make_ ctx (E_const (c,args)) ty

  let subst_empty_ : subst =
    {m=Var.Map.empty; codom=Lazy.from_val Var.Set.empty}

  let subst_pp_ out (self:subst) : unit =
    if Var.Map.is_empty self.m then Fmt.string out "{}"
    else (
      let pp_b out (v,t) =
        Fmt.fprintf out "(@[%a := %a@])" Var.pp_with_ty v expr_pp_ t
      in
      Fmt.fprintf out "@[<hv>{@,%a@,}@]"
        (pp_iter ~sep:" " pp_b) (Var.Map.to_iter self.m)
    )

  (* bind a variable into a substitution. This computes the codomain. *)
  let subst_bind_ (subst:subst) v t : subst =
    let codom = lazy (
      free_vars ~init:(Lazy.force subst.codom) t
    ) in
    { m=Var.Map.add v t subst.m; codom; }

  (* find a new name for [v] that looks like
     [v.name] but is not captured in [set] *)
  let find_var_name_ v set : string =
    let rec aux i =
      let v_name = Printf.sprintf "%s%d" v.v_name i in
      let v' = {v with v_name} in
      if Var.Set.mem v' set then aux (i+1) else v_name
    in
    aux 0

  let subst_ ~recursive ctx e (subst:subst) : t =
    let rec loop subst e =
      let ty = lazy (
        match e.e_ty with
        | lazy None -> None
        | lazy (Some ty) -> Some (loop subst ty)
      ) in
      match view e with
      | E_var v ->
        begin match Var.Map.find v subst.m with
          | u ->
            if recursive then loop subst u else u
          | exception Not_found ->
            (* subst in type *)
            let ty = loop subst v.v_ty in
            var ctx {v with v_ty=ty}
        end
      | E_const (_, []) -> e
      | E_const (c, args) ->
        (* subst in args, thus changing the whole term's type *)
        mk_const_ ctx c (List.map (loop subst) args) ty
      | E_lam (v, body) ->
        (* the tricky case: the binder.
           We rename [v] if it occurs in the substitution's codomain (where it
           is normally free, so we don't want to capture it accidentally).
           We also re-bind [v] if its type changes. *)
        let v', body' =
          if Var.Map.mem v subst.m then (
            (* remove [v] from [subst] if it occurs in it, as we shadow it *)
            let v' = Var.map_ty v ~f:(loop subst) in
            let subst' = {subst with m=Var.Map.remove v subst.m} in
            let body' = loop subst' body in
            v', body'
          ) else if Var.Set.mem v (Lazy.force subst.codom) then (
            (* would capture a term of the substitution, we must rename [v]
               to avoid that. *)
            let v' = {
              v_name=find_var_name_ v (Lazy.force subst.codom);
              v_ty=loop subst v.v_ty
            } in
            let subst = subst_bind_ subst v (var ctx v') in
            let body' = loop subst body in
            v', body'
          ) else (
            let v' = Var.map_ty v ~f:(loop subst) in
            let body' = loop subst body in
            v', body'
          )
        in
        if Var.equal v v' && equal body body'
        then e (* fast path *)
        else make_ ctx (E_lam (v', body')) ty
      | _ ->
        map ctx subst e ~f:loop
          ~bind:(fun _ _ -> assert false) (* done in lambda above *)
    in
    if Var.Map.is_empty subst.m
    then e else loop subst e

  let[@inline] subst ~recursive ctx e subst =
    subst_ ~recursive ctx e subst

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
          let sigma = List.fold_left2 subst_bind_ subst_empty_ ty_vars args in
          Some (subst ~recursive:false ctx c.c_ty sigma)
        )
    in
    mk_const_ ctx c args ty

  let eq ctx ty =
    let eq = Lazy.force ctx.ctx_eq_c in
    const ctx eq [ty]

  let select ctx ty =
    let sel = Lazy.force ctx.ctx_select_c in
    const ctx sel [ty]

  let arrow ctx a b : t =
    if not (is_a_type a) || not (is_a_type b) then (
      errorf (fun k->k"arrow: both arguments must be types");
    );
    let ty = Lazy.from_val (Some (type_ ctx)) in
    make_ ctx (E_arrow (a,b)) ty

  let app ctx f a : t =
    ctx_check_e_uid ctx f;
    ctx_check_e_uid ctx a;

    let ty_f = ty_exn f in
    let ty_a = ty_exn a in

    let[@inline never] fail () =
      errorf
        (fun k->
          k"@[<2>kernel: cannot apply function@ `@[%a@]`@ \
           to argument `@[%a@]`@]@];@ \
           @[function has type@ `@[%a@]`,@ \
           but arg has type `@[%a@]`@]"
           pp f pp a pp ty_f pp ty_a)
    in

    let ty =
      match view ty_f with
      | E_arrow (ty_arg, ty_ret) when equal ty_arg ty_a ->
        ty_ret (* no instantiation needed *)
      | _ -> fail()
    in
    let ty = Lazy.from_val (Some ty) in
    let e = make_ ctx (E_app (f,a)) ty in
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

  let arrow_l ctx l ret : t = CCList.fold_right (arrow ctx) l ret

  let lambda ctx v bod : t =
    ctx_check_e_uid ctx v.v_ty;
    ctx_check_e_uid ctx bod;
    if not (is_a_type v.v_ty) then (
      errorf (fun k->k"lambda: variable %a must have a type as type"
                 Var.pp_with_ty v);
    );
    let ty = lazy (
      (* type of [λx:a. t] is [a -> typeof(t)] if [a] is a type *)
      Some (arrow ctx v.v_ty (ty_exn bod))
    ) in
    make_ ctx (E_lam (v, bod)) ty

  let lambda_l ctx = CCList.fold_right (lambda ctx)

  let unfold_app = unfold_app

  let unfold_eq e =
    let f, l = unfold_app e in
    match view f, l with
    | E_const ({c_name;_}, [_]), [a;b] when ID.equal c_name id_eq -> Some(a,b)
    | _ -> None

  let rec unfold_arrow e =
    match view e with
    | E_arrow (a,b) ->
      let args, ret = unfold_arrow b in
      a::args, ret
    | _ -> [], e

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
  module Set = CCSet.Make(AsKey)
  module Tbl = CCHashtbl.Make(AsKey)

  module Set_mod_alpha = Expr_set_alpha
end

module Subst = struct
  type t = subst = {
    m: expr Var.Map.t;
    codom: Var.Set.t lazy_t;
  }

  let[@inline] is_empty self = Var.Map.is_empty self.m
  let[@inline] find_exn x s = Var.Map.find x s.m
  let[@inline] get x s = Var.Map.get x s.m

  let empty = Expr.subst_empty_
  let bind = Expr.subst_bind_
  let pp = Expr.subst_pp_
  let[@inline] bind' x t s : t = bind s x t
  let[@inline] size self = Var.Map.cardinal self.m
  let[@inline] to_iter self = Var.Map.to_iter self.m

  let to_string = Fmt.to_string pp
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
    hyps: Expr_set_alpha.t;
    concl: Expr.t;
  }

  let make hyps concl : t = {hyps; concl}
  let make_l h c = make (Expr_set_alpha.of_list h) c
  let make_nohyps c : t = make Expr_set_alpha.empty c

  let[@inline] concl g = g.concl
  let[@inline] hyps g = g.hyps
  let[@inline] hyps_iter g = Expr_set_alpha.to_iter g.hyps

  let pp out (self:t) : unit =
    if Expr_set_alpha.is_empty self.hyps then (
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
      ctx_select_c=lazy (
        let type_ = Expr.type_ ctx in
        let lazy bool_ = ctx.ctx_bool in
        let a_ = Var.make "a" type_ in
        let ea = Expr.var ctx a_ in
        let typ = Expr.(arrow ctx (arrow ctx ea bool_) ea) in
        {c_name=id_select; c_args=C_ty_vars[a_]; c_ty=typ;
         c_def_loc=None; c_fixity=F_binder 10}
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
  let[@inline] hyps_iter self k = Expr_set_alpha.iter k self.th_hyps
  let[@inline] hyps_l self = Expr_set_alpha.elements self.th_hyps
  let[@inline] has_hyps self = not (Expr_set_alpha.is_empty self.th_hyps)
  let n_hyps self = Expr_set_alpha.cardinal self.th_hyps

  let pp out (th:t) =
    if has_hyps th then (
      Fmt.fprintf out "@[<hv1>%a@;<1 -1>|-@ %a@]" (pp_list Expr.pp) (hyps_l th)
        Expr.pp (concl th)
    ) else (
      Fmt.fprintf out "@[<1>|-@ %a@]" Expr.pp (concl th)
    )

  let to_string = Fmt.to_string pp
  let pp_quoted = Fmt.within "`" "`" pp

  let is_proof_of self (g:Goal.t) : bool =
    Expr.alpha_equiv self.th_concl (Goal.concl g) &&
    Expr_set_alpha.subset self.th_hyps (Goal.hyps g)

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
    wrap_exn (fun k->k"in assume `@[%a@]`:" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    if not (is_bool_ ctx e) then (
      error "assume takes a boolean"
    );
    make_ ctx (Expr_set_alpha.singleton e) e

  let axiom ctx e : t =
    wrap_exn (fun k->k"in axiom `@[%a@]`:" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    if not ctx.ctx_axioms_allowed then (
      error "the context does not accept new axioms, see `pledge_no_more_axioms`"
    );
    if not (is_bool_ ctx e) then (
      error "axiom takes a boolean"
    );
    make_ ctx Expr_set_alpha.empty e

  let merge_hyps_ = Expr_set_alpha.union

  let cut ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in cut@ th1=`@[%a@]`@ th2=`@[%a@]`@]:" pp th1 pp th2)
    @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    let b = concl th1 in
    let hyps = merge_hyps_ (hyps_ th1) (Expr_set_alpha.remove b (hyps_ th2)) in
    make_ ctx hyps (concl th2)

  let refl ctx e : t =
    ctx_check_e_uid ctx e;
    make_ ctx Expr_set_alpha.empty (Expr.app_eq ctx e e)

  let congr ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in congr@ th1=`@[%a@]`@ th2=`@[%a@]`@]:" pp th1 pp th2)
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

  let subst ~recursive ctx th s : t =
    let hyps = hyps_ th |> Expr_set_alpha.map (fun e -> Expr.subst ~recursive ctx e s) in
    let concl = Expr.subst ~recursive ctx (concl th) s in
    make_ ctx hyps concl

  let sym ctx th : t =
    wrap_exn (fun k->k"@[<2>in sym@ `@[%a@]`@]:" pp th) @@ fun () ->
    ctx_check_th_uid ctx th;
    match Expr.unfold_eq (concl th) with
    | None -> errorf (fun k->k"sym: concl of %a@ should be an equation" pp th)
    | Some (t,u) ->
      make_ ctx (hyps_ th) (Expr.app_eq ctx u t)

  let trans ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in trans@ %a@ %a@]:" pp_quoted th1 pp_quoted th2) @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th1), Expr.unfold_eq (concl th2) with
    | None, _ -> errorf (fun k->k"trans: concl of %a@ should be an equation" pp th1)
    | _, None -> errorf (fun k->k"trans: concl of %a@ should be an equation" pp th2)
    | Some (t,u), Some (u',v) ->
      if not (Expr.alpha_equiv u u') then (
        errorf (fun k->k"@[<2>kernel: trans: conclusions@ of %a@ and %a@ do not match@]" pp th1 pp th2)
      );
      let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
      make_ ctx hyps (Expr.app_eq ctx t v)

  let bool_eq ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<hv2>in bool_eq@ th1=%a@ th2=%a@]:"
                 pp_quoted th1 pp_quoted th2) @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    match Expr.unfold_eq (concl th2) with
    | None ->
      errorf (fun k->k"bool-eq should have a boolean equality as conclusion in %a"
                 pp th2)
    | Some (t, u) ->
      if Expr.alpha_equiv t (concl th1) then (
        let hyps = merge_hyps_ (hyps_ th1) (hyps_ th2) in
        make_ ctx hyps u
      ) else (
        errorf
          (fun k->k
              "bool-eq: mismatch,@ conclusion of %a@ does not match LHS of %a@ \
               (lhs is: `@[%a@]`)"
              pp_quoted th1 pp_quoted th2 Expr.pp t)
      )

  let bool_eq_intro ctx th1 th2 : t =
    wrap_exn (fun k->k"@[<2>in bool_eq_intro@ th1=`@[%a@]`@ th2=`@[%a@]`@]:"
                 pp th1 pp th2) @@ fun () ->
    ctx_check_th_uid ctx th1;
    ctx_check_th_uid ctx th2;
    let e1 = concl th1 in
    let e2 = concl th2 in
    let hyps =
      merge_hyps_
        (Expr_set_alpha.remove e1 (hyps_ th2))
        (Expr_set_alpha.remove e2 (hyps_ th1))
    in
    make_ ctx hyps (Expr.app_eq ctx e1 e2)

  let beta_conv ctx e : t =
    wrap_exn (fun k->k"@[<2>in beta-conv `@[%a@]`:" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    match Expr.view e with
    | E_app (f, a) ->
      (match Expr.view f with
       | E_lam (v, body) ->
         assert (Expr.equal v.v_ty (Expr.ty_exn a)); (* else `app` would have failed *)
         let subst = Subst.bind Subst.empty v a in
         let rhs = Expr.subst ctx ~recursive:false body subst in
         make_ ctx Expr_set_alpha.empty (Expr.app_eq ctx e rhs)
       | _ ->
         errorf (fun k->k"not a redex: function %a is not a lambda" Expr.pp f)
      )
    | _ ->
      errorf (fun k->k"not a redex: %a not an application" Expr.pp e)

  let abs ctx th v : t =
    wrap_exn (fun k->k"@[<2>in abs `@[%a@]` var %a:" pp th Var.pp v) @@ fun () ->
    ctx_check_th_uid ctx th;
    ctx_check_e_uid ctx v.v_ty;
    match Expr.unfold_eq th.th_concl with
    | Some (a,b) ->
      let is_in_hyp hyp = Iter.mem ~eq:Var.equal v (Expr.free_vars_iter hyp) in
      if Expr_set_alpha.exists is_in_hyp th.th_hyps then (
        errorf (fun k->k"variable `%a` occurs in an hypothesis@ of %a" Var.pp v pp th);
      );
      make_ ctx th.th_hyps
        (Expr.app_eq ctx (Expr.lambda ctx v a) (Expr.lambda ctx v b))
    | None -> errorf (fun k->k"conclusion of `%a`@ is not an equation" pp th)

  let new_basic_definition ctx ?def_loc (e:expr) : t * const =
    Log.debugf 5 (fun k->k"(@[new-basic-def@ :eqn `%a`@])" Expr.pp e);
    wrap_exn (fun k->k"@[<2>in new-basic-def `@[%a@]`@]:" Expr.pp e) @@ fun () ->
    ctx_check_e_uid ctx e;
    match Expr.unfold_eq e with
    | None ->
      errorf (fun k->k"new-basic-def: expect an equation `x=rhs`,@ got %a" Expr.pp e)
    | Some (x, rhs) ->
      if Expr.contains rhs ~sub:x then (
        errorf (fun k->k"RHS %a@ contains variable %a" Expr.pp rhs Expr.pp x)
      );
      let x_var = match Expr.view x with
        | E_var v -> v
        | _ ->
          errorf (fun k-> k "LHS must be a variable,@ but got %a" Expr.pp x)
      in

      let fvars = Expr.free_vars rhs in
      let ty_vars_l = Var.Set.to_list fvars in
      begin match List.find (fun v -> not (Expr.is_eq_to_type v.v_ty)) ty_vars_l with
        | v ->
          errorf
            (fun k->k"RHS contains free variable `@[%a : %a@]`@ which is not a type variable"
                Var.pp v Expr.pp v.v_ty)
        | exception Not_found -> ()
      end;

      let c = Expr.new_const ctx ?def_loc (Var.name x_var) ty_vars_l (Var.ty x_var) in
      let c_e = Expr.const ctx c (List.map (Expr.var ctx) ty_vars_l) in
      let th = make_ ctx Expr_set_alpha.empty (Expr.app_eq ctx c_e rhs) in
      th, c

  let new_basic_type_definition ctx
      ?ty_vars:provided_ty_vars
      ~name ~abs ~repr ~thm_inhabited () : New_ty_def.t =
    wrap_exn (fun k->k"@[<2>in new-basic-ty-def %s `@[%a@]`@]:"
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

    let ty_vars_l = match provided_ty_vars with
      | None -> Var.Set.to_list fvars (* pick any order *)
      | Some l ->
        if not (Var.Set.equal fvars (Var.Set.of_list l)) then (
          errorf
            (fun k->k
                "list of type variables (%a) in new-basic-ty-def@ does not match %a"
                (Fmt.Dump.list Var.pp) (Var.Set.to_list fvars)
                (Fmt.Dump.list Var.pp) l);
        );
        l
    in
    let ty_vars_expr_l = ty_vars_l |> CCList.map (Expr.var ctx) in

    Log.debugf 5
      (fun k->k"(@[new-basic-ty-def@ :name `%s`@ :phi %a@ \
                :ty-vars %a@ :repr `%s`@ :abs `%s`@])"
           name pp_quoted thm_inhabited (Fmt.Dump.list Var.pp) ty_vars_l repr abs);

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
      make_ ctx Expr_set_alpha.empty eqn
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
      make_ ctx Expr_set_alpha.empty (Expr.app_eq ctx phi_x eq_t2_x)
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

