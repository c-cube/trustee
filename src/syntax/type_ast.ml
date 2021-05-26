
open Sigs

module K = Kernel
module A = Parse_ast
module AE = A.Expr
module KProof = Proof

type position = Position.t
type location = A.location
let noloc: location = Loc.none

type expr = {
  view: view;
  mutable ty: ty option;
  loc: location;
}

and ty = expr

(** Free variable *)
and var = {
  v_name: string;
  v_ty: ty;
}

(** Bound variable *)
and bvar = {
  bv_name: ID.t;
  bv_ty: ty;
  bv_loc: location;
}

and binding = bvar * expr

and view =
  | Kind
  | Type
  | Bool
  | Ty_arrow of ty * ty
  | Var of var
  | BVar of bvar
  | Meta of meta
  | Const of {
      c: K.const;
      args: ty list;
    }
  | App of expr * expr
  | Lambda of bvar * expr
  | Eq of expr * expr
  | Let of binding list * expr
  | KExpr of K.Expr.t

and meta = {
  meta_name: string;
  meta_type: expr;
  meta_loc: location;
  mutable meta_deref: expr option;
}

(** Pure typing environment *)
and ty_env = {
  env_consts: K.const A.with_loc Str_map.t;
  env_theorems: K.Thm.t A.with_loc Str_map.t;
}

type subst = (var * expr) list

type typing_state = {
  ctx: K.Ctx.t;
  mutable fvars: var Str_map.t;
  mutable notation: Notation.t;
  mutable ty_env: ty_env;
  mutable cur_file: string;
  mutable gensym: int;
  mutable to_gen: meta list; (* to generalize *)
}

(* view auto-dereferences *)
let [@inline][@unroll 1] rec view_expr_ e = match e.view with
  | Meta {meta_deref=Some u;_} -> view_expr_ u
  | v -> v

let unfold_app_ e =
  let[@unroll 1] rec aux acc e = match view_expr_ e with
    | App (f,a) -> aux (a::acc) f
    | _ -> e, acc
  in
  aux [] e

let unfold_lam e =
  let[@unroll 1] rec aux acc e = match view_expr_ e with
    | Lambda (v,e) -> aux (v::acc) e
    | _ -> List.rev acc, e
  in
  aux [] e

module Meta = struct
  type t = meta
  let make ~loc s ty : t =
    {meta_deref=None; meta_name=s; meta_type=ty; meta_loc=loc;}
  let equal (a:t) (b:t) : bool = a == b
  let pp out m = Fmt.fprintf out "?%s" m.meta_name
end

(** Follow assigned meta-variables *)
let[@inline][@unroll 1] rec expr_deref_ (e:expr) : expr =
  match e.view with
  | Meta {meta_deref=Some u; _} -> expr_deref_ u
  | _ -> e

let rec pp_expr_ out (e:expr) : unit =
  match view_expr_ e with
  | Kind -> Fmt.string out "kind"
  | Type -> Fmt.string out "type"
  | Bool -> Fmt.string out "bool"
  | Var v -> Fmt.string out v.v_name
  | BVar v -> ID.pp out v.bv_name
  | Ty_arrow (a,b) ->
    Fmt.fprintf out "%a@ -> %a" pp_atom_ a pp_expr_ b;
  | Const {c;args=[]} -> K.Const.pp out c
  | Const {c;args} ->
    Fmt.fprintf out "%a@ %a" K.Const.pp c (pp_list pp_atom_) args
  | App _ ->
    let f, l = unfold_app_ e in
    Fmt.fprintf out "(@[%a@ %a@])" pp_atom_ f (pp_list pp_atom_) l
  | Meta v -> Meta.pp out v
  | Lambda _ ->
    let vars, bod = unfold_lam e in
    Fmt.fprintf out "(@[\\%a.@ %a@])" (pp_list pp_bvar_ty) vars pp_expr_ bod
  | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp_expr_ a pp_expr_ b
  | Let (bs,bod) ->
    let pp_b out (v,e) : unit =
      Fmt.fprintf out "@[%a@ = %a@]" ID.pp v.bv_name pp_expr_ e in
    Fmt.fprintf out "(@[let %a in@ %a@])" (pp_list ~sep:" and " pp_b) bs pp_expr_ bod
  | KExpr e -> K.Expr.pp out e
and pp_atom_ out e =
  let e = expr_deref_ e in
  match e.view with
  | Kind | Type | Var _ | BVar _ | Meta _ | Const {args=[];_} ->
    pp_expr_ out e
  | _ -> Fmt.fprintf out "(@[%a@])" pp_expr_ e
and pp_var out v = Fmt.string out v.v_name
and pp_bvar out v = ID.pp out v.bv_name
and pp_bvar_ty out (v:bvar) : unit =
  Fmt.fprintf out "(@[%a@ : %a@])" ID.pp v.bv_name pp_atom_ v.bv_ty

let ty_env_empty_ : ty_env = {
  env_consts=Str_map.empty;
  env_theorems=Str_map.empty;
}

(** {2 Satellite types} *)

module Var = struct
  type t = var
  let make v_name v_ty : var = {v_name; v_ty; }
  let pp = pp_var
  let to_string = Fmt.to_string pp
end

module BVar = struct
  type t = bvar
  let make ~loc bv_name bv_ty : bvar = {bv_name; bv_ty; bv_loc=loc; }
  let compare a b = ID.compare a.bv_name b.bv_name
  let pp = pp_bvar
  let to_string = Fmt.to_string pp
  let pp_with_ty = pp_bvar_ty

  let as_queryable (self:t) = object
    inherit Queryable.t
    method loc = self.bv_loc
    method pp out () = Fmt.fprintf out "@[bound variable:@ %a@]" pp_bvar_ty self
  end

  module As_key = struct
    type nonrec t = t
    let compare = compare
  end
  module Map = CCMap.Make(As_key)
end

module Expr = struct
  type t = expr
  let view = view_expr_
  let unfold_app = unfold_app_

  let deref_ = expr_deref_

  (** Iterate on immediate subterms *)
  let iter ~f ~f_bind b_acc (e:expr) : unit =
    CCOpt.iter (fun u -> f b_acc u) e.ty;
    match view e with
    | Kind | Type | Bool | Const _ | Meta _ | Var _ | BVar _ | KExpr _ -> ()
    | Ty_arrow (a, b) | Eq (a,b) | App (a,b) ->
      f b_acc a;
      f b_acc b
    | Lambda (v, bod) ->
      f b_acc v.bv_ty;
      let b_acc = f_bind b_acc v in
      f b_acc bod
    | Let (bs, bod) ->
      let b_acc =
        List.fold_left
          (fun b_acc (v,u) ->
             f b_acc v.bv_ty;
             f b_acc u;
             f_bind b_acc v)
        b_acc bs
      in
      f b_acc bod

  exception E_contains

  (* does [e] contain the meta [sub_m] *)
  let contains_meta ~sub_m (e:expr) : bool =
    let rec aux () e =
      match view e with
      | Meta m' when Meta.equal sub_m m' ->
        raise_notrace E_contains
      | _ ->
        iter () e ~f_bind:(fun () _ -> ()) ~f:aux
    in
    try aux () e; false
    with E_contains -> true

  let contains_bvar ~bv (e:expr) : bool =
    let rec aux () e =
      match view e with
      | BVar v when ID.equal v.bv_name bv.bv_name ->
        raise_notrace E_contains
      | _ ->
        iter () e ~f_bind:(fun () _ -> ()) ~f:aux
    in
    try aux () e; false
    with E_contains -> true

  (* are [a] and [b] the same bound var under given [renaming] (maps bound vars
     to other bound vars)? *)
  let same_bvar_ renaming a b : bool =
    let a = try ID.Map.find a.bv_name renaming with Not_found -> a.bv_name in
    let b = try ID.Map.find b.bv_name renaming with Not_found -> b.bv_name in
    ID.equal a b

  let pp out e = Fmt.fprintf out "`@[%a@]`" pp_expr_ e

  let kind_ = {view=Kind; loc=noloc; ty=None}
  let[@inline] mk_ ~loc view ty : expr = {view; loc; ty=Some ty}

  let[@inline] loc e = e.loc
  let[@inline] ty e = match e.ty with Some t -> t | None -> assert false
  let get_ty = ty
  let pp = pp

  (** {2 Core operations} *)

  let type_ : expr = mk_ ~loc:noloc Type kind_
  let bool : expr = mk_ ~loc:noloc Bool type_
  let meta ~loc s ty : expr * meta =
    let m = Meta.make ~loc s ty in
    mk_ ~loc (Meta m) ty, m

  (* fresh type name *)
  let fresh_ty_name_ =
    let prefixes = "abcdefghijkl" in
    fun env ->
      let n = env.gensym in
      env.gensym <- 1 + n;
      let len = String.length prefixes in
      let c = prefixes.[n mod len] in
      let suff = n / len in
      if suff = 0 then Printf.sprintf "'%c" c
      else Printf.sprintf "'%c%d" c suff

  let fresh_meta_name_ =
    fun env ->
      let n = env.gensym in
      env.gensym <- 1 + n;
      Printf.sprintf "#X%d" n

  let ty_var ~loc s : expr = mk_ ~loc (Var (Var.make s type_)) type_
  let ty_meta ~loc env : ty * meta =
    let name = fresh_ty_name_ env in
    let m = Meta.make ~loc name type_ in
    mk_ ~loc (Meta m) type_, m
  let ty_arrow ~loc a b : ty = mk_ ~loc (Ty_arrow (a,b)) type_
  let var ~loc (v:var) : expr = mk_ ~loc (Var v) v.v_ty
  let var' ~loc name ty : expr = var ~loc (Var.make name ty)
  let bvar ~loc (v:bvar) : expr = mk_ ~loc (BVar v) v.bv_ty

  let is_eq_to_type (e:expr) = match view e with
    | Type -> true
    | _ -> false
  let[@inline] is_a_type e = is_eq_to_type (ty e)

  (* convert a kernel expression back into a type *)
  let rec ty_of_expr ~loc e0 (subst:ty Str_map.t) : ty =
    let rec aux env e =
      match K.Expr.view e with
      | K.Expr.E_const (c, args) ->
        let args = List.map (aux env) args in
        const ~loc c args
      | K.Expr.E_type -> type_
      | K.Expr.E_var v ->
        begin match Str_map.get v.v_name subst with
          | None -> var ~loc (Var.make v.v_name (aux env v.v_ty))
          | Some e -> e
        end
      | K.Expr.E_bound_var v ->
        begin match List.nth env v.bv_idx with
          | exception Not_found ->
            errorf (fun k->k"unbound variable db%d@ in type of %a" v.bv_idx K.Expr.pp e)
          | t -> t
        end
      | K.Expr.E_arrow (a, b) ->
        assert (K.Expr.is_a_type a && K.Expr.is_a_type b);
        let a = aux env a in
        let b = aux env b in
        ty_arrow ~loc a b
      | _ ->
        errorf (fun k->k"cannot convert kernel expression %a@ to a type" K.Expr.pp e)
    in
    aux [] e0

  and const ~loc c args : expr =
    let subst = match K.Const.args c with
      | K.Const.C_arity _ -> Str_map.empty
      | K.Const.C_ty_vars vs ->
        assert (List.length vs = List.length args);
        List.fold_left2
          (fun s v ty -> Str_map.add v.K.v_name ty s)
          Str_map.empty vs args
    in
    mk_ ~loc (Const {c;args}) (ty_of_expr ~loc (K.Const.ty c) subst)

  let of_k_expr ~loc e : expr =
    let ty = ty_of_expr ~loc (K.Expr.ty_exn e) Str_map.empty in
    mk_ ~loc (KExpr e) ty

  let subst_bvars (m:expr ID.Map.t) (e:expr) : expr =
    let rec aux m e =
      let e = deref_ e in
      match e.ty with
      | None -> assert (e==kind_); e
      | Some ty ->
        let ty = aux m ty in
        let loc = e.loc in
        match e.view with
        | KExpr _ -> e
        | Kind | Type | Bool | Const _ | Meta _ | Var _ -> {e with ty=Some ty}
        | BVar v ->
          begin match ID.Map.find v.bv_name m with
            | u -> {u with loc}
            | exception Not_found -> e
          end
        | App (a,b) -> mk_ ~loc (App (aux m a, aux m b)) ty
        | Eq(a,b) -> mk_ ~loc (Eq(aux m a, aux m b)) ty
        | Ty_arrow(a,b) -> mk_ ~loc (Ty_arrow(aux m a, aux m b)) ty
        | Lambda (v, bod) ->
          let m, v' = rename_bvar m v in
          mk_ ~loc (Lambda (v', aux m bod)) ty
        | Let (bs, bod) ->
          let m, bs =
            CCList.fold_map
              (fun m1 (v,t) ->
                 let m1, v' = rename_bvar m1 v in
                 let t = aux m t in
                 ID.Map.add v.bv_name (mk_ ~loc:noloc (BVar v') ty) m1, (v',t))
              m bs
          in
          mk_ ~loc (Let (bs, aux m bod)) ty
    (* rename a bound variable to avoid capture. Adds [v -> v'] to [m]. *)
    and rename_bvar m v =
      let ty = aux m v.bv_ty in
      let v' = {v with bv_name=ID.copy v.bv_name; bv_ty=ty} in
      ID.Map.add v.bv_name (mk_ ~loc:noloc (BVar v') ty) m, v'
    in
    aux m e

  type unif_err_trace = (expr*expr) list
  exception E_unif_err of unif_err_trace

  let pp_unif_trace_ out (st:unif_err_trace) : unit =
    Fmt.fprintf out "@[<hv>";
    List.iter (fun (e1,e2) ->
        Fmt.fprintf out "@[<2>- unifying@ %a@ and %a@];@ "
          pp (deref_ e1) pp (deref_ e2))
      st;
    Fmt.fprintf out "@]"

  (* compute type of [f a] *)
  let rec ty_app_ env ~loc (f:expr) (a:expr) : ty =
    let ty_f = deref_ (ty f) in
    let ty_a = deref_ (ty a) in
    let unif_exn_ a b = match unif_ a b with
      | Ok () -> ()
      | Error st ->
        errorf
          (fun k->k
              "@[<hv2>type error@ in the application \
               @[<2>of %a@ of type %a@]@ @[<2>to term %a@ of type %a@]:@ \
               unification error in the following trace:@ %a@]"
              pp f pp ty_f pp a pp ty_a
              pp_unif_trace_ st)
    in
    begin match view ty_f with
      | Ty_arrow (f_arg, f_ret) ->
        unif_exn_ f_arg ty_a;
        f_ret
      | _ ->
        let ty_ret, meta = ty_meta ~loc env in
        env.to_gen <- meta :: env.to_gen;
        unif_exn_ ty_f (ty_arrow ~loc ty_a ty_ret);
        ty_ret
    end

  (* unify two terms. This only needs to be complete for types. *)
  and unif_ (a:expr) (b:expr) : (unit, unif_err_trace) result =
    let[@inline] fail_ st a b =
      Log.debugf 10 (fun k->k"unif fail: %a@ and %a" pp a pp b);
      raise_notrace (E_unif_err ((a,b) :: st))
    in
    let rec aux st renaming a b =
      let a = deref_ a in
      let b = deref_ b in
      if a == b then ()
      else (
        let st' = (a,b)::st in
        begin match a.ty, b.ty with
          | Some tya, Some tyb -> aux st' renaming tya tyb
          | None, None -> ()
          | Some _, None | None, Some _ -> fail_ st' a b
        end;
        match a.view, b.view with
        | Type, Type | Kind, Kind | Bool, Bool -> ()
        | KExpr e1, KExpr e2 when K.Expr.equal e1 e2 -> ()
        | Bool, Const c when K.Const.is_eq_to_bool c.c -> ()
        | Const c, Bool when K.Const.is_eq_to_bool c.c -> ()
          (* FIXME
        | Type, Const (c,[]) when K.Const.is_eq_to_type c -> ()
        | Const c, Type when K.Expr.is_eq_to_type c.c -> ()
             *)
        | Var a, Var b when a.v_name = b.v_name -> ()
        | BVar a, BVar b
          when
            ID.equal a.bv_name b.bv_name
            || same_bvar_ renaming a b
          -> ()
        | Const c1, Const c2 when K.Const.equal c1.c c2.c ->
          aux_l st renaming a b c1.args c2.args
        | Ty_arrow (a1,a2), Ty_arrow (b1,b2) ->
          aux st' renaming a1 b1;
          aux st' renaming a2 b2;
        | Eq (a1,a2), Eq (b1,b2)
        | App (a1,a2), App (b1,b2) ->
          aux st' renaming a1 b1;
          aux st' renaming a2 b2;
        | Meta m1, Meta m2 when Meta.equal m1 m2 -> ()
        | Meta m1, _ ->
          if contains_meta ~sub_m:m1 b then (
            fail_ st a b
          );
          m1.meta_deref <- Some b;
        | _, Meta m2 ->
          if contains_meta ~sub_m:m2 a then (
            fail_ st a b
          );
          m2.meta_deref <- Some a;
        | Let _, _ ->
          fail_ st a b (* TODO? *)
        | (Type | Bool | Kind | Var _ | BVar _ | Eq _ | KExpr _
          | Const _ | App _ | Ty_arrow _ | Lambda _), _ ->
          fail_ st a b
      )
    and aux_l st renaming t1 t2 l1 l2 =
      match l1, l2 with
      | [], [] -> ()
      | [], _ | _, [] -> fail_ st t1 t2
      | x1::tl1, x2::tl2 ->
        aux st renaming x1 x2;
        aux_l st renaming t1 t2 tl1 tl2
    in
    try aux [] ID.Map.empty a b; Ok ()
    with E_unif_err st -> Error st

  let app env (f:expr) (a:expr) : expr =
    let loc = Loc.(f.loc ++ a.loc) in
    let ty = ty_app_ ~loc env f a in
    mk_ ~loc (App (f,a)) ty

  let app_l env f l = List.fold_left (fun f x -> app env f x) f l

  let let_ ~loc bs bod : expr = mk_ ~loc (Let (bs, bod)) (ty bod)

  let lambda ~loc v bod : expr =
    let ty_lam =
      let tyv = deref_ v.bv_ty in
      if is_eq_to_type tyv then (
        errorf (fun k->k"lambda: cannot bind on a type variable %a@ at %a"
                   BVar.pp v Loc.pp loc);
      ) else (
        ty_arrow ~loc tyv (ty bod)
      )
    in
    mk_ ~loc (Lambda (v, bod)) ty_lam

  let lambda_l ~loc vs bod : expr =
    List.fold_right (lambda ~loc) vs bod

  let eq a b : expr =
    let loc = Loc.(a.loc ++ b.loc) in
    mk_ ~loc (Eq (a,b)) bool
  let wildcard ~loc env : expr * meta =
    ty_meta ~loc env

  let to_string = Fmt.to_string @@ Fmt.hvbox pp

  let to_k_expr ?(subst=ID.Map.empty) (ctx:K.Ctx.t) (e:expr) : K.Expr.t =
    (* [bs] is the mapping from bound variables to expressions, with their
       binding point DB level. *)
    let rec aux (bs:_ ID.Map.t) k e : K.Expr.t =
      let recurse = aux bs k in
      let loc = loc e in
      (*Log.debugf 50 (fun k'->k' "@[<hv>>> conv-expr %a@ k: %d ty: %a@ bs: {@[%a@]}@]"
                       pp e k pp (ty e)
                       (ID.Map.pp ID.pp (Fmt.Dump.pair K.Expr.pp Fmt.int)) bs);*)
      match view e with
      | Meta {meta_deref=Some _; _} -> assert false
      | Meta {meta_deref=None; _} ->
        errorf (fun k->k"meta %a@ has not been generalized at %a"
                   pp e Loc.pp loc)
      | Kind ->
        errorf (fun k->k"cannot translate `kind`@ at %a" Loc.pp loc)
      | Type -> K.Expr.type_ ctx
      | Bool -> K.Expr.bool ctx
      | Var { v_name; v_ty } ->
        let ty = recurse v_ty in
        K.Expr.var ctx (K.Var.make v_name ty)
      | Ty_arrow (a, b) ->
        K.Expr.arrow ctx (recurse a) (recurse b)
      | BVar v ->
        begin match ID.Map.find v.bv_name bs with
          | (e, k_e) ->
            assert (k >= k_e);
            K.Expr.db_shift ctx e (k - k_e)
          | exception Not_found ->
            errorf
              (fun k->k"variable %a is not bound@ at %a"
                  pp e Loc.pp loc)
        end
      | Const c ->
        let args = List.map recurse c.args in
        K.Expr.const ctx c.c args
      | App (f, a) ->
        K.Expr.app ctx (recurse f) (recurse a)
      | Eq (a, b) ->
        K.Expr.app_eq ctx (recurse a) (recurse b)
      | Let (bindings, body) ->
        let bs' =
          List.fold_left
            (fun bs' (v,t) ->
               let t = recurse t in
               (* let does not bind anything in the final term, no need to change k *)
               ID.Map.add v.bv_name (t,k) bs')
            bs bindings
        in
        aux bs' k body
      | Lambda (v, bod) ->
        let ty = recurse v.bv_ty in
        let bs = ID.Map.add v.bv_name
            (K.Expr.bvar ctx 0 (K.Expr.db_shift ctx ty 1), k+1) bs in
        let bod = aux bs (k+1) bod in
        K.Expr.lambda_db ctx ~name:(ID.name v.bv_name) ~ty_v:ty bod
      | KExpr e -> e
    in
    let subst = ID.Map.map (fun v -> v, 0) subst in
    aux subst 0 e

  let rec as_queryable e = object
    inherit Queryable.t
    method loc = e.loc
    method pp out () = Fmt.fprintf out "@[<hv>expr: %a@ type: %a@]" pp e pp (ty e)
    method! children yield =
      let yield_e e = yield (as_queryable e) in
      let yield_bv v = yield (BVar.as_queryable v); yield (as_queryable v.bv_ty) in
      begin match view e with
        | Kind | Type | Bool | Const _ | Meta _ | Var _ | BVar _ | KExpr _ -> ()
        | Ty_arrow (a, b) | Eq (a,b) | App (a,b) -> yield_e a; yield_e b
        | Lambda (v, bod) -> yield_bv v; yield_e bod
        | Let (bs, bod) ->
          List.iter (fun (v,u) -> yield_bv v; yield_e u) bs; yield_e bod
      end

    method! def_loc : _ option =
      match view e with
      | BVar v -> Some v.bv_loc (* binding point *)
      | Const {c; _} ->
        let r = K.Const.def_loc c in
        Log.debugf 5 (fun k->k"def-loc for %a: %a" pp e (Fmt.opt Loc.pp) r);
        r
      | _ -> None
  end
end

module Subst = struct
  type t = subst

  let to_list l = l
  let empty : t = []
  let add v e s = (v,e) :: s

  let is_empty = CCList.is_empty
  let pp out (self:t) : unit =
    if is_empty self then Fmt.string out "{}"
    else (
      let pp_b out (v,t) =
        Fmt.fprintf out "(@[%a := %a@])" Var.pp v Expr.pp t
      in
      Fmt.fprintf out "@[<hv>{@,%a@,}@]"
        (pp_list ~sep:" " pp_b) self
    )
  let to_string = Fmt.to_string pp

  let to_k_subst ?(subst=ID.Map.empty) ctx (self:t) =
    List.fold_left
      (fun s (v,t) ->
         let v = K.Var.make v.v_name (Expr.to_k_expr ~subst ctx v.v_ty) in
         let t = Expr.to_k_expr ~subst ctx t in
         K.Subst.bind s v t)
      K.Subst.empty self
end

let name_with_def_as_q ?def_loc (name:string) ~loc pp_def def : Queryable.t =
  let pp out () = Fmt.fprintf out "%s :=@ %a" name pp_def def in
  Queryable.mk_pp ?def_loc ~loc ~pp ()
let id_with_def_as_q ?def_loc (id:ID.t) ~loc pp_def def : Queryable.t =
  let pp out () = Fmt.fprintf out "%a :=@ %a" ID.pp id pp_def def in
  Queryable.mk_pp ?def_loc ~loc ~pp ()

module Ty_env = struct
  type t = ty_env

  let declare_const name (c:K.const A.with_loc) (self:t) : t =
    Log.debugf 5 (fun k->k"declare new const@ :name %S@ :expr %a@ :ty %a@ :ty-vars %a"
                     name K.Const.pp c.A.view K.Expr.pp (K.Const.ty c.A.view)
                     K.Const.pp_args (K.Const.args c.view));
    {self with env_consts = Str_map.add name c self.env_consts}

  let define_thm name th (self:t) : t =
    {self with env_theorems = Str_map.add name th self.env_theorems }

  type named_object =
    | N_const of K.const A.with_loc
    | N_thm of K.Thm.t A.with_loc
    | N_rule of Proof.Rule.t A.with_loc

  let find_rule (_self:t) name : KProof.Rule.t option =
    match Proof.Rule.find_builtin name with
    | Some _ as r -> r
    | None ->
      None (* TODO: lookup in locally defined rules *)

  let find_const self name : K.const A.with_loc option =
    Str_map.get name self.env_consts

  let find_thm self name : K.Thm.t A.with_loc option =
    Str_map.get name self.env_theorems

  let find_named (self:t) name : named_object option =
    try Some (N_const (Str_map.find name self.env_consts))
    with Not_found ->
    try Some (N_thm (Str_map.find name self.env_theorems))
    with Not_found ->
    match find_rule self name with
    | Some r -> Some (N_rule {view=r; loc=noloc}) (* FIXME: store location for defined rules *)
    | None ->
      None (* TODO: look in local defined rules *)

  let empty : t = ty_env_empty_

  let iter (self:t) : _ Iter.t =
    let i1 =
      Str_map.to_iter self.env_consts
      |> Iter.map (fun (n,c) -> n, N_const c)
    and i2 =
      Str_map.to_iter self.env_theorems
      |> Iter.map (fun (n,th) -> n, N_thm th)
    and i3 =
      (* TODO: locally defined rules *)
      Iter.of_list Proof.Rule.builtins
      |> Iter.map (fun r -> Proof.Rule.name r, N_rule {A.view=r;loc=noloc})
    in
    Iter.append_l [i3; i1; i2]

  let completions (self:t) (s:string) : _ Iter.t =
    iter self
    |> Iter.filter (fun (name,_) -> CCString.prefix ~pre:s name)

  let pp_named_object out = function
    | N_const c ->
      Fmt.fprintf out "%a : %a" K.Const.pp c.A.view K.Expr.pp (K.Const.ty c.A.view)
    | N_thm th -> K.Thm.pp_quoted out th.A.view
    | N_rule r ->
      let module R = Proof.Rule in
      Fmt.fprintf out "%a : %a" R.pp r.A.view R.pp_signature (R.signature r.A.view)

  let string_of_named_object = Fmt.to_string pp_named_object

  let loc_of_named_object = function
    | N_const e -> e.A.loc
    | N_rule r -> r.A.loc
    | N_thm th -> th.A.loc

  let pp out (self:t) : unit =
    let k_of_no = function
      | N_const _ -> "expr"
      | N_thm _ -> "thm"
      | N_rule _ -> "rule"
    in
    let pp_pair out (name,c) = Fmt.fprintf out "(@[%s : %s@])" name (k_of_no c) in
    Fmt.fprintf out "{@[<hv>ty_env@ %a@;<0 -1>@]}" (Fmt.iter pp_pair) (iter self)

  let name_with_def_as_q ~loc (n:named_object) : Queryable.t = object
    inherit Queryable.t
    method loc = loc
    method! def_loc = Some (loc_of_named_object n)
    method pp out () = match n with
      | N_const c -> K.Const.pp out c.view
      | N_thm th -> K.Thm.pp_quoted out th.view
      | N_rule r -> Proof.Rule.pp out r.view
  end

  let to_string = Fmt.to_string pp
end

(** {2 Typing state}

    This environment is (mostly) functional, and is used to handle
    scoping and to map names into constants and expressions and their type.
*)
module Typing_state = struct
  type t = typing_state

  let copy self = {self with to_gen=self.to_gen}
  let ty_env self = self.ty_env

  let generalize_ty_vars (self:t) : unit =
    let metas = self.to_gen in
    self.to_gen <- metas;
    List.iter
      (fun m ->
         match m.meta_deref with
         | Some _ -> ()
         | None ->
           (* TODO: emit warning if this is a type variable *)
           let v = Var.make m.meta_name m.meta_type in
           m.meta_deref <- Some (Expr.var ~loc:noloc v))
      metas;
    ()

  let declare_const (self:t) name c : unit =
    self.ty_env <- Ty_env.declare_const name c self.ty_env

  let define_thm (self:t) name th : unit =
    self.ty_env <- Ty_env.define_thm name th self.ty_env

  type named_object = Ty_env.named_object

  let find_thm self name : K.Thm.t A.with_loc option =
    Ty_env.find_thm self.ty_env name

  let find_named (self:t) name : named_object option =
    Ty_env.find_named self.ty_env name

  let create ?ty_env ctx : t =
    let ty_env = match ty_env with
      | Some e -> e
      | None ->
        Ty_env.empty
        |> Ty_env.declare_const "bool" {A.view=K.Const.bool ctx; loc=noloc}
    in
    let env = {
      ctx;
      cur_file="";
      gensym=0;
      ty_env;
      fvars=Str_map.empty;
      notation=Notation.empty_hol;
      to_gen=[];
    } in
    env
end

(** {2 Processing proofs} *)
module Proof = struct
  module R = Proof.Rule

  type t = {
    loc: location;
    view: view
  }

  and view =
    | Proof_atom of step
    | Proof_steps of {
        lets: pr_let list;
        (** intermediate steps *)
        ret: step;
        (** proof to return *)
      }

  (** named steps *)
  and pr_let =
    | Let_expr of bvar * expr
    | Let_step of ID.t A.with_loc * step

  and step = {
    s_loc: location;
    s_view: step_view;
    mutable s_thm: K.Thm.t option
  }

  (* TODO: put a loc on each rule and rule_arg, so we can query them *)
  and step_view =
    | Pr_apply_rule of Proof.Rule.t A.with_loc * rule_arg list
    | Pr_sub_proof of t
    | Pr_error of unit Fmt.printer (* parse error *)

  (** An argument to a rule *)
  and rule_arg =
    | Arg_var_step of {
        name: ID.t;
        loc: location; (* loc of the variable *)
        points_to: step;
      }
    | Arg_step of step
    | Arg_thm of K.Thm.t A.with_loc * location
    | Arg_expr of expr
    | Arg_subst of subst

  type rule_signature = Proof.Rule.signature

  let[@inline] view p = p.view
  let[@inline] loc p = p.loc

  let rec pp out (self:t) : unit =
    Fmt.fprintf out "@[<hv>@[<hv2>proof@ ";
    begin match self.view with
      | Proof_atom s -> pp_step ~top:true out s
      | Proof_steps {lets; ret} ->
        List.iter (fun l -> Fmt.fprintf out "%a@ " pp_pr_let l) lets;
        pp_step ~top:true out ret
    end;
    Fmt.fprintf out "@]@ end@]"

  and pp_pr_let out = function
    | Let_expr (v,e) ->
      Fmt.fprintf out "@[<2>let expr %a =@ %a in@]" BVar.pp v Expr.pp e
    | Let_step (name,p) ->
      Fmt.fprintf out "@[<2>let %a =@ %a in@]"
        ID.pp name.view (pp_step ~top:true) p

  and pp_step ~top out (s:step) : unit =
    match s.s_view with
    | Pr_apply_rule (r, []) when top -> R.pp out r.view
    | Pr_apply_rule (r, args) ->
      if not top then Fmt.char out '(';
      Fmt.fprintf out "@[<hv2>%a@ %a@]" R.pp r.view (pp_list pp_rule_arg) args;
      if not top then Fmt.char out ')';
    | Pr_sub_proof p -> pp out p
    | Pr_error e -> Fmt.fprintf out "<@[error:@ %a@]>" e ()

  and pp_step_with_res out (self:step) : unit =
    Fmt.fprintf out "`@[%a@]`%a"
      (pp_step ~top:true) self (pp_step_res "returns") self

  and pp_step_res sep out (self:step) : unit =
    match self.s_thm with
    | None -> ()
    | Some th -> Fmt.fprintf out "@ %s %a" sep K.Thm.pp_quoted th

  and pp_rule_arg out (a:rule_arg) : unit =
    match a with
    | Arg_var_step {name; points_to; _} ->
      Fmt.fprintf out "@[%a%a@]" ID.pp name (pp_step_res ":=") points_to
    | Arg_step s -> pp_step ~top:false out s (* always in ( ) *)
    | Arg_thm (th,_) -> K.Thm.pp_quoted out th.view
    | Arg_expr e -> Expr.pp out e
    | Arg_subst s -> Subst.pp out s

  (* expose a proof to LSP queries *)
  let rec as_queryable (self:t) : Queryable.t = object
    inherit Queryable.t
    method pp out () = pp out self
    method loc = self.loc
    method! children =
      match self.view with
      | Proof_atom a -> Iter.return (step_as_q a)
      | Proof_steps {lets; ret} ->
        Iter.cons (step_as_q ret)
          (Iter.of_list lets |> Iter.flat_map let_as_q)
  end
  and step_as_q (self:step) : Queryable.t = object
    inherit Queryable.t
    method pp out () = pp_step_with_res out self
    method loc = self.s_loc
    method! children = match self.s_view with
      | Pr_apply_rule (r, l) ->
        Iter.cons (rule_as_q r)
          (Iter.of_list l |> Iter.filter_map arg_q)
      | Pr_sub_proof p -> Iter.return (as_queryable p)
      | Pr_error _ -> Iter.empty
  end
  and rule_as_q (r:R.t A.with_loc) : Queryable.t = object
    inherit Queryable.t
    method loc = r.loc
    method pp out () =
      (* TODO: inline doc for each rule *)
      Fmt.fprintf out "@[<v>rule %a.@ @[<hv>signature:@ %a@]@]" R.pp r.view
        R.pp_signature (R.signature r.view)
  end
  and arg_q (self:rule_arg) : Queryable.t option =
    match self with
    | Arg_step s -> Some (step_as_q s)
    | Arg_expr e -> Some (Expr.as_queryable e)
    | Arg_thm (th,loc) ->
      Some (Queryable.mk_pp ~def_loc:th.loc ~loc ~pp:K.Thm.pp_quoted th.view)
    | Arg_var_step v ->
      Some (Queryable.mk_pp ~def_loc:v.points_to.s_loc ~loc:v.loc ~pp:pp_rule_arg self)
    | Arg_subst _ -> None
  and let_as_q (l:pr_let) : Queryable.t Iter.t =
    match l with
    | Let_expr (v, e) ->
      Iter.of_list [BVar.as_queryable v; Expr.as_queryable e]
    | Let_step (v, s) ->
      let v_as_q = match s.s_thm with
        | None -> []
        | Some th ->
          [id_with_def_as_q v.view ~loc:v.loc K.Thm.pp_quoted th]
      in
      Iter.of_list (v_as_q @ [step_as_q s])

  let to_string = Fmt.to_string pp
  let pp_rule_signature = R.pp_signature

  let iter_subs (p:t) : t Iter.t =
    match p.view with
    | Proof_atom _
    | Proof_steps _ -> Iter.empty (* TODO *)

  let mk ~loc (view:view) : t = {view; loc}
  let mk_step ~loc (s_view:step_view) : step =
    {s_view; s_loc=loc; s_thm=None; }

  type env = {
    e_subst: K.Expr.t ID.Map.t;
    e_th: K.Thm.t ID.Map.t; (* steps *)
  }

  (* how to run a proof, and obtain a theorem at the end *)
  let run_exn ?(on_step_res=fun _ _ ->())
      (ctx:K.Ctx.t) (self:t) : K.Thm.t =
    let module KR = KProof.Rule in
    let rec run_pr (env:env) (p:t) =
      let loc = p.loc in
      try
        match p.view with
        | Proof_atom s -> run_step env s
        | Proof_steps { lets; ret } ->
          let env =
            List.fold_left
              (fun env l ->
                match l with
                | Let_expr (v,u) ->
                  let u = Expr.to_k_expr ~subst:env.e_subst ctx u in
                  {env with e_subst=ID.Map.add v.bv_name u env.e_subst}
                | Let_step (name,s) ->
                  let th = run_step env s in
                  on_step_res s th;
                  {env with e_th = ID.Map.add name.view th env.e_th})
              env lets in
          run_step env ret
      with e ->
        errorf ~src:e (fun k->k"@[<2>while checking proof@ at %a@]" Loc.pp loc)

    and run_step env (s:step) : K.Thm.t =
      let loc = s.s_loc in
      match s.s_thm with
      | Some th -> th
      | None ->
        let th =
          try
            match s.s_view with
            | Pr_sub_proof p -> run_pr env p
            | Pr_error e ->
              errorf (fun k->k"invalid proof step@ at %a:@ %a" Loc.pp loc e())
            | Pr_apply_rule (r, args) ->
              let args = List.map (conv_arg ~loc env) args in
              Log.debugf 10
                (fun k->k"apply rule %a@ to args %a"
                    KR.pp r.view (Fmt.Dump.list KR.pp_arg_val) args);
              KR.apply ctx r.view args
          with e ->
            errorf ~src:e
              (fun k->k"@[<2>while checking proof step@ at %a@]"
                  Loc.pp loc)
        in
        s.s_thm <- Some th; (* cache the result *)
        th

    (* convert a rule argument *)
    and conv_arg ~loc env = function
      | Arg_expr e ->
        KR.AV_expr (Expr.to_k_expr ~subst:env.e_subst ctx e)
      | Arg_subst s ->
        KR.AV_subst (Subst.to_k_subst ~subst:env.e_subst ctx s)
      | Arg_step s ->
        let th = run_step env s in
        KR.AV_thm th
      | Arg_thm (th,_) -> KR.AV_thm th.view
      | Arg_var_step v ->
        begin match ID.Map.find v.name env.e_th with
          | th -> KR.AV_thm th
          | exception Not_found ->
            errorf
              (fun k->k"unbound proof step `%a`@ at %a" ID.pp v.name Loc.pp loc)
        end
    in
    run_pr {e_th=ID.Map.empty; e_subst=ID.Map.empty} self

  let run ?on_step_res ctx (self:t) : K.Thm.t or_error =
    try Ok (run_exn ?on_step_res ctx self)
    with Trustee_error.E e -> Error e
end

module Goal = struct
  type t = {
    hyps: expr list;
    concl: expr;
    loc: location;
  }

  let make ~loc hyps concl : t = {hyps; concl; loc}
  let pp out (self:t) : unit =
    if CCList.is_empty self.hyps then (
      Fmt.fprintf out "@[?-@ %a@]" Expr.pp self.concl
    ) else (
      Fmt.fprintf out "@[<hv>%a@ ?-@ %a@]"
        (pp_list ~sep:", " Expr.pp) self.hyps
        Expr.pp self.concl
    )
  let to_string = Fmt.to_string pp

  let as_queryable (self:t) : Queryable.t = object
    inherit Queryable.t
    method loc = self.loc
    method pp out () = pp out self
    method! children =
      Iter.cons (Expr.as_queryable self.concl)
        (Iter.of_list self.hyps |> Iter.map Expr.as_queryable)
  end

  let to_k_goal ctx self : K.Goal.t =
    K.Goal.make_l
      (List.map (Expr.to_k_expr ctx) self.hyps)
      (Expr.to_k_expr ctx self.concl)
end

module Thm = K.Thm

(** {2 type inference} *)
module Ty_infer = struct
  type st = typing_state

  let unif_exn_ ~loc e a b = match Expr.unif_ a b with
    | Ok () -> ()
    | Error st ->
      errorf
        (fun k->k
            "@[<hv2>type error@ \
             @[while inferring the type @[<2>of %a@ at %a@]@]:@ \
             unification error in the following trace:@ %a@]"
            AE.pp e Loc.pp loc Expr.pp_unif_trace_ st)

  let unif_type_with_ ~loc e ty = match Expr.unif_ (Expr.ty e) ty with
    | Ok () -> ()
    | Error st ->
      errorf
        (fun k->k
            "@[<hv2>type error@ \
             @[<2>while unifying the type @[<2>of %a@ at %a@]@ with %a@]:@ \
             unification error in the following trace:@ %a@]"
            Expr.pp e Loc.pp loc Expr.pp ty
            Expr.pp_unif_trace_ st)

  type binding = BV of bvar | V of var

  let infer_expr_full_ ~bv:bv0
      (st:typing_state) (vars:A.var list) (e0:AE.t) : bvar list * expr =
    (* type inference.
       @param bv the local variables, for scoping *)
    let rec inf_rec_ (bv:binding Str_map.t) (e:AE.t) : expr =
      let loc = AE.loc e in
      (* Log.debugf 15 (fun k->k"infer-rec loc=%a e=`%a`" Loc.pp loc AE.pp e); *)
      let unif_exn_ a b = unif_exn_ ~loc e a b in
      begin match AE.view e with
        | A.Type -> Expr.type_
        | A.Ty_arrow (a, b) -> Expr.ty_arrow ~loc (inf_rec_ bv a) (inf_rec_ bv b)
        | A.Var v when Str_map.mem v.A.v_name bv ->
          (* use variable in scope, but change location of the expression *)
          begin match Str_map.find v.A.v_name bv with
            | BV bv -> Expr.bvar ~loc bv (* bound variable *)
            | V v -> Expr.var ~loc v
          end
        | A.Var va ->
          let v =
            match Str_map.find va.A.v_name st.fvars with
            | v' ->
              begin match va.A.v_ty with
                | Some ty ->
                  (* unify expected type with actual type *)
                  let ty = inf_rec_ bv ty in
                  unif_exn_ ty v'.v_ty
                | None -> ()
              end;
              v'
            | exception Not_found ->
              let ty = match va.A.v_ty with
                | Some ty -> inf_rec_ bv ty
                | None ->
                  let ty, m = Expr.ty_meta ~loc st in
                  st.to_gen <- m :: st.to_gen;
                  ty
              in
              let v = Var.make va.A.v_name ty in
              st.fvars <- Str_map.add v.v_name v st.fvars;
              v
          in
          Expr.var ~loc v
        | A.Wildcard ->
          let t, m = Expr.wildcard ~loc st in
          st.to_gen <- m :: st.to_gen;
          t
        | A.Meta {name;ty} ->
          let ty = match ty with
            | None -> Expr.type_
            | Some ty -> inf_rec_ bv ty
          in
          let t, m = Expr.meta ~loc name ty in
          st.to_gen <- m :: st.to_gen;
          t
        | A.Eq (a,b) ->
          let a = inf_rec_ bv a in
          let b = inf_rec_ bv b in
          unif_exn_ (Expr.ty a) (Expr.ty b);
          Expr.eq a b
        | A.K_expr e -> Expr.of_k_expr ~loc e
        | A.K_const c -> infer_const_ ~loc st c
        | A.App (f,a) ->
          let f = inf_rec_ bv f in
          let a = inf_rec_ bv a in
          Expr.app st f a
        | A.With (vs, bod) ->
          let bv =
            List.fold_left
              (fun bv v ->
                 let ty = infer_ty_opt_ ~loc ~default:Expr.type_ bv v.A.v_ty in
                 let var = Var.make v.A.v_name ty in
                 Str_map.add v.A.v_name (V var) bv)
              bv vs
          in
          inf_rec_ bv bod
        | A.Lambda (vars, bod) ->
          let bv, vars =
            CCList.fold_map
              (fun bv v ->
                 let v' = infer_bvar_ bv v in
                 Str_map.add v.A.v_name (BV v') bv, v')
              bv vars
          in
          let bod = inf_rec_ bv bod in
          Expr.lambda_l ~loc vars bod
        | A.Bind { b; b_loc=_; vars; body } ->
          let f = inf_rec_ bv b in
          Log.debugf 5 (fun k->k"binder: f=%a@ ty=%a" Expr.pp f Expr.pp (Expr.ty f));
          let bv, vars =
            CCList.fold_map
              (fun bv v ->
                 let v' = infer_bvar_ bv v in
                 Str_map.add v.A.v_name (BV v') bv, v')
              bv vars
          in
          let body = inf_rec_ bv body in
          Log.debugf 5 (fun k->k"body: f=%a@ ty=%a" Expr.pp body Expr.pp (Expr.ty body));
          (* now for each [v], create [f (\x. bod)] *)
          CCList.fold_right
            (fun bv body ->
               let lam = Expr.lambda ~loc bv body in
               let e = Expr.app st f lam in
               Log.debugf 5 (fun k->k"app: f=%a@ ty=%a" Expr.pp e Expr.pp (Expr.ty e));
               e)
            vars body
        | A.Let (bindings, body) ->
          let bv', bindings =
            CCList.fold_map
              (fun bv' (v,t) ->
                 let v' = infer_bvar_ bv v in
                 let t = inf_rec_ bv t in
                 unif_exn_ v'.bv_ty (Expr.ty t);
                 let bv' = Str_map.add v.A.v_name (BV v') bv' in
                 bv', (v', t))
              bv bindings
          in
          Expr.let_ ~loc bindings @@ inf_rec_ bv' body
        end

    and infer_const_ ~loc env c : expr =
      (*Log.debugf 50 (fun k->k"infer-const %a at %a" A.Const.pp c Loc.pp loc);*)
      let arity =
        match K.Const.args c with
        | K.Const.C_arity n -> n
        | K.Const.C_ty_vars vs -> List.length vs
      in
      let args =
        CCList.init arity
          (fun _ ->
             let ty, m = Expr.ty_meta ~loc env in
             env.to_gen <- m :: env.to_gen;
             ty)
      in
      Expr.const ~loc c args

    and infer_ty_opt_ ~loc ?default bv ty : ty =
      match ty with
      | None ->
        begin match default with
          | Some ty -> ty
          | None ->
            let ty, m = Expr.ty_meta ~loc st in
            st.to_gen <- m :: st.to_gen;
            ty
        end
      | Some ty0 ->
        let ty = inf_rec_ bv ty0 in
        if not @@ (Expr.is_a_type ty || Expr.is_eq_to_type ty) then (
          unif_exn_ ~loc ty0 ty Expr.type_;
        );
        ty
    and infer_bvar_ ?default bv v : bvar =
      let ty_v = infer_ty_opt_ ?default ~loc:v.A.v_loc bv v.A.v_ty in
      let v' = BVar.make ~loc:v.A.v_loc (ID.make v.A.v_name) ty_v in
      v'
    in
    let bv, vars =
      CCList.fold_map
        (fun bv v ->
           let v' = infer_bvar_ bv v in
           Str_map.add v.A.v_name (BV v') bv, v')
        bv0 vars
    in
    let e = inf_rec_ bv e0 in
    vars, e

  let infer_expr_vars env vars e0 : bvar list * expr =
    infer_expr_full_ ~bv:Str_map.empty env vars e0

  let infer_expr (st:st) (e0:AE.t) : expr =
    let _, e = infer_expr_vars st [] e0 in
    e

  let infer_expr_with_ty env e0 ty : expr =
    let e = infer_expr env e0 in
    unif_exn_ ~loc:(AE.loc e0) e0 ty (Expr.ty e);
    e

  let infer_ty env e0 : ty =
    let e = infer_expr env e0 in
    if not @@ (Expr.is_eq_to_type e || Expr.is_a_type e) then (
      (* if not already a type or kind, force it to be *)
      unif_exn_ ~loc:(AE.loc e0) e0 (Expr.ty e) (Expr.ty e);
    );
    e

  let infer_expr_bool env e0 : expr =
    infer_expr_with_ty env e0 Expr.bool

  let infer_goal st (g:A.Goal.t) : Goal.t * K.Goal.t =
    let hyps = List.map (infer_expr_bool st) g.A.Goal.hyps in
    let concl = infer_expr_bool st g.A.Goal.concl in
    Typing_state.generalize_ty_vars st;
    let loc =
      List.fold_left (fun loc e -> Loc.merge loc (Expr.loc e))
        (Expr.loc concl) hyps
    in
    let goal = Goal.make ~loc hyps concl in
    let kgoal = Goal.to_k_goal st.ctx goal in
    goal, kgoal

  let and_then_generalize st f =
    let x = f() in
    Typing_state.generalize_ty_vars st;
    x

  type pr_env = {
    e_expr: binding Str_map.t;
    e_step: (ID.t * Proof.step) Str_map.t;
  }

  let infer_proof (st:st) (pr:A.Proof.t) : Proof.t =
    let ty_env = st.ty_env in
    let rec infer_proof (pr_env:pr_env) (pr:A.Proof.t) : Proof.t =
      let loc = A.Proof.loc pr in
      match A.Proof.view pr with
      | A.Proof.Proof_atom s ->
        let s = infer_step pr_env s in
        Proof.mk ~loc (Proof.Proof_atom s)
      | A.Proof.Proof_steps { lets; ret } ->
        (* convert let-steps, inline let-expr bindings *)
        let pr_env = ref pr_env in
        let lets =
          CCList.map
            (function
              | A.Proof.Let_expr (name,e) ->
                let _, e = infer_expr_full_ ~bv:(!pr_env).e_expr st [] e in
                let bv = BVar.make ~loc:name.loc (ID.make name.view) (Expr.ty e) in
                pr_env := {
                  (!pr_env) with
                  e_expr=Str_map.add name.view (BV bv) (!pr_env).e_expr;
                };
                Proof.Let_expr (bv, e)
              | A.Proof.Let_step (name,s) ->
                let name_id = ID.make name.view in
                let s = infer_step !pr_env s in
                pr_env := {
                  (!pr_env) with
                  e_step=Str_map.add name.view (name_id,s) (!pr_env).e_step;
                };
                Proof.Let_step ({A.view=name_id; loc=name.loc}, s))
            lets
        in
        let ret = infer_step !pr_env ret in
        Proof.mk ~loc (Proof.Proof_steps {lets; ret})
    (* convert individual steps *)
    and infer_step (pr_env:pr_env) (s:A.Proof.step) : Proof.step =
      let loc = A.Proof.s_loc s in
      match A.Proof.s_view s with
      | A.Proof.Pr_error e ->
        Proof.mk_step ~loc (Proof.Pr_error e)
      | A.Proof.Pr_apply_rule (r, args) ->
        let r_loc = r.loc in
        let r = match Ty_env.find_rule ty_env r.view with
          | None ->
            errorf (fun k->k"unknown rule '%s'@ at %a" r.view Loc.pp loc)
          | Some r -> r
        in
        let args = List.map (conv_arg pr_env) args in
        Proof.mk_step ~loc (Proof.Pr_apply_rule ({view=r;loc=r_loc}, args))
      | A.Proof.Pr_sub_proof p ->
        let p = infer_proof pr_env p in
        Proof.mk_step ~loc (Proof.Pr_sub_proof p)

    and conv_arg (pr_env:pr_env) (a:A.Proof.rule_arg) : Proof.rule_arg =
      match a with
      | A.Proof.Arg_var s ->
        let loc = s.A.loc in
        begin match
            Str_map.get s.A.view pr_env.e_expr,
            Str_map.get s.A.view pr_env.e_step
          with
          | Some (BV bv), _ -> Proof.Arg_expr (Expr.bvar ~loc bv)
          | Some (V v), _ -> Proof.Arg_expr (Expr.var ~loc v)
          | None, Some (id,s) -> Proof.Arg_var_step {name=id; loc; points_to=s}
          | None, None ->
            begin match Typing_state.find_thm st s.A.view with
              | Some th -> Proof.Arg_thm (th, loc)
              | None ->
                errorf
                  (fun k->k "unknown proof variable '%s'@ at %a" s.view Loc.pp loc)
            end
        end
      | A.Proof.Arg_step s ->
        let s = infer_step pr_env s in
        Proof.Arg_step s
      | A.Proof.Arg_expr e ->
        let _, e = infer_expr_full_ ~bv:pr_env.e_expr st [] e in
        Proof.Arg_expr e
      | A.Proof.Arg_subst _s ->
        errorf (fun k->k"TODO: convert subst")
    in
    let e0 = {e_expr=Str_map.empty; e_step=Str_map.empty} in
    infer_proof e0 pr
end

module Index = struct
  (* TODO: at some point, if [qs] is too large, group them into sub-lists
     wrapped in a "queryable" that has as location the merge of all their locations.
     This is a very simple form of indexing *)

  type idx = {
    qs: Queryable.t list;
    ty_envs: (location * ty_env) list;
  }

  type t =
    | Fake
    | Idx of idx

  let empty : t = Idx {qs=[]; ty_envs=[]}
  let fake : t = Fake

  let size = function
    | Idx {qs;_} -> List.length qs
    | Fake -> 0

  let find (self:t) (pos:Position.t) : Queryable.t list =
    let rec aux (q:Queryable.t) : _ list option =
      Log.debugf 20 (fun k->k"(@[examine queryable@ `%a`@ at %a@])" q#pp () Loc.pp q#loc);
      if Loc.contains q#loc pos then (
        Log.debugf 5 (fun k->k"(@[matched queryable@ `%a`@ at %a@])" q#pp () Loc.pp q#loc);
        let sub = Iter.find_map aux q#children |> CCOpt.get_or ~default:[] in
        Some (q::sub)
      ) else None
    in
    begin match self with
    | Fake -> []
    | Idx {qs;_} ->
      match CCList.find_map aux qs with
      | None -> []
      | Some l -> List.rev l (* put deeper result first *)
    end

  let update_ (self:t ref) ~f =
    begin match !self with
      | Idx idx -> self := Idx (f idx)
      | Fake -> ()
    end

  let add_q (self:t ref) x : unit =
    update_ self ~f:(fun idx -> {idx with qs=x::idx.qs})
  let add_env (self:t ref) env ~loc : unit =
    update_ self ~f:(fun idx -> {idx with ty_envs = (loc,env) :: idx.ty_envs})

  let find_ty_env (self:t) (pos:Position.t) : ty_env =
    let rec find = function
      | [] -> Ty_env.empty
      | (loc, env) :: _ when Loc.contains loc pos -> env
      | _ :: tl -> find tl
    in
    match self with
    | Fake -> Ty_env.empty
    | Idx idx -> find idx.ty_envs
end

module Process_stmt = struct
  type t = {
    st: Typing_state.t;
    on_show: location -> unit Fmt.printer -> unit;
    on_error: location -> unit Fmt.printer -> unit;
  }

  let reset_ (self:t) =
    self.st.fvars <- Str_map.empty;
    ()

  let top_decl_ ~loc self name ty : ty =
    let ty =
      Ty_infer.and_then_generalize self.st
        (fun () -> Ty_infer.infer_ty self.st ty)
    in
    let kty = Expr.to_k_expr self.st.ctx ty in
    let ty_vars = [] in (* FIXME: use free vars of kty? *)
    let c = K.Expr.new_const ~def_loc:loc self.st.ctx name ty_vars kty in
    Typing_state.declare_const self.st name {A.view=c;loc};
    ty

  let top_def_ ~loc self name (th_name:string A.with_loc option)
      vars ret body : ty * expr * K.Thm.t =
    (* turn [def f x y := bod] into [def f := \x y. bod] *)
    let vars, e = Ty_infer.infer_expr_vars self.st vars body in
    let def_rhs = Expr.lambda_l ~loc:e.loc vars e in
    let ty_rhs = Expr.ty def_rhs in
    (* now ensure that [f vars : ret] *)
    let ty_ret = match ret with
      | None -> ty_rhs
      | Some ret ->
        let ret = Ty_infer.infer_ty self.st ret in
        (* [ret] should be the type of [real_def x1…xn] *)
        let e_app =
          Expr.app_l self.st def_rhs
            (List.map
               (fun bv -> Expr.var' ~loc:bv.bv_loc (ID.name bv.bv_name) bv.bv_ty)
               vars)
        in
        Ty_infer.unif_type_with_ ~loc e_app ret;
        ret
    in
    Typing_state.generalize_ty_vars self.st;
    (* the defining equation `name = def_rhs` *)
    let def_eq = Expr.eq (Expr.var' ~loc:name.A.loc name.A.view ty_rhs) def_rhs in
    let th, ke =
      K.Thm.new_basic_definition self.st.ctx ~def_loc:loc
        (Expr.to_k_expr self.st.ctx def_eq) in
    Typing_state.declare_const self.st name.A.view {A.view=ke;loc};
    CCOpt.iter
      (fun th_name -> Typing_state.define_thm self.st th_name.A.view {A.view=th;loc}) th_name;
    ty_ret, def_rhs, th

  let top_show_ self ~loc s : bool * Queryable.t list =
    let named = Typing_state.find_named self.st s in
    begin match named with
      | Some (Ty_env.N_const c as n) ->
        self.on_show loc (fun out () ->
            Fmt.fprintf out "@[<2>expr:@ `@[%a@]`@ with type: %a@]" K.Const.pp c.A.view
              K.Expr.pp (K.Const.ty c.A.view));
        true, [Ty_env.name_with_def_as_q ~loc n]
      | Some (Ty_env.N_thm th as n) ->
        self.on_show loc (fun out () ->
            Fmt.fprintf out "@[<2>theorem:@ %a@]" K.Thm.pp_quoted th.A.view);
        true, [Ty_env.name_with_def_as_q ~loc n]
      | Some (Ty_env.N_rule r as n) ->
        self.on_show loc (fun out () ->
            Fmt.fprintf out "@[<2>rule:@ %a@]" KProof.Rule.pp r.A.view);
        true, [Ty_env.name_with_def_as_q ~loc n]
      | None ->
        self.on_show loc (fun out () -> Fmt.fprintf out "not found");
        false, []
    end

  let top_axiom_ self name thm : expr =
    let e =
      Ty_infer.and_then_generalize self.st
        (fun () -> Ty_infer.infer_expr_with_ty self.st thm Expr.bool)
    in
    let ke = Expr.to_k_expr self.st.ctx e in
    let th = K.Thm.axiom self.st.ctx [] ke in
    Typing_state.define_thm self.st name {A.view=th;loc=e.loc};
    e

  let top_proof_ self proof : Proof.t * K.Thm.t or_error =
    (* convert proof *)
    let pr =
      Ty_infer.infer_proof self.st proof
    in
    Log.debugf 10 (fun k->k"typed proof:@ %a" Proof.pp pr);
    let th = Proof.run
        self.st.ctx pr
        ~on_step_res:(fun s th ->
            self.on_show s.Proof.s_loc
              (fun out() -> K.Thm.pp_quoted out th))
    in
    pr, th

  let top_goal_ ~loc self goal proof : bool * Goal.t * Proof.t =
    let goal, kgoal = Ty_infer.infer_goal self.st goal in
    Log.debugf 5 (fun k->k"inferred goal:@ %a" K.Goal.pp kgoal);
    let pr, th = top_proof_ self proof in
    begin match th with
      | Ok th when K.Thm.is_proof_of th kgoal ->
        self.on_show loc
          (fun out() ->
             Fmt.fprintf out "@[<2>goal proved@ with theorem %a@]" K.Thm.pp_quoted th);
        true, goal, pr
      | Ok th ->
        self.on_error loc
          (fun out() ->
             Fmt.fprintf out "@[<2>proof@ yields theorem %a@ but goal was %a@]"
               K.Thm.pp_quoted th K.Goal.pp kgoal);
        false, goal, pr
      | Error e ->
        self.on_error loc
          (fun out() ->
             Fmt.fprintf out "@[<2>proof is not valid@ %a@]"
               Trustee_error.pp e);
        false, goal, pr
    end

  let top_thm_ ~loc self name goal proof : bool * Goal.t * Proof.t * K.Thm.t option =
    let goal, kgoal = Ty_infer.infer_goal self.st goal in
    Log.debugf 5 (fun k->k"inferred goal:@ %a" K.Goal.pp kgoal);
    let pr, th = top_proof_ self proof in
    begin match th with
      | Ok th when K.Thm.is_proof_of th kgoal ->
        Typing_state.define_thm self.st name {A.view=th;loc=goal.loc};
        true, goal, pr, Some th
      | Ok th ->
        self.on_error loc
          (fun out() ->
             Fmt.fprintf out "@[<2>proof@ yields theorem %a@ but goal was %a@]"
               K.Thm.pp_quoted th K.Goal.pp kgoal);
        false, goal, pr, Some th
      | Error e ->
        self.on_error loc
          (fun out() ->
             Fmt.fprintf out "@[<2>proof@ is invalid:@ %a@]"
               Trustee_error.pp e);
        false, goal, pr, None
    end

  let top_ (self:t) st (idx:Index.t) : Index.t =
    Log.debugf 2 (fun k->k"(@[TA.process-stmt@ `%a`@])" A.Top_stmt.pp st);
    reset_ self;
    let idx = ref idx in
    let loc = A.Top_stmt.loc st in
    Index.add_env idx ~loc self.st.ty_env;
    let ok =
      try
        match A.Top_stmt.view st with
        | A.Top_enter_file s ->
          self.st.cur_file <- s;
          true
        | A.Top_decl { name; ty } ->
          let ty = top_decl_ ~loc self name.view ty in
          Index.add_q idx (name_with_def_as_q ~loc:name.loc name.view Expr.pp ty);
          Index.add_q idx (Expr.as_queryable ty);
          true
        | A.Top_def { name; th_name; vars; ret; body } ->
          let ty_ret, rhs, th = top_def_ self ~loc name th_name vars ret body in
          Log.debugf 5 (fun k->k "top-def: theorem is %a" K.Thm.pp_quoted th);
          Index.add_q idx (Expr.as_queryable ty_ret);
          Index.add_q idx (Expr.as_queryable rhs);
          true
        | A.Top_fixity { name; fixity } ->
          let c =
            match Ty_env.find_const self.st.ty_env name.A.view with
            | Some c -> c.A.view
            | None ->
              errorf (fun k->k"constant `%s` not in scope" name.A.view)
          in
          Index.add_q idx (name_with_def_as_q name.view ~loc:name.loc K.Const.pp c);
          self.st.notation <- Notation.declare name.A.view fixity self.st.notation;
          true
        | A.Top_axiom {name; thm} ->
          let th = top_axiom_ self name.A.view thm in
          Index.add_q idx
            (name_with_def_as_q ~loc:name.A.loc name.A.view Expr.pp th);
          Index.add_q idx (Expr.as_queryable th);
          true
        | A.Top_goal { goal; proof } ->
          let ok, goal, proof = top_goal_ ~loc self goal proof in
          Index.add_q idx (Goal.as_queryable goal);
          Index.add_q idx (Proof.as_queryable proof);
          ok
        | A.Top_theorem { name; goal; proof } ->
          let ok, goal, proof, thm = top_thm_ ~loc self name.view goal proof in
          Index.add_q idx
            (match thm with
             | None -> name_with_def_as_q name.view ~loc:name.loc Goal.pp goal
             | Some th -> name_with_def_as_q name.view ~loc:name.loc Thm.pp_quoted th
            );
          Index.add_q idx (Goal.as_queryable goal);
          Index.add_q idx (Proof.as_queryable proof);
          ok
        | A.Top_show s ->
          let ok, qs = top_show_ self ~loc s.view in
          (* add to index *)
          List.iter (Index.add_q idx) qs;
          ok
        | A.Top_show_expr e ->
          let e = Ty_infer.infer_expr self.st e in
          self.on_show loc (fun out () ->
              Fmt.fprintf out "@[<v>@[<2>expr:@ %a@]@ @[<2>as-kernel-expr:@ %a@]@]"
                Expr.pp e K.Expr.pp (Expr.to_k_expr self.st.ctx e));
          Index.add_q idx (Expr.as_queryable e);
          true
        | A.Top_show_proof proof ->
          let proof, th = top_proof_ self proof in
          Index.add_q idx (Proof.as_queryable proof);
          begin match th with
            | Ok th ->
              self.on_show loc
                (fun out () ->
                   Fmt.fprintf out "@[<hv>result:@ %a@]" K.Thm.pp_quoted th);
              true
            | Error e ->
              self.on_error loc e.pp;
              false
          end
        | A.Top_error { msg } ->
          self.on_error loc msg;
          false
      with
      | Trustee_error.E e ->
        self.on_error loc (fun out () -> Trustee_error.pp out e);
        false
    in
    if ok then (
      Log.debugf 1
        (fun k->k"@[<v>@[<2>@{<green>OK@}:@ %a@]@ loc: %a@]"
            A.Top_stmt.pp st Loc.pp (A.Top_stmt.loc st));
    );
    !idx

  let top ~on_show ~on_error idx (st:Typing_state.t) (stmt:A.top_statement) : Index.t =
    let state = {st; on_show; on_error} in
    let idx = top_ state stmt idx in
    idx
end

let process_stmt = Process_stmt.top

