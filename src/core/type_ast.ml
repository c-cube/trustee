
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
  | Ty_pi of bvar * ty
  | Var of var
  | BVar of bvar
  | Meta of meta
  | Const of {
      c: K.Expr.t;
    }
  | App of expr * expr
  | Lambda of bvar * expr
  | Eq of expr * expr
  | Let of binding list * expr

and meta = {
  meta_name: string;
  meta_type: expr;
  meta_loc: location;
  mutable meta_deref: expr option;
}

type subst = (var * expr) list

type env = {
  ctx: K.Ctx.t;
  mutable cur_file: string;
  mutable consts: K.Expr.t Str_map.t;
  mutable fvars: var Str_map.t;
  mutable theorems: K.Thm.t Str_map.t;
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

let rec pp_expr_ out (e:expr) : unit =
  match view_expr_ e with
  | Kind -> Fmt.string out "kind"
  | Type -> Fmt.string out "type"
  | Bool -> Fmt.string out "bool"
  | Var v -> Fmt.string out v.v_name
  | BVar v -> ID.pp out v.bv_name
  | Ty_arrow (a,b) ->
    Fmt.fprintf out "%a@ -> %a" pp_atom_ a pp_expr_ b;
  | Ty_pi (v, bod) ->
    Fmt.fprintf out "(@[pi %a.@ %a@])" pp_bvar v pp_expr_ bod
  | Const {c} -> K.Expr.pp out c
  | App _ ->
    let f, l = unfold_app_ e in
    Fmt.fprintf out "(@[%a@ %a@])" pp_expr_ f (pp_list pp_expr_) l
  | Meta v -> Meta.pp out v
  | Lambda _ ->
    let vars, bod = unfold_lam e in
    Fmt.fprintf out "(@[\\%a.@ %a@])" (pp_list pp_bvar_ty) vars pp_expr_ bod
  | Eq (a,b) -> Fmt.fprintf out "(@[=@ %a@ %a@])" pp_expr_ a pp_expr_ b
  | Let (bs,bod) ->
    let pp_b out (v,e) : unit =
      Fmt.fprintf out "@[%a@ = %a@]" ID.pp v.bv_name pp_expr_ e in
    Fmt.fprintf out "(@[let %a in@ %a@])" (pp_list ~sep:" and " pp_b) bs pp_expr_ bod
and pp_atom_ out e =
  match e.view with
  | Type | Var _ | Meta _ | Const _ -> pp_expr_ out e
  | _ -> Fmt.fprintf out "(@[%a@])" pp_expr_ e
and pp_var out v = Fmt.string out v.v_name
and pp_bvar out v = ID.pp out v.bv_name
and pp_bvar_ty out (v:bvar) : unit =
  Fmt.fprintf out "(@[%a@ : %a@])" ID.pp v.bv_name pp_expr_ v.bv_ty

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

  (** Follow assigned meta-variables *)
  let[@inline][@unroll 1] rec deref_ (e:expr) : expr =
    match e.view with
    | Meta {meta_deref=Some u; _} -> deref_ u
    | _ -> e

  (** Iterate on immediate subterms *)
  let iter ~f ~f_bind b_acc (e:expr) : unit =
    CCOpt.iter (fun u -> f b_acc u) e.ty;
    match view e with
    | Kind | Type | Bool | Const _ | Meta _ | Var _ | BVar _ -> ()
    | Ty_arrow (a, b) | Eq (a,b) | App (a,b) ->
      f b_acc a;
      f b_acc b
    | Ty_pi (v, bod) | Lambda (v, bod) ->
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
  let ty_pi ~loc v bod : ty =
    if contains_bvar ~bv:v bod then (
      mk_ ~loc (Ty_pi (v,bod)) type_
    ) else (
      (* canonical form: pi are always bound, so that type unification works *)
      ty_arrow ~loc v.bv_ty bod
    )
  let ty_pi_l ~loc vars bod : ty = List.fold_right (ty_pi ~loc) vars bod

  let var ~loc (v:var) : expr = mk_ ~loc (Var v) v.v_ty
  let var' ~loc name ty : expr = var ~loc (Var.make name ty)
  let bvar ~loc (v:bvar) : expr = mk_ ~loc (BVar v) v.bv_ty

  let is_eq_to_type (e:expr) = match view e with
    | Type -> true
    | _ -> false
  let[@inline] is_a_type e = is_eq_to_type (ty e)

  (* convert a kernel expression back into a type *)
  let rec ty_of_expr ~loc e0 : ty =
    let rec aux env e =
      match K.Expr.view e with
      | K.Expr.E_const _ -> const ~loc e
      | K.Expr.E_type -> type_
      | K.Expr.E_bound_var v ->
        begin match List.nth env v.bv_idx with
          | exception Not_found ->
            errorf (fun k->k"unbound variable db%d@ in type of %a" v.bv_idx K.Expr.pp e)
          | t -> t
        end
      | K.Expr.E_pi (ty_v, bod) ->
        assert (K.Expr.is_eq_to_type ty_v || K.Expr.is_a_type ty_v);
        let bv = BVar.make ~loc (ID.makef "_a_%d" (List.length env)) (aux env ty_v) in
        ty_pi ~loc bv @@ aux (bvar ~loc bv::env) bod
      | _ ->
        errorf (fun k->k"cannot convert %a@ to a type" K.Expr.pp e)
    in
    aux [] e0

  and const ~loc c : expr =
    mk_ ~loc (Const {c; }) (ty_of_expr ~loc (K.Expr.ty_exn c))

  let subst_bvars (m:expr ID.Map.t) (e:expr) : expr =
    let rec aux m e =
      let e = deref_ e in
      match e.ty with
      | None -> assert (e==kind_); e
      | Some ty ->
        let ty = aux m ty in
        let loc = e.loc in
        match e.view with
        | Kind | Type | Bool | Const _ | Meta _ | Var _ -> {e with ty=Some ty}
        | BVar v ->
          begin match ID.Map.find v.bv_name m with
            | u -> {u with loc}
            | exception Not_found -> e
          end
        | App (a,b) -> mk_ ~loc (App (aux m a, aux m b)) ty
        | Eq(a,b) -> mk_ ~loc (Eq(aux m a, aux m b)) ty
        | Ty_arrow(a,b) -> mk_ ~loc (Ty_arrow(aux m a, aux m b)) ty
        | Ty_pi (v, bod) ->
          let m, v' = rename_bvar m v in
          mk_ ~loc (Ty_pi (v', aux m bod)) ty
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
      | Ty_pi (f_v, f_ret) ->
        unif_exn_ f_v.bv_ty ty_a;
        (* substitute! *)
        subst_bvars (ID.Map.singleton f_v.bv_name a) f_ret
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
        | Type, Const c when K.Expr.is_eq_to_type c.c -> ()
        | Const c, Type when K.Expr.is_eq_to_type c.c -> ()
        | Bool, Const c when K.Expr.is_eq_to_bool c.c -> ()
        | Const c, Bool when K.Expr.is_eq_to_bool c.c -> ()
        | Var a, Var b when a.v_name = b.v_name -> ()
        | BVar a, BVar b
          when
            ID.equal a.bv_name b.bv_name
            || same_bvar_ renaming a b
          -> ()
        | Const a, Const b when K.Expr.equal a.c b.c -> ()
        | Ty_arrow (a1,a2), Ty_arrow (b1,b2) ->
          aux st' renaming a1 b1;
          aux st' renaming a2 b2;
        | Eq (a1,a2), Eq (b1,b2)
        | App (a1,a2), App (b1,b2) ->
          aux st' renaming a1 b1;
          aux st' renaming a2 b2;
        | Ty_pi (v1,b1), Ty_pi (v2,b2)
        | Lambda (v1,b1), Lambda (v2,b2) ->
          aux st' renaming v1.bv_ty v2.bv_ty;
          let renaming =
            let bv = ID.copy v1.bv_name in
            renaming |> ID.Map.add v1.bv_name bv |> ID.Map.add v2.bv_name bv
          in
          aux st' renaming b1 b2
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
        | (Type | Bool | Kind | Var _ | BVar _ | Eq _
          | Const _ | App _ | Ty_arrow _ | Ty_pi _ | Lambda _), _ ->
          fail_ st a b
      )
    in
    try aux [] ID.Map.empty a b; Ok ()
    with E_unif_err st -> Error st

  let app ~loc env (f:expr) (a:expr) : expr =
    let ty = ty_app_ ~loc env f a in
    mk_ ~loc (App (f,a)) ty

  let app_l ~loc env f l = List.fold_left (fun f x -> app ~loc env f x) f l

  let let_ ~loc bs bod : expr = mk_ ~loc (Let (bs, bod)) (ty bod)

  let lambda ~loc v bod : expr =
    let ty_lam =
      let tyv = deref_ v.bv_ty in
      if is_eq_to_type tyv then (
        ty_pi ~loc v (ty bod)
      ) else (
        ty_arrow ~loc tyv (ty bod)
      )
    in
    mk_ ~loc (Lambda (v, bod)) ty_lam

  let lambda_l ~loc vs bod : expr =
    List.fold_right (lambda ~loc) vs bod

  let eq ~loc a b : expr = mk_ ~loc (Eq (a,b)) bool
  let wildcard ~loc env : expr * meta =
    ty_meta ~loc env

  let to_string = Fmt.to_string @@ Fmt.hvbox pp

  let to_k_expr ?(subst=ID.Map.empty) (ctx:K.Ctx.t) (e:expr) : K.Expr.t =
    (* [bs] is the mapping from bound variables to expressions, with their
       binding point DB level. *)
    let rec aux (bs:_ ID.Map.t) k e : K.Expr.t =
      let recurse = aux bs k in
      let loc = loc e in
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
          | (e, k_e) -> K.Expr.db_shift ctx e (k - k_e - 1)
          | exception Not_found ->
            errorf
              (fun k->k"variable %a is not bound@ at %a"
                  pp e Loc.pp loc)
        end
      | Const e -> e.c
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
      | Ty_pi (v, bod) ->
        let ty = recurse v.bv_ty in
        let bs = ID.Map.add v.bv_name (K.Expr.bvar ctx 0 ty, k) bs in
        let bod = aux bs (k+1) bod in
        K.Expr.pi_db ctx ~ty_v:ty bod
      | Lambda (v, bod) ->
        let ty = recurse v.bv_ty in
        let bs = ID.Map.add v.bv_name (K.Expr.bvar ctx 0 ty, k) bs in
        let bod = aux bs (k+1) bod in
        K.Expr.lambda_db ctx ~ty_v:ty bod
    in
    let subst = ID.Map.map (fun v -> v, 0) subst in
    aux subst 0 e

  let rec as_queryable e = object
    inherit Queryable.t
    method loc = e.loc
    method pp out () = Fmt.fprintf out "@[<hv>expr: %a@ type: %a@]" pp e pp (ty e)
    method! children yield =
      let yield_e e = yield (as_queryable e) in
      let yield_bv v = yield (BVar.as_queryable v) in
      begin match view e with
        | Kind | Type | Bool | Const _ | Meta _ | Var _ | BVar _ -> ()
        | Ty_arrow (a, b) | Eq (a,b) | App (a,b) -> yield_e a; yield_e b
        | Ty_pi (v, bod) | Lambda (v, bod) -> yield_bv v; yield_e bod
        | Let (bs, bod) ->
          List.iter (fun (v,u) -> yield_bv v; yield_e u) bs; yield_e bod
      end
  end
end

module Subst = struct
  type t = subst

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
         K.Subst.bind v t s)
      K.Subst.empty self
end

(** {2 Typing Environment}

    This environment is (mostly) functional, and is used to handle
    scoping and to map names into constants and expressions and their type.
    *)

module Env = struct
  type t = env

  let copy self = {self with to_gen=self.to_gen}

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
    Log.debugf 5 (fun k->k"declare new const@ :name %S@ :expr %a@ :ty %a"
                     name K.Expr.pp c K.Expr.pp (K.Expr.ty_exn c));
    self.consts <- Str_map.add name c self.consts

  let define_thm (self:t) name th : unit =
    self.theorems <- Str_map.add name th self.theorems

  type named_object =
    | N_expr of K.Expr.t
    | N_thm of K.Thm.t
    | N_rule of Proof.Rule.t

  let find_rule (_self:t) name : KProof.Rule.t option =
    match Proof.Rule.find_builtin name with
    | Some _ as r -> r
    | None ->
      None (* TODO: lookup in locally defined rules *)

  let find_thm self name : K.Thm.t option =
    Str_map.get name self.theorems

  let find_named (self:t) name : named_object option =
    try Some (N_expr (Str_map.find name self.consts))
    with Not_found ->
    try Some (N_thm (Str_map.find name self.theorems))
    with Not_found ->
    match find_rule self name with
    | Some r -> Some (N_rule r)
    | None ->
      None (* TODO: look in local defined rules *)

  let create ctx : t =
    let env = {
      ctx;
      cur_file="";
      gensym=0;
      consts=Str_map.empty;
      fvars=Str_map.empty;
      theorems=Str_map.empty;
      to_gen=[];
    } in
    declare_const env "bool" (K.Expr.bool ctx);
    declare_const env "type" (K.Expr.type_ ctx);
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
    | Let_step of ID.t * step

  and step = {
    s_loc: location;
    s_view: step_view;
  }

  and step_view =
    | Pr_apply_rule of Proof.Rule.t * rule_arg list
    | Pr_sub_proof of t
    | Pr_error of unit Fmt.printer (* parse error *)

  (** An argument to a rule *)
  and rule_arg =
    | Arg_var_step of ID.t
    | Arg_step of step
    | Arg_thm of K.Thm.t
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
        ID.pp name (pp_step ~top:true) p

  and pp_step ~top out (s:step) : unit =
    match s.s_view with
    | Pr_apply_rule (r, []) when top -> R.pp out r
    | Pr_apply_rule (r, args) ->
      if not top then Fmt.char out '(';
      Fmt.fprintf out "@[<hv2>%a@ %a@]" R.pp r (pp_list pp_rule_arg) args;
      if not top then Fmt.char out ')';
    | Pr_sub_proof p -> pp out p
    | Pr_error e -> Fmt.fprintf out "<@[error:@ %a@]>" e ()

  and pp_rule_arg out (a:rule_arg) : unit =
    match a with
    | Arg_var_step s -> ID.pp out s
    | Arg_step s -> pp_step ~top:false out s (* always in ( ) *)
    | Arg_thm th -> K.Thm.pp_quoted out th
    | Arg_expr e -> Expr.pp out e
    | Arg_subst s -> Subst.pp out s

  let rec as_queryable (self:t) : Queryable.t = object
    inherit Queryable.t
    method pp out () = pp out self
    method loc = self.loc
    method! children = assert false
  end
  and step_q (self:step) : Queryable.t = object
    inherit Queryable.t
    method pp out () = pp_step ~top:true out self
    method loc = self.s_loc
    method! children = match self.s_view with
      | Pr_apply_rule (_, l) ->
        Iter.of_list l
        |> Iter.filter_map arg_q
      | Pr_sub_proof p -> Iter.return (as_queryable p)
      | Pr_error _ -> Iter.empty
  end
  and arg_q (self:rule_arg) : Queryable.t option =
    match self with
    | Arg_step s -> Some (step_q s)
    | Arg_expr e -> Some (Expr.as_queryable e)
    | Arg_subst _ | Arg_var_step _ | Arg_thm _ -> None

  let to_string = Fmt.to_string pp
  let pp_rule_signature = R.pp_signature

  let iter_subs (p:t) : t Iter.t =
    match p.view with
    | Proof_atom _
    | Proof_steps _ -> Iter.empty (* TODO *)

  let mk ~loc (view:view) : t = {view; loc}
  let mk_step ~loc (s_view:step_view) : step = {s_view; s_loc=loc}

  type env = {
    e_subst: K.Expr.t ID.Map.t;
    e_th: K.Thm.t ID.Map.t; (* steps *)
  }

  (* how to run a proof, and obtain a theorem at the end *)
  let run (ctx:K.Ctx.t) (self:t) : K.Thm.t =
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
                  {env with e_th = ID.Map.add name th env.e_th})
              env lets in
          run_step env ret
      with e ->
        errorf ~src:e (fun k->k"@[<2>while checking proof@ at %a@]" Loc.pp loc)

    and run_step env (s:step) : K.Thm.t =
      let loc = s.s_loc in
      try
        match s.s_view with
        | Pr_sub_proof p -> run_pr env p
        | Pr_error e ->
          errorf (fun k->k"invalid proof step@ at %a:@ %a" Loc.pp loc e())
        | Pr_apply_rule (r, args) ->
          let args = List.map (conv_arg ~loc env) args in
          Log.debugf 10
            (fun k->k"apply rule %a@ to args %a"
                KR.pp r (Fmt.Dump.list KR.pp_arg_val) args);
          KR.apply ctx r args
      with e ->
        errorf ~src:e
          (fun k->k"@[<2>while checking proof step@ at %a@]"
               Loc.pp loc)

    (* convert a rule argument *)
    and conv_arg ~loc env = function
      | Arg_expr e ->
        KR.AV_expr (Expr.to_k_expr ~subst:env.e_subst ctx e)
      | Arg_subst s ->
        KR.AV_subst (Subst.to_k_subst ~subst:env.e_subst ctx s)
      | Arg_step s ->
        let th = run_step env s in
        KR.AV_thm th
      | Arg_thm th -> KR.AV_thm th
      | Arg_var_step s ->
        begin match ID.Map.find s env.e_th with
          | th -> KR.AV_thm th
          | exception Not_found ->
            errorf
              (fun k->k"unbound proof step `%a`@ at %a" ID.pp s Loc.pp loc)
        end
    in
    run_pr {e_th=ID.Map.empty; e_subst=ID.Map.empty} self
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
  (* add meta variables as type arguments *)
  let complete_ty_args_ ~loc (env:env) (e:expr) : expr =
    let rec aux e =
      let ty_e = Expr.ty e in
      match Expr.view ty_e with
      | Ty_pi (x, _) when Expr.is_eq_to_type x.bv_ty ->
        (* [e] has type [pi a:type. …], so we assume [a] is implicit and
           create a new meta [?x : a], and then complete [e ?x] *)
        let tyv, m = Expr.ty_meta ~loc env in
        env.to_gen <- m :: env.to_gen;
        let e = Expr.app ~loc env e tyv in
        aux e
      | _ -> e
    in
    aux e

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
      (env:env) (vars:A.var list) (e0:AE.t) : bvar list * expr =
    (* type inference.
       @param bv the local variables, for scoping *)
    let rec inf_rec_ (bv:binding Str_map.t) (e:AE.t) : expr =
      let loc = AE.loc e in
      Log.debugf 7 (fun k->k"infer-rec loc=%a e=`%a`" Loc.pp loc AE.pp e);
      let unif_exn_ a b = unif_exn_ ~loc e a b in
      begin match AE.view e with
        | A.Type -> Expr.type_
        | A.Ty_arrow (a, b) -> Expr.ty_arrow ~loc (inf_rec_ bv a) (inf_rec_ bv b)
        | A.Ty_pi (vars, body) ->
          let bv, vars =
            CCList.fold_map
              (fun bv v ->
                 let v' = infer_bvar_ ~default:Expr.type_ bv v in
                 Str_map.add v.A.v_name (BV v') bv, v')
              bv vars
          in
          Expr.ty_pi_l ~loc vars @@ inf_rec_ bv body
        | A.Var v when Str_map.mem v.A.v_name bv ->
          (* use variable in scope, but change location of the expression *)
          begin match Str_map.find v.A.v_name bv with
            | BV bv -> Expr.bvar ~loc bv (* bound variable *)
            | V v -> Expr.var ~loc v
          end
        | A.Var v ->
          let v =
            match Str_map.find v.A.v_name env.fvars with
            | v' ->
              begin match v.A.v_ty with
                | Some ty ->
                  (* unify expected type with actual type *)
                  let ty = inf_rec_ bv ty in
                  unif_exn_ ty v'.v_ty
                | None -> ()
              end;
              v'
            | exception Not_found ->
              let ty = match v.A.v_ty with
                | Some ty -> inf_rec_ bv ty
                | None ->
                  let ty, m = Expr.ty_meta ~loc env in
                  env.to_gen <- m :: env.to_gen;
                  ty
              in
              let v = Var.make v.A.v_name ty in
              env.fvars <- Str_map.add v.v_name v env.fvars;
              v
          in
          Expr.var ~loc v
        | A.Wildcard ->
          let t, m = Expr.wildcard ~loc env in
          env.to_gen <- m :: env.to_gen;
          t
        | A.Meta {name;ty} ->
          let ty = match ty with
            | None -> Expr.type_
            | Some ty -> inf_rec_ bv ty
          in
          let t, m = Expr.meta ~loc name ty in
          env.to_gen <- m :: env.to_gen;
          t
        | A.Eq (a,b) ->
          let a = inf_rec_ bv a in
          let b = inf_rec_ bv b in
          unif_exn_ (Expr.ty a) (Expr.ty b);
          Expr.eq ~loc a b
        | A.Const {c;at} ->
          (* convert directly into a proper kernel constant *)
          infer_const_ c ~loc ~at
        | A.App (f,l) ->
          let f = inf_rec_ bv f in
          let l = List.map (inf_rec_ bv) l in
          Expr.app_l ~loc env f l
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
        | A.Bind { c; at; vars; body } ->
          let f = infer_const_ ~loc ~at c in
          let bv, vars =
            CCList.fold_map
              (fun bv v ->
                 let v' = infer_bvar_ bv v in
                 Str_map.add v.A.v_name (BV v') bv, v')
              bv vars
          in
          let body = inf_rec_ bv body in
          (* now for each [v], create [f (\x. bod)] *)
          CCList.fold_right
            (fun bv body ->
               let lam = Expr.lambda ~loc bv body in
               Expr.app ~loc env f lam)
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

    and infer_const_ ~at ~loc c : expr =
      let t =
        let c = match c with
          | A.C_k c -> c
          | A.C_local name ->
            match K.Ctx.find_const_by_name env.ctx name with
            | None ->
              errorf
                (fun k->k"cannot find constant `@[%a@]`@ at %a"
                     A.Const.pp c Loc.pp loc)
            | Some c -> K.Expr.const env.ctx c
        in
        Expr.const ~loc c
      in
      if at then t else complete_ty_args_ ~loc env t

    and infer_ty_opt_ ~loc ?default bv ty : ty =
      match ty with
      | None ->
        begin match default with
          | Some ty -> ty
          | None ->
            let ty, m = Expr.ty_meta ~loc env in
            env.to_gen <- m :: env.to_gen;
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

  let infer_expr (env:env) (e0:AE.t) : expr =
    let _, e = infer_expr_vars env [] e0 in
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

  let infer_goal env (g:A.Goal.t) : Goal.t * K.Goal.t =
    let hyps = List.map (infer_expr_bool env) g.A.Goal.hyps in
    let concl = infer_expr_bool env g.A.Goal.concl in
    Env.generalize_ty_vars env;
    let loc =
      List.fold_left (fun loc e -> Loc.merge loc (Expr.loc e))
        (Expr.loc concl) hyps
    in
    let goal = Goal.make ~loc hyps concl in
    let kgoal = Goal.to_k_goal env.ctx goal in
    goal, kgoal

  let and_then_generalize env f =
    let x = f() in
    Env.generalize_ty_vars env;
    x

  type pr_env = {
    e_expr: binding Str_map.t;
    e_step: ID.t Str_map.t;
  }

  let infer_proof (env:env) (pr:A.Proof.t) : Proof.t =
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
                let _, e = infer_expr_full_ ~bv:(!pr_env).e_expr env [] e in
                let bv = BVar.make ~loc:e.loc (ID.make name) (Expr.ty e) in
                pr_env := {
                  (!pr_env) with
                  e_expr=Str_map.add name (BV bv) (!pr_env).e_expr;
                };
                Proof.Let_expr (bv, e)
              | A.Proof.Let_step (name,s) ->
                let name_id = ID.make name in
                let s = infer_step !pr_env s in
                pr_env := {
                  (!pr_env) with
                  e_step=Str_map.add name name_id (!pr_env).e_step;
                };
                Proof.Let_step (name_id, s))
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
        let r = match Env.find_rule env r with
          | None ->
            errorf (fun k->k"unknown rule '%s'@ at %a" r Loc.pp loc)
          | Some r -> r
        in
        let args = List.map (conv_arg ~loc pr_env) args in
        Proof.mk_step ~loc (Proof.Pr_apply_rule (r, args))
      | A.Proof.Pr_sub_proof p ->
        let p = infer_proof pr_env p in
        Proof.mk_step ~loc (Proof.Pr_sub_proof p)

    and conv_arg ~loc (pr_env:pr_env) (a:A.Proof.rule_arg) : Proof.rule_arg =
      match a with
      | A.Proof.Arg_var s ->
        begin match
            Str_map.get s pr_env.e_expr,
            Str_map.get s pr_env.e_step
          with
          | Some (BV bv), _ -> Proof.Arg_expr (Expr.bvar ~loc bv)
          | Some (V v), _ -> Proof.Arg_expr (Expr.var ~loc v)
          | None, Some id -> Proof.Arg_var_step id
          | None, None ->
            begin match Env.find_thm env s with
              | Some th -> Proof.Arg_thm th
              | None ->
                errorf
                  (fun k->k "unknown proof variable '%s'@ at %a" s Loc.pp loc)
            end
        end
      | A.Proof.Arg_step s ->
        let s = infer_step pr_env s in
        Proof.Arg_step s
      | A.Proof.Arg_expr e ->
        let _, e = infer_expr_full_ ~bv:pr_env.e_expr env [] e in
        Proof.Arg_expr e
      | A.Proof.Arg_subst _s ->
        errorf (fun k->k"TODO: convert subst")
    in
    let e0 = {e_expr=Str_map.empty; e_step=Str_map.empty} in
    infer_proof e0 pr
end

module Index = struct
  type t = Queryable.t list
  let empty : t = []
  let size = List.length

  let find (self:t) (pos:Position.t) : Queryable.t list =
    let rec aux (q:Queryable.t) : _ list option =
      Log.debugf 6 (fun k->k"examine queryable %a at %a" q#pp () Loc.pp q#loc);
      if Loc.contains q#loc pos then (
        let sub = Iter.find_map aux q#children |> CCOpt.get_or ~default:[] in
        Some (q::sub)
      ) else None
    in
    begin match CCList.find_map aux self with
      | None -> []
      | Some l -> List.rev l (* put deeper result first *)
    end

  let add_cond ~index x l = if index then x::l else l
end

module Process_stmt = struct
  type t = {
    env: env;
    on_show: location -> unit Fmt.printer -> unit;
    on_error: location -> unit Fmt.printer -> unit;
  }

  let top_decl_ self name ty : ty =
    let ty =
      Ty_infer.and_then_generalize self.env
        (fun () -> Ty_infer.infer_ty self.env ty)
    in
    let kty = Expr.to_k_expr self.env.ctx ty in
    let c = K.Expr.new_const self.env.ctx name kty in
    Env.declare_const self.env name c;
    ty

  let top_def_ ~loc self name th_name vars ret body : ty * expr =
    (* turn [def f x y := bod] into [def f := \x y. bod] *)
    let vars, e = Ty_infer.infer_expr_vars self.env vars body in
    let def_rhs = Expr.lambda_l ~loc vars e in
    let ty_rhs = Expr.ty def_rhs in
    (* now ensure that [f vars : ret] *)
    begin match ret with
      | None -> ()
      | Some ret ->
        let ret = Ty_infer.infer_ty self.env ret in
        (* [ret] should be the type of [real_def x1…xn] *)
        let e_app =
          Expr.app_l ~loc self.env def_rhs
            (List.map
               (fun bv -> Expr.var' ~loc (ID.name bv.bv_name) bv.bv_ty)
               vars)
        in
        Ty_infer.unif_type_with_ ~loc e_app ret
    end;
    Env.generalize_ty_vars self.env;
    (* the defining equation `name = def_rhs` *)
    let def_eq = Expr.eq ~loc (Expr.var' ~loc name ty_rhs) def_rhs in
    let th, ke =
      K.Thm.new_basic_definition self.env.ctx
        (Expr.to_k_expr self.env.ctx def_eq) in
    Env.declare_const self.env name ke;
    CCOpt.iter (fun th_name -> Env.define_thm self.env th_name th) th_name;
    ty_rhs, def_rhs

  let top_show_ self ~loc s : bool =
    begin match Env.find_named self.env s with
      | Some (Env.N_expr e) ->
        self.on_show loc (fun out () ->
            Fmt.fprintf out "@[<2>expr:@ `@[%a@]`@ with type: %a@]" K.Expr.pp e
              (Fmt.Dump.option K.Expr.pp) (K.Expr.ty e));
        true
      | Some (Env.N_thm th) ->
        self.on_show loc (fun out () ->
            Fmt.fprintf out "@[<2>theorem:@ %a@]" K.Thm.pp th);
        true
      | Some (Env.N_rule r) ->
        self.on_show loc (fun out () ->
            Fmt.fprintf out "@[<2>rule:@ %a@]" KProof.Rule.pp r);
        true
      | None ->
        self.on_show loc (fun out () -> Fmt.fprintf out "not found");
        false
    end

  let top_axiom_ self name thm : expr =
    let e =
      Ty_infer.and_then_generalize self.env
        (fun () -> Ty_infer.infer_expr_with_ty self.env thm Expr.bool)
    in
    let ke = Expr.to_k_expr self.env.ctx e in
    let th = K.Thm.axiom self.env.ctx ke in
    Env.define_thm self.env name th;
    e

  let top_proof_ self goal proof : Goal.t * K.Goal.t * Proof.t * K.Thm.t =
    let goal, kgoal = Ty_infer.infer_goal self.env goal in
    Log.debugf 5 (fun k->k"inferred goal:@ %a" K.Goal.pp kgoal);
    (* convert proof *)
    let pr =
      Ty_infer.infer_proof self.env proof
    in
    Log.debugf 10 (fun k->k"typed proof:@ %a" Proof.pp pr);
    let th = Proof.run self.env.ctx pr in
    goal, kgoal, pr, th

  let top_goal_ ~loc self goal proof : bool * Goal.t =
    let goal, kgoal, _pr, th = top_proof_ self goal proof in
    if K.Thm.is_proof_of th kgoal then (
      self.on_show loc
        (fun out() ->
           Fmt.fprintf out "@[<2>goal proved@ with theorem `@[%a@]`@]" K.Thm.pp th);
      true, goal
    ) else (
      self.on_error loc
        (fun out() ->
           Fmt.fprintf out "@[<2>proof@ yields theorem %a@ but goal was %a@]"
             K.Thm.pp th K.Goal.pp kgoal);
      false, goal
    )

  let top_thm_ ~loc self name goal proof : bool * Goal.t =
    let goal, kgoal, _pr, th = top_proof_ self goal proof in
    if K.Thm.is_proof_of th kgoal then (
      Env.define_thm self.env name th;
      true, goal
    ) else (
      self.on_error loc
        (fun out() ->
           Fmt.fprintf out "@[<2>proof@ yields theorem %a@ but goal was %a@]"
             K.Thm.pp th K.Goal.pp kgoal);
      false, goal
    )

  let top_ (self:t) st ~index (idx:Index.t) : Index.t =
    Log.debugf 2 (fun k->k"(@[TA.process-stmt@ %a@])" A.Top_stmt.pp st);
    let ok, idx =
      let loc = A.Top_stmt.loc st in
      try
        match A.Top_stmt.view st with
        | A.Top_enter_file s ->
          self.env.cur_file <- s;
          true, idx
        | A.Top_decl { name; ty } ->
          let ty = top_decl_ self name ty in
          true, Index.add_cond ~index (Expr.as_queryable ty) idx
        | A.Top_def { name; th_name; vars; ret; body } ->
          let ty_ret, rhs = top_def_ self ~loc name th_name vars ret body in
          let idx =
            idx
            |> Index.add_cond ~index (Expr.as_queryable ty_ret)
            |> Index.add_cond ~index (Expr.as_queryable rhs)
          in
          true, idx
        | A.Top_fixity { name; fixity } ->
          let c =
            match K.Ctx.find_const_by_name self.env.ctx name with
            | Some c -> c
            | None -> errorf (fun k->k"constant `%s` not in scope" name)
          in
          K.Const.set_fixity c fixity;
          true, idx
        | A.Top_axiom {name; thm} ->
          let th = top_axiom_ self name thm in
          let idx = Index.add_cond ~index (Expr.as_queryable th) idx in
          true, idx
        | A.Top_goal { goal; proof } ->
          let ok, goal = top_goal_ ~loc self goal proof in
          ok, Index.add_cond ~index (Goal.as_queryable goal) idx
        | A.Top_theorem { name; goal; proof } ->
          let ok, goal = top_thm_ ~loc self name goal proof in
          ok, Index.add_cond ~index (Goal.as_queryable goal) idx
        | A.Top_show s ->
          (* TODO: add to index *)
          top_show_ self ~loc s, idx
        | A.Top_show_expr e ->
          let e = Ty_infer.infer_expr self.env e in
          self.on_show loc (fun out () ->
              Fmt.fprintf out "@[<v>@[<2>expr:@ %a@]@ @[<2>as-kernel-expr:@ %a@]@]"
                Expr.pp e K.Expr.pp (Expr.to_k_expr self.env.ctx e));
          let idx = Index.add_cond ~index (Expr.as_queryable e) idx in
          true, idx
        | A.Top_show_proof _ ->
          (* TODO
          let idx = Index.add_cond ~index (Expr.as_queryable e) idx in
             *)
          error "TODO" (* TODO *)
        | A.Top_error { msg } ->
          self.on_error loc msg;
          false, idx
      with
      | Trustee_error.E e ->
        self.on_error loc (fun out () -> Trustee_error.pp out e);
        false, idx
    in
    if ok then (
      Log.debugf 1
        (fun k->k"@[<v>@[<2>@{<green>OK@}:@ %a@]@ loc: %a@]"
            A.Top_stmt.pp st Loc.pp (A.Top_stmt.loc st));
    );
    idx

  let top ~index ~on_show ~on_error (env, idx : env * Index.t)
      (st:A.top_statement) : env * Index.t =
    let state = {env; on_show; on_error} in
    let idx = top_ ~index state st idx in
    env, idx
end

let process_stmt = Process_stmt.top

