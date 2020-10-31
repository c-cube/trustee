
open Sigs

module K = Kernel
module A = Parse_ast
module AE = A.Expr

type position = A.position
let nopos: position = Position.none

type expr = {
  view: view;
  mutable ty: ty option;
  pos: position;
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
  meta_pos: position;
  mutable meta_deref: expr option;
}

type env = {
  ctx: K.Ctx.t;
  mutable cur_file: string;
  mutable tys: ty ID.Map.t;
  mutable fvars: var Str_map.t;
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

module Meta = struct
  type t = meta
  let make ~pos s ty : t =
    {meta_deref=None; meta_name=s; meta_type=ty; meta_pos=pos;}
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
  | Lambda (v,bod) ->
    Fmt.fprintf out "(@[\\%a.@ %a@])" pp_bvar_ty v pp_expr_ bod
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
end

module BVar = struct
  type t = bvar
  let make bv_name bv_ty : bvar = {bv_name; bv_ty; }
  let pp = pp_bvar
  let pp_with_ty = pp_bvar_ty
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

  (* are [a] and [b] the same bound var under given [renaming] (maps bound vars
     to other bound vars)? *)
  let same_bvar_ renaming a b : bool =
    let a = try ID.Map.find a.bv_name renaming with Not_found -> a.bv_name in
    let b = try ID.Map.find b.bv_name renaming with Not_found -> b.bv_name in
    ID.equal a b

  let pp out e = Fmt.fprintf out "`@[%a@]`" pp_expr_ e

  let kind_ = {view=Kind; pos=nopos; ty=None}
  let[@inline] mk_ ~pos view ty : expr = {view; pos; ty=Some ty}

  let[@inline] pos e = e.pos
  let[@inline] ty e = match e.ty with Some t -> t | None -> assert false
  let get_ty = ty
  let pp = pp

  (** {2 Core operations} *)

  let type_ : expr = mk_ ~pos:nopos Type kind_
  let bool : expr = mk_ ~pos:nopos Bool type_
  let meta ~pos s ty : expr * meta =
    let m = Meta.make ~pos s ty in
    mk_ ~pos (Meta m) ty, m

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

  let ty_var ~pos s : expr = mk_ ~pos (Var (Var.make s type_)) type_
  let ty_meta ~pos env : ty * meta =
    let name = fresh_ty_name_ env in
    let m = Meta.make ~pos name type_ in
    mk_ ~pos (Meta m) type_, m
  let ty_arrow ~pos a b : ty = mk_ ~pos (Ty_arrow (a,b)) type_
  let ty_pi ~pos v bod : ty = mk_ ~pos (Ty_pi (v,bod)) type_
  let ty_pi_l ~pos vars bod : ty = List.fold_right (ty_pi ~pos) vars bod

  let var ~pos (v:var) : expr = mk_ ~pos (Var v) v.v_ty
  let bvar ~pos (v:bvar) : expr = mk_ ~pos (BVar v) v.bv_ty

  let is_eq_to_type (e:expr) = match view e with
    | Type -> true
    | _ -> false
  let[@inline] is_a_type e = is_eq_to_type (ty e)

  (* convert a kernel expression back into a type *)
  let rec ty_of_expr ~pos e0 : ty =
    let rec aux env e =
      match K.Expr.view e with
      | K.Expr.E_const _ -> const ~pos e
      | K.Expr.E_type -> type_
      | K.Expr.E_bound_var v ->
        begin match List.nth env v.bv_idx with
          | exception Not_found ->
            errorf (fun k->k"unbound variable db%d@ in type of %a" v.bv_idx K.Expr.pp e)
          | t -> t
        end
      | K.Expr.E_pi (ty_v, bod) ->
        assert (K.Expr.is_eq_to_type ty_v || K.Expr.is_a_type ty_v);
        let bv = BVar.make (ID.makef "_a_%d" (List.length env)) (aux env ty_v) in
        ty_pi ~pos bv @@ aux (bvar ~pos bv::env) bod
      | _ ->
        errorf (fun k->k"cannot convert %a@ to a type" K.Expr.pp e)
    in
    aux [] e0

  and const ~pos c : expr =
    mk_ ~pos (Const {c; }) (ty_of_expr ~pos (K.Expr.ty_exn c))

  let subst_bvars (m:expr ID.Map.t) (e:expr) : expr =
    let rec aux m e =
      let e = deref_ e in
      match e.ty with
      | None -> assert (e==kind_); e
      | Some ty ->
        let ty = aux m ty in
        let pos = e.pos in
        match e.view with
        | Kind | Type | Bool | Const _ | Meta _ | Var _ -> {e with ty=Some ty}
        | BVar v ->
          begin match ID.Map.find v.bv_name m with
            | u -> {u with pos}
            | exception Not_found -> e
          end
        | App (a,b) -> mk_ ~pos (App (aux m a, aux m b)) ty
        | Eq(a,b) -> mk_ ~pos (Eq(aux m a, aux m b)) ty
        | Ty_arrow(a,b) -> mk_ ~pos (Ty_arrow(aux m a, aux m b)) ty
        | Ty_pi (v, bod) ->
          let m, v' = rename_bvar m v in
          mk_ ~pos (Ty_pi (v', aux m bod)) ty
        | Lambda (v, bod) ->
          let m, v' = rename_bvar m v in
          mk_ ~pos (Lambda (v', aux m bod)) ty
        | Let (bs, bod) ->
          let m, bs =
            CCList.fold_map
              (fun m1 (v,t) ->
                 let m1, v' = rename_bvar m1 v in
                 let t = aux m t in
                 ID.Map.add v.bv_name (mk_ ~pos:nopos (BVar v') ty) m1, (v',t))
              m bs
          in
          mk_ ~pos (Let (bs, aux m bod)) ty
    (* rename a bound variable to avoid capture. Adds [v -> v'] to [m]. *)
    and rename_bvar m v =
      let ty = aux m v.bv_ty in
      let v' = {bv_name=ID.copy v.bv_name; bv_ty=ty} in
      ID.Map.add v.bv_name (mk_ ~pos:nopos (BVar v') ty) m, v'
    in
    aux m e

  type unif_err_trace = (expr*expr) list
  exception E_unif_err of unif_err_trace

  (* compute type of [f a] *)
  let rec ty_app_ env ~pos (f:expr) (a:expr) : ty =
    let ty_f = deref_ (ty f) in
    let ty_a = deref_ (ty a) in
    let unif_exn_ a b = match unif_ a b with
      | Ok () -> ()
      | Error st ->
        errorf
          (fun k->k
              "@[<2>type error@ in the application \
               @[<2>of %a@ of type %a@]@ @[<2>to term %a@ of type %a@]:@ \
               unification error in the following trace:@ %a"
              pp f pp ty_f pp a pp ty_a
              Fmt.Dump.(list @@ pair pp pp) st)
    in
    begin match view ty_f with
      | Ty_arrow (f_arg, f_ret) ->
        unif_exn_ f_arg ty_a;
        f_ret
      | Ty_pi (f_v, f_ret) ->
        unif_exn_ f_v.bv_ty ty_a;
        (* substitute! *)
        subst_bvars (ID.Map.singleton f_v.bv_name ty_a) f_ret
      | _ ->
        let ty_ret, meta = ty_meta ~pos env in
        env.to_gen <- meta :: env.to_gen;
        unif_exn_ ty_f (ty_arrow ~pos ty_a ty_ret);
        ty_ret
    end

  (* unify two terms. This only needs to be complete for types. *)
  and unif_ (a:expr) (b:expr) : (unit, unif_err_trace) result =
    let[@inline] fail_ st a b =
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
          | Some _, None | None, Some _ -> fail_ st a b
        end;
        match a.view, b.view with
        | Type, Type | Kind, Kind | Bool, Bool -> ()
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

  let app ~pos env (f:expr) (a:expr) : expr =
    let ty = ty_app_ ~pos env f a in
    mk_ ~pos (App (f,a)) ty

  let app_l ~pos env f l = List.fold_left (fun f x -> app ~pos env f x) f l

  let let_ ~pos bs bod : expr = mk_ ~pos (Let (bs, bod)) (ty bod)

  let lambda ~pos v bod : expr =
    let ty_lam =
      let tyv = deref_ v.bv_ty in
      if is_a_type tyv then (
        ty_pi ~pos v (ty bod)
      ) else (
        ty_arrow ~pos v.bv_ty (ty bod)
      )
    in
    mk_ ~pos (Lambda (v, bod)) ty_lam

  let lambda_l ~pos vs bod : expr =
    List.fold_right (lambda ~pos) vs bod

  let eq ~pos a b : expr = mk_ ~pos (Eq (a,b)) bool
  let wildcard ~pos env : expr * meta =
    ty_meta ~pos env

  let to_string = Fmt.to_string @@ Fmt.hvbox pp

  let to_k_expr (ctx:K.Ctx.t) (e:expr) : K.Expr.t =
    let rec aux bs k e : K.Expr.t =
      let recurse = aux bs k in
      let pos = pos e in
      match view e with
      | Meta {meta_deref=Some _; _} -> assert false
      | Meta {meta_deref=None; _} ->
        errorf (fun k->k"meta %a@ has not been generalized at %a"
                   pp e Position.pp pos)
      | Kind ->
        errorf (fun k->k"cannot translate `kind`@ at %a" Position.pp pos)
      | Type -> K.Expr.type_ ctx
      | Bool -> K.Expr.bool ctx
      | Var { v_name; v_ty } ->
        let ty = recurse v_ty in
        K.Expr.var ctx (K.Var.make v_name ty)
      | Ty_arrow (a, b) ->
        K.Expr.arrow ctx (recurse a) (recurse b)
      | BVar v ->
        begin match ID.Map.find v.bv_name bs with
          | (e, k_e) -> K.Expr.db_shift ctx e (k - k_e)
          | exception Not_found ->
            errorf
              (fun k->k"variable %a is not bound@ at %a"
                  pp e Position.pp pos)
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
        let bs = ID.Map.add v.bv_name (K.Expr.bvar ctx k ty, k) bs in
        let bod = aux bs (k+1) bod in
        K.Expr.pi_db ctx ~ty_v:ty bod
      | Lambda (v, bod) ->
        let ty = recurse v.bv_ty in
        let bs = ID.Map.add v.bv_name (K.Expr.bvar ctx k ty, k) bs in
        let bod = aux bs (k+1) bod in
        K.Expr.lambda_db ctx ~ty_v:ty bod
    in
    aux ID.Map.empty 0 e
end

(** {2 Typing Environment}

    This environment is (mostly) functional, and is used to handle
    scoping and to map names into constants and expressions and their type.
    *)

module Env = struct
  type t = env

  let create ctx : t =
    {ctx;
     cur_file="";
     tys=ID.Map.empty;
     gensym=0;
     fvars=Str_map.empty;
     to_gen=[];
    }

  let copy self = {self with tys=self.tys}

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
           m.meta_deref <- Some (Expr.var ~pos:nopos v))
      metas;
    ()
end

(** {2 type inference} *)
module Ty_infer = struct
  (* add meta variables as type arguments *)
  let complete_ty_args_ ~pos (env:env) (e:expr) : expr =
    let rec aux e =
      let ty_e = Expr.ty e in
      match Expr.view ty_e with
      | Ty_pi (x, _) when Expr.is_eq_to_type x.bv_ty ->
        (* [e] has type [pi a:type. …], so we assume [a] is implicit and
           create a new meta [?x : a], and then complete [e ?x] *)
        let tyv, m = Expr.ty_meta ~pos env in
        env.to_gen <- m :: env.to_gen;
        let e = Expr.app ~pos env e tyv in
        aux e
      | _ -> e
    in
    aux e

  let infer_expr (env:env) (e0:AE.t) : expr =
    let unif_exn_ ~pos e a b = match Expr.unif_ a b with
      | Ok () -> ()
      | Error st ->
        errorf
          (fun k->k
              "@[<2>type error@ while inferring the type @[<2>of %a@ at %a@]:@ \
               unification error in the following trace:@ %a"
              AE.pp e Position.pp pos
              Fmt.Dump.(list @@ pair Expr.pp Expr.pp) st)
    in

    (* type inference.
       @param bv the local variables, for scoping *)
    let rec inf_rec_ (bv:expr Str_map.t) (e:AE.t) : expr =
      let pos = AE.pos e in
      let unif_exn_ a b = unif_exn_ ~pos e a b in
      begin match AE.view e with
        | A.Type -> Expr.type_
        | A.Ty_arrow (a, b) -> Expr.ty_arrow ~pos (inf_rec_ bv a) (inf_rec_ bv b)
        | A.Ty_pi (vars, body) ->
          let bv, vars =
            CCList.fold_map
              (fun bv v ->
                 let v' = infer_bvar_ ~pos bv v in
                 Str_map.add v.A.v_name (Expr.bvar ~pos v') bv, v')
              bv vars
          in
          Expr.ty_pi_l ~pos vars @@ inf_rec_ bv body
        | A.Var v ->
          let v =
            match Str_map.find v.A.v_name env.fvars with
            | v' ->
              begin match v.A.v_ty with
                | Some ty ->
                  (* unify expected type with actual type *)
                  let ty = inf_rec_ bv ty in
                  unif_exn_ ty v'.v_ty | None -> ()
              end;
              v'
            | exception Not_found ->
              let ty = match v.A.v_ty with
                | Some ty -> inf_rec_ bv ty
                | None ->
                  let ty, m = Expr.ty_meta ~pos env in
                  env.to_gen <- m :: env.to_gen;
                  ty
              in
              let v = Var.make v.A.v_name ty in
              env.fvars <- Str_map.add v.v_name v env.fvars;
              v
          in
          Expr.var ~pos v
        | A.Wildcard ->
          let t, m = Expr.wildcard ~pos env in
          env.to_gen <- m :: env.to_gen;
          t
        | A.Meta {name;ty} ->
          let ty = match ty with
            | None -> Expr.type_
            | Some ty -> inf_rec_ bv ty
          in
          let t, m = Expr.meta ~pos name ty in
          env.to_gen <- m :: env.to_gen;
          t
        | A.Eq (a,b) ->
          let a = inf_rec_ bv a in
          let b = inf_rec_ bv b in
          unif_exn_ (Expr.ty a) (Expr.ty b);
          Expr.eq ~pos a b
        | A.Const {c;at} ->
          (* convert directly into a proper kernel constant *)
          let t =
            let c = match c with
              | A.C_k c -> c
              | A.C_local name ->
                match K.Ctx.find_const_by_name env.ctx name with
                | None ->
                  errorf
                    (fun k->k"cannot find constant %a@ at %a"
                         A.Const.pp c Position.pp pos)
                | Some c -> K.Expr.const env.ctx c
            in
            Expr.const ~pos c
          in
          if at then t else complete_ty_args_ ~pos env t
        | A.App (f,l) ->
          let f = inf_rec_ bv f in
          let l = List.map (inf_rec_ bv) l in
          Expr.app_l ~pos env f l
        | A.With (vs, bod) ->
          let bv =
            List.fold_left
              (fun bv v ->
                 let ty = infer_ty_opt_ ~pos bv v.A.v_ty in
                 let var = Expr.var ~pos (Var.make v.A.v_name ty) in
                 Str_map.add v.A.v_name var bv)
              bv vs
          in
          inf_rec_ bv bod
        | A.Lambda (vars, bod) ->
          let bv, vars =
            CCList.fold_map
              (fun bv v ->
                 let v' = infer_bvar_ ~pos bv v in
                 Str_map.add v.A.v_name (Expr.bvar ~pos v') bv, v')
              bv vars
          in
          Expr.lambda_l ~pos vars @@ inf_rec_ bv bod
        | A.Bind _ -> assert false (* TODO *)
        | A.Let (bindings, body) ->
          let bv', bindings =
            CCList.fold_map
              (fun bv' (v,t) ->
                 let v' = infer_bvar_ ~pos bv v in
                 let t = inf_rec_ bv t in
                 unif_exn_ v'.bv_ty (Expr.ty t);
                 let bv' = Str_map.add v.A.v_name (Expr.bvar ~pos v') bv' in
                 bv', (v', t))
              bv bindings
          in
          Expr.let_ ~pos bindings @@ inf_rec_ bv' body
        end

     and infer_ty_opt_ ~pos bv ty : ty =
       match ty with
       | None -> Expr.type_
       | Some ty0 ->
         let ty = inf_rec_ bv ty0 in
         if not @@ Expr.is_eq_to_type ty then (
           unif_exn_ ~pos ty0 ty Expr.type_;
         );
         ty
     and infer_bvar_ ~pos bv v : bvar =
       let ty_v = infer_ty_opt_ ~pos bv v.A.v_ty in
       let v' = BVar.make (ID.make v.A.v_name) ty_v in
       v'
    in
    inf_rec_ Str_map.empty e0
end

let process_stmt
  ~on_show ~on_error
  (env:env) (st:A.top_statement) : env =
  Log.debugf 2 (fun k->k"(@[TA.process-stmt@ %a@])" A.Top_stmt.pp st);
  begin
    let pos = A.Top_stmt.pos st in
    try
      match A.Top_stmt.view st with
      | A.Top_enter_file s ->
        env.cur_file <- s
      | A.Top_def _
      | A.Top_decl _
      | A.Top_fixity _
      | A.Top_axiom _
      | A.Top_goal _
      | A.Top_theorem _
      | A.Top_show _ ->
        error "TODO" (* TODO *)
      | A.Top_show_expr e ->
        let e = Ty_infer.infer_expr env e in
        on_show pos (fun out () -> Fmt.fprintf out "expr %a" Expr.pp e)
      | A.Top_show_proof _ ->
        error "TODO" (* TODO *)
      | A.Top_error { msg } ->
        on_error pos msg
    with
    | Trustee_error.E e ->
      on_error pos (fun out () -> Trustee_error.pp out e)
  end;
  env
