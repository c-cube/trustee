

open Common_
module A = Parse_ast
module TA = Type_ast
module Log = Trustee_core.Log

type expr = TA.expr
type ty = TA.ty
type 'a meta_var = 'a TA.Meta_var.t

let (let@) f x = f x

module Or_error = struct
  type 'a t = ('a, Loc.t * Error.t) result
  exception E of Loc.t * Error.t
  let fail ~loc err = raise (E (loc, Error.make ~loc err))
  let failf ~loc k =
    let msg () =
      let r = ref "" in
      k (fun fmt -> Fmt.kasprintf (fun s ->  r:= s) fmt);
      !r
    in
    raise (E (loc, Error.make' ~loc msg))
end
type 'a or_error = 'a Or_error.t

(** State used for type inference.

    In particular it stores the environment in which expressions
    are typed. *)
module State : sig
  type t

  val create : env:Env.t -> unit -> t

  val to_generalize :
    t ->
    ty meta_var list

  val find_free_var : t -> string -> TA.Expr.var option

  val add_fvar : t -> TA.Var.t -> unit

  val reset : t -> unit

  val new_ty_meta : t -> loc:Loc.t -> TA.expr
  (** Allocate a new type metavariable *)

  val update_env : t -> (Env.t -> Env.t) -> unit

  val env : t -> Env.t
end = struct

  let names_ = "abcdefghijkl"

  type t = {
    mutable i: int;
    mutable to_gen : ty meta_var list;
    mutable fvars: TA.Expr.var Str_map.t;
    mutable env: Env.t;
  }

  let to_generalize self = self.to_gen
  let update_env self f = self.env <- f self.env
  let env self = self.env

  let find_free_var self (s:string) = Str_map.find_opt s self.fvars

  let reset self =
    self.to_gen <- [];
    self.fvars <- Str_map.empty

  let add_fvar self (v:TA.Var.t) =
    self.fvars <- Str_map.add v.name v self.fvars

  (* fresh type meta *)
  let new_ty_meta self ~loc =
    let off, coeff =
      let n = String.length names_ in
      self.i mod n, self.i / n
    in
    let c = names_.[off] in
    let name =
      if coeff = 0 then Printf.sprintf "'%c" c
      else Printf.sprintf "'%c%d" c coeff
    in
    self.i <- self.i + 1;
    let id = ID.make name in
    let m = TA.Meta_var.make ~loc ~ty:TA.Expr.type_ id in
    self.to_gen <- m :: self.to_gen;
    TA.Expr.mk_ ~loc ~ty:TA.Expr.type_ @@ Meta m

  let create ~env () : t =
    { to_gen=[];
      env;
      i=0;
      fvars=Str_map.empty;
    }

end

module type S = sig
  val state : State.t

  module Expr : sig
    val infer : A.Expr.t -> TA.Expr.t or_error
    val infer_reify : A.Expr.t -> TA.Expr.t
  end

  module Top : sig
    val infer : A.Top.t -> TA.Top.t list or_error
    val infer_reify : A.Top.t -> TA.Top.t list
  end
end

module Make(Arg : sig
    val state : State.t
  end) : S
= struct
  let state = Arg.state

  module Expr = struct
    type expr = TA.Expr.t
    open TA.Expr

    (** Substitute bound variables with expressions *)
    let subst_bvars (m:t ID.Map.t) (e:t) : t =
      let rec aux m e =
        let e = deref_ e in
        match e.ty with
        | None -> assert (e==TA.Init_.kind); e
        | Some ty ->
          let ty = aux m ty in
          let loc = e.loc in
          match e.view with
          | Kind | Type | Meta _ | Const{args=[];_} | Var _ ->
            {e with ty=Some ty}
          | Const {c; args} ->
            let args = aux_l m args in
            {e with ty=Some ty; view=Const {c; args}}
          | BVar v ->
            begin match ID.Map.find v.id m with
              | u -> {u with loc}
              | exception Not_found -> e
            end
          | App (f,a) -> mk_ ~loc ~ty @@ App (aux m f, aux m a)
          | Eq(a,b) -> mk_ ~loc ~ty @@ Eq(aux m a, aux m b)
          | Ty_arrow(arg,ret) ->
            mk_ ~loc ~ty @@ Ty_arrow(aux m arg, aux m ret)
          | Lambda (v, bod) ->
            let m, v' = rename_bvar m v in
            mk_ ~loc ~ty @@ Lambda (v', aux m bod)
          | Let (bs, bod) ->
            let m, bs =
              CCList.fold_map
                (fun m1 ((v:bvar),rhs) ->
                   let m1, v' = rename_bvar m1 v in
                   let v' = TA.BVar.map_ty v' ~f:(aux m) in
                   let v'_as_e = mk_ ~loc:v'.loc ~ty:v'.ty @@ BVar v' in
                   let rhs = aux m rhs in
                   ID.Map.add v.id v'_as_e m1, (v',rhs))
                m bs
            in
            mk_ ~loc ~ty @@ Let (bs, aux m bod)
          | Error err ->
            mk_ ~loc ~ty @@ Error err

      and aux_l m l = CCList.map (aux m) l

      (* rename a bound variable to avoid capture. Adds [v -> v'] to [m]. *)
      and rename_bvar m (v:bvar) : _ * bvar =
        let ty = aux m v.ty in
        let v' = {v with id=ID.copy v.id; ty=ty} in
        let v'_as_e = mk_ ~loc:v.loc ~ty:v'.ty @@ BVar v' in
        ID.Map.add v.id v'_as_e m, v'
      in
      aux m e

    (** Unification.

        Unification is intended to work on types, more precisely
        on types with meta-variables. It is required for type inference. *)
    module Unif : sig
      (** Error trace in case of unification failure *)
      type err_trace = (expr*expr) list

      val pp_err_trace : err_trace Fmt.printer

      val ty_app : loc:Loc.t -> t -> t -> (ty, err_trace) result
      (** [ty_app f a] computes the type of [f a] *)

      val ty_app_l : loc:Loc.t -> t -> t list -> (ty, err_trace) result
      (** [ty_app_l f args] computes the type of [f args] *)

      val unify : t -> t -> (unit, err_trace) result
      (** [unify a b] unifies the expressions [a] and [b], modifying their meta-variables.
          @raise E if it fails. *)
    end = struct

      type err_trace = (expr*expr) list
      exception E of err_trace

      let pp_err_trace out (st:err_trace) : unit =
        Fmt.fprintf out "@[<hv>";
        List.iter (fun (e1,e2) ->
            Fmt.fprintf out "@[<2>- unifying@ %a@ and %a@];@ "
              pp (deref_ e1) pp (deref_ e2))
          st;
        Fmt.fprintf out "@]"

      (* are [a] and [b] the same bound var under given [renaming] (maps bound vars
         to other bound vars)? *)
      let same_bvar_ renaming (a:bvar) (b:bvar) : bool =
        let a = try ID.Map.find a.id renaming with Not_found -> a.id in
        let b = try ID.Map.find b.id renaming with Not_found -> b.id in
        ID.equal a b

      exception E_contains

      (* does [e] contain the meta [sub_m] *)
      let contains_meta ~sub_m (e:expr) : bool =
        let rec aux () e =
          match view e with
          | Meta m' when TA.Meta_var.equal sub_m m' ->
            raise_notrace E_contains
          | _ ->
            iter () e ~f_bind:(fun () _ -> ()) ~f:aux
        in
        try aux () e; false
        with E_contains -> true

      let contains_bvar ~(bv:bvar) (e:expr) : bool =
        let rec aux () e =
          match view e with
          | BVar v when ID.equal v.id bv.id ->
            raise_notrace E_contains
          | _ ->
            iter () e ~f_bind:(fun () _ -> ()) ~f:aux
        in
        try aux () e; false
        with E_contains -> true

      (* compute type of [f a] *)
      let rec ty_app_ ~loc (ty_f:expr) (arg:expr) : ty =
        let ty_f = deref_ ty_f in
        let ty_arg = deref_ (ty_exn arg) in

        begin match view ty_f with
          | Ty_arrow (f_arg, f_ret) ->
            unif_rec_ f_arg ty_arg;
            f_ret
          | _ ->
            (* unify with an arrow [ty_arg -> ?ret], return [?ret] *)
            let ty_ret = State.new_ty_meta state ~loc in
            unif_rec_ ty_f (mk_ ~loc ~ty:type_ @@ Ty_arrow(ty_arg, ty_ret));
            ty_ret
        end

      (* unify two terms. This only needs to be complete for types. *)
      and unif_rec_ (a:expr) (b:expr) : unit =
        let[@inline] fail_ st a b =
          raise_notrace (E ((a,b) :: st))
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
            | Type, Type | Kind, Kind -> ()
            | Var a, Var b when a.name = b.name -> ()
            | BVar a, BVar b
              when ID.equal a.id b.id || same_bvar_ renaming a b
              -> ()
            | Const c1, Const c2 when TA.Const.equal c1.c c2.c ->
              aux_l st renaming a b c1.args c2.args
            | Ty_arrow (a1,a2), Ty_arrow (b1,b2) ->
              aux st' renaming a1 b1;
              aux st' renaming a2 b2;
            | Eq (a1,a2), Eq (b1,b2)
            | App (a1,a2), App (b1,b2) ->
              aux st' renaming a1 b1;
              aux st' renaming a2 b2;
            | Meta m1, Meta m2 when TA.Meta_var.equal m1 m2 -> ()
            | Meta m1, _ ->
              if contains_meta ~sub_m:m1 b then (
                fail_ st a b
              );
              assert (m1.deref==None);
              m1.deref <- Some b;
            | _, Meta m2 ->
              if contains_meta ~sub_m:m2 a then (
                fail_ st a b
              );
              assert (m2.deref == None);
              m2.deref <- Some a;
            | Let _, _ ->
              fail_ st a b (* TODO? *)
            | (Type | Kind | Var _ | BVar _ | Eq _ | Error _
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
        aux [] ID.Map.empty a b

      let unify a b : (unit, err_trace) result =
        try
          unif_rec_ a b;
          Ok ()
        with E err -> Error err

      let ty_app ~loc f arg : (ty, err_trace) result =
        try
          let ty = ty_app_ ~loc (ty_exn f) arg in
          Ok ty
        with E err -> Error err

      let ty_app_l ~loc f args =
        let ty_f = ty_exn f in
        try
          let ty = List.fold_left (ty_app_ ~loc) ty_f args in
          Ok ty
        with E err -> Error err
    end

    let type_ = TA.Init_.type_
    let ty_var ~loc s : t = mk_ ~loc ~ty:type_ (Var (TA.Var.make ~loc s type_))
    let ty_meta ~loc (id:ID.t) : ty =
      mk_ ~loc ~ty:type_ @@ Meta (TA.Meta_var.make ~ty:type_ ~loc id)
    let ty_arrow ~loc a b : ty = mk_ ~loc ~ty:type_ (Ty_arrow (a,b))
    let ty_arrow_l ~loc args ret : ty = CCList.fold_right (ty_arrow ~loc) args ret

    let bvar ~loc (v:bvar) : t = mk_ ~loc ~ty:v.ty (BVar v)
    let var ~loc (v:var) : t = mk_ ~loc ~ty:v.ty (Var v)
    let var' ~loc v ty : t = var ~loc (TA.Var.make ~loc v ty)

    let bool : t =
      mk_ ~loc:Loc.none ~ty:TA.Const.bool.ty @@
      Const {c=TA.Const.bool; args=[]}

    (* composite constructors *)

    let let_ ~loc bs bod : t = mk_ ~loc ~ty:(ty_exn bod) @@ Let (bs, bod)

    let lambda ~loc v bod : t =
      let ty = ty_arrow ~loc (TA.BVar.ty v) (ty_exn bod) in
      mk_ ~loc ~ty @@ Lambda (v, bod)

    let lambda_l ~loc vs bod =
      CCList.fold_right (lambda ~loc) vs bod

    let error ~loc ~ty err : t = mk_ ~loc ~ty @@ Error err

    let[@inline] is_equal_to_type (self:t) : bool =
      match view self with | Type -> true | _ -> false

    (** is the expression a type? *)
    let is_ty (self:t) : bool = is_equal_to_type (ty_exn self)

    (* eval [f()], but catches errors and turn them into expression nodes. *)
    let guard_err_ ~loc f =
      try f()
      with Error.E err ->
        (* wrap in an error *)
        let ty = error ~loc ~ty:type_ @@ Error.make "unknown type" in
        error ~loc ~ty @@ err

    (* TODO: unify a.ty b.ty. If it fails, turn into
        Error with type bool and message explaining why it fails *)
    let eq ~loc a b : t =
      let ty = ty_exn a in
      (* TODO: unify ty (ty_exn b) *)
      mk_ ~loc ~ty @@ Eq (a,b)

    let const ~loc (c:TA.const) args : t =
      let@ () = guard_err_ ~loc in
      let@ () =
        Error.guard (Error.wrapf ~loc "expr.const %a %a" TA.Const.pp c (Fmt.Dump.list pp) args)
      in
      begin match c.args, args with
        | C_arity 0, [] -> mk_ ~loc ~ty:type_ @@ Const {c;args}
        | C_vars [], [] -> mk_ ~loc ~ty:type_ @@ Const {c;args}

        | C_arity n, _ ->
          if not (List.length args=n && List.for_all is_ty args) then (
            Error.fail "wrong arity"
          );
          mk_ ~loc ~ty:type_ @@ Const {c;args}
        | C_vars vars, _ ->
          if not(List.length args=List.length vars) then Error.fail "wrong arity";
          if not (List.for_all is_ty args) then Error.fail "an argument is not a type";

          let subst =
            List.fold_left2
              (fun m (v:bvar) a -> ID.Map.add v.id a m)
              ID.Map.empty vars args in
          let ty = subst_bvars subst c.ty in
          mk_ ~loc ~ty @@ Const {c; args}
      end

    let app f (arg:t) : t =
      let loc = Loc.(f.loc ++ arg.loc) in
      let ty = match Unif.ty_app ~loc f arg with
        | Ok ty -> ty
        | Error err ->
          Error.failf ~loc
            (fun k->k"Cannot apply `%a`@ to `%a`@ trace: %a"
                pp f pp arg Unif.pp_err_trace err)
      in
      mk_ ~loc ~ty @@ App (f, arg)

    let app_l (f:t) (args:t list) : t =
      List.fold_left app f args

    module AE = A.Expr

    let unif_exn_ ~loc e a b =
      match Unif.unify a b with
      | Ok () -> ()
      | Error st ->
        Or_error.failf ~loc
          (fun k->k
              "@[<hv2>type error@ \
               @[while inferring the type @[<2>of %a@]@]:@ \
               unification error in the following trace:@ %a@]"
              AE.pp e Unif.pp_err_trace st)

    let unif_type_with_ ~loc e ty =
      match Unif.unify (ty_exn e) ty with
      | Ok () -> ()
      | Error st ->
        Or_error.failf ~loc
          (fun k->k
              "@[<hv2>type error@ \
               @[<2>while unifying the type @[<2>of %a@]@ with %a@]:@ \
               unification error in the following trace:@ %a@]"
              pp e pp ty Unif.pp_err_trace st)

    type binding = BV of bvar | V of var

    let rec infer_ ~reify (bv:binding Str_map.t) (e:A.Expr.t) : expr =
      let module Expr = TA.Expr in
      let inf_rec_ = infer_ ~reify in
      let loc = AE.loc e in
      (* Log.debugf 15 (fun k->k"infer-rec loc=%a e=`%a`" Loc.pp loc AE.pp e); *)

      (* reify errors, if required *)
      let wrap f =
        if reify then guard_err_ ~loc f
        else f()
      in
      wrap @@ fun () ->

      begin match AE.view e with
        | AE.Type -> Expr.type_

        | AE.Error err ->
          let ty = State.new_ty_meta state ~loc in
          error ~loc ~ty @@ err

        | AE.Ty_arrow (a, b) ->
          ty_arrow_l ~loc (List.map (inf_rec_ bv) a) (inf_rec_ bv b)

        | AE.Var v when Str_map.mem v.name bv ->
          (* use variable in scope, but change location of the expression *)
          begin match Str_map.find v.name bv with
            | BV bv -> bvar ~loc bv (* bound variable *)
            | V v -> var ~loc v
          end

        | AE.Var va ->
            begin match
              State.find_free_var state va.name,
              Env.find_const va.name (State.env state)
            with
            | Some v', _ ->
              begin match va.A.Var.ty with
                | None -> ()
                | Some ty ->
                  (* unify expected type with actual type *)
                  let ty = inf_rec_ bv ty in
                  unif_exn_ ~loc e ty v'.TA.Var.ty
              end;
              var ~loc v'

            | None, Some c ->
              (* named variable *)
              infer_const_ ~loc c

            | None, None ->
              (* new free variable *)
              let ty = match va.ty with
                | Some ty -> inf_rec_ bv ty
                | None -> State.new_ty_meta state ~loc
              in
              let v = TA.Var.make ~loc va.name ty in
              State.add_fvar state v;
              var ~loc v
          end

        | AE.Wildcard ->
          State.new_ty_meta state ~loc

        | AE.Meta _ ->
          assert false (* TODO: do we want to handle that?
          let ty = match ty with
            | None -> Expr.type_
            | Some ty -> inf_rec_ bv ty
          in
          let t, m = Expr.meta ~loc name ty in
          st.to_gen <- m :: st.to_gen;
          t
                       *)

        | AE.Eq (a,b) ->
          let a = inf_rec_ bv a in
          let b = inf_rec_ bv b in
          unif_exn_ ~loc e (ty_exn a) (ty_exn b);
          eq ~loc a b

        | AE.App (f,args) ->
          let f = inf_rec_ bv f in
          let args = List.map (inf_rec_ bv) args in
          app_l f args

        | AE.With (vs, bod) ->
          let bv =
            List.fold_left
              (fun bv (v:AE.var) ->
                 let ty =
                   infer_ty_opt_ ~reify ~loc ~default:type_ bv v.ty in
                 let var = TA.Var.make ~loc v.name ty in
                 Str_map.add v.name (V var) bv)
              bv vs
          in
          (* return the body, removing "with" *)
          inf_rec_ bv bod

        | AE.Lambda (vars, bod) ->
          let bv, vars =
            CCList.fold_map
              (fun bv (v:AE.var) ->
                 let v' = infer_bvar_ ~reify bv v in
                 Str_map.add v.name (BV v') bv, v')
              bv vars
          in
          let bod = inf_rec_ bv bod in
          lambda_l ~loc vars bod

        | AE.Bind { b; vars; body } ->

          (* resolve binder *)
          let b =
            match Env.find_const (A.Const.name b) (State.env state) with
            | None ->
              Error.failf ~loc
                (fun k->k"Unknown constant %a" A.Const.pp b)

            | Some c -> c
          in

          (* Log.debugf 5 (fun k->k"binder: f=%a@ ty=%a" Expr.pp f Expr.pp (Expr.ty f));*)
          let bv, vars =
            CCList.fold_map
              (fun bv (v:AE.var) ->
                 let v' = infer_bvar_ ~reify bv v in
                 Str_map.add v.name (BV v') bv, v')
              bv vars
          in
          let body = inf_rec_ bv body in
          (* Log.debugf 5 (fun k->k"body: f=%a@ ty=%a" Expr.pp body Expr.pp (Expr.ty body));*)

          (* now for each [v], create [b (\x. bod)] *)
          CCList.fold_right
            (fun bv body ->
               let b = infer_const_ ~loc b in
               let lam = lambda ~loc bv body in
               let e = app b lam in
               Log.debugf 5 (fun k->k"app: f=%a@ ty=%a" Expr.pp e Expr.pp (ty_exn e));
               e)
            vars body

        | AE.Let (bindings, body) ->
          let bv', bindings =
            CCList.fold_map
              (fun bv' ((v:AE.var),t) ->
                 let v' = infer_bvar_ ~reify bv v in
                 let t = inf_rec_ bv t in
                 unif_exn_ ~loc:Loc.(v.loc ++ t.loc) e v'.ty (ty_exn t);
                 let bv' = Str_map.add v.name (BV v') bv' in
                 bv', (v', t))
              bv bindings
          in
          let_ ~loc bindings @@ inf_rec_ bv' body
      end

    and infer_const_ ~loc (c:TA.Const.t) : expr =
      (*Log.debugf 50 (fun k->k"infer-const %a at %a" A.Const.pp c Loc.pp loc);*)
      let arity =
        match TA.Const.args c with
        | TA.Const.C_arity n -> n
        | TA.Const.C_vars vs -> List.length vs
      in
      let args =
        CCList.init arity (fun _ -> State.new_ty_meta ~loc state)
      in
      const ~loc c args

    and infer_ty_opt_ ~reify ~loc ?default bv ty : ty =
      match ty with
      | None ->
        begin match default with
          | Some ty -> ty
          | None -> State.new_ty_meta state ~loc
        end
      | Some ty0 ->
        let ty = infer_ ~reify bv ty0 in
        if not @@ (TA.Expr.is_a_type ty || TA.Expr.is_eq_to_type ty) then (
          unif_exn_ ~loc ty0 ty TA.Expr.type_;
        );
        ty

    and infer_bvar_ ~reify ?default bv (v:AE.var) : bvar =
      let ty_v = infer_ty_opt_ ~reify ?default ~loc:v.loc bv v.ty in
      let v' = TA.BVar.make ~loc:v.loc (ID.make v.name) ty_v in
      v'

    let infer (e:A.Expr.t) : expr or_error =
      try Ok (infer_ ~reify:false Str_map.empty e)
      with Or_error.E (loc,err) -> Error (loc,err)

    let infer_reify (e:A.Expr.t) : expr =
      infer_ ~reify:true Str_map.empty e
  end

  module Top = struct
    let infer_ ~reify (top:A.Top.t) : TA.Top.t list =
      let loc = A.Top.loc top in
      begin match A.Top.view top with
        | A.Top.Show e ->
          let e = Expr.infer_ ~reify Str_map.empty e in
          [TA.Top.show ~loc e]

        | _ ->
          Log.debugf 1 (fun k->k"TODO: handle %a" A.Top.pp top);
          []
      end

    let infer top =
      try Ok (infer_ ~reify:false top)
      with Or_error.E (loc,err) -> Error (loc, err)

    let infer_reify top = infer_ ~reify:true top
    (*
    type t = {
      st: Typing_state.t;
      on_show: Loc.t -> unit Fmt.printer -> unit;
      on_error: Loc.t -> unit Fmt.printer -> unit;
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
       *)
  end

end

let make (st:State.t) : (module S) =
  let module M = Make(struct
      let state=st
    end) in
  (module M:S)

(* FIXME
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
*)

(* TODO: fix that and move it into its own module?
   *)

