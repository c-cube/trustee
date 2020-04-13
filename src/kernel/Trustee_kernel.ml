
(** {1 The Kernel of Trust for Trustee}

    This file contains the whole kernel of trust for Trustee: terms (with
    type-checking constructors), and theorems.

    If this code is correct, then the rest of Trustee cannot build an invalid
    theorem, even by introducing new axioms (since they are tracked in theorems).
*)

module Fmt = CCFormat

type 'a iter = ('a -> unit) -> unit
let pp_list ppx out l =
  Fmt.(list ~sep:(return "@ ") ppx) out l

module type S = sig
  (** {2 Errors} *)

  exception Error of unit Fmt.printer

  val error_ : unit Fmt.printer -> 'a
  val errorf_ :
    ?pre:(Format.formatter -> unit) ->
    ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> 'b

  val error_wrapf_ : (Format.formatter -> unit -> unit) ->
    ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> 'b

  (** {2 Identifiers}

      Identifiers represent a given logic symbols. A handful are predefined,
      the other ones are introduced by the user or the problem to check. *)
  module ID : sig
    type t

    val make : string -> t

    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
    val pp : t Fmt.printer
    val fresh_copy : t -> t
    module Map : Map.S with type key = t

    val pp_int_ : bool ref
  end

  (** {2 Exprs}

      Logical expressions, types, and formulas. *)
  module Expr : sig
    type t

    type var
    type var_content
    type const_content

    type view =
      | Type
      | Kind
      | Const of const_content
      | Var of var_content
      | App of t * t
      | Lambda of var * t
      | Arrow of t * t
      | Pi of var * t

    val view : t -> view
    val ty : t -> t option
    val ty_exn : t -> t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
    val pp : t Fmt.printer
    val pp_inner : t Fmt.printer

    val type_ : t
    val kind : t
    val bool : t
    val app : t -> t -> t
    val app_l : t -> t list -> t
    val arrow : t -> t -> t
    val arrow_l : t list -> t -> t
    val (@->) : t -> t -> t
    val new_const : string -> t -> t
    val new_const_infix : string -> t -> t
    val new_var : string -> t -> var
    val new_var' : string -> t -> t
    val var : var -> t
    val var_of_c : var_content -> var
    val lambda : var -> t -> t
    val pi : var -> t -> t

    val eq_const : t
    val imply_const : t
    val select_const : t

    val eq : t -> t -> t
    val imply : t -> t -> t

    val subst1 : var -> t -> in_:t -> t
    (** [subst1 v t ~in_:u] builds the term [u [v:=t]] where all instances of
        [v] are replaced by [t]. *)

    val var_map_ty : var -> (t -> t) -> var
    (** Apply [f] to the variable's type *)

    val is_bool : t -> bool
    val is_a_type : t -> bool
    val is_a_bool : t -> bool
    val is_var : t -> bool

    val is_closed : t -> bool

    val alpha_equiv : t -> t -> bool
    (** [alpha_equiv t u] is true iff [t] and [u] are alpha-equivalent, i.e.
        equal up to renaming of bound variables. *)

    val unfold_app : t -> t * t list
    (** [unfold_app (f a b c)] is [f, [a;b;c]] *)

    val as_var_exn : t -> var
    (** [as_var_exn v] is the variable [v].
        @raise Error if the term is not a variable. *)

    val unfold_eq_exn : t -> t * t
    (** [unfold_eq_exn (= a b)] is [(a,b)].
        @raise Error if the term is not an equality. *)

    type term = t

    module Var : sig
      type t = var

      val equal : t -> t -> bool

      val name : t -> ID.t
      val name_str : t -> string
      val ty : t -> term

      val pp : t Fmt.printer

      val has_ty : t -> term -> bool
      (** [Var.has_ty v ty] is true iff [ty v = ty] *)

      module Set : Set.S with type elt = t
      module Map : Map.S with type key = t
      module Tbl : Hashtbl.S with type key = t
    end

    type subst

    module Subst : sig
      type t = subst

      val empty : t
      (** Empty substitution *)

      val add : var -> term -> t -> t
      (** [add v t subst] binds [v |-> t] in a new substitution *)

      val remove : var -> t -> t
      (** [remove v subst] removes [v] from the substitution, if present *)

      val find : t -> var -> term option

      val find_exn : t -> var -> term
      (** @raise Not_found if the variable isn't bound *)

      val of_list : (var*term) list -> t
      val to_list : t -> (var*term) list
      val iter : (var -> term -> unit) -> t -> unit
      val pp : t Fmt.printer

      val apply : t -> (term -> term)
      (** [apply subst] is a function that instantiates terms it's applied to
          using [subst]. It contains an internal cache. *)
    end

    module Set : Set.S with type elt = t
    module Tbl : Hashtbl.S with type key = t
  end

  (** {2 Theorems}

      Here lies the core of the LCF system: the only values of type
      {!Thm.t} that can be constructed are valid consequences of the
      logic's axioms.

      The rules are heavily inspired from HOL light's "fusion.ml" module.
  *)
  module Thm : sig
    type t

    type axiom = {
      ax_name: ID.t;
      ax_thm: t;
    }

    val pp : t Fmt.printer
    val concl : t -> Expr.t
    val hyps_l : t -> Expr.t list
    val hyps_iter : t -> Expr.t iter
    val dep_on_axioms : t -> axiom iter

    val view_l: t -> Expr.t * Expr.t list * axiom iter

    (** Creation of new terms *)

    val refl : Expr.t -> t
    (** [refl t] is [ |- t=t ] *)

    val assume : Expr.t -> t
    (** [assume F] is [F |- F] *)

    val trans : t -> t -> t
    (** [trans (F1 |- a=b) (F2 |- b'=c)] is [F1, F2 |- a=c]
        where [b] and [b'] are alpha equivalent. *)

    val congr : t -> t -> t
    (** [congr (F1 |- f=g) (F2 |- t=u)] is [F1, F2 |- f t=g u] *)

    val abs : Expr.var -> t -> t
    (** [abs x (F |- t=u)] is [F |- (λx.t)=(λx.u)].
        Fails if [x] occurs freely in [F]. *)

    val cut : ?fail_if_not_found:bool -> lemma:t -> t -> t
    (** [cut (F1 |- b) ~lemma:(F2, b |- c)] is [F1, F2 |- c].
        This fails if [b] does not occur {b syntactically} in the hypothesis
        of the second theorem.

        NOTE: this is not strictly necessary, as it's not an axiom in HOL light,
        but we include it here anyway.
    *)

    val mp : t -> t -> t
    (** [mp (F1 |- a) (F2 |- a' ==> b)] is [F1, F2 |- b]
        where [a] and [a'] are alpha equivalent. *)

    val bool_eq : eq:t -> t -> t
    (** [bool_eq ~eq:(F1 |- a=b) (F2 |- a)] is [F1, F2 |- b].
        This is the boolean equivalent of transitivity. *)

    val bool_eq_intro : t -> t -> t
    (** [bool_eq_intro (F1, a |- b) (F2, b |- a) is [F1, F2 |- b=a].
        This is a way of building a boolean [a=b] from proofs of
        [a==>b] and [b==>a] (or [a|-b] and [b|-a]).
        *)

    val instantiate : t -> Expr.subst -> t
    (** [instantiate thm σ] produces
        [ Fσ |- Gσ]  where [thm] is [F |- G] *)

    val beta : Expr.t -> Expr.t -> t * Expr.t
    (** [beta (λx.u) a] is [ |- (λx.u) a = u[x:=a] ].
        [u[x:=a]] is returned along. *)

    val beta_conv : Expr.t -> t
    (** [beta_conv ((λx.u) a)] is [ |- (λx.u) a = u[x:=a]].
        Fails if the term is not a beta-redex. *)

    val new_basic_definition : Expr.t -> t * Expr.t
    (** [new_basic_definition (x=t)] where [x] is a variable and [t] a term
        with a closed type,
        returns a theorem [|- x=t] where [x] is now a constant, along with
        the constant [x] *)

    val axiom : string -> Expr.t list -> Expr.t -> t * axiom
    (** Create a new axiom [assumptions |- concl] with the given name.
        The axiom is tracked in all theorems that use it, see {!dep_on_axioms}.
        {b use with caution} *)
  end
end

module Make() : S = struct
  exception Error of unit Fmt.printer

  let error_ f = raise (Error f)
  let errorf_ ?(pre=fun _->()) k =
    raise (Error (fun out () ->
        pre out;
        k (fun fmt ->
            Format.kfprintf (fun fmt -> Format.fprintf fmt "@?") out fmt)))

  let error_wrapf_ f1 f2 =
    errorf_ ~pre:(fun out -> Fmt.fprintf out "%a@ " f1 ()) f2

  let () =
    Printexc.register_printer
      (function
        | Error f -> Some (Fmt.sprintf "@[<v1>@{<Red>Error@}:@ %a@]" f ())
        | _ -> None)

  module ID = struct
    type t = {name: string; id: int}

    let equal r1 r2 = CCInt.equal r1.id r2.id
    let compare r1 r2 = CCInt.compare r1.id r2.id
    let hash {name;id} = CCHash.(combine3 10 (string name)(int id))
    let name id = id.name

    let pp_int_ = ref false
    let pp out {name;id} =
      if !pp_int_ then Fmt.fprintf out "%s/%d" name id
      else Fmt.string out name

    let make =
      let n = ref 0 in
      fun name ->
        incr n;
        {name; id= !n}

    let fresh_copy self = make self.name

    module As_key = struct type nonrec t=t let compare=compare end
    module Map = Map.Make(As_key)
  end

  module Expr = struct
    type display = Normal | Infix
    type t = {
      mutable id: int;
      view: view;
      mutable ty: t option; (* computed lazily; only kind has no type *)
    }
    and var_content = {
      v_name: ID.t;
      v_ty: t;
      mutable v_self: t;
    }
    and const_content = {
      c_name: ID.t;
      c_ty: t; (** invariant: this type is closed *)
      c_display: display;
    }
    and var = t
    and view =
      | Type
      | Kind
      | Const of const_content
      | Var of var_content
      | App of t * t
      | Lambda of var * t
      | Arrow of t * t
      | Pi of var * t

    let equal a b = a.id = b.id
    let hash a = CCHash.int a.id
    let view t = t.view
    let ty t = t.ty
    let ty_exn t = match t.ty with
      | Some ty -> ty
      | None -> errorf_ (fun k->k "term has no type")
    let compare a b = CCInt.compare a.id b.id

    let const_eq c1 c2 = ID.equal c1.c_name c2.c_name
    let const_hash c = ID.hash c.c_name
    let var_eq v1 v2 = ID.equal v1.v_name v2.v_name && equal v1.v_ty v2.v_ty
    let var_hash v = CCHash.(combine2 (ID.hash v.v_name) (hash v.v_ty))

    module type HASHCONSABLE = sig
      type t
      val equal : t -> t -> bool
      val hash : t -> int
      val set_id : t -> int -> unit
    end

    module Make_hashcons(A : HASHCONSABLE): sig
      val hashcons : A.t -> A.t
    end = struct
      module W = Weak.Make(A)

      let tbl_ = W.create 1024
      let n_ = ref 0

      (* hashcons terms *)
      let hashcons t =
        if !n_ = max_int then errorf_ (fun k->k"kot: hashconsing: id set exhausted");
        let t' = W.merge tbl_ t in
        if t == t' then (
          incr n_;
          A.set_id t' !n_;
        );
        t'
    end

    module H = Make_hashcons(struct
        type nonrec t = t
        let equal a b =
          match a.view, b.view with
          | Type, Type | Kind, Kind -> true
          | Lambda (a1,a2), Lambda (b1,b2) -> equal a1 b1 && equal a2 b2
          | Pi (a1,a2), Pi (b1,b2) -> equal a1 b1 && equal a2 b2
          | Arrow (a1,a2), Arrow (b1,b2) -> equal a1 b1 && equal a2 b2
          | Const v1, Const v2 -> const_eq v1 v2
          | Var v1, Var v2 -> var_eq v1 v2
          | App (a1,b1), App (a2,b2) -> equal a1 a2 && equal b1 b2
          | (Lambda _ | Arrow _ | Pi _ | Type | Kind | App _ | Const _ | Var _), _ -> false

        let hash ty = match ty.view with
          | Kind -> 222
          | Type -> 1
          | Const v -> CCHash.(combine2 5 (const_hash v))
          | Var v -> CCHash.(combine2 10 (var_hash v))
          | App (a, b) -> CCHash.(combine3 20 (hash a) (hash b))
          | Lambda (a, b) -> CCHash.(combine3 30 (hash a) (hash b))
          | Pi (a, b) -> CCHash.(combine3 40 (hash a) (hash b))
          | Arrow (a, b) -> CCHash.(combine3 50 (hash a) (hash b))

        let set_id ty id = assert (ty.id = -1); ty.id <- id
      end)

    module As_key = struct
      type nonrec t = t
      let equal = equal
      let hash = hash
      let compare=compare
    end
    module Set = Set.Make(As_key)
    module Tbl = Hashtbl.Make(As_key)
    module Map = Map.Make(As_key)

    let kind = H.hashcons {view=Kind; id= -1; ty=None}
    let make_with_ ~k view =
      let t = {view; id= -1; ty=None} in
      let u = H.hashcons t in
      if t == u then (
        k u;
      );
      u

    let make_ view ty = make_with_ view ~k:(fun u -> u.ty <- Some (ty ()))

    let type_ = make_ Type (fun () -> kind)

    let unfold_app t =
      let rec aux acc t =
        match t.view with
        | App (f, u) -> aux (u::acc) f
        | _ -> t, acc
      in
      aux [] t

    let rec pp_rec out t =
      match t.view with
      | Kind -> Fmt.string out "Kind"
      | Type -> Fmt.string out "Type"
      | Const c -> ID.pp out c.c_name
      | Var v -> ID.pp out v.v_name
      | Lambda (a,b) -> Fmt.fprintf out "(@[\\%a:%a.@ %a@])" pp_rec a pp_inner (ty_exn a) pp_rec b
      | Pi (a,b) -> Fmt.fprintf out "@[@<1>Π%a:%a.@ %a@]" pp_rec a pp_inner (ty_exn a) pp_rec b
      | Arrow (a,b) -> Fmt.fprintf out "@[%a@ -> %a@]" pp_inner a pp_rec b
      | App _ ->
        let f, args = unfold_app t in
        assert (args<>[]);
        begin match f.view, args with
          | Const {c_display=Infix; c_name; _}, [a;b] ->
            Fmt.fprintf out "@[%a@ @[<1>%a@ %a@]@]" pp_inner a ID.pp c_name pp_inner b
          | Const {c_display=Infix; c_name; _}, _::_::_ ->
            (* display [= u a b] as [a = b] *)
            let ifx_args, args = CCList.take_drop (List.length args-2) args in
            let ifx_all_types =
              List.for_all
                (fun a -> CCOpt.map_or ~default:false (equal type_) (ty a))
                ifx_args
            in
            begin match args with
              | [a;b] when ifx_all_types  ->
                Fmt.fprintf out "@[%a@ %a %a@]"
                  pp_inner a ID.pp c_name pp_inner b
              | _ ->
                (* just default to prefix notation *)
                Fmt.fprintf out "@[%a@ %a@]" pp_rec f (pp_list pp_inner) args
            end
          | _ ->
            Fmt.fprintf out "@[%a@ %a@]" pp_rec f (pp_list pp_inner) args
        end

    and pp_inner out t =
      match t.view with
      | Arrow _ | Pi _ | App _ -> Fmt.fprintf out "(@[%a@])" pp_rec t
      | Lambda _ | Type | Kind | Var _ | Const _ -> pp_rec out t

    let pp out t = pp_rec out t

    (** is [t] a closed term? *)
    let is_closed (t:t) : bool =
      let rec aux bnd t =
        begin match t.ty with
          | None -> true | Some ty -> aux bnd ty
        end
        &&
        begin match t.view with
          | Kind | Type | Const _ -> true
          | Var _ -> Set.mem t bnd
          | Pi (x,u) | Lambda (x,u) ->
            aux bnd (ty_exn x) && aux (Set.add x bnd) u
          | App (f,t) -> aux bnd f && aux bnd t
          | Arrow (a,b) -> aux bnd a && aux bnd b
        end
      in
      aux Set.empty t

    let var (v:var) : t = v
    let var' v : t = make_ (Var v) (fun () -> v.v_ty)

    let new_const_ display s ty : t =
      (* type must be closed! *)
      if not (is_closed ty) then (
        errorf_
          (fun k->k"cannot declare constant %s@ with non-closed type %a"
              s pp ty)
      );
      make_ (Const {c_name=ID.make s; c_ty=ty; c_display=display})
        (fun () -> ty)

    type term = t

    module Var = struct
      type t = var
      let pp = pp
      let ty = ty_exn
      let name v = match v.view with Var v -> v.v_name | _ -> assert false
      let name_str v = ID.name (name v)
      let equal = equal
      let has_ty v t = equal (ty v) t

      module Set = Set
      module Tbl = Tbl
      module Map = Map
    end

    let new_const = new_const_ Normal
    let new_const_infix = new_const_ Infix
    let var_of_c v = v.v_self

    let new_var s ty : t =
      let vc = {v_name=ID.make s; v_ty=ty; v_self=ty } in
      make_with_ (Var vc) ~k:(fun self -> self.ty <- Some ty; vc.v_self <- self)
    let new_var' = new_var

    let bool = new_const "Bool" type_
    let arrow a b : t = make_ (Arrow (a,b)) (fun () -> type_)
    let arrow_l l ret : t = List.fold_right arrow l ret
    let (@->) = arrow

    let pi v body : t =
      if not @@ Var.has_ty v type_ then (
        errorf_
          (fun k->k"@[pi: variable %a@ should have type Type, not %a@]"
              Var.pp v pp_inner (Var.ty v));
      );
      if not @@ equal type_ (ty_exn body) then (
        errorf_
          (fun k->k"@[pi: body %a@ should have type Type, not %a@]"
              pp body pp_inner (ty_exn body));
      );
      make_ (Pi (v,body)) (fun () -> type_)

    let lambda v body : t =
      (* type of [λx:a. body] is [a->b] where [body:b],
         except if [a==type] in which case we use [Πx:type. b] *)
      let mk_ty() =
        let ty_v = Var.ty v in
        if equal ty_v type_ then (
          pi v (ty_exn body)
        ) else (
          arrow ty_v (ty_exn body)
        )
      in
      make_ (Lambda (v,body)) mk_ty

    let var_map_ty v f =
      match v.view with
      | Var v -> var' {v with v_ty=f v.v_ty}
      | _ -> assert false

    let rec app a b : t =
      let get_ty () = match a.ty, b.ty with
        | Some {view=Arrow (a_arg, a_ret); _}, Some ty_b when equal a_arg ty_b ->
          a_ret
        | Some {view=Pi (a_v, a_ty_body); _}, Some ty_b when equal (ty_exn a_v) ty_b ->
          (* substitute [b] for [a_v] in [a_ty_body] to obtain the type
             of [a b] *)
          subst1 a_v b ~in_:a_ty_body
        | _ ->
          errorf_
            (fun k->k "@[type mismatch:@ cannot apply @[%a@ : %a@]@ to @[%a : %a@]@]"
               pp_inner a pp_inner (ty_exn a) pp_inner b pp_inner (ty_exn b))
      in
      make_ (App (a,b)) get_ty

    (** substitution of [x] with [by] *)
    and subst1 (x:var) by ~in_ : t =
      (* TODO: use a local table to traverse term as a DAG? *)
      let rec aux t =
        if equal t x then by
        else (
          match t.view with
          | Type | Kind | Const _ -> t
          | Var v -> var' {v with v_ty=aux v.v_ty}
          | App (f, u) ->
            let f' = aux f in
            let u' = aux u in
            if f==f' && u==u' then t else app f' u'
          | Pi (y, _) | Lambda (y, _) when equal x y -> t (* shadowed *)
          | Lambda (y, body) -> lambda (aux y) (aux body)
          | Pi (y, body) -> pi (aux y) (aux body)
          | Arrow (a,b) -> arrow (aux a) (aux b)
        )
      in
      aux in_

    let alpha_equiv t u : bool =
      let n = ref 0 in
      let rec check (vm:int Var.Map.t) t1 t2 : bool =
        t1 == t2 ||
        begin match t1.view, t2.view with
          | Type, _ | Kind, _ | Const _, _ -> false (* would be equal *)
          | Var _, Var _ ->
            begin match Var.Map.find t1 vm, Var.Map.find t2 vm with
              | i, j -> i=j
              | exception Not_found -> false
            end
          | Arrow (a1,b1), Arrow (a2,b2) | App (a1,b1), App (a2,b2) ->
            check vm a1 a2 && check vm b1 b2
          | Pi (x1,b1), Pi (x2,b2) | Lambda (x1,b1), Lambda (x2,b2) ->
            check vm (Var.ty x1) (Var.ty x2) &&
            (* check [x1=x2 |- b1 = b2] *)
            begin
              let i = !n in
              incr n;
              let vm = vm |> Var.Map.add x1 i |> Var.Map.add x2 i in
              check vm b1 b2
            end
          | (Var _ | App _ | Arrow _ | Pi _ | Lambda _), _ -> false
        end
      in
      check Var.Map.empty t u

    let app_l f l = List.fold_left app f l

    let eq_const : t =
      let a = new_var "α" type_ in
      let ty = pi a (a @-> a @-> bool) in
      new_const_ Infix "=" ty

    let imply_const : t = new_const_ Infix "==>" (bool @-> bool @-> bool)

    let select_const : t =
      let a = new_var "α" type_ in
      let ty = pi a ((a @-> bool) @-> a) in
      new_const_ Normal "select" ty

    let eq a b : t = app_l eq_const [ty_exn a; a; b]
    let imply a b : t = app_l imply_const [a;b]

    let is_a_type t : bool = match t.ty with
      | Some ty -> equal ty type_
      | None -> false
    let is_bool = equal bool
    let is_a_bool t = match t.ty with Some b -> is_bool b | None -> false
    let is_var t = match t.view with Var _ -> true | _ -> false

    let as_var_exn t = match t.view with
      | Var _ -> t
      | _ -> errorf_ (fun k->k "%a is not a variable" pp t)

    let unfold_eq_exn t =
      try
        match t.view with
        | App (a, b) ->
          (match a.view with
           | App (a1,a2) ->
             (match a1.view with
              | App (f, _ty) when equal f eq_const -> a2,b
              | _ -> raise_notrace Exit)
           | _ -> raise_notrace Exit)
        | _ -> raise_notrace Exit
      with Exit -> errorf_ (fun k->k "%a is not an equation" pp t)

    module Subst = struct
      type t = term Map.t
      let empty : t = Map.empty
      let add (v:var) t self : t =
        assert (is_var v);
        Map.add v t self

      let remove = Map.remove
      let find_exn self v = Map.find v self
      let find self v = try Some (find_exn self v) with Not_found -> None
      let to_list self = Map.fold (fun v t l -> (v,t) :: l) self []
      let iter = Map.iter

      let pp out (self:t) =
        let pp_binding out (v,t) = Fmt.fprintf out "(@[%a@ := %a@])" pp v pp t in
        Fmt.fprintf out "{@[%a@]}" (pp_list pp_binding) (to_list self)

      let of_list l : t = List.fold_left (fun s (v,t) -> add v t s) empty l

      let apply (self:t) : term -> term =
        let apply_cache = Tbl.create 16 in
        let rec aux t =
          match t.view with
          | Type | Kind | Const _ -> t
          | t_view ->
            match Tbl.find apply_cache t with
            | u -> u
            | exception Not_found ->
              let u =
                match t_view with
                | Type | Kind | Const _ -> assert false
                | Var v ->
                  begin match Map.find t self with
                    | u -> u
                    | exception Not_found -> var' {v with v_ty=aux v.v_ty}
                  end
                | App (f, u) ->
                  let f' = aux f in
                  let u' = aux u in
                  if f==f' && u==u' then t else app f' u'
                | Lambda (y, body) ->
                  let y' = rebind_ y in
                  lambda y' (aux body)
                | Pi (y, body) ->
                  let y' = rebind_ y in
                  pi y' (aux body)
                | Arrow (a,b) -> arrow (aux a) (aux b)
              in
              Tbl.add apply_cache t u;
              u
        and rebind_ (v:var) : var =
          match v.view with
          | Var vi ->
            let v' =
              {vi with v_name=ID.fresh_copy vi.v_name; v_ty = aux vi.v_ty}
              |> var'
            in
            Tbl.add apply_cache v v';
            v'
          | _ -> assert false
        in
        aux
    end
    type subst = Subst.t
  end

  module Thm = struct
    type t = {
      concl: Expr.t;
      hyps: Expr.Set.t;
      dep_on_axioms: axiom ID.Map.t lazy_t; (* axioms this depends on *)
    }
    and axiom = {
      ax_name: ID.t;
      ax_thm: t;
    }

    let _deps self k = ID.Map.iter (fun _ ax -> k ax) (Lazy.force self.dep_on_axioms)
    let concl self = self.concl
    let hyps_iter self k = Expr.Set.iter k self.hyps
    let hyps_l self = Expr.Set.elements self.hyps
    let dep_on_axioms self = _deps self
    let view_l self = self.concl, Expr.Set.elements self.hyps, _deps self
    let pp out self =
      if Expr.Set.is_empty self.hyps then (
        Fmt.fprintf out "@[|- %a@]" Expr.pp_inner self.concl
      ) else (
        Fmt.fprintf out "@[%a@ |- %a@]"
          Fmt.(list ~sep:(return ",@ ") Expr.pp_inner) (Expr.Set.elements self.hyps)
          Expr.pp_inner self.concl
      )

    let _no_ax = lazy ID.Map.empty
    let make_ concl hyps dep_on_axioms : t = {concl; hyps; dep_on_axioms}

    let merge_ax_ (lazy m1) (lazy m2) =
      lazy (
        let merge_ _id ax1 _ax2 = Some ax1 in
        ID.Map.union merge_ m1 m2
      )

    let err_unless_bool_ what t =
      if not (Expr.is_a_bool t) then (
        errorf_ (fun k->k "%s: needs boolean term, not %a" what Expr.pp t)
      )

    let assume t : t =
      err_unless_bool_ "assume" t;
      make_ t (Expr.Set.singleton t) _no_ax

    let refl t : t = make_ (Expr.eq t t) Expr.Set.empty _no_ax

    let beta f t : t * _ =
      match Expr.view f with
      | Expr.Lambda (v, body) when Expr.Var.has_ty v (Expr.ty_exn t) ->
        let rhs = Expr.subst1 v t ~in_:body in
        let concl = Expr.eq (Expr.app f t) rhs in
        make_ concl Expr.Set.empty _no_ax, rhs
      | _ ->
        errorf_ (fun k->k "(@[thm.beta:@ %a is not a lambda@])" Expr.pp f)

    let beta_conv t : t =
      match Expr.view t with
      | App (a, b) -> fst (beta a b)
      | _ -> errorf_ (fun k->k"@[<1>beta_conv: not a redex:@ %a@]" Expr.pp t)

    let abs x (th:t) : t =
      try
        let t, u = Expr.unfold_eq_exn th.concl in
        make_
          (Expr.eq (Expr.lambda x t) (Expr.lambda x u))
          th.hyps th.dep_on_axioms
      with Error msg ->
        error_wrapf_ msg (fun k->k"(@[in@ abs %a@ %a@])" Expr.Var.pp x pp th)

    let mp t1 t2 =
      match Expr.unfold_app t2.concl with
      | f, [a;b] when Expr.equal Expr.imply_const f ->
        if not (Expr.equal a t1.concl || Expr.alpha_equiv a t1.concl) then (
          errorf_ (fun k->k "(@[mp: LHS of implication@ in %a@ does not match@])" pp t2)
        );
        make_ b (Expr.Set.union t1.hyps t2.hyps)
          (merge_ax_ t1.dep_on_axioms t2.dep_on_axioms)
      | _ ->
        errorf_ (fun k->k "(@[mp: thm %a@ should have an implication as conclusion@])" pp t2)

    let bool_eq ~eq:th1 th2 : t =
      try
        let a, b = Expr.unfold_eq_exn th1.concl in
        err_unless_bool_ "bool_eq" a;
        err_unless_bool_ "bool_eq" b;
        if not (Expr.equal a th2.concl || Expr.alpha_equiv a th2.concl) then (
          errorf_
            (fun k->k "(@[<hv1>conclusion of %a@ does not match LHS of@ %a@])"
                pp th1 pp th2);
        );
        make_ b (Expr.Set.union th1.hyps th2.hyps)
          (merge_ax_ th1.dep_on_axioms th2.dep_on_axioms)
      with Error msg ->
        error_wrapf_ msg (fun k->k "(@[in@ bool-eq@ %a@ %a@])" pp th1 pp th2)

    let bool_eq_intro th1 th2 : t =
      make_ (Expr.eq th1.concl th2.concl)
        Expr.Set.(union (remove th1.concl th2.hyps) (remove th2.concl th1.hyps))
        (merge_ax_ th1.dep_on_axioms th2.dep_on_axioms)

    let trans t1 t2 : t =
      try
        let a1, b1 = Expr.unfold_eq_exn t1.concl in
        let a2, b2 = Expr.unfold_eq_exn t2.concl in
        if not (Expr.equal b1 a2 || Expr.alpha_equiv b1 a2) then (
          errorf_
            (fun k->k "(@[<1>trans:@ %a@ and %a do not match@])" Expr.pp b1 Expr.pp a2)
        );
        make_ (Expr.eq a1 b2) (Expr.Set.union t1.hyps t2.hyps)
          (merge_ax_ t1.dep_on_axioms t2.dep_on_axioms)
      with Error e ->
        error_wrapf_ e (fun k->k"@[<1>in trans@ with thm1: %a@ and thm2: %a@]" pp t1 pp t2)

    let congr th1 th2 : t =
      try
        let f, g = Expr.unfold_eq_exn th1.concl in
        let t, u = Expr.unfold_eq_exn th2.concl in
        make_
          (Expr.eq (Expr.app f t) (Expr.app g u))
          (Expr.Set.union th1.hyps th2.hyps)
          (merge_ax_ th1.dep_on_axioms th2.dep_on_axioms)
      with Error f ->
        error_wrapf_ f (fun k->k "(@[in congr@ :th1 %a@ :th2 %a@])" pp th1 pp th2)

    let instantiate (t:t) (subst:Expr.subst) : t =
      let inst = Expr.Subst.apply subst in
      make_ (inst t.concl) (Expr.Set.map inst t.hyps) t.dep_on_axioms

    let cut ?(fail_if_not_found=true) ~lemma:l a : t =
      let {concl=concl_l; hyps=hyps_l; dep_on_axioms=_} = l in
      if not fail_if_not_found || Expr.Set.mem a.concl hyps_l then (
        let hyps = Expr.Set.remove a.concl hyps_l in
        let hyps = Expr.Set.union a.hyps hyps in
        make_ concl_l hyps (merge_ax_ a.dep_on_axioms l.dep_on_axioms)
      ) else (
        errorf_
          (fun k->k "(@[cut:@ conclusion of %a@ does not appear in hyps of %a@])"
              pp a pp l)
      )

    let new_basic_definition (t:Expr.t) : t * Expr.t =
      try
        let x, rhs = Expr.unfold_eq_exn t in
        if not (Expr.is_var x) then (
          errorf_ (fun k->k"new_basic_definition: %a should be a variable" Expr.pp x);
        );
        if not (Expr.is_closed rhs) then (
          errorf_ (fun k->k"new_basic_definition: %a should be closed" Expr.pp rhs);
        );
        let x = Expr.as_var_exn x in
        (* checks that the type of [x] is closed *)
        let c = Expr.new_const (ID.name @@ Expr.Var.name x) (Expr.Var.ty x) in
        let th = make_ (Expr.eq c rhs) Expr.Set.empty _no_ax in
        th, c
      with Error msg ->
        error_wrapf_ msg (fun k->k "(@[in new_basic_definition@ %a@])" Expr.pp t)

    let axiom name hyps concl : t * axiom =
      err_unless_bool_ "axiom" concl;
      List.iter (err_unless_bool_ "axiom") hyps;
      let ax_name = ID.make name in
      let rec thm = {
        concl; hyps=Expr.Set.of_list hyps;
        dep_on_axioms=lazy (ID.Map.singleton ax_name ax);
      }
      and ax = {
        ax_name;
        ax_thm=thm;
      }in
      thm, ax
  end
end
