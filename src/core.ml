
(** {1 The Core data structures for Trustee}

    This file contains the whole kernel of trust for Trustee: terms (with
    type-checking constructors), and theorems.
*)

module Fmt = CCFormat

let pp_list ppx out l =
  Fmt.(list ~sep:(return "@ ") ppx) out l

let invalid_argf msg = Fmt.kasprintf invalid_arg msg

(** {2 Identifiers}

    Identifiers represent a given logic symbols. A handful are predefined,
    the other ones are introduced by the user or the problem to check. *)
module ID : sig
  type t

  val make : string -> t

  val equal : t -> t -> bool
  val hash : t -> int
  val pp : t Fmt.printer
end = struct
  type t = {name: string; id: int}

  let equal r1 r2 = r1.id = r2.id && String.equal r1.name r2.name
  let hash {name;id} = CCHash.(combine3 10 (string name)(int id))

  let pp out {name;id=_} = Fmt.string out name

  let make =
    let n = ref 0 in
    fun name ->
      incr n;
      {name; id= !n}
end

(** {2 Exprs}

    Logical expressions, types, and formulas. *)
module Expr
  : sig
  type t

  type var
  type var_content
  type subst

  type view =
    | Type
    | Kind
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
  val new_sym : string -> t -> t
  val new_var : string -> t -> var
  val var : var -> t
  val lambda : var -> t -> t
  val lambda_l : var list -> t -> t
  val pi : var -> t -> t

  val true_ : t
  val false_ : t
  val eq_const : t
  val and_const : t
  val or_const : t
  val not_const : t

  val eq : t -> t -> t
  val and_ : t -> t -> t
  val or_ : t -> t -> t
  val and_l : t list -> t
  val or_l : t list -> t
  val not_ : t -> t

  val subst1 : var -> t -> in_:t -> t
  (** [subst1 v t ~in_:u] builds the term [u [v:=t]] where all instances of
      [v] are replaced by [t]. *)

  val is_bool : t -> bool
  val is_a_type : t -> bool
  val is_a_bool : t -> bool
  val is_var : t -> bool

  val unfold_app : t -> t * t list
  (** [unfold_app (f a b c)] is [f, [a;b;c]] *)

  type term = t

  module Set : Set.S with type elt = t
  module Tbl : Hashtbl.S with type key = t

  module Var : sig
    type t = var
    val ty : var -> term
    val pp : t Fmt.printer
    val has_ty : var -> term -> bool
    (** [Var.has_ty v ty] is true iff [ty v = ty] *)
  end

  module Subst : sig
    type t = subst

    val empty : t
    val add : var -> term -> t -> t
    val of_list : (var*term) list -> t
    val pp : t Fmt.printer

    val apply : t -> (term -> term)
    (** [apply subst] is a function that instantiates terms it's applied to
        using [subst]. It contains an internal cache. *)
  end
end
= struct
  type display = Normal | Infix
  type t = {
    mutable id: int;
    view: view;
    mutable ty: t option; (* computed lazily; only kind has no type *)
  }
  and var_content = {
    v_name: ID.t;
    v_ty: t;
    v_display: display;
  }
  and var = t
  and view =
    | Type
    | Kind
    | Var of var_content
    | App of t * t
    | Lambda of var * t
    | Arrow of t * t
    | Pi of var * t

  let equal a b = a.id = b.id
  let hash a = CCHash.int a.id
  let view t = t.view
  let ty t = t.ty
  let ty_exn t = match t.ty with Some ty -> ty | None -> invalid_argf "term has no type"
  let compare a b = CCInt.compare a.id b.id

  let var_eq v1 v2 = ID.equal v1.v_name v2.v_name
  let var_hash v = ID.hash v.v_name

  module H = Hashcons.Make(struct
      type nonrec t = t
      let equal a b =
        match a.view, b.view with
        | Type, Type | Kind, Kind -> true
        | Lambda (a1,a2), Lambda (b1,b2) -> equal a1 b1 && equal a2 b2
        | Pi (a1,a2), Pi (b1,b2) -> equal a1 b1 && equal a2 b2
        | Arrow (a1,a2), Arrow (b1,b2) -> equal a1 b1 && equal a2 b2
        | Var v1, Var v2 -> var_eq v1 v2
        | App (a1,b1), App (a2,b2) -> equal a1 a2 && equal b1 b2
        | (Lambda _ | Arrow _ | Pi _ | Type | Kind | App _ | Var _), _ -> false

      let hash ty = match ty.view with
        | Kind -> 222
        | Type -> 1
        | Var v -> CCHash.(combine2 10 (var_hash v))
        | App (a, b) -> CCHash.(combine3 20 (hash a) (hash b))
        | Lambda (a, b) -> CCHash.(combine3 30 (hash a) (hash b))
        | Pi (a, b) -> CCHash.(combine3 40 (hash a) (hash b))
        | Arrow (a, b) -> CCHash.(combine3 50 (hash a) (hash b))

      let set_id ty id = assert (ty.id = -1); ty.id <- id
    end)

  let kind = H.hashcons {view=Kind; id= -1; ty=None}
  let make_ view ty =
    let t = {view; id= -1; ty=None} in
    let u = H.hashcons t in
    if t == u then (
      u.ty <- Some (ty ());
    );
    u

  let type_ = make_ Type (fun () -> kind)

  let unfold_app t =
    let rec aux acc t =
      match t.view with
      | App (f, u) -> aux (u::acc) f
      | _ -> t, acc
    in
    aux [] t

  let rec pp out t =
    match t.view with
    | Kind -> Fmt.string out "Kind"
    | Type -> Fmt.string out "Type"
    | Var v -> ID.pp out v.v_name
    | Lambda (a,b) -> Fmt.fprintf out "@[\\%a:%a.@ %a@]" pp a pp (ty_exn a) pp b
    | Pi (a,b) -> Fmt.fprintf out "@[@<1>Π%a:%a.@ %a@]" pp a pp (ty_exn a) pp b
    | Arrow (a,b) -> Fmt.fprintf out "@[%a@ -> %a@]" pp a pp b
    | App _ ->
      let f, args = unfold_app t in
      assert (args<>[]);
      begin match f.view, args with
        | Var {v_display=Infix; v_name; _}, [a;b] ->
          Fmt.fprintf out "@[%a@ %a %a@]" pp_inner a ID.pp v_name pp_inner b
        | Var {v_display=Infix; v_name; _}, _::_::_ ->
          (* display [= u a b] as [a `= u` b] *)
          let ifx_args, args = CCList.take_drop (List.length args-2) args in
          begin match ifx_args, args with
            | [u], [a;b] ->
              Fmt.fprintf out "@[%a@ @[%a_%a@] %a@]"
                pp_inner a ID.pp v_name pp_inner u pp_inner b
            | _, [a;b] ->
              Fmt.fprintf out "@[%a@ `@[%a@ %a@]` %a@]"
                pp_inner a ID.pp v_name (pp_list pp_inner) ifx_args pp_inner b
            | _ -> assert false
          end
        | _ ->
          Fmt.fprintf out "@[%a@ %a@]" pp f (pp_list pp_inner) args
      end

  and pp_inner out t =
    match t.view with
    | Lambda _ | Arrow _ | Pi _ | App _ -> Fmt.fprintf out "(@[%a@])" pp t
    | Type | Kind | Var _ -> pp out t

  let var (v:var) : t = v
  let var' v : t = make_ (Var v) (fun () -> v.v_ty)
  let new_var_ display s ty : t =
    make_ (Var {v_name=ID.make s; v_ty=ty; v_display=display}) (fun () -> ty)
  let new_var name ty : t = new_var_ Normal name ty
  let new_sym = new_var

  let bool = new_var "Bool" type_
  let arrow a b : t = make_ (Arrow (a,b)) (fun () -> type_)
  let arrow_l l ret : t = List.fold_right arrow l ret
  let (@->) = arrow

  let lambda v body : t = make_ (Lambda (v,body)) (fun () -> arrow (ty_exn v) (ty_exn body))
  let lambda_l vs body : t = List.fold_right lambda vs body
  let pi v body : t = make_ (Pi (v,body)) (fun () -> type_)

  let rec app a b : t =
    let get_ty () = match a.ty, b.ty with
      | Some {view=Arrow (a_arg, a_ret); _}, Some ty_b when equal a_arg ty_b ->
        a_ret
      | Some {view=Pi (a_v, a_body); _}, Some ty_b when equal (ty_exn a_v) ty_b ->
        (* substitute [b] for [a_v] in [a_body] *)
        subst1 a_v b ~in_:a_body
      | _ ->
        invalid_argf "@[type mismatch:@ cannot apply @[%a@ : %a@]@ to %a@]" pp a pp (ty_exn a) pp b
    in
    make_ (App (a,b)) get_ty

  (* substitution of [x] with [by] *)
  and subst1 (x:var) by ~in_ : t =
    let rec aux t =
      if equal t x then by
      else (
        match t.view with
        | Type | Kind -> t
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

  let app_l f l = List.fold_left app f l

  let eq_const : t =
    let a = new_var "α" type_ in
    let ty = pi a (a @-> a @-> bool) in
    new_var_ Infix "=" ty

  let true_ = new_var "true" bool
  let false_ = new_var "false" bool
  let and_const : t = new_var_ Infix "/\\" (bool @-> bool @-> bool)
  let or_const : t = new_var_ Infix "\\/" (bool @-> bool @-> bool)
  let not_const : t = new_var "~" (bool @-> bool)

  let eq a b : t = app_l eq_const [ty_exn a; a; b]
  let and_ a b : t = app_l and_const [a;b]
  let or_ a b : t = app_l or_const [a;b]
  let not_ a : t = app not_const a
  let rec and_l = function [] -> true_ | [t] -> t | t :: ts -> and_ t (and_l ts)
  let rec or_l = function [] -> false_ | [t] -> t | t :: ts -> or_ t (or_l ts)

  let is_a_type t : bool = match t.ty with
    | Some ty -> equal ty type_
    | None -> false
  let is_bool = equal bool
  let is_a_bool t = match t.ty with Some b -> is_bool b | None -> false
  let is_var t = match t.view with Var _ -> true | _ -> false

  type term = t

  module As_key = struct
    type nonrec t = t
    let equal = equal
    let hash = hash
    let compare=compare
  end
  module Set = Set.Make(As_key)
  module Tbl = Hashtbl.Make(As_key)
  module Map = Map.Make(As_key)

  module Var = struct
    type t = var
    let pp = pp
    let ty = ty_exn
    let has_ty v t = equal (ty v) t
  end

  module Subst = struct
    type t = term Map.t
    let empty : t = Map.empty
    let add (v:var) t self : t =
      assert (is_var v);
      Map.add v t self

    let to_list self = Map.fold (fun v t l -> (v,t) :: l) self []

    let pp out (self:t) =
      let pp_binding out (v,t) = Fmt.fprintf out "(@[%a@ := %a@])" pp v pp t in
      Fmt.fprintf out "{@[%a@]}" (pp_list pp_binding) (to_list self)

    let of_list l : t = List.fold_left (fun s (v,t) -> add v t s) empty l

    let apply (self:t) : term -> term =
      let tbl = Tbl.create 8 in
      let rec aux t =
        match Tbl.find tbl t with
        | u -> u
        | exception Not_found ->
          let u =
            match t.view with
            | Type | Kind -> t
            | Var v ->
              begin match Map.find t self with
                | u -> u
                | exception Not_found -> var' {v with v_ty=aux v.v_ty}
              end
            | App (f, u) ->
              let f' = aux f in
              let u' = aux u in
              if f==f' && u==u' then t else app f' u'
            | Lambda (y, body) -> lambda (aux y) (aux body)
            | Pi (y, body) -> pi (aux y) (aux body)
            | Arrow (a,b) -> arrow (aux a) (aux b)
          in
          Tbl.add tbl t u;
          u
      in
      aux
  end
  type subst = Subst.t
end


(** {2 Theorems}

    Here lies the core of the LCF system: the only values of type
    {!Thm.t} that can be constructed are valid consequences of the
    logic's axioms. *)
module Thm : sig
  type t

  val pp : t Fmt.printer
  val concl : t -> Expr.t
  val hyps : t -> Expr.Set.t

  val view_l: t -> Expr.t * Expr.t list

  (** Creation of new terms *)

  val refl : Expr.t -> t
  (** [refl t] is [ |- t=t ] *)

  val assume : Expr.t -> t
  (** [assume F] is [F |- F] *)

  val cut : t -> t -> t
  (** [cut (F1 |- b) (F2, b |- c)] is [F1, F2 |- c] *)

  val cut_l : t list -> t -> t
  (** [multi_cut thm_l thm] does simultaneous cuts of the hypothesis
      of [thm] with the conclusions in [thm_l]. *)

  val instantiate : t -> Expr.subst -> t
  (** [instantiate thm σ] produces
      [ Fσ |- Gσ]  where [thm] is [F |- G] *)


  (* TODO: [cong_t]: [ f=g, a=b |- f a=g b] *)
  (* TODO: some connectives, like [a |- a=true], [a=true |- a],
     [~a |- a=false], [a=false |- ~a], [a, b |- a /\ b], [a |- a \/ b],
     [b |- a \/ b] *)

  val beta : Expr.t -> Expr.t -> t
  (** [beta (λx.u) a] is [ |- (λx.u) a = u[x:=a] ] *)

  val eq_leibniz : Expr.t -> Expr.t -> p:Expr.t -> t
  (** [leibniz a b P]: [a=b, P a |- P b], beta-normalized *)

  val cong_ax : t
  (** axiom [f=g, x=y |- f x=g y] *)

  val cong_fol : Expr.t -> Expr.t list -> Expr.t list -> t
  (** [cong f l1 l2] makes the congruence axiom for [∧l1=l2 ==> f l1=f2 l2] *)
end = struct
  type t = {
    concl: Expr.t;
    hyps: Expr.Set.t;
  }
  (* TODO: a bitfield to register where [beta], choice, excluded middle, etc.
     were used? *)

  let concl self = self.concl
  let hyps self = self.hyps
  let view_l self = self.concl, Expr.Set.elements self.hyps
  let pp out self =
    if Expr.Set.is_empty self.hyps then (
      Fmt.fprintf out "@[|- %a@]" Expr.pp_inner self.concl
    ) else (
      Fmt.fprintf out "@[%a@ |- %a@]"
        Fmt.(list ~sep:(return ",@ ") Expr.pp_inner) (Expr.Set.elements self.hyps)
        Expr.pp_inner self.concl
    )

  let make_ concl hyps : t = {concl; hyps}
  let make_l_ concl hyps : t = {concl; hyps=Expr.Set.of_list hyps}

  let assume t : t =
    if not (Expr.is_a_bool t) then (
      invalid_argf "assume: needs boolean term, not %a" Expr.pp t
    );
    make_ t (Expr.Set.singleton t)

  let refl t : t = make_ (Expr.eq t t) Expr.Set.empty

  let beta f t : t =
    match Expr.view f with
    | Expr.Lambda (v, body) when Expr.Var.has_ty v (Expr.ty_exn t) ->
      let concl =
        Expr.eq
          (Expr.app f t)
          (Expr.subst1 v t ~in_:body)
      in
      make_ concl Expr.Set.empty
    | _ ->
      invalid_argf "thm.beta: f must be a lambda,@ not %a" Expr.pp f

  let eq_leibniz a b ~p : t =
    if not Expr.(equal (ty_exn a) (ty_exn b)) then (
      invalid_argf "thm.eq_leibniz: %a and %a do not have the same type"
        Expr.pp a Expr.pp b
    );
    match Expr.view p with
    | Expr.Lambda (v, body) when Expr.Var.has_ty v (Expr.ty_exn a) ->
      let concl = Expr.subst1 v b ~in_:body in
      let hyps = [Expr.subst1 v a ~in_:body; Expr.eq a b] in
      make_l_ concl hyps
    | _ ->
      invalid_argf "thm.eq_leibniz: P must be a lambda,@ not %a" Expr.pp_inner p

  let cong_ax : t =
    let a = Expr.new_sym "α" Expr.type_ in
    let b = Expr.new_sym "β" Expr.type_ in
    let f = Expr.new_sym "f" Expr.(a @-> b) in
    let g = Expr.new_sym "g" Expr.(a @-> b) in
    let x = Expr.new_sym "x" a in
    let y = Expr.new_sym "y" a in
    make_l_ Expr.(eq (app f x) (app g y)) [Expr.eq f g; Expr.eq x y]

  let instantiate (t:t) (subst:Expr.subst) : t =
    let inst = Expr.Subst.apply subst in
    make_ (inst t.concl) (Expr.Set.map inst t.hyps)

  let cong_fol f l1 l2 : t =
    if List.length l1 <> List.length l2 then (
      invalid_arg "cong_f: incompatible length"
    );
    let app1 = Expr.app_l f l1 in
    let app2 = Expr.app_l f l2 in
    if not (Expr.equal (Expr.ty_exn app1) (Expr.ty_exn app2)) then (
      invalid_argf "cong: terms %a and %a have incompatible types"
        Expr.pp app1 Expr.pp app2
    );
    make_ (Expr.eq app1 app2)
      (List.map2 Expr.eq l1 l2 |> Expr.Set.of_list)

  (* TODO: remove refl hyps, using filter? *)

  let cut_l l b : t =
    let {concl=concl_b; hyps=hyps_b} = b in
    if List.for_all (fun a -> Expr.Set.mem a.concl hyps_b) l then (
      let hyps =
        List.fold_left (fun hyps a -> Expr.Set.remove a.concl hyps) hyps_b l
      in
      let hyps =
        List.fold_left (fun hyps a -> Expr.Set.union a.hyps hyps) hyps l
      in
      make_ concl_b hyps
    ) else (
  invalid_argf "cut: a conclusion in %a@ does not belong in hyps of %a"
    (Fmt.Dump.list pp) l pp b
    )

  let cut a b : t = cut_l [a] b
end
