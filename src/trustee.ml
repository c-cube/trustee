
module Fmt = CCFormat

let pp_list ppx out l =
  Fmt.(list ~sep:(return "@ ") ppx) out l

let invalid_argf msg = Fmt.kasprintf invalid_arg msg

(** {2 Identifiers}

    Identifiers represent a given logic symbols. A handful are predefined,
    the other ones are introduced by the user or the problem to check. *)
module ID : sig
  type t

  type builtin =
    | Eq | Not | And | Or | Imply | Bool

  type view =
    | Builtin of builtin
    | Named of {name: string; id: int}

  val make : string -> t

  val equal : t -> t -> bool
  val hash : t -> int
  val pp : t Fmt.printer

  val eq : t
  val not_ : t
  val and_ : t
  val or_ : t
  val imply : t
  val bool : t
end = struct
  type builtin =
    | Eq | Not | And | Or | Imply | Bool

  type view =
    | Builtin of builtin
    | Named of {name: string; id: int}

  type t = view

  let equal a b =
    match a, b with
    | Builtin a, Builtin b -> a=b
    | Named r1, Named r2 -> r1.id = r2.id && String.equal r1.name r2.name
    | (Builtin _ | Named _), _ -> false

  let hash = function
    | Named {name;id} -> CCHash.(combine3 10 (string name)(int id))
    | Builtin b -> CCHash.(combine2 20 (poly b))

  let str_of_builtin = function
    | Eq -> "=" | Not -> "~" | And -> "/\\" | Or -> "\\/"
    | Imply -> "==>" | Bool -> "Bool"

  let pp out = function
    | Builtin b -> Fmt.string out (str_of_builtin b)
    | Named {name;id=_} -> Fmt.string out name

  let make =
    let n = ref 0 in
    fun name ->
      incr n;
      Named {name; id= !n}

  let eq = Builtin Eq
  let not_ = Builtin Not
  let and_ = Builtin And
  let or_ = Builtin Or
  let imply = Builtin Imply
  let bool = Builtin Bool
end

(** {2 Types}

    Polymorphic types. *)
module Ty : sig
  type var = ID.t
  type t

  type view =
    | Arrow of t * t
    | App of ID.t * t list
    | Var of var

  val bool : t
  val app : ID.t -> t list -> t
  val const : ID.t -> t
  val var : var -> t
  val arrow : t -> t -> t
  val arrow_l : t list -> t -> t
  val (@->) : t -> t -> t

  val view : t -> view
  val equal : t -> t -> bool
  val hash : t -> int
  val pp : t Fmt.printer

  val is_bool : t -> bool
end = struct
  type var = ID.t

  type t = {
    view: view;
    mutable id: int;
  }

  and view =
    | Arrow of t * t
    | App of ID.t * t list
    | Var of var

  let equal a b = a.id = b.id
  let hash a = CCHash.int a.id
  let view a = a.view

  let rec pp out ty =
    match ty.view with
    | Var v -> ID.pp out v
    | Arrow (a,b) -> Fmt.fprintf out "@[%a@ -> %a@]" pp_inner a pp b
    | App (c, []) -> ID.pp out c
    | App (c, l) -> Fmt.fprintf out "(@[%a@ %a@])" ID.pp c (pp_list pp_inner) l

  and pp_inner out ty =
    match ty.view with
    | Arrow _ -> Fmt.fprintf out "(@[%a@])" pp ty
    | _ -> pp out ty

  module H = Hashcons.Make(struct
      type nonrec t = t
      let equal a b =
        match a.view, b.view with
        | Arrow (a1,a2), Arrow (b1,b2) -> equal a1 b1 && equal a2 b2
        | Var v1, Var v2 -> ID.equal v1 v2
        | App (c1,l1), App (c2,l2) -> ID.equal c1 c2 && CCList.equal equal l1 l2
        | (Arrow _ | App _ | Var _), _ -> false

      let hash ty = match ty.view with
        | Var v -> CCHash.(combine2 10 (ID.hash v))
        | App (c, l) -> CCHash.(combine3 20 (ID.hash c) (list hash l))
        | Arrow (a, b) -> CCHash.(combine3 30 (hash a) (hash b))

      let set_id ty id = assert (ty.id = -1); ty.id <- id
    end)

  let make_ view = H.hashcons {view; id= -1}

  let arrow a b : t = make_ (Arrow (a,b))
  let arrow_l l ret : t = List.fold_right arrow l ret
  let app c l : t = make_ (App (c, l))
  let const c : t = app c []
  let var v : t = make_ (Var v)
  let bool : t = const ID.bool
  let (@->) = arrow

  let is_bool ty = equal bool ty
end

(** {2 Typed Variables}

    A variable is a typed identifier. It can represent bound variables or
    defined/axiomatized constants. *)
module Var : sig
  type t = private {name: ID.t; ty: Ty.t}

  val name : t -> ID.t
  val ty : t -> Ty.t
  val make : ID.t -> Ty.t -> t
  val equal : t -> t -> bool
  val hash : t -> int
  val pp : t Fmt.printer
end = struct
  type t = {name: ID.t; ty: Ty.t}
  let name v = v.name
  let ty v = v.ty
  let make name ty : t = {name;ty}
  let equal v1 v2 = ID.equal v1.name v2.name && Ty.equal v1.ty v2.ty
  let hash v = CCHash.combine3 42 (ID.hash v.name) (Ty.hash v.ty)
  let pp out v = Fmt.fprintf out "(@[%a : %a@])" ID.pp v.name Ty.pp v.ty
end

(** {2 Terms}

    Logical expressions and formulas. *)
module Term : sig
  type t

  type view =
    | App of t * t
    | Lam of Var.t * t
    | Var of Var.t

  val view : t -> view
  val ty : t -> Ty.t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t Fmt.printer

  val app : t -> t -> t
  val app_l : t -> t list -> t
  val var : Var.t -> t
  val lam : Var.t -> t -> t
  val lam_l : Var.t list -> t -> t
  val eq_const : Ty.t -> t
  val eq : t -> t -> t

  module Set : Set.S with type elt = t
  module Tbl : Hashtbl.S with type key = t
end = struct
  type t = {
    mutable id: int;
    view: view;
    ty: Ty.t;
  }

  and view =
    | App of t * t
    | Lam of Var.t * t
    | Var of Var.t

  let equal a b = a.id = b.id
  let hash a = CCHash.int a.id
  let view t = t.view
  let ty t = t.ty
  let compare a b = CCInt.compare a.id b.id

  let rec pp out t =
    match t.view with
    | Var v -> Var.pp out v
    | Lam (a,b) -> Fmt.fprintf out "@[\\%a.@ %a@]" Var.pp a pp b
    | App (a, b) -> Fmt.fprintf out "%a@ %a" pp a pp_inner b

  and pp_inner out t =
    match t.view with
    | Lam _ | App _ -> Fmt.fprintf out "(@[%a@])" pp t
    | _ -> pp out t

  module H = Hashcons.Make(struct
      type nonrec t = t
      let equal a b =
        match a.view, b.view with
        | Lam (a1,a2), Lam (b1,b2) -> Var.equal a1 b1 && equal a2 b2
        | Var v1, Var v2 -> Var.equal v1 v2
        | App (a1,b1), App (a2,b2) -> equal a1 a2 && equal b1 b2
        | (Lam _ | App _ | Var _), _ -> false

      let hash ty = match ty.view with
        | Var v -> CCHash.(combine2 10 (Var.hash v))
        | App (a, b) -> CCHash.(combine3 20 (hash a) (hash b))
        | Lam (a, b) -> CCHash.(combine3 30 (Var.hash a) (hash b))

      let set_id ty id = assert (ty.id = -1); ty.id <- id
    end)

  let make_ view ty = H.hashcons {view; id= -1; ty}

  let app a b : t =
    let ty = match Ty.view a.ty with
      | Ty.Arrow (a1,a2) when Ty.equal a1 b.ty -> a2
      | _ -> invalid_argf "@[type mismatch:@ cannot apply %a@ to %a@]" pp a pp b
    in
    make_ (App (a,b)) ty

  let var v : t = make_ (Var v) (Var.ty v)
  let lam v body : t = make_ (Lam (v,body)) (Ty.arrow (Var.ty v) (ty body))
  let lam_l vs body : t = List.fold_right lam vs body
  let app_l f l = List.fold_left app f l

  let eq_const ty : t = var (Var.make ID.eq Ty.(ty @-> ty @-> bool))
  let eq a b : t =
    if not (Ty.equal a.ty b.ty) then (
      invalid_argf "cannot build equality between %a@ and %a: incompatible types" pp a pp b
    );
    app (app (eq_const a.ty) a) b

  module As_key = struct
    type nonrec t = t
    let equal = equal
    let hash = hash
    let compare=compare
  end
  module Set = Set.Make(As_key)
  module Tbl = Hashtbl.Make(As_key)
end


(** {2 Theorems}

    Here lies the core of the LCF system: the only values of type
    {!Thm.t} that can be constructed are valid consequences of the
    logic's axioms. *)
module Thm : sig
  type t

  val pp : t Fmt.printer
  val concl : t -> Term.t
  val hyps : t -> Term.Set.t

  (** Creation of new terms *)

  val refl : Term.t -> t
  (** [refl t] is [ |- t=t ] *)

  val assume : Term.t -> t
  (** [assume F] is [F |- F] *)

  val mp : t -> t -> t
  (** [mp (F1, a |- b) (F2, b |- c)] is [F1, F2, a |- c] *)

  val cong : Term.t -> Term.t list -> Term.t list -> t
  (** [cong f l1 l2] makes the congruence axiom for [∧l1=l2 ==> f l1=f2 l2] *)
end = struct
  type t = {
    concl: Term.t;
    hyps: Term.Set.t;
  }

  let concl self = self.concl
  let hyps self = self.hyps
  let pp out self =
    if Term.Set.is_empty self.hyps then (
      Fmt.fprintf out "@[|- %a@]" Term.pp self.concl
    ) else (
      Fmt.fprintf out "@[%a@ |- %a@]"
        Fmt.(list ~sep:(return ",@ ") Term.pp) (Term.Set.elements self.hyps) Term.pp self.concl
    )

  let make_ concl hyps : t = {concl; hyps}

  let assume t : t =
    if not (Ty.is_bool @@ Term.ty t) then (
      invalid_argf "assume: needs boolean term, not %a" Term.pp t
    );
    make_ t (Term.Set.singleton t)

  let refl t : t = make_ (Term.eq t t) Term.Set.empty

  let cong f l1 l2 : t =
    if List.length l1 <> List.length l2 then (
      invalid_arg "cong: incompatible length"
    );
    let app1 = Term.app_l f l1 in
    let app2 = Term.app_l f l2 in
    if not (Ty.equal (Term.ty app1) (Term.ty app2)) then (
      invalid_argf "cong: terms %a and %a have incompatible types"
        Term.pp app1 Term.pp app2
    );
    make_ (Term.eq app1 app2)
      (List.map2 Term.eq l1 l2 |> Term.Set.of_list)

  (* TODO: remove refl hyps, using filter? *)

  let mp a b : t =
    let {concl=concl_b; hyps=hyps_b} = b in
    if Term.Set.mem (concl a) hyps_b then (
      let new_hyps =
        Term.Set.union (hyps a) (Term.Set.remove (concl a) hyps_b)
      in
      make_ concl_b new_hyps
    ) else (
      invalid_argf "mp: %a@ does not belong in hyps of %a" Term.pp (concl a) pp b
    )
end
