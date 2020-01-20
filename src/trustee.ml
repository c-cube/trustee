
module Fmt = CCFormat

let pp_list ppx out l =
  Fmt.(list ~sep:(return "@ ") ppx) out l

let invalid_argf msg = Fmt.kasprintf invalid_arg msg

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

module Ty : sig
  type var = ID.t
  type t

  type view =
    | Arrow of t * t
    | App of ID.t * t list
    | Var of var

  val app : ID.t -> t list -> t
  val const : ID.t -> t
  val var : var -> t
  val arrow : t -> t -> t
  val arrow_l : t list -> t -> t

  val view : t -> view
  val equal : t -> t -> bool
  val hash : t -> int
  val pp : t Fmt.printer
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
end

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

module Expr : sig
  type t

  type view =
    | App of t * t
    | Lam of Var.t * t
    | Var of Var.t

  val view : t -> view
  val ty : t -> Ty.t

  val app : t -> t -> t
  val app_l : t -> t list -> t
  val var : Var.t -> t
  val lam : Var.t -> t -> t
  val lam_l : Var.t list -> t -> t
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
end
