
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

  val type_ : t
  val kind : t
  val bool : t
  val app : t -> t -> t
  val app_l : t -> t list -> t
  val arrow : t -> t -> t
  val arrow_l : t list -> t -> t
  val (@->) : t -> t -> t
  val new_var : string -> t -> t
  val var : var -> t
  val lambda : var -> t -> t
  val lambda_l : var list -> t -> t
  val pi : var -> t -> t
  val eq_const : t
  val eq : t -> t -> t

  val is_bool : t -> bool
  val is_a_type : t -> bool
  val is_a_bool : t -> bool

  module Set : Set.S with type elt = t
  module Tbl : Hashtbl.S with type key = t
end
= struct
  type t = {
    mutable id: int;
    view: view;
    mutable ty: t option; (* computed lazily; only kind has no type *)
  }
  and var_content = {
    v_name: ID.t;
    v_ty: t;
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

  let rec pp out t =
    match t.view with
    | Kind -> Fmt.string out "Kind"
    | Type -> Fmt.string out "Type"
    | Var v -> ID.pp out v.v_name
    | Lambda (a,b) -> Fmt.fprintf out "@[\\%a:%a.@ %a@]" pp a pp (ty_exn a) pp b
    | Pi (a,b) -> Fmt.fprintf out "@[@<1>Π%a:%a.@ %a@]" pp a pp (ty_exn a) pp b
    | Arrow (a,b) -> Fmt.fprintf out "@[%a@ -> %a@]" pp a pp b
    | App (a, b) -> Fmt.fprintf out "@[%a@ %a@]" pp a pp_inner b

  and pp_inner out t =
    match t.view with
    | Lambda _ | Arrow _ | Pi _ | App _ -> Fmt.fprintf out "(@[%a@])" pp t
    | Type | Kind | Var _ -> pp out t

  let var (v:var) : t = v
  let var' v : t = make_ (Var v) (fun () -> v.v_ty)
  let new_var (s:string) (ty:t) : t =
    make_ (Var {v_name=ID.make s; v_ty=ty}) (fun () -> ty)

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
        subst a_v b ~in_:a_body
      | _ ->
        invalid_argf "@[type mismatch:@ cannot apply @[%a@ : %a@]@ to %a@]" pp a pp (ty_exn a) pp b
    in
    make_ (App (a,b)) get_ty

  (* substitution of [x] with [by] *)
  and subst (x:var) by ~in_ : t =
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
    new_var "=" ty

  let eq a b : t = app_l eq_const [ty_exn a; a; b]

  let is_a_type t : bool = match t.ty with
    | Some ty -> equal ty type_
    | None -> false
  let is_bool = equal bool
  let is_a_bool t = match t.ty with Some b -> is_bool b | None -> false

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
  val concl : t -> Expr.t
  val hyps : t -> Expr.Set.t

  (** Creation of new terms *)

  val refl : Expr.t -> t
  (** [refl t] is [ |- t=t ] *)

  val assume : Expr.t -> t
  (** [assume F] is [F |- F] *)

  val cut : t -> t -> t
  (** [cut (F1 |- b) (F2, b |- c)] is [F1, F2 |- c] *)

  (* TODO: [multi_cut thm_l thm], like cut but does _parallel_ resolution.
     same conclusion as [thm]. *)
  (* TODO: [cong_t]: [ f=g, a=b |- f a=g b] *)
  (* TODO: [inst σ thm]: [ Fσ |- Gσ]  where [thm] is [F |- G] *)
  (* TODO: [beta (λx.u) a]: [ |- (λx.u) a = u[x:=a] ] *)
  (* TODO: [leibniz a b P]: [a=b, P a |- P b], beta-normalized *)
  (* TODO: some connectives, like [a |- a=true], [a=true |- a],
     [~a |- a=false], [a=false |- ~a], [a, b |- a /\ b], [a |- a \/ b],
     [b |- a \/ b] *)

  val cong : Expr.t -> Expr.t list -> Expr.t list -> t
  (** [cong f l1 l2] makes the congruence axiom for [∧l1=l2 ==> f l1=f2 l2] *)
end = struct
  type t = {
    concl: Expr.t;
    hyps: Expr.Set.t;
  }

  let concl self = self.concl
  let hyps self = self.hyps
  let pp out self =
    if Expr.Set.is_empty self.hyps then (
      Fmt.fprintf out "@[|- %a@]" Expr.pp self.concl
    ) else (
      Fmt.fprintf out "@[%a@ |- %a@]"
        Fmt.(list ~sep:(return ",@ ") Expr.pp) (Expr.Set.elements self.hyps) Expr.pp self.concl
    )

  let make_ concl hyps : t = {concl; hyps}

  let assume t : t =
    if not (Expr.is_a_bool t) then (
      invalid_argf "assume: needs boolean term, not %a" Expr.pp t
    );
    make_ t (Expr.Set.singleton t)

  let refl t : t = make_ (Expr.eq t t) Expr.Set.empty

  let cong f l1 l2 : t =
    if List.length l1 <> List.length l2 then (
      invalid_arg "cong: incompatible length"
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

  let cut a b : t =
    let {concl=concl_b; hyps=hyps_b} = b in
    if Expr.Set.mem (concl a) hyps_b then (
      let new_hyps =
        Expr.Set.union (hyps a) (Expr.Set.remove (concl a) hyps_b)
      in
      make_ concl_b new_hyps
    ) else (
      invalid_argf "mp: %a@ does not belong in hyps of %a" Expr.pp (concl a) pp b
    )
end
