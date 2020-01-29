
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
  module Map : Map.S with type key = t
end = struct
  type t = {name: string; id: int}

  let equal r1 r2 = CCInt.equal r1.id r2.id
  let compare r1 r2 = CCInt.compare r1.id r2.id
  let hash {name;id} = CCHash.(combine3 10 (string name)(int id))

  let pp out {name;id=_} = Fmt.string out name

  let make =
    let n = ref 0 in
    fun name ->
      incr n;
      {name; id= !n}


  module As_key = struct type nonrec t=t let compare=compare end
  module Map = Map.Make(As_key)
end

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
      | Error f -> Some (Fmt.asprintf "@[<1>@{<Red>Error@}:@ %a@]" f ())
      | _ -> None)

(** {2 Exprs}

    Logical expressions, types, and formulas. *)
module Expr
  : sig
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
  val new_var : string -> t -> var
  val new_var' : string -> t -> t
  val var : var -> t
  val lambda : var -> t -> t
  val lambda_l : var list -> t -> t
  val pi : var -> t -> t

  val true_ : t
  val false_ : t
  val eq_const : t
  val imply_const : t
  val and_const : t
  val or_const : t
  val not_const : t

  val eq : t -> t -> t
  val imply : t -> t -> t
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

  val as_var_exn : t -> var
  (** [as_var_exn v] is the variable [v].
      @raise Error if the term is not a variable. *)

  val unfold_eq_exn : t -> t * t
  (** [unfold_eq_exn (= a b)] is [(a,b)].
      @raise Error if the term is not an equality. *)

  val unfold_lambda_exn : t -> var * t
  (** [unfold_lambda_exn (λx. t)] is [(x,t)].
      @raise Error if the term is not a lambda. *)

  type term = t

  module Var : sig
    type t = var

    val equal : t -> t -> bool

    val ty : var -> term

    val pp : t Fmt.printer

    val has_ty : var -> term -> bool
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
= struct
  type display = Normal | Infix
  type t = {
    mutable id: int;
    view: view;
    mutable ty: t option; (* computed lazily; only kind has no type *)
  }
  and var_content = {
    v_name: string;
    v_ty: t;
  }
  and const_content = {
    c_name: ID.t;
    c_ty: t;
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
  let var_eq v1 v2 = String.equal v1.v_name v2.v_name && equal v1.v_ty v2.v_ty
  let var_hash v = CCHash.(combine2 (string v.v_name) (hash v.v_ty))

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
    | Const c -> ID.pp out c.c_name
    | Var v -> Fmt.string out v.v_name
    | Lambda (a,b) -> Fmt.fprintf out "(@[\\%a:%a.@ %a@])" pp a pp (ty_exn a) pp b
    | Pi (a,b) -> Fmt.fprintf out "@[@<1>Π%a:%a.@ %a@]" pp a pp (ty_exn a) pp b
    | Arrow (a,b) -> Fmt.fprintf out "@[%a@ -> %a@]" pp a pp b
    | App _ ->
      let f, args = unfold_app t in
      assert (args<>[]);
      begin match f.view, args with
        | Const {c_display=Infix; c_name; _}, [a;b] ->
          Fmt.fprintf out "@[%a@ %a %a@]" pp_inner a ID.pp c_name pp_inner b
        | Const {c_display=Infix; c_name; _}, _::_::_ ->
          (* display [= u a b] as [a `= u` b] *)
          let ifx_args, args = CCList.take_drop (List.length args-2) args in
          begin match ifx_args, args with
            | [u], [a;b] ->
              Fmt.fprintf out "@[%a@ @[%a_%a@] %a@]"
                pp_inner a ID.pp c_name pp_inner u pp_inner b
            | _, [a;b] ->
              Fmt.fprintf out "@[%a@ `@[%a@ %a@]` %a@]"
                pp_inner a ID.pp c_name (pp_list pp_inner) ifx_args pp_inner b
            | _ -> assert false
          end
        | _ ->
          Fmt.fprintf out "@[%a@ %a@]" pp f (pp_list pp_inner) args
      end

  and pp_inner out t =
    match t.view with
    | Arrow _ | Pi _ | App _ -> Fmt.fprintf out "(@[%a@])" pp t
    | Lambda _ | Type | Kind | Var _ | Const _ -> pp out t

  let var (v:var) : t = v
  let var' v : t = make_ (Var v) (fun () -> v.v_ty)
  let new_const_ display s ty : t =
    make_ (Const {c_name=ID.make s; c_ty=ty; c_display=display})
      (fun () ->
         (* TODO: assert that the type is closed *)
         ty)
  let new_const = new_const_ Normal
  let new_var s ty : t = make_ (Var {v_name=s; v_ty=ty; }) (fun () -> ty)
  let new_var' = new_var

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
        errorf_
          (fun k->k "@[type mismatch:@ cannot apply @[%a@ : %a@]@ to @[%a : %a@]@]"
             pp_inner a pp_inner (ty_exn a) pp_inner b pp_inner (ty_exn b))
    in
    make_ (App (a,b)) get_ty

  (* substitution of [x] with [by] *)
  and subst1 (x:var) by ~in_ : t =
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

  let app_l f l = List.fold_left app f l

  let eq_const : t =
    let a = new_var "α" type_ in
    let ty = pi a (a @-> a @-> bool) in
    new_const_ Infix "=" ty

  let true_ = new_var "true" bool
  let false_ = new_var "false" bool
  let imply_const : t = new_const_ Infix "==>" (bool @-> bool @-> bool)
  let and_const : t = new_const_ Infix "/\\" (bool @-> bool @-> bool)
  let or_const : t = new_const_ Infix "\\/" (bool @-> bool @-> bool)
  let not_const : t = new_var "~" (bool @-> bool)

  let eq a b : t = app_l eq_const [ty_exn a; a; b]
  let imply a b : t = app_l imply_const [a;b]
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

  let unfold_lambda_exn t = match t.view with
    | Lambda (x, u) -> x, u
    | _ -> errorf_ (fun k->k"%a is not a lambda" pp t)

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
    let equal = equal
    let has_ty v t = equal (ty v) t

    module Set = Set
    module Tbl = Tbl
    module Map = Map
  end

  module Subst = struct
    type t = term Map.t
    let empty : t = Map.empty
    let add (v:var) t self : t =
      assert (is_var v);
      Map.add v t self

    let find_exn self v = Map.find v self
    let find self v = try Some (find_exn self v) with Not_found -> None
    let to_list self = Map.fold (fun v t l -> (v,t) :: l) self []
    let iter = Map.iter

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
            | Type | Kind | Const _ -> t
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
          Tbl.add tbl t u;
          u
      and rebind_ (v:var) : var =
        match v.view with
        | Var vi ->
          let v' = var' {vi with v_ty = aux vi.v_ty} in
          Tbl.add tbl v v';
          v'
        | _ -> assert false
      in
      aux
  end
  type subst = Subst.t
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
  val hyps : t -> Expr.Set.t
  val dep_on_axioms : t -> axiom iter

  val view_l: t -> Expr.t * Expr.t list * axiom iter

  (** Creation of new terms *)

  val refl : Expr.t -> t
  (** [refl t] is [ |- t=t ] *)

  val assume : Expr.t -> t
  (** [assume F] is [F |- F] *)

  val trans : t -> t -> t
  (** [trans (F1 |- a=b) (F2 |- b=c)] is [F1, F2 |- a=c] *)

  val cong : t -> t -> t
  (** [cong (F1 |- f=g) (F2 |- t=u)] is [F1, F2 |- f t=g u] *)

  val abs : Expr.var -> t -> t
  (** [abs x (F |- t=u)] is [F |- (λx.t)=(λx.u)] *)

  val cut : t -> t -> t
  (** [cut (F1 |- b) (F2, b |- c)] is [F1, F2 |- c] *)

  val mp : t -> t -> t
  (** [mp (F1 |- a) (F2 |- a ==> b)] is [F1, F2 |- b] *)

  val bool_eq : t -> t -> t
  (** [bool_eq (F1 |- a=b) (F2 |- a)] is [F1, F2 |- b].
      This is the boolean equivalent of transitivity. *)

  val bool_eq_intro : t -> t -> t
  (** [bool_eq_intro (F1, a |- b) (F2, b |- a) is [F1, F2 |- a=b].
      This is a way of building a boolean [a=b] from proofs of [a==>b] and [b==>a].
      *)

  val instantiate : t -> Expr.subst -> t
  (** [instantiate thm σ] produces
      [ Fσ |- Gσ]  where [thm] is [F |- G] *)

  (* TODO: some connectives, like [a |- a=true], [a=true |- a],
     [~a |- a=false], [a=false |- ~a], [a, b |- a /\ b], [a |- a \/ b],
     [b |- a \/ b] *)

  val beta : Expr.t -> Expr.t -> t * Expr.t
  (** [beta (λx.u) a] is [ |- (λx.u) a = u[x:=a] ].
      [u[x:=a]] is returned along. *)

  val axiom : string -> Expr.t list -> Expr.t -> t * axiom
  (** Create a new axiom [assumptions |- concl] with the given name.
      The axiom is tracked in all theorems that use it, see {!dep_on_axioms}.
      {b use with caution} *)
end = struct
  type t = {
    concl: Expr.t;
    hyps: Expr.Set.t;
    dep_on_axioms: axiom ID.Map.t lazy_t; (* axioms this depends on *)
  }
  and axiom = {
    ax_name: ID.t;
    ax_thm: t;
  }
  (* TODO: a bitfield to register where [beta], choice, excluded middle, etc.
     were used? *)

  let _deps self k = ID.Map.iter (fun _ ax -> k ax) (Lazy.force self.dep_on_axioms)
  let concl self = self.concl
  let hyps self = self.hyps
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
  let make_l_ concl hyps dep_on_axioms : t =
    make_ concl (Expr.Set.of_list hyps) dep_on_axioms

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
      errorf_ (fun k->k "thm.beta: f must be a lambda,@ not %a" Expr.pp f)

  let abs x (th:t) : t =
    try
      let t, u = Expr.unfold_eq_exn th.concl in
      make_
        (Expr.eq (Expr.lambda x t) (Expr.lambda x u))
        th.hyps th.dep_on_axioms
    with Error msg ->
      error_wrapf_ msg (fun k->k"in @[abs %a@ %a@]" Expr.Var.pp x pp th)

  let mp t1 t2 =
    match Expr.unfold_app t2.concl with
    | f, [a;b] when Expr.equal Expr.imply_const f ->
      if not (Expr.equal a t1.concl) then (
        errorf_ (fun k->k "mp: LHS of implication in %a@ does not match" pp t2)
      );
      make_ b (Expr.Set.union t1.hyps t2.hyps)
        (merge_ax_ t1.dep_on_axioms t2.dep_on_axioms)
    | _ ->
      errorf_ (fun k->k "mp: thm %a@ should have an implication as conclusion" pp t2)

  let bool_eq th1 th2 : t =
    try
      let a, b = Expr.unfold_eq_exn th1.concl in
      err_unless_bool_ "bool_eq" a;
      err_unless_bool_ "bool_eq" b;
      if not (Expr.equal a th2.concl) then (
        errorf_ (fun k->k "conclusion of %a does not match LHS of %a" pp th2 pp th1);
      );
      make_ b (Expr.Set.union th1.hyps th2.hyps)
        (merge_ax_ th1.dep_on_axioms th2.dep_on_axioms)
    with Error msg ->
      error_wrapf_ msg (fun k->k"bool-eq %a %a" pp th1 pp th2)

  let bool_eq_intro th1 th2 : t =
    make_ (Expr.eq th1.concl th2.concl)
      Expr.Set.(union (remove th1.concl th2.hyps) (remove th2.concl th1.hyps))
      (merge_ax_ th1.dep_on_axioms th2.dep_on_axioms)

  let trans t1 t2 =
    match Expr.unfold_app t1.concl, Expr.unfold_app t2.concl with
    | (f1, [_;a1;b1]), (f2, [_;a2;b2])
      when Expr.equal Expr.eq_const f1 && Expr.equal Expr.eq_const f2 ->
      if not (Expr.equal b1 a2) then (
        errorf_
          (fun k->k "trans: %a and %a do not match" Expr.pp b1 Expr.pp a2)
      );
      make_ (Expr.eq a1 b2) (Expr.Set.union t1.hyps t2.hyps)
        (merge_ax_ t1.dep_on_axioms t2.dep_on_axioms)
    | _ ->
      errorf_ (fun k->k"trans: invalid args %a@ and %a" pp t1 pp t2)

  let cong th1 th2 : t =
    try
      let f, g = Expr.unfold_eq_exn th1.concl in
      let t, u = Expr.unfold_eq_exn th2.concl in
      make_
        (Expr.eq (Expr.app f t) (Expr.app g u))
        (Expr.Set.union th1.hyps th2.hyps)
        (merge_ax_ th1.dep_on_axioms th2.dep_on_axioms)
    with Error f ->
      error_wrapf_ f (fun k->k "in (@[cong@ %a@ %a@])" pp th1 pp th2)

  let instantiate (t:t) (subst:Expr.subst) : t =
    let inst = Expr.Subst.apply subst in
    make_ (inst t.concl) (Expr.Set.map inst t.hyps) t.dep_on_axioms

  let cut a b : t =
    let {concl=concl_b; hyps=hyps_b; dep_on_axioms=_} = b in
    if Expr.Set.mem a.concl hyps_b then (
      let hyps = Expr.Set.remove a.concl hyps_b in
      let hyps = Expr.Set.union a.hyps hyps in
      make_ concl_b hyps (merge_ax_ a.dep_on_axioms b.dep_on_axioms)
    ) else (
      errorf_
        (fun k->k "cut: conclusion of %a@ does not belong in hyps of %a"
            pp a pp b)
    )

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
