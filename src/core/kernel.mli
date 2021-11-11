
(** {1 Kernel of trust} *)

open Sigs

type ctx
type expr
type ty = expr
type const
type ty_const = const
type thm
type theory

type location = Loc.t

type var = {
  v_name: string;
  v_ty: ty;
}
type ty_var = var

type bvar = {
  bv_idx: int;
  bv_ty: ty;
}

type expr_view =
  | E_kind
  | E_type
  | E_var of var
  | E_bound_var of bvar
  | E_const of const * expr list
  | E_app of expr * expr
  | E_lam of string * expr * expr
  | E_arrow of expr * expr

module Name : sig
  type t
  val equal_str : t -> string -> bool
  include Sigs.EQ with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.HASH with type t := t
  include Sigs.PP with type t := t
end

module Const : sig
  type t = const
  include Sigs.EQ with type t := t
  include PP with type t := t

  val def_loc : t -> location option

  type args =
    | C_ty_vars of ty_var list
    | C_arity of int

  val name : t -> Name.t
  val args : t -> args
  val ty : t -> ty

  val pp_args : args Fmt.printer
  val pp_with_ty : t Fmt.printer

  val eq : ctx -> t
  val bool : ctx -> t
  val select : ctx -> t
  (** Choice constant *)

  val is_eq_to_bool : t -> bool
  val is_eq_to_eq : t -> bool
end

(** {2 Free Variables} *)
module Var : sig
  type t = var

  val name : t -> string
  val ty : t -> ty
  val make : string -> ty -> t
  val makef : ('a, Format.formatter, unit, t) format4 -> ty -> 'a
  val map_ty : t -> f:(ty -> ty) -> t

  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.PP with type t := t
  val pp_with_ty : t Fmt.printer

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end

(** Bound variables *)
module BVar : sig
  type t = bvar
  val make : int -> ty -> t
  include Sigs.PP with type t := t
end

(** Substitutions *)
module Subst : sig
  type t
  include Sigs.PP with type t := t
  val find_exn : var -> t -> expr
  val empty : t
  val is_empty : t -> bool
  val is_renaming : t -> bool
  val mem : var -> t -> bool
  val bind : t -> var -> expr -> t
  val bind' : var -> expr -> t -> t
  val size : t -> int
  val to_iter : t -> (var * expr) Iter.t
  val of_list : (var * expr) list -> t
  val of_iter : (var * expr) Iter.t -> t
end

(** {2 Expressions and Types} *)

(** Expression API.

    This module type is parametrized by a ['a with_ctx] type
    which is typically either [ctx -> 'a] (when the context is explicit)
    or just ['a] (when the context is in scope). Intuitively ['a with_ctx]
    is just how we express that a function depends on the context. *)
module type EXPR = sig
  type t = expr

  type view = expr_view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const * t list
    | E_app of t * t
    | E_lam of string * expr * expr
    | E_arrow of expr * expr

  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.PP with type t := t

  val pp_depth : max_depth:int -> t Fmt.printer
  (** Print the term and insert ellipsis in subterms above given depth.
      Useful to print very deep terms *)

  val view : t -> view
  val ty : t -> ty option
  val ty_exn : t -> ty
  val is_closed : t -> bool
  val is_eq_to_type : t -> bool
  val is_eq_to_bool : t -> bool
  val is_a_bool : t -> bool
  val is_a_type : t -> bool
  (** Is the type of [e] equal to [Type]? *)

  val iter : f:(bool -> t -> unit) -> t -> unit
  (** [iter ~f e] calls [f] on immediate subterms of [e].
      It calls [f true u] if [u] is an immediate subterm under a binder,
      and [f false u] otherwise. *)

  val exists : f:(bool -> t -> bool) -> t -> bool
  val for_all : f:(bool -> t -> bool) -> t -> bool

  val contains : t -> sub:t -> bool
  val free_vars : ?init:Var.Set.t -> t -> Var.Set.t
  val free_vars_iter : t -> var Iter.t

  val unfold_app : t -> t * t list
  val unfold_eq : t -> (t * t) option
  val unfold_arrow : t -> t list * t

  val return_ty : t -> t
  val as_const : t -> (Const.t * ty list) option
  val as_const_exn : t -> Const.t * ty list

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t

  val iter_dag : f:(t -> unit) -> t -> unit
  (** [iter_dag ~f e] calls [f] once on each unique subterm of [e]. *)

  type 'a with_ctx

  val subst : (recursive:bool -> t -> Subst.t -> t) with_ctx

  val type_ : t with_ctx
  val bool : t with_ctx
  val eq : (ty -> t) with_ctx
  val select : (ty -> t) with_ctx
  val var : (var -> t) with_ctx
  val const : (const -> ty list -> t) with_ctx
  val new_const : (?def_loc:location -> string -> ty_var list -> ty -> const) with_ctx
  val new_ty_const : (?def_loc:location -> string -> int -> const) with_ctx
  val var_name : (string -> ty -> t) with_ctx
  val bvar : (int -> ty -> t) with_ctx
  val app : (t -> t -> t) with_ctx
  val app_l : (t -> t list -> t) with_ctx
  val app_eq : (t -> t -> t) with_ctx
  val lambda : (var -> t -> t) with_ctx
  val lambda_l : (var list -> t -> t) with_ctx
  val lambda_db : (name:string -> ty_v:ty -> t -> t) with_ctx
  val arrow : (t -> t -> t) with_ctx
  val arrow_l : (t list -> t -> t) with_ctx

  val map : (f:(bool -> t -> t) -> t -> t) with_ctx

  val db_shift: (t -> int -> t) with_ctx

  val open_lambda : (t -> (var * t) option) with_ctx
  (** [open_lambda (\x. t)] introduces a new free variable [y],
      and returns [Some (y, t[x := y])]. Otherwise it returns [None] *)

  val open_lambda_exn : (t -> var * t) with_ctx
  (** Unsafe version of {!open_lambda}.
      @raise Error.Error if the term is not a lambda. *)
end

(** Explicit expression API with context *)
module Expr : EXPR with type 'a with_ctx := (ctx -> 'a)

(** Expression API where context is implicit *)
module type EXPR_FOR_CTX = EXPR
  with type 'a with_ctx := 'a
   and module Tbl = Expr.Tbl
     and module Set = Expr.Set
     and module Map = Expr.Map

(** Expression module where the context is implicit *)
val make_expr : ctx -> (module EXPR_FOR_CTX)

(** {2 Toplevel goals} *)

(** Goals

    A goal is simply a conjecture that does not have been proved yet.
    It might therefore be invalid. *)
module Goal : sig
  type t = private {
    hyps: Expr.Set.t;
    concl: Expr.t;
  }

  val make : Expr.Set.t -> Expr.t -> t
  val make_l : Expr.t list -> Expr.t -> t
  val make_nohyps : Expr.t -> t

  val concl : t -> Expr.t
  val hyps : t -> Expr.Set.t
  val hyps_iter : t -> Expr.t iter

  include Sigs.PP with type t := t
end

(** Data returned by a new type definition *)
module New_ty_def : sig
  type t = {
    tau: ty_const;
    (** The new type constructor *)

    fvars: var list;
    (** List of type variables *)

    c_abs: const;
    (** Function from the general type to `tau` *)

    c_repr: const;
    (** Function from `tau` back to the general type *)

    abs_thm: thm;
    (** `abs_thm` is `|- abs (repr x) = x` *)

    abs_x: var;
    (** Variable used in [abs_thm] *)

    repr_thm: thm;
    (** `repr_thm` is `|- Phi x <=> repr (abs x) = x` *)

    repr_x: var;
    (** Variable used in [repr_thm] *)
  }
end

(** {2 Theorems and Deduction Rules}

    The API to build theorems ensure that only valid theorems are produced,
    following the LCF tradition. *)

(** Theorem API.

    This module type is parametrized by a ['a with_ctx] type
    which is typically either [ctx -> 'a] (when the context is explicit)
    or just ['a] (when the context is in scope). Intuitively ['a with_ctx]
    is just how we express that a function depends on the context. *)
module type THM = sig
  type t = thm

  include Sigs.PP with type t := t
  val pp_quoted : t Fmt.printer

  val concl : t -> expr

  val hyps_iter : t -> expr iter

  val hyps_l : t -> expr list

  val hyps_sorted_l : t -> expr list
  (** List of hypothesis of this theorem, sorted, and deduplicated. *)
  
  val n_hyps : t -> int
  (** Number of hypothesis of this theorem *)

  val has_hyps : t -> bool
  (** Does this theorem have any hypothesis? Similar to [n_hyps th > 0]
      but faster *)

  (* TODO: store proofs optionally *)

  val is_proof_of : t -> Goal.t -> bool
  (** Is this theorem a proof of the given goal? *)

  type 'a with_ctx
  (** How is the {!ctx} passed to the functions? *)

  (** {3 Deduction rules} *)

  val assume : (expr -> t) with_ctx
  (** `assume e` returns `e |- e`. *)

  val axiom : (expr list -> expr -> t) with_ctx
  (** `axiom hyps e` is `hyps |- e`. Fails if [pledge_no_more_axioms] was called *)

  val cut : (t -> t -> t) with_ctx
  (** `cut (F1 |- b) (F2, b |- c)` is `F1, F2 |- c`.
      Fails if `b` does not occur {b syntactically} in the hypothesis of
      the second theorem. *)

  val refl : (expr -> t) with_ctx
  (** `refl e` returns `|- e=e` *)

  val congr : (t -> t -> t) with_ctx
  (** `congr (|- f=g) (|- t=u)` is `|- (f t) = (g u)` *)

  val subst : recursive:bool -> (t -> Subst.t -> t) with_ctx
  (** `subst (A |- t) \sigma` is `A\sigma |- t\sigma` *)

  val sym : (t -> t) with_ctx
  (** `sym (|- t=u)` is `|- u=t` *)

  val trans : (t -> t -> t) with_ctx
  (** trans (F1 |- t=u)` `(F2 |- u=v)` is `F1, F2 |- t=v` *)

  val bool_eq : (t -> t -> t) with_ctx
  (** `bool_eq (F1 |- a) (F2 |- a=b)` is `F1, F2 |- b`.
      This is the boolean equivalent of transitivity. *)

  val bool_eq_intro : (t -> t -> t) with_ctx
    (** `bool_eq_intro (F1, a |- b) (F2, b |- a)` is `F1, F2 |- b=a`.
        This is a way of building a boolean `a=b` from proofs of
        `a|-b` and `b|-a`. *)

  val beta_conv : (expr -> t) with_ctx
  (** `beta_conv ((λx.u) a)` is `|- (λx.u) a = u[x:=a]`.
      Fails if the term is not a beta-redex. *)

  val abs : (var -> t -> t) with_ctx
  (** `abs (F |- a=b) x` is `F |- (\x. a) = (\x. b)`
      fails if `x` occurs in `F`. *)

  val new_basic_definition :
    (?def_loc:location -> expr -> t * const) with_ctx
  (** `new_basic_definition (x=t)` where `x` is a variable and `t` a term
      with a closed type,
      returns a theorem `|- x=t` where `x` is now a constant, along with
      the constant `x`.  *)


  val new_basic_type_definition :
    (?ty_vars:ty_var list ->
    name:string ->
    abs:string ->
    repr:string ->
    thm_inhabited:thm ->
    unit ->
    New_ty_def.t) with_ctx
  (** Introduce a new type operator.

      Here, too, we follow HOL light:
      `new_basic_type_definition(tau, abs, repr, inhabited)`
      where `inhabited` is the theorem `|- Phi x` with `x : ty`,
      defines a new type operator named `tau` and two functions,
      `abs : ty -> tau` and `repr: tau -> ty`.

      It returns a struct `New_ty_def.t` containing `tau, absthm, reprthm`, where:
      - `tau` is the new (possibly parametrized) type operator
      - `absthm` is `|- abs (repr x) = x`
      - `reprthm` is `|- Phi x <=> repr (abs x) = x`

      @param ty_var if provided, use the type variables in the given order.
      It must be the exact set of free variables of [thm_inhabited].
  *)
end

(** Theorems, with explicit context *)
module Thm : THM with type 'a with_ctx := (ctx -> 'a)

(** Theorem API specialized for a context *)
module type THM_FOR_CTX = THM with type 'a with_ctx := 'a

(** Make a theorem API specialized for the given context *)
val make_thm : ctx -> (module THM_FOR_CTX)

(** {2 Theories}

    Theories are similar to OpenTheory's theories.

    A theory bundles input constants/theorems (assumptions),
    and defined constants/theorems (proved in the theory).
    It can be composed or interpreted (renaming of constants).

    TODO: make the theories explicit and always present in the theorems
    (using perhaps some form of patricia tree with good sharing, so it's
    easy to merge theories when applying binary inference rules
*)

(** Theory *)
module Theory : sig
  type t = theory

  include Sigs.PP with type t := t

  val with_ :
    ctx -> name:string ->
    (t -> unit) -> t

  val assume : t -> expr list -> expr -> thm
  (** [assume theory hyps concl] creates the theorem
      [hyps |- concl] as a parameter of the theory [theory]. *)

  val assume_const : t -> const -> unit

  val assume_ty_const : t -> ty_const -> unit

  val add_const : t -> const -> unit

  val add_ty_const : t -> ty_const -> unit

  val add_theorem : t -> thm -> unit

  val find_const : t -> string -> const option
  (** Find a constant used or defined in this theory by its name *)

  val find_ty_const : t -> string -> ty_const option
  (** Find a type constant used or defined in this theory by its name *)

  (** {3 Composition} *)

  type interpretation = string Str_map.t

  val instantiate :
    interp:interpretation ->
    t -> t
  (** [instantiate ~interp theory] renames constants according to [interpr].
      This can change the types of some terms if [interp] renames type constants. *)

  val compose :
    ?interp:interpretation ->
    t list -> t -> t
  (** [compose l theory], where [theory = Gamma |> Delta] proves [Delta]
      under assumptions [Gamma], and where [l = [Gamma1 |> Delta1, …]]
      is a list of theories, returns
      [Gamma1, …, Gamma_n, Gamma \ {Delta1 U … U Delta_n} |> Delta].

      In other words, it uses the theores proved in [l] to discharge some
      of the assumptions in [theory], and adds assumptions of [l]
      to the result instead.

      @param interp if provided, instantiate theory with this interpretation first. *)

  val union : ctx -> name:string -> t list -> t
  (** Union of several theories *)
end

(** {2 Context}

    The context is storing the term state, list of axioms,
    and other parameters.
    Terms from distinct contexts must never be mixed. *)
module Ctx : sig
  type t = ctx

  val create : unit -> t

  val pledge_no_more_axioms : t -> unit
  (** Forbid the creation of new axioms. From now on, this logical context
      is frozen. *)

  val axioms : t -> thm iter
end


(**/**)
val __pp_ids: bool ref
(**/**)
