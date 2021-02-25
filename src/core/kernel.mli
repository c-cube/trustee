
(** {1 Kernel of trust} *)

open Sigs

type ctx
type expr
type ty = expr
type const
type ty_const = const
type thm

type fixity = Fixity.t
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

module Const : sig
  type t = const
  include Sigs.EQ with type t := t
  include PP with type t := t

  val fixity : t -> fixity
  val set_fixity : t -> fixity -> unit
  val def_loc : t -> location option

  type args =
    | C_ty_vars of ty_var list
    | C_arity of int

  val args : t -> args
  val pp_args : args Fmt.printer
  val ty : t -> ty

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

  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.PP with type t := t
  val pp_with_ty : t Fmt.printer

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end

module BVar : sig
  type t = bvar
  val make : int -> ty -> t
  include Sigs.PP with type t := t
end

(** {2 Substitutions} *)
module Subst : sig
  type t = expr Var.Map.t
  include Sigs.PP with type t := t
  val find_exn : var -> t -> expr
  val get : var -> t -> expr option
  val empty : t
  val is_empty : t -> bool
  val bind : var -> expr -> t -> t
  val size : t -> int
  val to_iter : t -> (var * expr) Iter.t
end

(** {2 Expressions and Types} *)
module Expr : sig
  type t = expr

  type view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const * t list
    | E_app of t * t
    | E_lam of t * t
    | E_arrow of expr * expr

  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.PP with type t := t

  val view : t -> view
  val ty : t -> ty option
  val ty_exn : t -> ty
  val is_closed : t -> bool
  val is_eq_to_type : t -> bool
  val is_eq_to_bool : t -> bool
  val is_a_bool : t -> bool
  val is_a_type : t -> bool
  (** Is the type of [e] equal to [Type]? *)

  val subst : ctx -> t -> Subst.t -> t

  val type_ : ctx -> t
  val bool : ctx -> t
  val eq : ctx -> ty -> t
  val select : ctx -> ty -> t
  val var : ctx -> var -> t
  val const : ctx -> const -> ty list -> t
  val new_const : ctx -> ?def_loc:location -> string -> ty_var list -> ty -> const
  val new_ty_const : ctx -> ?def_loc:location -> string -> int -> const
  val var_name : ctx -> string -> ty -> t
  val bvar : ctx -> int -> ty -> t
  val app : ctx -> t -> t -> t
  val app_l : ctx -> t -> t list -> t
  val app_eq : ctx -> t -> t -> t
  val lambda : ctx -> var -> t -> t
  val lambda_l : ctx -> var list -> t -> t
  val lambda_db : ctx -> ty_v:ty -> t -> t
  val arrow : ctx -> t -> t -> t
  val arrow_l : ctx -> t list -> t -> t

  val map : ctx -> f:(bool -> t -> t) -> t -> t
  val iter : f:(bool -> t -> unit) -> t -> unit
  val exists : f:(bool -> t -> bool) -> t -> bool
  val for_all : f:(bool -> t -> bool) -> t -> bool

  val contains : t -> sub:t -> bool
  val free_vars : t -> Var.Set.t
  val free_vars_iter : t -> var Iter.t
  val db_shift: ctx -> t -> int -> t

  val unfold_app : t -> t * t list
  val unfold_eq : t -> (t * t) option
  val unfold_arrow : t -> t list * t
  val as_const : t -> (Const.t * ty list) option
  val as_const_exn : t -> Const.t * ty list

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end

(** {2 Toplevel goals}

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

(** {2 Theorems and Deduction Rules} *)
module Thm : sig
  type t = thm

  include Sigs.PP with type t := t
  val pp_quoted : t Fmt.printer

  val concl : t -> expr
  val hyps_iter : t -> expr iter
  val hyps_l : t -> expr list
  val has_hyps : t -> bool
  val n_hyps : t -> int
  (* TODO: store proofs optionally *)

  val is_proof_of : t -> Goal.t -> bool
  (** Is this theorem a proof of the given goal? *)

  (** {3 Deduction rules} *)

  val assume : ctx -> expr -> t
  (** `assume e` returns `e |- e`. *)

  val axiom : ctx -> expr -> t
  (** `axiom e` is `|- e`. Fails if [pledge_no_more_axioms] was called *)

  val cut : ctx -> t -> t -> t
  (** `cut (F1 |- b) (F2, b |- c)` is `F1, F2 |- c`.
      Fails if `b` does not occur {b syntactically} in the hypothesis of
      the second theorem. *)

  val refl : ctx -> expr -> t
  (** `refl e` returns `|- e=e` *)

  val congr : ctx -> t -> t -> t
  (** `congr (|- f=g) (|- t=u)` is `|- (f t) = (g u)` *)

  val subst : ctx -> t -> Subst.t -> t
  (** `subst (A |- t) \sigma` is `A\sigma |- t\sigma` *)

  val sym : ctx -> t -> t
  (** `sym (|- t=u)` is `|- u=t` *)

  val trans : ctx -> t -> t -> t
  (** trans (F1 |- t=u)` `(F2 |- u=v)` is `F1, F2 |- t=v` *)

  val bool_eq : ctx -> t -> t -> t
  (** `bool_eq (F1 |- a) (F2 |- a=b)` is `F1, F2 |- b`.
      This is the boolean equivalent of transitivity. *)

  val bool_eq_intro : ctx -> t -> t -> t
    (** `bool_eq_intro (F1, a |- b) (F2, b |- a)` is `F1, F2 |- b=a`.
        This is a way of building a boolean `a=b` from proofs of
        `a|-b` and `b|-a`. *)

  val beta_conv : ctx -> expr -> t
  (** `beta_conv ((λx.u) a)` is `|- (λx.u) a = u[x:=a]`.
      Fails if the term is not a beta-redex. *)

  val abs : ctx -> t -> var -> t
  (** `abs (F |- a=b) x` is `F |- (\x. a) = (\x. b)`
      fails if `x` occurs in `F`. *)

  val new_basic_definition :
    ctx -> ?def_loc:location ->
    expr -> t * const
  (** `new_basic_definition (x=t)` where `x` is a variable and `t` a term
      with a closed type,
      returns a theorem `|- x=t` where `x` is now a constant, along with
      the constant `x`.  *)


  val new_basic_type_definition :
    ctx ->
    ?ty_vars:ty_var list ->
    name:string ->
    abs:string ->
    repr:string ->
    thm_inhabited:thm ->
    unit ->
    New_ty_def.t
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

  val find_const_by_name : t -> string -> const option
end

