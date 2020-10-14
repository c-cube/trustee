
(** {1 Kernel of trust} *)

open Sigs

(** {2 Generative Identifiers}

    This is a representation of a name that is unambiguous even in the presence
    of scoping *)
module ID : sig
  type t

  val make : string -> t
  val makef : ('a, Format.formatter, unit, t) format4 -> 'a
  val copy : t -> t

  val id : t -> int
  val name : t -> string

  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.PP with type t := t

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end

type ctx
type expr
type ty = expr
type const
type thm

type fixity =
  | F_normal
  | F_left_assoc of int
  | F_right_assoc of int
  | F_prefix of int
  | F_postfix of int
  | F_binder of int

type var = {
  v_name: string;
  v_ty: ty;
}

type bvar = {
  bv_idx: int;
  bv_ty: ty;
}

(** {2 Fixity} *)
module Fixity : sig
  type t = fixity
  val pp : t Fmt.printer
  val to_string : t -> string

  val normal : t
  val lassoc : int -> t
  val rassoc : int -> t
  val prefix : int -> t
  val postfix : int -> t

  val get_prec : t -> int
end

module Const : sig
  type t = const
  val fixity : t -> fixity
  val set_fixity : t -> fixity -> unit
  val pp : t Fmt.printer
end

(** {2 Free Variables} *)
module Var : sig
  type t = var

  val name : t -> string
  val ty : t -> ty
  val make : string -> ty -> t

  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.PP with type t := t

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end

(** {2 Expressions and Types} *)
module Expr : sig
  type t = expr

  type view =
    | E_kind
    | E_type
    | E_var of var
    | E_bound_var of bvar
    | E_const of const
    | E_app of t * t
    | E_lam of t * t
    | E_pi of t * t

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

  val subst : ctx -> t -> t Var.Map.t -> t

  val type_ : ctx -> t
  val bool : ctx -> t
  val eq : ctx -> t
  val var : ctx -> var -> t
  val const : ctx -> const -> t
  val new_const : ctx -> string -> ty -> t
  val new_ty_const : ctx -> string -> t
  val var_name : ctx -> string -> ty -> t
  val bvar : ctx -> int -> ty -> t
  val app : ctx -> t -> t -> t
  val app_l : ctx -> t -> t list -> t
  val app_eq : ctx -> t -> t -> t
  val lambda : ctx -> var -> t -> t
  val lambda_l : ctx -> var list -> t -> t
  val lambda_db : ctx -> ty_v:ty -> t -> t
  val pi : ctx -> var -> t -> t
  val pi_l : ctx -> var list -> t -> t
  val pi_db : ctx -> ty_v:ty -> t -> t
  val arrow : ctx -> t -> t -> t
  val arrow_l : ctx -> t list -> t -> t

  val map : ctx -> f:(bool -> t -> t) -> t -> t
  val iter : f:(bool -> t -> unit) -> t -> unit
  val contains : t -> sub:t -> bool
  val free_vars : t -> Var.Set.t

  val unfold_app : t -> t * t list
  val unfold_eq : t -> (t * t) option

  module Set : CCSet.S with type elt = t
  module Map : CCMap.S with type key = t
  module Tbl : CCHashtbl.S with type key = t
end

module New_ty_def : sig
  type t = {
    tau: expr;
    (** the new type constructor *)
    fvars: var list;
    c_abs: expr;
    (** Function from the general type to `tau` *)
    c_repr: expr;
    (** Function from `tau` back to the general type *)
    abs_thm: thm;
    (** `abs_thm` is `|- abs (repr x) = x` *)
    abs_x: var;
    repr_thm: thm;
    (** `repr_thm` is `|- Phi x <=> repr (abs x) = x` *)
    repr_x: var;
  }
end

(** {2 Theorems and Deduction Rules} *)
module Thm : sig
  type t = thm

  include Sigs.PP with type t := t

  val concl : t -> expr
  val hyps_iter : t -> expr iter
  val hyps_l : t -> expr list
  val has_hyps : t -> bool
  val n_hyps : t -> int
  (* TODO: store proofs optionally *)

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

  val congr_ty : ctx -> t -> ty -> t
  (** `congr_ty (|- f=g) ty` is `|- (f ty) = (g ty)` where `ty` is a type *)

  val sym : ctx -> t -> t
  (** `sym (|- t=u)` is `|- u=t` *)

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

  val new_basic_definition : ctx -> expr -> t * expr
  (** `new_basic_definition (x=t)` where `x` is a variable and `t` a term
      with a closed type,
      returns a theorem `|- x=t` where `x` is now a constant, along with
      the constant `x`.  *)


  val new_basic_type_definition :
    ctx ->
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

