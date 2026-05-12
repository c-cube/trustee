(** {1 Kernel of trust} *)

open Sigs

type ctx
type expr
type ty = expr
type const_def
type const
type ty_const = const
type thm
type theory

type var = {
  v_name: string;
  v_ty: ty;
}

type ty_var = var

type bvar = {
  bv_idx: int;
  bv_ty: ty;
}

type expr_set

type sequent = private {
  concl: expr;
  hyps: expr_set;
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
  | E_box of sequent

type ty_or_error =
  | Kind
  | Ty of expr
  | Ill_typed of string

(** Logic constants *)
module Const : sig
  type t = const
  type def = const_def

  include Sigs.EQ with type t := t
  include PP with type t := t

  type args =
    | C_ty_vars of ty_var list
    | C_arity of int

  val name : t -> string
  val chash : t -> Chash.t
  val args : t -> args
  val ty : t -> ty
  val labels : t -> (string * string) list
  val pp_args : args Fmt.printer
  val pp_with_ty : t Fmt.printer
  val eq : ctx -> t
  val bool : ctx -> t
  val select : ctx -> t

  val get_def : ctx -> t -> def option
  val get_def_exn : ctx -> t -> def
end

(** Constant definitions. *)
module Const_def : sig
  type t = const_def

  include PP with type t := t
  include Sigs.SER1 with type t := t and type state := ctx

  val approx_def : t -> [ `Other | `Param | `Ty_def of expr | `Def of expr ]
end

(** Proofs. *)
module Proof : sig
  type arg =
    | Pr_expr of expr
    | Pr_subst of (var * expr) list

  type t = private
    | Pr_dummy
    | Pr_main of t
    | Pr_step of {
        rule: string;
        args: arg list;
        parents: thm list;
      }

  val is_main : t -> bool
  val is_main_or_dummy : t -> bool
end

(** Linear proofs. *)
module Linear_proof : sig
  type t

  type arg = Proof.arg =
    | Pr_expr of expr
    | Pr_subst of (var * expr) list

  type step = {
    concl: sequent;
    rule: string;
    args: arg list;
    parents: int list;
  }

  include Sigs.SER1 with type t := t and type state := ctx

  val steps : t -> (int * step) Iter.t
  val of_thm_proof : thm -> t
end

(** Free Variables *)
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

  include Sigs.SER1 with type t := t and type state := ctx
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
  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t
  include Sigs.SER1 with type t := t and type state := ctx

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

(** Expressions *)
module Expr : sig
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
    | E_box of sequent

  val chash : t -> Chash.t

  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t
  include Sigs.COMPARE with type t := t
  include Sigs.PP with type t := t
  include Sigs.SER1 with type t := t and type state := ctx

  val pp_depth : max_depth:int -> t Fmt.printer

  val view : t -> view
  val ty : t -> ty option
  val ty_exn : t -> ty
  val is_closed : t -> bool
  val is_eq_to_type : t -> bool
  val is_eq_to_bool : t -> bool
  val is_a_bool : t -> bool
  val is_a_type : t -> bool
  val is_lam : t -> bool
  val is_arrow : t -> bool
  val is_error : t -> bool

  val iter : f:(bool -> t -> unit) -> t -> unit
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

  val iter_dag : iter_ty:bool -> f:(t -> unit) -> t -> unit
  val iter_dag' : iter_ty:bool -> t -> t Iter.t

  type 'a with_ctx = ctx -> 'a

  val subst : (recursive:bool -> t -> Subst.t -> t) with_ctx
  val type_ : t with_ctx
  val bool : t with_ctx
  val eq : (ty -> t) with_ctx
  val select : (ty -> t) with_ctx
  val var : (var -> t) with_ctx
  val const : (const -> ty list -> t) with_ctx
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
  val box : (sequent -> t) with_ctx
  val map : (f:(bool -> t -> t) -> t -> t) with_ctx
  val db_shift : (t -> int -> t) with_ctx
  val open_lambda : (t -> (var * t) option) with_ctx
  val open_lambda_exn : (t -> var * t) with_ctx
  val mk_error : (string -> t) with_ctx
  val app_or_error : (t -> t -> t) with_ctx
  val lambda_or_error : (var -> t -> t) with_ctx
end

module Sequent : sig
  type t = sequent = private {
    concl: expr;
    hyps: expr_set;
  }

  val equal : t -> t -> bool
  val make : expr_set -> Expr.t -> t
  val make_l : Expr.t list -> Expr.t -> t
  val make_nohyps : Expr.t -> t
  val concl : t -> Expr.t
  val hyps : t -> expr_set
  val n_hyps : t -> int
  val hyps_l : t -> Expr.t list
  val hyps_iter : t -> Expr.t iter
  val iter_exprs : t -> Expr.t Iter.t

  include Sigs.PP with type t := t
end

(** Data returned by a new type definition *)
module New_ty_def : sig
  type t = {
    tau: ty_const;
    fvars: var list;
    c_abs: const;
    c_repr: const;
    abs_thm: thm;
    abs_x: var;
    repr_thm: thm;
    repr_x: var;
  }
end

(** {2 Theorems and Deduction Rules} *)

(** Theorem API. *)
module Thm : sig
  type t = thm

  include Sigs.PP with type t := t

  val pp_depth : max_depth:int -> t Fmt.printer
  val pp_quoted : t Fmt.printer
  val concl : t -> expr

  include Sigs.EQ with type t := t
  include Sigs.HASH with type t := t

  val sequent : t -> Sequent.t
  val is_fully_concrete : t -> bool
  val chash : t -> Chash.t
  val proof : t -> Proof.t
  val make_main_proof : t -> unit

  val hyps_iter : t -> expr iter
  val hyps_l : t -> expr list
  val hyps_sorted_l : t -> expr list
  val iter_exprs : t -> Expr.t Iter.t
  val n_hyps : t -> int
  val has_hyps : t -> bool
  val is_proof_of : t -> Sequent.t -> bool

  type 'a with_ctx = ctx -> 'a

  val assume : (expr -> t) with_ctx
  val axiom : (expr list -> expr -> t) with_ctx
  val cut : (t -> t -> t) with_ctx
  val refl : (expr -> t) with_ctx
  val congr : (t -> t -> t) with_ctx
  val subst : recursive:bool -> (t -> Subst.t -> t) with_ctx
  val sym : (t -> t) with_ctx
  val trans : (t -> t -> t) with_ctx
  val bool_eq : (t -> t -> t) with_ctx
  val bool_eq_intro : (t -> t -> t) with_ctx
  val beta_conv : (expr -> t) with_ctx
  val abs : (var -> t -> t) with_ctx
  val new_basic_definition : (expr -> t * const) with_ctx
  val new_basic_type_definition :
    (?ty_vars:ty_var list ->
    name:string ->
    abs:string ->
    repr:string ->
    thm_inhabited:thm ->
    unit ->
    New_ty_def.t)
    with_ctx
  val box : (thm -> thm) with_ctx
  val assume_box : (sequent -> thm) with_ctx
end

(** {2 Theories} *)

(** Theory *)
module Theory : sig
  type t = theory

  include Sigs.PP with type t := t

  val with_ : ctx -> name:string -> (t -> unit) -> t
  val name : t -> string
  val assume : t -> expr list -> expr -> thm
  val add_assumption_const : t -> const -> unit
  val assume_const : t -> string -> ty_var list -> ty -> const
  val assume_ty_const : t -> string -> arity:int -> const
  val add_const : t -> const -> unit
  val add_ty_const : t -> ty_const -> unit
  val add_theorem : t -> thm -> unit
  val find_const : t -> string -> const option
  val find_ty_const : t -> string -> ty_const option
  val param_consts : t -> const list
  val param_theorems : t -> thm list
  val consts : t -> const list
  val theorems : t -> thm list

  type interpretation = string Str_map.t

  val instantiate : interp:interpretation -> t -> t
  val compose : ?interp:interpretation -> t list -> t -> t
  val union : ctx -> name:string -> t list -> t
end

(** Context *)
module Ctx : sig
  type t = ctx

  val create :
    ?def_cache_size:int ->
    ?storage:Storage.t ->
    ?store_proofs:bool ->
    ?store_concrete_definitions:bool ->
    unit ->
    t

  val pledge_no_more_axioms : t -> unit
  val n_exprs : t -> int
  val axioms : t -> thm iter
  val new_skolem_const : t -> string -> var list -> ty -> const
  val new_skolem_ty_const : t -> string -> arity:int -> const
end

(**/**)

val __pp_ids : bool ref

(**/**)
