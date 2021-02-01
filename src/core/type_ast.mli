
(** {1 Typing AST}

    This AST is used for type inference, and is generally the stable target
    for anything IDE-like.
*)

open Sigs

module K = Kernel
module A = Parse_ast

type expr
type position = Position.t
type location = A.location

type ty = expr

and var = {
  v_name: string;
  v_ty: ty;
}

and bvar = {
  bv_name: ID.t;
  bv_ty: ty;
  bv_loc: location;
}

and binding = bvar * expr

(** View of an expression *)
and view =
  | Kind
  | Type
  | Bool
  | Ty_arrow of ty * ty
  | Ty_pi of bvar * ty
  | Var of var
  | BVar of bvar
  | Meta of meta
  | Const of {
      c: K.Expr.t;
    }
  | App of expr * expr
  | Lambda of bvar * expr
  | Eq of expr * expr
  | Let of binding list * expr

and meta

type subst

(** Typing environment *)
type ty_env

(** {2 Satellite types} *)

module Var : sig
  type t = var
  include PP with type t := t
end

module BVar : sig
  type t = bvar
  include PP with type t := t
end

(* {2 Expressions} *)
module Expr : sig
  type t = expr
  include PP with type t := expr
  include Queryable.S with type t := t

  val to_k_expr :
    ?subst:K.Expr.t ID.Map.t ->
    K.Ctx.t ->
    expr -> K.Expr.t
  val loc : t -> location
end

(** {2 Substitutions} *)
module Subst : sig
  type t = subst
  include PP with type t := t

  val to_k_subst :
    ?subst:K.Expr.t ID.Map.t ->
    K.Ctx.t -> t -> K.Subst.t
end

(** {2 Typing environment}

    This environment is (mostly) functional, and is used to handle
    scoping and to map names into constants and expressions and their type. *)
module Ty_env : sig
  type t = ty_env

  val empty : t

  type named_object =
    | N_expr of K.Expr.t A.with_loc
    | N_thm of K.Thm.t A.with_loc
    | N_rule of Proof.Rule.t A.with_loc

  val find_thm : t -> string -> K.Thm.t A.with_loc option

  val find_named : t -> string -> named_object option

  val completions : t -> string -> (string * named_object) Iter.t

  val iter : t -> (string * named_object) Iter.t

  include PP with type t := t

  val pp_named_object : named_object Fmt.printer
  val string_of_named_object : named_object -> string
end

(** {2 Typing state}

    This environment is (mostly) functional, and is used to handle
    scoping and to map names into constants and expressions and their type.
    *)
module Typing_state : sig
  type t

  val create : ?ty_env:Ty_env.t -> K.Ctx.t -> t

  val ty_env : t -> Ty_env.t

  val generalize_ty_vars : t -> unit
  (** Generalize remaining variables. This modifies terms previously
      obtained with this environment and {!infer}. *)
end

(** {2 Proofs} *)
module Proof : sig
  type t
  type step
  val loc : t -> location

  type view =
    | Proof_atom of step
    | Proof_steps of {
        lets: pr_let list;
        (** intermediate steps *)
        ret: step;
        (** proof to return *)
      }

  (** named steps *)
  and pr_let =
    | Let_expr of bvar * expr
    | Let_step of ID.t A.with_loc * step

  and step_view =
    | Pr_apply_rule of Proof.Rule.t A.with_loc * rule_arg list
    | Pr_sub_proof of t
    | Pr_error of unit Fmt.printer (* parse error *)

  (** An argument to a rule *)
  and rule_arg =
    | Arg_var_step of {
        name: ID.t;
        loc: location; (* loc of the variable *)
        points_to: step;
      }
    | Arg_step of step
    | Arg_thm of K.Thm.t A.with_loc * location
    | Arg_expr of expr
    | Arg_subst of subst

  type rule_signature = Proof.Rule.signature

  include PP with type t := t
  include Queryable.S with type t := t
  val pp_pr_let : pr_let Fmt.printer
  val pp_rule_arg : rule_arg Fmt.printer
  val pp_rule_signature : rule_signature Fmt.printer

  (** Run the proof to get a kernel theorem (or a failure) *)
  val run :
    ?on_step_res:(step -> K.Thm.t -> unit) ->
    K.Ctx.t -> t -> K.Thm.t or_error

  val run_exn :
    ?on_step_res:(step -> K.Thm.t -> unit) ->
    K.Ctx.t -> t -> K.Thm.t
end

module Goal : sig
  type t = private {
    hyps: expr list;
    concl: expr;
    loc: location;
  }
  include Sigs.PP with type t := t
  include Queryable.S with type t := t
  val to_k_goal : K.Ctx.t -> t -> K.Goal.t
end

module Thm = K.Thm

(* {2 type inference} *)
module Ty_infer : sig
  val infer_expr : Typing_state.t -> A.expr -> expr
  val infer_goal : Typing_state.t -> A.Goal.t -> Goal.t * K.Goal.t
  val infer_proof : Typing_state.t -> A.Proof.t -> Proof.t
end

(** {2 Object index} *)

module Index : sig
  type t

  val empty : t

  val fake : t (** will not be updated *)

  val size : t -> int

  val find : t -> Position.t -> Queryable.t list
  (** Find items that overlap this position, from the most
      to the least narrow *)

  val find_ty_env :  t -> Position.t -> ty_env
end

(** {2 Process statements} *)

val process_stmt :
  on_show:(location -> unit Fmt.printer -> unit) ->
  on_error:(location -> unit Fmt.printer -> unit) ->
  Index.t ->
  Typing_state.t ->
  A.top_statement ->
  Index.t
(** Process a toplevel statement, returning a new environment
    and updated index. *)
