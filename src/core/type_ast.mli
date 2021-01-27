
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
type env

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

(** {2 Typing Environment}

    This environment is (mostly) functional, and is used to handle
    scoping and to map names into constants and expressions and their type.
    *)
module Env : sig
  type t = env

  val create : K.Ctx.t -> t

  val copy : t -> t
  (** Make a copy. The two copies share the same underlying context
      but nothing else. *)

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
    | Let_step of ID.t * step

  and step_view =
    | Pr_apply_rule of Proof.Rule.t * rule_arg list
    | Pr_sub_proof of t
    | Pr_error of unit Fmt.printer (* parse error *)

  (** An argument to a rule *)
  and rule_arg =
    | Arg_var_step of ID.t
    | Arg_step of step
    | Arg_thm of K.Thm.t
    | Arg_expr of expr
    | Arg_subst of subst

  type rule_signature = Proof.Rule.signature

  include PP with type t := t
  include Queryable.S with type t := t
  val pp_pr_let : pr_let Fmt.printer
  val pp_rule_arg : rule_arg Fmt.printer
  val pp_rule_signature : rule_signature Fmt.printer

  (** Run the proof to get a kernel theorem (or a failure) *)
  val run : K.Ctx.t -> t -> K.Thm.t
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
  val infer_expr : env -> A.expr -> expr
  val infer_goal : env -> A.Goal.t -> Goal.t * K.Goal.t
  val infer_proof : env -> A.Proof.t -> Proof.t
end

(** {2 Object index} *)

module Index : sig
  type t

  val empty : t
  val size : t -> int

  val find : t -> Position.t -> Queryable.t list
  (** Find items that overlap this position, from the most
      to the least narrow *)
end

(** {2 Process statements} *)

val process_stmt :
  index:bool ->
  on_show:(location -> unit Fmt.printer -> unit) ->
  on_error:(location -> unit Fmt.printer -> unit) ->
  env * Index.t -> A.top_statement -> env * Index.t
(** Process a toplevel statement, returning a new environment
    and updated index. *)
