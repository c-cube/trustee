
(** {1 Typing AST}

    This AST is used for type inference, and is generally the stable target
    for anything IDE-like.
*)

open Sigs

module K = Kernel
module A = Parse_ast

type expr
type position = A.position

type ty = expr

and var = {
  v_name: string;
  v_ty: ty;
}

and bvar = {
  bv_name: ID.t;
  bv_ty: ty;
}

and binding = bvar * expr

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

(** Typing environment *)
type env

module Expr : sig
  type t = expr
  include PP with type t := expr
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
end

(* {2 type inference} *)

val infer : Env.t -> Parse_ast.expr -> expr

val generalize : Env.t -> unit
(** Generalize remaining variables. This modifies terms previously
    obtained with this environment and {!infer}. *)

val to_expr : K.Ctx.t -> expr -> K.Expr.t

