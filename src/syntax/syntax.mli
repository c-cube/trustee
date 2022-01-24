
(** {1 Expression parser} *)

open Common_
module LL = Local_loc
module A = Parse_ast

(** {2 Parser} *)

(* TODO: remove Env? we should only need a Notation.t,
   and update it on the fly. *)

val parse_expr :
  notation:Notation.Ref.t ->
  Lexer.t -> A.Expr.t

val parse_top :
  notation:Notation.Ref.t ->
  Lexer.t ->
  A.Top.t option

val parse_top_l :
  notation:Notation.Ref.t ->
  Lexer.t ->
  A.Top.t list
(** Parse statements, updating notations when they are declared. *)
