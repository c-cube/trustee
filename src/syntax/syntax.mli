
(** Parser.

    This is the main parser for Trustee's input syntax.
    We use parser combinators from {!Parser}. *)

open Common_

module LL = Local_loc
module A = Parse_ast
module P = Parser

val expr :
  notation:Notation.Ref.t ->
  A.Expr.t P.t

val parse_top :
  notation:Notation.Ref.t ->
  A.Top.t option P.t

val parse_top_l :
  notation:Notation.Ref.t ->
  A.Top.t list P.t
(** Parse statements, updating notations when they are declared. *)
