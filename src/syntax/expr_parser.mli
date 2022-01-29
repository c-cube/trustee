
(** Expression parser *)

open Common_
module LL = Local_loc
module A = Parse_ast

type 'a or_error = ('a, Loc.t * Error.t) result

val parse_expr :
  notation:Notation.t ->
  Lexer.t -> A.Expr.t or_error

val expr_of_string :
  ?loc_offset:int ->
  ?src_string:string ->
  ?file:string ->
  notation:Notation.t ->
  string -> A.Expr.t or_error
(** Parse expression.
    @param loc_offset is added to all locations. See {!Lexer.create}. *)
