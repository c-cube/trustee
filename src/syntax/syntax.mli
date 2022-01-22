
(** {1 Expression parser} *)

open Common_
module LL = Local_loc
module A = Parse_ast

type token =
  | LPAREN
  | RPAREN
  | COLON
  | DOT
  | COMMA
  | SEMI_COLON
  | WILDCARD
  | QUESTION_MARK
  | QUESTION_MARK_STR of string
  | SYM of string
  | QUOTE_STR of string (* 'foo *)
  | QUOTED_STR of string
  | LET
  | IN
  | AND
  | EQDEF
  | NUM of string
  | BY
  | END
  | ERROR of char
  | EOF

module Token : sig
  type t = token
  include PP with type t := t
  val equal : t -> t -> bool
end

(** {2 Lexer} *)
module Lexer : sig
  type t = token Tok_stream.t
  module S = Tok_stream
  val create : file:string -> string -> t
end

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
