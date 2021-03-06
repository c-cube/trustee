
(** {1 Expression parser} *)

open Sigs

module K = Kernel
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

type location = A.location

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

val parse_expr :
  ?q_args:K.Expr.t list ->
  env:A.Env.t -> Lexer.t -> A.expr

val parse_top :
  env:A.Env.t ->
  Lexer.t ->
  A.top_statement option

val parse_top_l_process :
  ?file:string ->
  env:A.Env.t ->
  Lexer.t ->
  A.top_statement list
(** Parse statements, processing each one with {!Parse_ast.Env.process}
    as soon as it is produced *)

(** {2 Parse and perform type inference} *)

val parse_expr_infer :
  ?q_args:K.Expr.t list ->
  ctx:K.Ctx.t ->
  env:A.Env.t ->
  Lexer.t ->
  K.expr
