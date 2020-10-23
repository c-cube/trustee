
(** {1 Expression parser} *)

open Sigs

module K = Kernel
module A = Parse_ast

type token =
  | LPAREN
  | RPAREN
  | COLON
  | DOT
  | WILDCARD
  | QUESTION_MARK
  | QUESTION_MARK_STR of string
  | SYM of string
  | QUOTED_STR of string
  | LET
  | IN
  | AND
  | AT_SYM of string
  | NUM of string
  | END
  | ERROR of char
  | EOF

type position = A.position

module Token : sig
  type t = token
  include PP with type t := t
  val equal : t -> t -> bool
end

(** {2 Lexer} *)
module Lexer : sig
  type t

  val create : string -> t
  val next : t -> token
  val cur : t -> token

  val to_list : t -> token list

  val pos : t -> Position.t
end

(** {2 Parser} *)

val parse_ast :
  ?q_args:K.Expr.t list ->
  ctx:K.Ctx.t ->
  Lexer.t ->
  A.expr

val parse :
  ?q_args:K.Expr.t list ->
  ctx:K.Ctx.t ->
  Lexer.t ->
  K.expr
