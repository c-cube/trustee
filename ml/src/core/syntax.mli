
(** {1 Expression parser} *)

open Sigs

module K = Kernel

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
  | AT_SYM of string
  | NUM of string
  | ERROR of char
  | EOF

type position = Position.t

module Token : sig
  type t = token
  val pp : t Fmt.printer
  val equal : t -> t -> bool
end

(** {2 Lexer} *)
module Lexer : sig
  type t

  val create : string -> t
  val next : t -> token
  val cur : t -> token

  val pos : t -> position
end

(** {2 Parser} *)
val parse :
  ?q_args:K.Expr.t list ->
  ctx:K.Ctx.t ->
  Lexer.t ->
  K.expr
