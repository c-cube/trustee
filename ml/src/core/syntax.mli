
(** {1 Expression parser} *)

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

type position = {
  line: int;
  col: int;
}

(** {2 Lexer} *)
module Lexer : sig
  type t

  val create : string -> t
  val next : t -> token
  val cur : t -> token

  val pos : t -> position
end
