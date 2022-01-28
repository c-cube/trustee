
open Common_

type t =
  | LPAREN
  | RPAREN

  | COLON
  | DOT
  | COMMA

  | WILDCARD
  | QUESTION_MARK

  | LET
  | IN
  | EQDEF

  | QUESTION_MARK_STR of string
  | SYM of string
  | QUOTE_STR of string (* 'foo *)
  | QUOTED_STR of string
  | NUM of string

  | ERROR of char
  | EOF

let pp out = function
  | LPAREN -> Fmt.string out "'('"
  | RPAREN -> Fmt.string out "')'"
  | COLON -> Fmt.string out "':'"
  | DOT -> Fmt.string out "'.'"
  | COMMA -> Fmt.string out "','"
  | LET -> Fmt.string out "LET"
  | IN -> Fmt.string out "IN"
  | EQDEF -> Fmt.string out "EQDEF"
  | WILDCARD -> Fmt.string out "WILDCARD"
  | QUESTION_MARK -> Fmt.string out "QUESTION_MARK"
  | QUESTION_MARK_STR s -> Fmt.fprintf out "(QUESTION_MARK_STR %S)" s
  | SYM s -> Fmt.fprintf out "(SYM %S)" s
  | QUOTE_STR s -> Fmt.fprintf out "(QUOTE_STR %S)" s
  | QUOTED_STR s -> Fmt.fprintf out "(QUOTED_STR %S)" s
  | NUM s -> Fmt.fprintf out "(NUM %S)" s
  | ERROR c -> Fmt.fprintf out "(ERROR '%c')" c
  | EOF -> Fmt.string out "EOF"
let to_string = Fmt.to_string pp
let equal : t -> t -> bool = (=)
