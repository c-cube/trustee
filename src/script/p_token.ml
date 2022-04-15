
type t =
  | EOI
  | IDENT of string
  | COLON_STR of string
  | QUOTED_STR of string
  | INT of string
  | VAR
  | LET
  | SEMI
  | FN
  | EQUAL
  | COMMA
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | LBRACE
  | RBRACE
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | LT
  | LEQ
  | GT
  | GEQ
  [@@deriving show {with_path=false}]

type token = t [@@deriving show]
