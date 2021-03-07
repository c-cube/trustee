
(** {1 Interpretation files}

    See http://www.gilith.com/opentheory/interpretation.html
*)

type item =
  | I_ty of string * string
  | I_const of string * string

type t = {
  items: item list;
}

val size : t -> int

val pp : t Fmt.printer

module P = CCParse

val parse_item : item P.t

val parse : t P.t
val of_string : string -> t or_error
