
(** {1 Interpretation files}

    See http://www.gilith.com/opentheory/interpretation.html
*)

open Common_
type 'a or_error = 'a Trustee_core.Error.or_error

type item =
  | I_ty of string * string
  | I_const of string * string

type t = item list

val size : t -> int
val items_iter : t -> item Iter.t
val is_empty : t -> bool

val pp : t Fmt.printer

val to_html : t -> Html.elt

module P = CCParse

val parse_item : item P.t
val item_of_string : string -> item or_error

val parse : t P.t
val of_string : string -> t or_error
