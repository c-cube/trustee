
open Common_

type t = private {
  loc: Loc.t;
  view: view;
}
and view =
  | Atom of string
  | List of t list
  | Dollar of string
  | Error of Error.t
type sexp = t

val pp : t Fmt.printer
val to_string : t -> string

module Parse : sig
  type t

  val create : filename:string -> string -> t

  val parse1 : t -> sexp option

  val parse : t -> sexp list
end

val of_string : filename:string -> string -> sexp option
val of_string_l : filename:string -> string -> sexp list


