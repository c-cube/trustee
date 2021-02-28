
type t = private {
  path: string list;
  name: string;
}

(** Remove quotes around a string of the form ["foo"] *)
val unescape : string -> string

include PP with type t := t

val of_string : string -> t
