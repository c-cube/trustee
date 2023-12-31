type t = private {
  path: string list;
  name: string;
}

val unescape : string -> string
(** Remove quotes around a string of the form ["foo"] *)

include PP with type t := t

val of_string : string -> t
