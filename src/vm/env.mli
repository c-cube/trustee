
type value = Value.t

type t

val empty : t

val parent : t -> t option

val add : t -> string -> value -> t

val find : t -> string -> value option
