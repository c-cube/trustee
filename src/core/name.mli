

(** Symbols *)

type t

val make : string -> t
val equal_str : t -> string -> bool
val to_string : t -> string

include Sigs.EQ with type t := t
include Sigs.COMPARE with type t := t
include Sigs.HASH with type t := t
include Sigs.PP with type t := t

module Map : CCMap.S with type key = t
