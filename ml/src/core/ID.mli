
(** {1 Generative Identifiers}

  This is a representation of a name that is unambiguous even in the presence
  of scoping *)

open Sigs

type t

val make : string -> t
val makef : ('a, Format.formatter, unit, t) format4 -> 'a
val copy : t -> t

val id : t -> int
val name : t -> string

include Sigs.EQ with type t := t
include Sigs.HASH with type t := t
include Sigs.COMPARE with type t := t
include Sigs.PP with type t := t

module Set : CCSet.S with type elt = t
module Map : CCMap.S with type key = t
module Tbl : CCHashtbl.S with type key = t
