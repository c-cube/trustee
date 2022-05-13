
open Sigs

type t = {
  name: string;
  chash : Chash.t;
}

val make : string -> Chash.t -> t
val name : t -> string
val chash : t -> Chash.t
val chasher : t Chash.hasher

val pp_name : t Fmt.printer

include PP with type t := t
include EQ with type t := t
include COMPARE with type t := t
include HASH with type t := t

val enc : t Cbor_pack.Enc.t
val dec : t Cbor_pack.Dec.t

