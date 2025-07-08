(** Cryptographic hash *)

open Sigs

type t

include PP with type t := t
include EQ with type t := t
include COMPARE with type t := t
include HASH with type t := t

type ctx
(** Context to build a hash *)

val create : unit -> ctx
val finalize : ctx -> t
val dummy : t
val of_string_exn : string -> t

type 'a hasher = ctx -> 'a -> unit

val run : 'a hasher -> 'a -> t
val string : ctx -> string -> unit
val int : ctx -> int -> unit
val sub : ctx -> t -> unit
val enc : t Cbor_pack.Enc.t
val dec : t Cbor_pack.Dec.t

module Tbl : CCHashtbl.S with type key = t

val unsafe_to_bytes : t -> bytes
val unsafe_of_bytes : bytes -> t
