
(** Cbor-pack *)

(** CBOR value.

    Compatible with the "CBOR.Simple" module. *)
type cbor =
  [ `Array of cbor list
  | `Bool of bool
  | `Bytes of string
  | `Float of float
  | `Int of int
  | `Map of (cbor * cbor) list
  | `Null
  | `Simple of int
  | `Tag of int * cbor
  | `Text of string
  | `Undefined ]

type t = {
  h: cbor Vec.t; (* heap *)
  k: cbor; (* key *)
}

type cbor_pack = t

module Enc : sig
  type encoder

  type ptr = cbor

  val int : int -> cbor

  val bool : bool -> cbor

  val list : cbor list -> cbor

  val text : string -> cbor

  val blob : string -> cbor

  val map : (cbor * cbor) list -> cbor

  val add_entry : encoder -> cbor -> ptr

  val init : unit -> encoder

  val finalize : encoder -> key:cbor -> cbor_pack

  type 'a t = encoder -> 'a -> cbor
end

module Dec : sig
  type 'a t

  val fix : ('a t -> 'a t) -> 'a t

  val return : 'a -> 'a t

  val fail : string -> _ t

  val value : cbor t

  val int : int t

  val bool : bool t

  val text : string t

  val blob : string t

  val field : string -> 'a t -> 'a t

  val list : 'a t -> 'a list t

  val apply : 'a t -> cbor -> 'a t

  val (let+) : 'a t -> ('a -> 'b) -> 'b t

  val (and+) : 'a t -> 'b t -> ('a * 'b) t

  val (let* ) : 'a t -> ('a -> 'b t) -> 'b t

  val run : 'a t -> cbor_pack -> ('a, string) result
end


