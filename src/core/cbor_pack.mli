
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

  val pair : cbor -> cbor -> cbor

  val text : string -> cbor

  val blob : string -> cbor

  val map : (cbor * cbor) list -> cbor

  val add_entry : encoder -> cbor -> ptr

  val init : unit -> encoder

  val finalize : encoder -> key:cbor -> cbor_pack

  type 'a t = encoder -> 'a -> cbor

  type 'a key

  val make_key : (module Hashtbl.HashedType with type t = 'a) -> 'a key

  val memo : 'a key -> 'a t -> 'a t
  (** Memoized encoder using a key for finding if an entry exists
    for this value *)
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

  val pair : 'a t -> 'b t -> ('a * 'b) t

  val map : 'a t -> 'b t -> ('a * 'b) list t

  val apply : 'a t -> cbor -> 'a t

  val apply_l : 'a t -> cbor list -> 'a list t

  val delay : (unit -> 'a t) -> 'a t

  type 'a key

  val make_key : unit -> 'a key

  val memo : 'a key -> 'a t -> 'a t

  val (let+) : 'a t -> ('a -> 'b) -> 'b t

  val (and+) : 'a t -> 'b t -> ('a * 'b) t

  val (let* ) : 'a t -> ('a -> 'b t) -> 'b t

  val run : 'a t -> cbor_pack -> ('a, string) result
end

val encode : 'a Enc.t -> 'a -> cbor

val encode_to_string : 'a Enc.t -> 'a -> string

val cbor_to_string : cbor -> string

val decode : 'a Dec.t -> cbor -> ('a, string) result

val decode_string : 'a Dec.t -> string -> ('a, string) result

val decode_string_exn : 'a Dec.t -> string -> 'a
(** Same as {!decode_string} but can raise
    @raise Failure if decoding failed. *)

val cbor_of_string : string -> cbor
