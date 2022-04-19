
(** Parser for the basic syntax.

    This syntax is, for now, only intended for testing and possibly as
    an internal compilation target. *)

open Sigs

type chunk = VM.Chunk.t
type stanza = VM.Stanza.t

(** Scoping environment for the virtual machine.

    This environment contains local names, and is required for parsing.
*)
module Scoping_env : sig
  type t
  (** A persistent env *)

  val empty : t

  val pp : t Fmt.printer
end

(** Parser state *)
type t

val create :
  ?prims:VM.Primitive.t Str_map.t ->
  string -> t
(** [create ?prims str] creates a parser that will parse [str],
    using [prims] as the additional primitives *)

val needs_more : string -> bool

val parse_chunk : t -> env:Scoping_env.t -> (chunk, Error.t) result

val parse_stanzas :
  t -> env:Scoping_env.t ->
  Scoping_env.t * (stanza Vec.t, Error.t) result

type primitive_map = VM.Primitive.t Str_map.t

val parse_chunk_string :
  ?prims:primitive_map ->
  Scoping_env.t -> string -> (chunk, Error.t) result

val parse_chunk_string_exn :
  ?prims:primitive_map ->
  Scoping_env.t -> string -> chunk

val parse_stanza_string :
  ?prims:primitive_map ->
  Scoping_env.t -> string -> Scoping_env.t * (stanza, Error.t) result

val parse_stanza_string_exn :
  ?prims:primitive_map ->
  Scoping_env.t -> string -> Scoping_env.t * stanza
