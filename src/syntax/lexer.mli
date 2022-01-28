
type t = Token.t Lstream.t

module S = Lstream

val create : ?loc_offset:int -> file:string -> string -> t
(** Create a new lexer.
    @param loc_offset is added to all locations. Default 0. *)
