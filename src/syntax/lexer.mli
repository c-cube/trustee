type t = Token.t Lstream.t

module S = Lstream

val create : ?loc_offset:int -> ?src_string:string -> file:string -> string -> t
(** [create ~file str] creates a new lexer on the string [src].
    @param loc_offset is added to all locations. Default 0.
    @param src_string string used for location reporting (default is to use [str]).
      offsets and loc_offset are relative to this string.
*)
