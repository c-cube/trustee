
type t = Token.t Lstream.t

module S = Lstream

val create : file:string -> string -> t
