type state

val create : St.t -> port:int -> state
val active_connections : state -> int
val active : state -> bool
val serve : state -> unit
