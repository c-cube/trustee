
val set_level : int -> unit
val get_level : unit -> int
val debugf : int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit
val debug : int -> string -> unit
val set_debug_out : Format.formatter -> unit

(**/**)
val mutex_ : Mutex.t option ref
(**/**)
