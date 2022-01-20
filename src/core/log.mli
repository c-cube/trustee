
val set_level : int -> unit

type logger = {
  log: 'a. int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit;
} [@@unboxed]

val void_logger : logger

val set_logger : logger -> unit

val debugf : int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit
val debug : int -> string -> unit

