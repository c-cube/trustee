
val set_level : int -> unit
val get_level : unit -> int

type logger = {
  log: 'a. int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit;
}

val void_logger : logger
val formatter_logger : Format.formatter -> logger

val log_to_file : filename:string -> unit
(** [log_to_file ~filename] sets a logger to print into the given file. *)

val set_logger : logger -> unit

val debugf : int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit
val debug : int -> string -> unit

