
(** {1 Locations}

    A location is a range between two positions in a string (a source file).
*)

open Sigs

type t = {
  file: string;
  start: Position.t;
  end_: Position.t;
}

val mk : string -> int -> int -> int -> int -> t
val mk_pair : string -> int*int -> int*int -> t

include PP with type t := t
val pp_opt : t option Fmt.printer
val none : t

val single : ?file:string -> Position.t -> t
val merge: t -> t -> t
val contains : t -> Position.t -> bool

module Infix : sig
  val (++) : t -> t -> t
  (** Short for merge *)
end
include module type of Infix

(**/**)
val set_file : Lexing.lexbuf -> string -> unit
val of_lexbuf : Lexing.lexbuf -> t
(**/**)
