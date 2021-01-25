
(** {1 Locations}

    A location is a range between two positions in a string (a source file).
*)

open Sigs

type t = {
  file: string;
  start: Position.t;
  end_: Position.t;
}

include PP with type t := t
val none : t

val single : ?file:string -> Position.t -> t
val merge: t -> t -> t
val contains : t -> Position.t -> bool

module Infix : sig
  val (++) : t -> t -> t
  (** Short for merge *)
end
include module type of Infix
