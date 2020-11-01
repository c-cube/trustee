
(** {1 Positions}

    A position in a string. Line and column are 1-based, so that compatibility
    with LSP is easier. *)

open Sigs

type t = {
  line: int;
  col: int;
}

include PP with type t := t
val none : t

val leq : t -> t -> bool
val min : t -> t -> t
val max : t -> t -> t
