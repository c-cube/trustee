
open Sigs

type position = Position.t
type t = {
  start: position;
  stop: position;
  file: string option;
}

val pp : t Fmt.printer
val none : t
