open Sigs

type t = {
  line: int;
  col: int;
}

val pp : t Fmt.printer
val none : t
