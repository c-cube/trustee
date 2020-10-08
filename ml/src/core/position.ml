open Sigs

type t = {
  line: int;
  col: int;
}

let none = {line=0; col=0}
let pp out (p:t) : unit =
  Fmt.fprintf out "%d:%d" p.line p.col
