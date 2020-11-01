open Sigs

type t = {
  line: int;
  col: int;
}

let none = {line=1; col=1}
let pp out (p:t) : unit =
  Fmt.fprintf out "%d:%d" p.line p.col
let to_string = Fmt.to_string pp
let leq a b = a.line < b.line || (a.line=b.line && a.col <= b.col)
let min a b = if leq a b then a else b
let max a b = if leq a b then b else a
