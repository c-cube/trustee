
open Sigs
module P = Position

type t = {
  start: Position.t;
  end_: Position.t;
}

let pp out (self:t) : unit =
  if self.start.P.line = self.end_.P.line then (
    Fmt.fprintf out "%d:%d-%d" self.start.P.line self.start.P.col self.end_.P.col
  ) else (
    Fmt.fprintf out "%d:%d-%d:%d"
      self.start.P.line self.start.P.col self.end_.P.line self.end_.P.col
  )
let to_string = Fmt.to_string pp

let none : t = {start=P.none; end_=P.none}
let single p = {start=p; end_=p}

let merge a b = {start=P.min a.start b.start; end_=P.max a.end_ b.end_}
let contains self p : bool =
  P.leq self.start p && P.leq p self.end_

module Infix = struct
  let (++) = merge
end
include Infix
