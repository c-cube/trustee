module Fmt = CCFormat

let () = assert (Sys.int_size = 63)

type t = int

let n_bits = 22
let mask_low = (1 lsl n_bits)-1

let col (self:t) = self land mask_low
let line (self:t) = self lsr n_bits

let pp out (self:t) : unit =
  Fmt.fprintf out "%d:%d" (line self) (col self)
let show = Fmt.to_string pp

let make ~line ~col : t =
  assert (col < mask_low);
  (line lsl n_bits) lor col

let none = make ~line:1 ~col:1
let (<=) a b = line a < line b || (line a=line b && col a <= col b)
let (<) a b = line a < line b || (line a=line b && col a < col b)
let (=) = (=)
let min a b = if a <= b then a else b
let max a b = if a <= b then b else a
