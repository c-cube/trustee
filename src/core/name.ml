
open Sigs

module H = CCHash
type t = string
let equal = String.equal
let equal_str = equal
let compare = String.compare
let hash = H.string
let pp = Fmt.string
let make s = s
let to_string s = s

module Map = Str_map
