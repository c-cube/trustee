
module Stdlib = CCShims_.Stdlib
module Option = CCOpt
module Fmt = CCFormat

type 'a iter = ('a -> unit) -> unit

module type EQ = sig
  type t
  val equal : t -> t -> bool
end

module type COMPARE = sig
  type t
  val compare : t -> t -> int
end

module type HASH = sig
  type t
  val hash : t -> int
end

module type PP = sig
  type t
  val pp : t Fmt.printer
  val to_string : t -> string
end

module type SER = sig
  type t
  val enc : t Cbor_pack.Enc.t
  val dec : t Cbor_pack.Dec.t
end

module type SER1 = sig
  type t
  type state
  val enc : t Cbor_pack.Enc.t
  val dec : state -> t Cbor_pack.Dec.t
end

let pp_list ?(sep=" ") ppx out l =
  Fmt.list ~sep:(fun out () -> Fmt.fprintf out "%s@," sep) ppx out l
let pp_iter ?(sep=" ") ppx out iter =
  Fmt.iter ~sep:(fun out () -> Fmt.fprintf out "%s@," sep) ppx out iter

let[@inline] (let@) f x = f x

module Str_tbl = CCHashtbl.Make(CCString)
module Str_map = CCMap.Make(CCString)
module Str_set = CCSet.Make(CCString)
