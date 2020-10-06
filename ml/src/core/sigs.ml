
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

exception Error of unit Fmt.printer * exn option

let error ?src msg = raise (Error ((fun out () -> Fmt.string out msg), src))
let errorf ?src k : 'a =
  let pp out () = k (fun fmt ->
      Fmt.kfprintf (fun _o -> ()) out fmt)
  in
  raise (Error (pp, src))

let pp_list ?(sep=" ") ppx out l =
  Fmt.list ~sep:(fun out () -> Fmt.fprintf out "@;%s" sep) ppx out l

module Str_tbl = CCHashtbl.Make(CCString)
