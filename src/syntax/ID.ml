open Common_

type t = {
  id: int;
  name: string;
}

let make =
  (* TODO: use some Atomic shim instead *)
  let n = ref 0 in
  fun name ->
    let x = { id = !n; name } in
    incr n;
    x

let makef fmt = Fmt.ksprintf ~f:make fmt
let[@inline] copy { name; _ } = make name
let[@inline] id id = id.id
let[@inline] name id = id.name
let[@inline] equal a b = a == b
let[@inline] compare a b = CCInt.compare a.id b.id
let[@inline] hash a = CCHash.int a.id

let pp_id_ =
  try
    match Sys.getenv "PP_ID" with
    | "1" | "true" -> true
    | _ -> false
  with _ -> false

let pp =
  if pp_id_ then
    fun out a ->
  Format.fprintf out "%s/%d" a.name a.id
  else
    fun out a ->
  Fmt.string out a.name

let to_string = Fmt.to_string pp

module AsKey = struct
  type nonrec t = t

  let equal = equal
  let compare = compare
  let hash = hash
end

module Map = CCMap.Make (AsKey)
module Set = CCSet.Make (AsKey)
module Tbl = CCHashtbl.Make (AsKey)
