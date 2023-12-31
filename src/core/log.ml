let enabled = true (* change here to get 0 overhead *)

let debug_level_ = ref 0

let set_level l = debug_level_ := l

type logger = {
  log:
    'a.
    int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit;
}
[@@unboxed]

let void_logger : logger = { log = (fun _ _ -> ()) }

let logger_ = ref void_logger

let set_logger l = logger_ := l

let[@inline] debugf l k = if enabled && l <= !debug_level_ then !logger_.log l k

let[@inline] debug l msg = debugf l (fun k -> k "%s" msg)
