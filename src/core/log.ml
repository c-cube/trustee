
let enabled = true (* change here to get 0 overhead *)

let debug_level_ = ref 0
let set_level l = debug_level_ := l
let get_level () = !debug_level_

type logger = {
  log: 'a. int -> ((('a, Format.formatter, unit, unit) format4 -> 'a) -> unit) -> unit;
}

let void_logger : logger = {
  log=fun _ _ -> ();
}

let formatter_logger out : logger =
  let start = Unix.gettimeofday() in
  { log=fun l k ->
    k (fun fmt ->
      Format.fprintf out "@[<2>@{<Blue>[%d|%.3f]@}@ "
        l (Unix.gettimeofday() -. start);
      Format.kfprintf
        (fun fmt -> Format.fprintf fmt "@]@.")
        out fmt)
  }

let logger_ = ref (formatter_logger Format.err_formatter)
let set_logger l = logger_ := l

let log_to_file ~filename : unit =
  let oc = open_out filename in
  let fmt = Format.formatter_of_out_channel oc in
  set_logger (formatter_logger fmt);
  at_exit (fun () ->
      Format.fprintf fmt "@?"; (* flush *)
      flush oc; close_out_noerr oc)

let[@inline] debugf l k =
  if enabled && l <= !debug_level_ then (
    (!logger_).log l k
  )

let[@inline] debug l msg = debugf l (fun k->k "%s" msg)
