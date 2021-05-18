
(* TODO: make this a super basic function reference;
   use [Logs] in applications *)

let enabled = true (* NOTE: change here for 0-overhead *)

let start_ = Unix.gettimeofday()

let debug_level_ = ref 0
let set_level l = debug_level_ := l
let get_level () = !debug_level_

let debug_fmt_ = ref Format.err_formatter

let set_debug_out f = debug_fmt_ := f
let mutex_ = ref None

(* does the printing, inconditionally *)
let debug_real_ l k =
  let mut = !mutex_ in
  k (fun fmt ->
    CCOpt.iter Mutex.lock mut;
    Format.fprintf !debug_fmt_ "@[<2>@{<Blue>[%d|%.3f]@}@ "
      l (Unix.gettimeofday() -. start_);
    Format.kfprintf
      (fun fmt -> Format.fprintf fmt "@]@."; CCOpt.iter Mutex.unlock mut)
      !debug_fmt_ fmt)

let[@inline] debugf l k =
  if enabled && l <= !debug_level_ then (
    debug_real_ l k;
  )

let[@inline] debug l msg = debugf l (fun k->k "%s" msg)
