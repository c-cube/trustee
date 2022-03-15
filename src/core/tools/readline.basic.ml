

let enabled_ = ref false
let init () = enabled_ := true
let hist_add _ = ()
let with_ f = init(); f()
let read_line pr =
  if !enabled_ then Printf.printf "%s%!" pr;
  try Some (input_line stdin)
  with End_of_file -> None
