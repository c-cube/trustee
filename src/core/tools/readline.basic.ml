

let init () = ()
let hist_add _ = ()
let with_ f = f()
let read_line pr =
  Printf.printf "%s%!" pr;
  try Some (input_line stdin)
  with End_of_file -> None
