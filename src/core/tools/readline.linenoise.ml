
let warn_ = function
  | Ok x -> x
  | Error err -> Printf.eprintf "readline: warning: %s\n%!" err

let filename = ".vm-repl.hist"

let with_ f =
  LNoise.history_load ~filename |> warn_;
  LNoise.history_set ~max_length:1000 |> warn_;
  CCFun.protect ~finally:(fun () -> LNoise.history_save ~filename |> warn_) f

let hist_add s : unit = LNoise.history_add s |> ignore

let read_line pr =
  LNoise.linenoise pr

