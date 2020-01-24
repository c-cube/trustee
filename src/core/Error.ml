
module Fmt = CCFormat

exception Error of string

let error s = raise (Error s)
let errorf fmt = Fmt.kasprintf error fmt

let () =
  Printexc.register_printer
    (function
      | Error msg -> Some (Fmt.asprintf "@{<Red>Error@}: %s" msg)
      | _ -> None)
