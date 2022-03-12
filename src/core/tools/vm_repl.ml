
module Fmt = CCFormat
open Trustee_core

let dump =
  VM.Primitive.make ~name:"dump"
    ~eval:(fun vm -> Fmt.printf "%a@." VM.dump vm)
    ()

let reset =
  VM.Primitive.make ~name:"reset"
    ~eval:(fun vm -> VM.reset vm)
    ()

let prims = [
  dump;
  reset;
] |> List.map (fun p -> VM.Primitive.name p, p)
  |> Str_map.of_list

let () =
  Sys.catch_break true;
  Readline.with_ @@ fun () ->

  let vm = VM.create() in

  let continue = ref true in
  while !continue do
    match Readline.read_line "> " |> Option.map String.trim with
    | Some "" -> ()
    | Some line ->
      (* FIXME: have a syntax to modify env, like `SET foo …` *)
      begin match VM.parse_string ~prims line with
        | Error err ->
          Fmt.printf "Error: %a@." Error.pp err
        | Ok c ->
          Readline.hist_add line;
          begin
            try
              VM.run vm c;
            with e ->
              Printf.eprintf "exception: %s\n%!" (Printexc.to_string e)
          end
      end
    | None -> continue := false
    | exception Sys.Break -> continue := false
  done;
  ()
