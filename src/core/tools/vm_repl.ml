
module Fmt = CCFormat
open Trustee_core

let show =
  VM.Primitive.make ~name:"show"
    ~eval:(fun vm ->
        let v = VM.pop_exn vm in
        Fmt.printf "%a@." VM.Value.pp v
    )
    ()

let dump =
  VM.Primitive.make ~name:"dump"
    ~eval:(fun vm -> Fmt.printf "%a@." VM.dump vm)
    ()

let setenv =
  VM.Primitive.make ~name:"setenv"
    ~eval:(fun vm ->
        let key = VM.pop_exn vm |> VM.Value.to_str_exn in
        let v = VM.pop_exn vm in
        Fmt.printf "assigning %s@." key;
        let env = VM.get_env vm |> VM.Env.add key v in
        VM.set_env vm env;
    )
    ()

let prims = [
  setenv;
  show;
  dump;
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

    (* do not even compile the following pragmas *)

    | Some "reset" -> VM.reset vm;
    | Some "dump" -> Fmt.printf "%a@." VM.dump vm;

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
            with
            | Error.E err ->
              Fmt.eprintf "%a@." Error.pp err;
            | e ->
              Printf.eprintf "exception: %s\n%!" (Printexc.to_string e)
          end
      end
    | None -> continue := false
    | exception Sys.Break -> continue := false
  done;
  ()
