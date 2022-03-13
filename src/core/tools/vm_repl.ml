
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

let help =
  "VM repl for Trustee.\n\
   Each line is interpreted separately.\n\
   \n\
   Special commands:\n\
  \ - 'help' to display this\n\
  \ - 'reset' to reset the VM\n\
  \ - 'dump' to display the VM's state\n\
  \ - 'set x …' sets 'x' to the (top) result of evaluating the RHS\n\
  "

let debug = ref false
let readline = ref true

let debug_hook vm i =
  Fmt.eprintf "@[<2>exec `%a`@ in %a@]@." VM.Instr.pp i VM.dump vm

let main () =
  let vm = VM.create() in
  if !debug then VM.set_debug_hook vm debug_hook;

  let parse_str str =
    match VM.parse_string ~prims str  with
    | Error err ->
      Fmt.printf "Error: %a@." Error.pp err;
      None
    | Ok c -> Some c
  in

  let eval_chunk ~vm c =
    if !debug then Fmt.eprintf "### eval chunk@.";
    try
      VM.run vm c;
    with
    | Error.E err ->
      Fmt.eprintf "%a@." Error.pp err;
    | e ->
      Printf.eprintf "exception: %s\n%!" (Printexc.to_string e)
  in

  let continue = ref true in
  while !continue do
    match Readline.read_line "> " |> Option.map String.trim with
    | Some "" -> ()

    (* do not even compile the following pragmas *)

    | Some "reset" -> VM.reset vm;
    | Some "dump" -> Fmt.printf "%a@." VM.dump vm;
    | Some ("help" as str) -> Readline.hist_add str; print_endline help;

    | Some line when CCString.prefix ~pre:"set " line ->
      Readline.hist_add line;

      let _, rest = CCString.Split.left_exn ~by:" " line in
      let name, rest = CCString.Split.left_exn ~by:" " rest in
      let name = String.trim name in

      begin match parse_str rest with
        | None -> ()
        | Some c ->

          (* run [c] in a different VM to get the value *)
          let vm' = VM.create ~env:(VM.get_env vm) () in
          if !debug then VM.set_debug_hook vm' debug_hook;

          eval_chunk ~vm:vm' c;

          (* assign result of evaluation to [k] *)
          let v = VM.pop_exn vm' in
          VM.set_env vm (VM.get_env vm |> VM.Env.add name v);
          Fmt.printf "defined %S@." name;
      end;

    | Some line ->
      Readline.hist_add line;

      begin match parse_str line with
        | None ->()
        | Some c -> eval_chunk ~vm c
      end
    | None -> continue := false
    | exception Sys.Break -> continue := false
  done;
  ()

let () =
  Sys.catch_break true;

  let args = [
    "--raw", Arg.Clear readline, " disable readline";
    "--debug", Arg.Set debug, " enable debug";
  ] |> Arg.align in
  Arg.parse args ignore "repl [opt*]";

  if !readline then Readline.with_ main else main()
