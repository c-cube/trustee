
module Fmt = CCFormat
open Trustee_core
module K = Kernel

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

let prims = [
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

let pp_err err =
  Fmt.eprintf "%a@." Error.pp err

let main () =
  let ctx = K.Ctx.create() in
  let vm = VM.create ~ctx () in
  let env = ref VM.Scoping_env.empty in
  if !debug then VM.set_debug_hook vm debug_hook;

  let parse_stanza_str str =
    let e, r = VM.parse_stanza_string ~prims !env str in
    env := e;
    if !debug then Format.eprintf "new env: %a@." VM.Scoping_env.pp !env;
    match r with
    | Error err ->
      pp_err err;
      None
    | Ok c -> Some c
  in

  let parse_chunk_str str =
    match VM.parse_chunk_string ~prims !env str with
    | Error err ->
      pp_err err;
      None
    | Ok c -> Some c
  in

  let eval_chunk ~env ~vm c =
    if !debug then Fmt.eprintf "### eval chunk@.";
    try
      VM.run vm c;
    with
    | Error.E err ->
      pp_err err;
    | e ->
      Printf.eprintf "exception: %s\n%!" (Printexc.to_string e)
  in

  let read_multiline line0 =
    let buf = Buffer.create 32 in
    Buffer.add_string buf line0;
    while VM.Parser.needs_more (Buffer.contents buf) do
      match Readline.read_line ".. " |> Option.map String.trim with
      | None -> raise End_of_file
      | Some "" -> ()
      | Some s ->
        if !readline then Readline.hist_add s;
        Buffer.add_char buf '\n';
        Buffer.add_string buf s
    done;
    Buffer.contents buf
  in

  let continue = ref true in
  while !continue do
    match Readline.read_line "> " |> Option.map String.trim with
    | Some "" -> ()

    (* do not even compile the following pragmas *)

    | Some "reset" -> VM.reset vm;
    | Some "dump" -> Fmt.printf "%a@." VM.dump vm;
    | Some ("help" as str) -> if !readline then Readline.hist_add str; print_endline help;

    | Some line ->
      if !readline then Readline.hist_add line;
      let code = read_multiline line in

      begin match parse_stanza_str code with
        | None -> ()
        | Some stanza ->

          if !debug then Format.eprintf "parsed stanza %a@." VM.Stanza.pp stanza;

          (* run [c] in a different VM to get the value *)
          let vm' = VM.create ~ctx () in
          if !debug then VM.set_debug_hook vm' debug_hook;

          VM.eval_stanza vm stanza;

          (* TODO
          (* assign result of evaluation to [k] *)
          let v = VM.pop_exn vm' in
          VM.set_env vm (VM.get_env vm |> VM.Env.add name v);
             *)
      end;
    | None -> continue := false
    | exception End_of_file -> continue := false
    | exception Sys.Break -> continue := false
    | exception Error.E err ->
      pp_err err;
  done;
  ()

let () =
  Sys.catch_break true;

  let color = ref true in
  let args = [
    "--raw", Arg.Clear readline, " disable readline";
    "--debug", Arg.Set debug, " enable debug";
    "-nc", Arg.Clear color, " disable colored output";
  ] |> Arg.align in
  Arg.parse args ignore "repl [opt*]";
  if !color then Fmt.set_color_default true;

  if !readline then Readline.with_ main else main()
