
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
  "VM checker for Trustee.\n\
   \n\
   Special functions:\n\
  \ - 'help' to display this\n\
  \ - 'show' to pop top value and display it\n\
  \ - 'dump' to display the VM's state\n\
  "

let debug = ref false

let debug_hook vm i =
  Fmt.eprintf "@[<2>exec `%a`@ in %a@]@." VM.Instr.pp i VM.dump vm

let pp_err err =
  Fmt.eprintf "%a@." Error.pp err

let main (files:string Vec.t) =
  let ctx = K.Ctx.create() in
  let vm = VM.create ~ctx () in
  let env = ref VM.Scoping_env.empty in
  if !debug then VM.set_debug_hook vm debug_hook;

  let eval_stanza stanza =
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
  in

  let read_file file =
    let str = CCIO.with_in file CCIO.read_all in
    let p = VM.Parser.create ~prims str in
    let env', stanzas = VM.Parser.parse_stanzas p ~env:!env in
    env := env';
    let stanzas = match stanzas with
      | Ok v -> v
      | Error err ->
        pp_err err;
        exit 1
    in
    Vec.iter eval_stanza stanzas;
  in

  Vec.iter read_file files;
  ()

let () =
  Sys.catch_break true;

  let color = ref true in
  let files = Vec.create() in
  let args = [
    "--debug", Arg.Set debug, " enable debug";
    "-nc", Arg.Clear color, " disable colored output";
  ] |> Arg.align in
  Arg.parse args (Vec.push files) "check [opt*]";
  if !color then Fmt.set_color_default true;
  main files

