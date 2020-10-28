
open Trustee_core
open Sigs

module Cat = struct
  let args = [
    "-d", Arg.Int Log.set_level, " debug level";
  ] |> Arg.align

  let run args =
    Log.debugf 1 (fun k->k"cat files %a" (Fmt.Dump.(list string)) args);
    () (* TODO: parse and print *)

end


let cmds = [
  "cat", (Cat.args, Cat.run);
]

let () =
  let args = ref [] in
  let anon_args = ref [] in
  let r = ref None in
  let help =
    Fmt.asprintf "@[<v>trustee_tk <cmd> [arg]*.@,@,Available commands:@ %a@]@."
      (pp_list (fun out (a,_) ->
           Fmt.fprintf out "@[<2>- %a@]@," Fmt.text a)) cmds
  in
  Arg.parse_dynamic args
    (fun s ->
       if CCOpt.is_some !r then (
         anon_args := s :: !anon_args
       ) else (
         match List.assoc s cmds with
         | exception Not_found ->
           raise (Arg.Bad "unknown command")
         | (args',r') ->
           args := args';
           r := Some r'
       ))
    help;
  match !r with
  | None -> Fmt.eprintf "please provide a command@."; exit 1
  | Some r -> r (List.rev !anon_args)

