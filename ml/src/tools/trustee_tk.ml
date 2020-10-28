
open Trustee_core.Sigs

module Log = Trustee_core.Log
module K = Trustee_core.Kernel
module A = Trustee_core.Parse_ast
module Syntax = Trustee_core.Syntax

module Cat = struct
  let args = [
    "-d", Arg.Int Log.set_level, " debug level";
  ] |> Arg.align

  let run args =
    Log.debugf 1 (fun k->k"cat files %a" (Fmt.Dump.(list string)) args);
    let ctx = K.Ctx.create() in
    let env = A.Env.create ctx in
    List.iter
      (fun file ->
         match CCIO.File.read file with
         | Ok s ->
           let lex = Syntax.Lexer.create s in
           let l = Syntax.parse_top_l_process ~file ~env lex in
           Fmt.printf "# file %S@." file;
           Fmt.printf "@[<v>%a@]@." (pp_list A.Top_stmt.pp) l
         | Error e ->
           errorf (fun k->k"cannot read '%s': %s" file e))
      args;
    ()

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

