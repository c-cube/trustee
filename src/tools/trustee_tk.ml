
open Trustee_core.Sigs

module Log = Trustee_core.Log
module K = Trustee_core.Kernel
module A = Trustee_core.Parse_ast
module TA = Trustee_core.Type_ast
module Syntax = Trustee_core.Syntax
module Loc = Trustee_core.Loc

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

module Check = struct
  let args = [
    "-d", Arg.Int Log.set_level, " debug level";
  ] |> Arg.align

  let run args =
    Log.debugf 1 (fun k->k"check files %a" (Fmt.Dump.(list string)) args);
    let ctx = K.Ctx.create() in
    let aenv = A.Env.create ctx in
    let tyenv = ref @@ TA.Env.create ctx in
    List.iter
      (fun file ->
         match CCIO.File.read file with
         | Ok s ->
           let lex = Syntax.Lexer.create ~file s in
           Fmt.printf "# file %S@." file;
           let l = Syntax.parse_top_l_process ~file ~env:aenv lex in
           let tyenv', _ =
             CCList.fold_left
               (fun env st ->
                  TA.process_stmt ~index:false
                    ~on_show:(fun loc pp ->
                        Fmt.printf "@[<2>@{<bold>>>> Show@}: at %a:@ %a@]@."
                          Loc.pp loc pp())
                    ~on_error:(fun loc pp ->
                        Fmt.printf "@[<2>@{<Red>Error@} at %a:@ %a@]@."
                          Loc.pp loc pp())
                    env st)
               (!tyenv, TA.Index.empty) l
           in
           tyenv := tyenv';
           Fmt.printf "# processed %S@." file;
         | Error e ->
           errorf (fun k->k"cannot read '%s': %s" file e))
      args;
    ()

end


let cmds = [
  "cat", (Cat.args, Cat.run);
  "check", (Check.args, Check.run);
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
  Fmt.set_color_default true;
  match !r with
  | None -> Fmt.eprintf "please provide a command@."; exit 1
  | Some r -> r (List.rev !anon_args)

