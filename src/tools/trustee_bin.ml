
open Trustee_core.Sigs

module Log = (val Logs.src_log @@ Logs.Src.create "bin")

module TC = Trustee_core
module TS = Trustee_syntax
module ITP = Trustee_itp

module Error = Trustee_core.Error
module K = Trustee_core.Kernel
module A = Trustee_syntax.Parse_ast
module TA = Trustee_syntax.Type_ast

(*
; TODO: use cmdliner to provide subcommands ("check", "repl", "opentheory", etc.)
; along with relevant options for CI, repl, etc.
   *)

module Cat = struct
  let debug= ref false
  let args = [
    "-d", Arg.Set debug, " enable debug";
  ] |> Arg.align

  let run args =
    ITP.Logger.setup_logs ~debug:!debug ();
    Log.app (fun k->k"cat files %a" (Fmt.Dump.(list string)) args);
    let notation = TS.Notation.Ref.create_hol () in
    List.iter
      (fun file ->
         match CCIO.File.read file with
         | Ok s ->
           let lex = TS.Lexer.create ~file s in
           let l = TS.Parser.run_exn lex @@ TS.Syntax.parse_top_l ~notation () in
           Fmt.printf "# file %S@." file;
           List.iter (Fmt.printf "%a@." A.Top.pp) l;
         | Error e ->
           Error.failf (fun k->k"cannot read '%s': %s" file e))
      args;
    ()

end

(* TODO
module Check = struct
  let args = [
    "-d", Arg.Int Log.set_level, " debug level";
  ] |> Arg.align

  let run args =
    Log.debugf 1 (fun k->k"check files %a" (Fmt.Dump.(list string)) args);
    let aenv = A.Env.create () in
    let ctx = K.Ctx.create() in
    let tyst = TA.Typing_state.create ctx in
    List.iter
      (fun file ->
         match CCIO.File.read file with
         | Ok s ->
           let lex = Syntax.Lexer.create ~file s in
           Fmt.printf "# file %S@." file;
           let l = Syntax.parse_top_l_process ~file ~env:aenv lex in
           let _idx =
             CCList.fold_left
               (fun idx stmt ->
                  TA.process_stmt idx tyst
                    ~on_show:(fun loc pp ->
                        Fmt.printf "@[<2>@{<bold>>>> Show@}: at %a:@ %a@]@."
                          Loc.pp loc pp())
                    ~on_error:(fun loc pp ->
                        Fmt.printf "@[<2>@{<Red>Error@} at %a:@ %a@]@."
                          Loc.pp loc pp())
                    stmt)
               TA.Index.fake l
           in
           Fmt.printf "# processed %S@." file;
         | Error e ->
           errorf (fun k->k"cannot read '%s': %s" file e))
      args;
    ()

end
   *)

module OT_check = struct
  module Article = Trustee_opentheory.Article
  module VM = Trustee_opentheory.VM

  let cat_ = ref false
  let debug = ref false

  let args = [
    "-d", Arg.Set debug, " enable debug";
    "-cat", Arg.Set cat_, " print back the parsed articles";
  ] |> Arg.align

  let run args =
    ITP.Logger.setup_logs ~debug:!debug ();
    Log.app (fun k->k"check opentheory files %a" (Fmt.Dump.(list string)) args);
    let ctx = K.Ctx.create() in
    let vm = VM.create ~in_scope:[] ctx in
    try
      List.iter
        (fun file ->
           CCIO.with_in file (fun ic ->
               let input = VM.Input.of_chan ic in
               match VM.parse_and_check_art ~name:(Filename.basename file) vm input with
               | Ok (_, art) ->
                 Fmt.printf "; parsed and validated '%s'@." file;
                 if !cat_ then (
                   Fmt.printf "%a@." Article.pp art;
                 );
                 if not (VM.has_empty_stack vm) then (
                   Fmt.eprintf "VM stack is not empty@."; exit 1
                 );
                 VM.clear_dict vm; (* not reused *)
               | Error e ->
                 Fmt.eprintf "error: %a@." Error.pp e;
                 raise Exit
             ))
        args;
    with Exit ->
      exit 1

end


let cmds = [
  "cat", (Cat.args, Cat.run);
  (* TODO
  "check", (Check.args, Check.run);
     *)
  "ot-check", (OT_check.args, OT_check.run);
]

let () =
  Printexc.record_backtrace true;
  let args = ref [] in
  let anon_args = ref [] in
  let r = ref None in
  let help =
    Fmt.asprintf "@[<v>trustee_tk <cmd> [arg]*.@,@,Available commands:@ %a@]@."
      (pp_list (fun out (a,_) ->
           Fmt.fprintf out "@[<2>- %a@]" Fmt.text a)) cmds
  in
  Arg.parse_dynamic args
    (fun s ->
       if Option.is_some !r then (
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

