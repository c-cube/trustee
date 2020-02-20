
open Trustee
module P = Trustee_syn.Parse

let hist_file =
  try Sys.getenv "HOME" ^ "/.trustee-hist"
  with Not_found -> "/tmp/.trustee-hist"

let fail_err_ = function
  | Ok () -> ()
  | Error msg -> failwith msg

let warn_err_ = function
  | Ok () -> ()
  | Error msg -> Format.printf "warning: %s@." msg

let process_statement _ctx s =
  match s with
  | Statement.St_load_opentheory p ->
    let art =
      CCIO.with_in p
        (fun ic -> CCIO.read_lines_gen ic |> Open_theory.parse_gen_exn) in
    Format.printf "@[<1>article:@ %a@]@." Open_theory.Article.pp art
  | Statement.St_decl _ -> ()
  | Statement.St_prove _ ->
    Format.printf "@{<Yellow> TODO@}: proof system@."

let load_file ctx file =
  Format.printf "loading %S…@." file;
  match
    let s = CCIO.with_in file CCIO.read_all in
    P.parse_statement_l_exn ctx s
  with
  | exception e ->
    Format.printf "error when loading %S: %s" file (Printexc.to_string e)
  | l -> List.iter (process_statement ctx) l

let loop ~to_load ctx =
  let rec loop () =
    match LNoise.linenoise "> " |> CCOpt.map String.trim with
    | exception Sys.Break -> loop ()
    | None -> print_endline "bye!"
    | Some "" -> loop ()
    | Some s ->
      LNoise.history_add s |> ignore;
      match P.parse_statement ctx s with
      | Error s ->
        Format.printf "parse error: %s@." s;
        loop ()
      | Ok s ->
        Format.printf "%a@." Statement.pp s;
        begin try
            process_statement ctx s;
          with Trustee.Error msg ->
            Format.printf "@[<1>@{<Red>Error@}:@ %a@]@." msg ()
        end;
        loop ()
  in
  List.iter (load_file ctx) to_load;
  loop ()

let () =
  let to_load = ref [] in
  let opts = [
    "--load", Arg.String (CCList.Ref.push to_load), " load given script";
    "-bt", Arg.Unit (fun () -> Printexc.record_backtrace true), " record backtraces";
  ] |> Arg.align in
  Arg.parse opts
    (fun _ -> raise (Arg.Bad "no arguments")) "cli [option*]";
  CCFormat.set_color_default true;
  LNoise.history_load ~filename:hist_file |> warn_err_;
  LNoise.history_set ~max_length:1000 |> warn_err_;
  LNoise.catch_break true;
  let ctx = Statement.Ctx.create() in
  CCFun.finally
    ~h:(fun () ->
        LNoise.history_save ~filename:hist_file |> warn_err_)
    ~f:(fun () -> loop ~to_load:(List.rev !to_load) ctx)
