
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
    Format.printf "article: %a@." Open_theory.Article.pp art
  | Statement.St_decl _ -> ()
  | Statement.St_prove _ ->
    Format.printf "@{<Yellow> TODO@}: proof system@."

let rec loop ctx =
  begin match LNoise.linenoise "> " |> CCOpt.map String.trim with
    | exception Sys.Break -> loop ctx
    | None -> print_endline "bye!"
    | Some "" -> loop ctx
    | Some s ->
      LNoise.history_add s |> ignore;
      match P.parse_statement ctx s with
      | Error s ->
        Format.printf "parse error: %s@." s;
        loop ctx
      | Ok s ->
        Format.printf "%a@." Statement.pp s;
        begin try
            process_statement ctx s;
          with Error.Error msg ->
            Format.printf "@{<Red>Error@}: %s@." msg
        end;
        loop ctx
  end

let () =
  CCFormat.set_color_default true;
  LNoise.history_load ~filename:hist_file |> warn_err_;
  LNoise.history_set ~max_length:1000 |> warn_err_;
  LNoise.catch_break true;
  let ctx = Statement.Ctx.create() in
  CCFun.finally
    ~h:(fun () ->
        LNoise.history_save ~filename:hist_file |> warn_err_)
    ~f:(fun () -> loop ctx)
