
open Trustee_opentheory

module K = Trustee_core.Kernel
module Log = Trustee_core.Log

let print_all idx =
  let {Idx.errors; theories; interps; _} = idx in
  List.iter
    (fun (s,thy) -> Fmt.printf "%s: %s@." s thy.Thy_file.name)
    theories;
  List.iter
    (fun (s,int) -> Fmt.printf "interp %s (%d lines)@." s (Interp_file.size int))
    interps;
  List.iter
    (fun (s,e) -> Fmt.printf "@{<Red>Error@} for %s: %a@." s Trustee_core.Error.pp e)
    errors;
  ()

let now() = Unix.gettimeofday()
let since_s t = now() -. t

type edge =
  | E_requires
  | E_sub

(* index theories by their name and versioned name *)
type theories = {
  theories: (string, Thy_file.t) Hashtbl.t;
}

let unquote_str = Util.unquote_str

let check_ (idx:Idx.t) ~progress_bar ~names : unit =
  let ctx = K.Ctx.create () in
  let eval_st =
    Eval.create ~cb:(new Eval.print_callbacks) ~progress_bar ~ctx ~idx () in

  Iter.iter
    (fun name ->
       match Eval.eval_theory eval_st name with
       | Ok _ -> ()
       | Error e ->
         Format.eprintf "error: %a" Trustee_core.Error.pp e)
    names;
  ()

let print = ref false
let check = ref []
let check_all = ref false
let progress_ = ref false

let main ~dir () =
  let idx =
    let t1 = now() in
    let r = Idx.list_dir dir in
    Fmt.printf "indexed `%s` in %.3fs@." dir (since_s t1);
    r
  in
  if !print then print_all idx;
  let theories = Iter.of_list idx.Idx.theories |> Iter.map snd in
  if !check_all then (
    check_ idx
      ~progress_bar:!progress_ ~names:(Iter.map Thy_file.name theories);
  ) else if !check <> [] then (
    check_ idx
      ~progress_bar:!progress_ ~names:(Iter.of_list !check)
  );
  ()

let () =
  let dir = ref "" in
  let color = ref true in
  let opts = [
    "-dir", Arg.Set_string dir, " set opentheory directory";
    "-print", Arg.Set print, " print the list of theories";
    "-check", Arg.Rest (fun s->check := s :: !check), " check given theories";
    "-check-all", Arg.Set check_all, " check all";
    "-nc", Arg.Clear color, " disable colors";
    "-d", Arg.Int Log.set_level, " set debug level";
    "--progress", Arg.Set progress_, " progress bar";
    "-p", Arg.Set progress_, " progress bar";
    "--bt", Arg.Unit (fun()->Printexc.record_backtrace true), " record backtraces";
  ] |> Arg.align in
  Arg.parse opts (fun _ -> failwith "invalid option") "trustee_ot [option*]";
  if !color then Fmt.set_color_default true;
  try main ~dir:!dir ()
  with Trustee_core.Error.E err as exn ->
    Fmt.eprintf "%a@." Trustee_core.Error.pp err;
    raise exn
