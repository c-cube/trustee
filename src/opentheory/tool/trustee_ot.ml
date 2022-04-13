
open Trustee_opentheory
open Common_
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

let print = ref false
let check = ref []
let check_all = ref false
let progress_ = ref false
let store_proofs_ = ref false

let main ~dir ~serve ~port () =
  let idx =
    let t1 = now() in
    let r = Idx.list_dir dir in
    Fmt.printf "indexed `%s` in %.3fs@." dir (since_s t1);
    r
  in
  if !print then print_all idx;
  let theories = Iter.of_list idx.Idx.theories |> Iter.map snd in

  (* TODO: use param for store_proofs *)
  let ctx = K.Ctx.create ~store_proofs:!store_proofs_ ~erase_defs:false () in
  let st =
    let progress_bar = !progress_ in
    St.create
      ~cb:(new Eval.print_callbacks) ~progress_bar ~ctx ~idx ()
  in

  let th_serve =
    if serve then Some (Thread.create (fun () -> Serve.serve st ~port) ()) else None
  in

  if !check_all then (
    Check_all.check ~st ~names:(Iter.map Thy_file.name theories) ();
  ) else if !check <> [] then (
    Check_all.check ~st ~names:(Iter.of_list !check) ()
  );
  (*
  Gc.full_major();
  Gc.compact();
     *)

  ignore (
    Thread.create
      (fun () ->
         while true do Thread.delay 5.; Jemalloc.release_free_memory () done)
      () : Thread.t);

  Option.iter Thread.join th_serve;
  ()

(* TODO: use Logs *)

let () =
  let dir = ref "" in
  let color = ref true in
  let serve = ref false in
  let port = ref 8089 in
  let set_debug n =
    if n>1 then H._enable_debug true;
    Log.set_level n;
    Logger.setup_logs ~debug:(n>1) ~level:n ();
  in
  Jemalloc.release_free_memory();
  let opts = [
    "--dir", Arg.Set_string dir, " set opentheory directory";
    "--print", Arg.Set print, " print the list of theories";
    "--check", Arg.Rest (fun s->check := s :: !check), " check given theories";
    "--check-all", Arg.Set check_all, " check all";
    "-nc", Arg.Clear color, " disable colors";
    "-d", Arg.Int set_debug, " set debug level";
    "--store-proofs", Arg.Set store_proofs_, " enable storage of proofs (takes a lot of ram)";
    "--progress", Arg.Set progress_, " progress bar";
    "--serve", Arg.Set serve, " launch web server";
    "--port", Arg.Set_int port, " set port for web server";
    "-p", Arg.Set_int port, " set port for web server";
    "--progress", Arg.Set progress_, " progress bar";
    "--bt", Arg.Unit (fun()->Printexc.record_backtrace true), " record backtraces";
  ] |> Arg.align in
  Arg.parse opts (fun _ -> failwith "invalid option") "trustee_ot [option*]";
  if !color then Fmt.set_color_default true;
  try main ~dir:!dir ~serve:!serve ~port:!port ()
  with Trustee_core.Error.E err as exn ->
    Fmt.eprintf "%a@." Trustee_core.Error.pp err;
    raise exn
