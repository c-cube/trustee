open Trustee_opentheory
open Common_
module Log = Trustee_core.Log

let print_all idx =
  let { Idx.errors; theories; interps; _ } = idx in
  List.iter (fun (s, thy) -> Fmt.printf "%s: %s@." s thy.Thy_file.name) theories;
  List.iter
    (fun (s, int) ->
      Fmt.printf "interp %s (%d lines)@." s (Interp_file.size int))
    interps;
  List.iter
    (fun (s, e) ->
      Fmt.printf "@{<Red>Error@} for %s: %a@." s Trustee_core.Error.pp e)
    errors;
  ()

let now () = Unix.gettimeofday ()

let since_s t = now () -. t

type edge =
  | E_requires
  | E_sub

(* index theories by their name and versioned name *)
type theories = { theories: (string, Thy_file.t) Hashtbl.t }

let unquote_str = Util.unquote_str

let print = ref false

let check = ref []

let check_all = ref false

let progress_ = ref false

let store_proofs_ = ref false

let use_sqlite = ref false

(* TODO: storage: use sqlite *)

let main ~dir ~serve ~port () =
  let idx =
    let t1 = now () in
    let r = Idx.list_dir dir in
    Fmt.printf "indexed `%s` in %.3fs@." dir (since_s t1);
    r
  in
  if !print then print_all idx;
  let theories = Iter.of_list idx.Idx.theories |> Iter.map snd in

  (* TODO: use param for store_proofs *)
  let storage =
    if !use_sqlite then
      Some (Trustee_sqlite.storage_xdg_cache ())
    else
      None
  in
  let ctx =
    K.Ctx.create ?storage ~store_proofs:!store_proofs_
      ~store_concrete_definitions:true ()
  in
  let st =
    let progress_bar = !progress_ in
    let cb =
      if serve then
        new Eval.log_callbacks
      else
        new Eval.print_callbacks
    in
    St.create ~cb ~progress_bar ~ctx ~idx ()
  in

  let th_serve =
    if serve then (
      let _th_metrics =
        Thread.create
          (fun () ->
            let gc = Tiny_httpd_prometheus.(GC_metrics.create global) in
            while true do
              Thread.delay 1.;
              Tiny_httpd_prometheus.GC_metrics.update gc
            done)
          ()
      in
      Some (Thread.create (fun () -> Serve.serve st ~port) ())
    ) else
      None
  in

  if !check_all then
    Check_all.check ~st ~names:(Iter.map Thy_file.name theories) ()
  else if !check <> [] then
    Check_all.check ~st ~names:(Iter.of_list !check) ();

  Option.iter Thread.join th_serve;
  ()

(* TODO: use Logs *)

let () =
  let dir = ref "" in
  let color = ref true in
  let serve = ref false in
  let port = ref 8089 in
  let debug = ref 1 in
  let opts =
    [
      "--dir", Arg.Set_string dir, " set opentheory directory";
      "--print", Arg.Set print, " print the list of theories";
      ( "--check",
        Arg.Rest (fun s -> check := s :: !check),
        " check given theories" );
      "--check-all", Arg.Set check_all, " check all";
      "-nc", Arg.Clear color, " disable colors";
      "-d", Arg.Set_int debug, " set debug level";
      ( "--store-proofs",
        Arg.Set store_proofs_,
        " enable storage of proofs (takes a lot of ram)" );
      "--progress", Arg.Set progress_, " progress bar";
      "--sqlite", Arg.Set use_sqlite, " use Sqlite as main storage";
      "--serve", Arg.Set serve, " launch web server";
      "--port", Arg.Set_int port, " set port for web server";
      "-p", Arg.Set_int port, " set port for web server";
      "--progress", Arg.Set progress_, " progress bar";
      ( "--bt",
        Arg.Unit (fun () -> Printexc.record_backtrace true),
        " record backtraces" );
    ]
    |> Arg.align
  in

  Log.set_level !debug;
  Logger.setup_logs ~debug:(!debug > 1) ~style:`SYSTEMD ~level:!debug ();

  Arg.parse opts (fun _ -> failwith "invalid option") "trustee_ot [option*]";
  if !color then Fmt.set_color_default true;
  try main ~dir:!dir ~serve:!serve ~port:!port () with
  | Failure s ->
    Fmt.eprintf "%s@." s;
    exit 1
  | Trustee_core.Error.E err ->
    Fmt.eprintf "%a@." Trustee_core.Error.pp err;
    exit 1
