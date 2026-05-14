open Trustee_opentheory
open Common_
module Log = Trustee_core.Log

let print_all idx =
  let@ _sp = Trace.with_span ~__FILE__ ~__LINE__ "print-all" in
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
let build_zip = ref ""
let proof_zip = ref ""
let progress_ = ref false
let store_proofs_ = ref false

(* TODO: storage: use on-disk region files *)

let main ~dir ~serve ~port () =
  let@ _sp = Trace.with_span ~__FILE__ ~__LINE__ "main" in
  let idx =
    let t1 = now () in
    let r = Idx.list_dir dir in
    Fmt.printf "indexed `%s` in %.3fs@." dir (since_s t1);
    r
  in
  if !print then print_all idx;
  let theories = Iter.of_list idx.Idx.theories |> Iter.map snd in

  (* serving requires a proof-zip *)
  if serve && !proof_zip = "" then (
    Printf.eprintf
      "error: --serve requires --proof-zip <file.zip>\n\
       Build one first with:\n\
      \  trustee_ot --dir <dir> --build-zip proofs.zip\n";
    exit 1
  );

  (* For build-zip: use a tracked storage to capture all const defs *)
  let ts_opt =
    if !build_zip <> "" then
      Some (Proof_zip.make_tracked_storage ())
    else
      None
  in
  (* --build-zip requires store_proofs to capture proof traces *)
  let store_proofs = !store_proofs_ || !build_zip <> "" in
  let ctx =
    let storage =
      match ts_opt with
      | Some ts -> Some (Proof_zip.tracked_as_storage ts)
      | None -> None
    in
    K.Ctx.create ?storage ~store_proofs ~store_concrete_definitions:true ()
  in
  let st =
    let progress_bar = !progress_ in
    let cb =
      if serve then
        new Eval.log_callbacks
      else
        new Eval.print_callbacks
    in
    let proof_zip_opt =
      if !proof_zip = "" then
        None
      else
        Some !proof_zip
    in
    St.create ~cb ~progress_bar ?proof_zip:proof_zip_opt ~ctx ~idx ()
  in

  let server_opt =
    if serve then (
      (* Server starts immediately -- theories are loaded on demand from zip *)
      let server = Serve.create st ~port in
      let _th_metrics =
        Thread.create
          (fun () ->
            let gc = Tiny_httpd_prometheus.(GC_metrics.create global) in
            let n_active =
              Tiny_httpd_prometheus.(Gauge.create global) "active-conms"
            in
            while true do
              Thread.delay 1.;
              Tiny_httpd_prometheus.GC_metrics.update gc;
              Tiny_httpd_prometheus.Gauge.set n_active
                (Serve.active_connections server);
              if not (Serve.active server) then exit 1
            done)
          ()
      in
      Some (server, Thread.create Serve.serve server)
    ) else
      None
  in

  if !build_zip <> "" then (
    (* build-zip: evaluate all theories with store_proofs=true and write zip *)
    let output = !build_zip in
    (* Topological sort: encode a theory only after all its requires are
       encoded. This ensures proof DAGs can be freed as early as possible
       because upstream theories are always processed before downstream ones. *)
    let names =
      let all = List.map Thy_file.name (Iter.to_list theories) in
      let name_set = Str_set.of_list all in
      (* deps: unversioned name -> list of unversioned dep names *)
      let deps name =
        try
          let thy = Idx.find_thy idx name in
          Thy_file.requires thy
          |> List.filter_map (fun req ->
                 (* req may be versioned; find it in idx and get unversioned *)
                 try Some (Idx.find_thy idx req |> Thy_file.name)
                 with _ -> None)
          |> List.filter (fun d -> Str_set.mem d name_set)
        with _ -> []
      in
      let sorted = ref [] in
      let visiting = Str_tbl.create 64 in
      let visited = Str_tbl.create 64 in
      let rec visit name =
        if not (Str_tbl.mem visited name) then
          if Str_tbl.mem visiting name then
            ()
          (* cycle: skip *)
          else (
            Str_tbl.add visiting name ();
            List.iter visit (deps name);
            Str_tbl.remove visiting name;
            Str_tbl.add visited name ();
            sorted := name :: !sorted
          )
      in
      List.iter visit all;
      Iter.of_list (List.rev !sorted)
    in
    let ts =
      match ts_opt with
      | Some ts -> ts
      | None -> assert false (* ts_opt is Some when build_zip <> "" *)
    in
    Fmt.printf "building proof zip: %s@." output;
    Proof_zip.build ~output ~eval:st.St.eval ~ts ~names
  ) else if !check_all then
    Check_all.check ~st ~names:(Iter.map Thy_file.name theories) ()
  else if !check <> [] then
    Check_all.check ~st ~names:(Iter.of_list !check) ();

  Option.iter (fun (_, t) -> Thread.join t) server_opt;
  ()

(* TODO: use Logs *)

let () =
  let@ () = Trace_tef.with_setup () in

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
      ( "--build-zip",
        Arg.Set_string build_zip,
        " build a zip of proof traces and store to given file" );
      ( "--proof-zip",
        Arg.Set_string proof_zip,
        " load proof traces from a zip file for serving" );
      "-nc", Arg.Clear color, " disable colors";
      "-d", Arg.Set_int debug, " set debug level";
      ( "--store-proofs",
        Arg.Set store_proofs_,
        " enable storage of proofs (takes a lot of ram)" );
      "--progress", Arg.Set progress_, " progress bar";
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
