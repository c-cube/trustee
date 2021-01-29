
module T = Trustee_core

module Log = T.Log
module K = T.Kernel
module PA = T.Parse_ast
module TA = T.Type_ast

open Task.Infix
type 'a m = 'a Task.m

open Lsp.Types

let lsp_pos_of_pos (p:T.Position.t) : Position.t =
  Position.create ~line:(p.line-1) ~character:(p.col+1)

let pos_of_lsp_pos (p:Position.t) : T.Position.t =
  T.Position.make ~line:(p.line+1) ~col:(p.character+1)

let lsp_range_of_loc (l:T.Loc.t) : Range.t =
  Range.create ~start:(lsp_pos_of_pos l.start) ~end_:(lsp_pos_of_pos l.end_)

type parsed_buffer = {
  penv: PA.Env.t;
  env: TA.Env.t;
  idx: TA.Index.t;
}

class trustee_server =
  let _ctx = K.Ctx.create () in
  object(self)
    inherit Jsonrpc2.server

    (* one env per document *)
    val buffers: (DocumentUri.t, parsed_buffer) Hashtbl.t = Hashtbl.create 32

    method private _on_doc ~(notify_back:Jsonrpc2.notify_back) (d:DocumentUri.t) (content:string) =
      (* TODO: use penv/env from dependencies, if any, once we have import *)

      let penv = PA.Env.create _ctx in
      let stmts =
        T.Syntax.parse_top_l_process
          ~file:d ~env:penv
          (T.Syntax.Lexer.create ~file:d content)
      in
      Log.debugf 3 (fun k->k "for %s: parsed %d statements" d (List.length stmts));

      let diags = ref [] in
      let env = TA.Env.create _ctx in
      let env, idx = List.fold_left
          (TA.process_stmt ~index:true
             ~on_show:(fun loc msg ->
                 let range = lsp_range_of_loc loc in
                 let message = Fmt.asprintf "@[info: %a@]" msg() in
                 let d = Diagnostic.create
                     ~severity:DiagnosticSeverity.Information
                     ~range ~message () in
                 diags := d :: !diags
               )
             ~on_error:(fun loc e ->
                 let range = lsp_range_of_loc loc in
                 let message = Fmt.asprintf "@[err: %a@]" e() in
                 let d = Diagnostic.create
                     ~severity:DiagnosticSeverity.Error ~range ~message () in
                 diags := d :: !diags
               ))
          (env, TA.Index.empty) stmts
      in

      Hashtbl.replace buffers d {penv; env; idx};

      let diags = List.rev !diags in
      Log.debugf 2 (fun k->k"send back %d diagnostics" (List.length diags));
      notify_back#send_diagnostic diags

    method on_notif_doc_did_open ~notify_back d ~content : unit m =
      Log.debugf 2 (fun k->k "did open %s (%d bytes)" d.uri (String.length content));
      self#_on_doc ~notify_back d.uri content

    method on_notif_doc_did_close ~notify_back:_ d : unit m =
      Log.debugf 2 (fun k->k "did close %s" d.uri);
      Hashtbl.remove buffers d.uri;
      Lwt.return ()

    method on_notif_doc_did_change ~notify_back d _c ~old_content:_old ~new_content : unit m =
      Log.debugf 5 (fun k->k "did update %s (%d bytes -> %d bytes)" d.uri
                   (String.length _old) (String.length new_content));
      self#_on_doc ~notify_back d.uri new_content

    (* ## requests ## *)

    method! on_req_hover ~uri ~pos (_d:Jsonrpc2.doc_state) : _ m =
      match Hashtbl.find buffers uri with
      | exception Not_found -> Lwt.return None
      | {idx; _} ->
        let pos = pos_of_lsp_pos pos in
        Log.debugf 1
          (fun k->k"lookup in idx (size %d) at pos %a"
              (TA.Index.size idx) T.Position.pp pos);
        let r =
          match TA.Index.find idx pos with
          | [] -> None
          | q :: _ ->
            Log.debugf 5 (fun k->k"found %a" q#pp ());
            let s = Fmt.to_string q#pp () in
            let r = Hover.create
                ~contents:(`MarkedString {MarkedString.value=s; language=None})
                ~range:(lsp_range_of_loc q#loc) ()
            in
            Some r
        in
        Lwt.return r

    method! on_req_definition ~uri ~pos _st : _ option Lwt.t =
      match Hashtbl.find buffers uri with
      | exception Not_found -> Lwt.return None
      | {idx;_} ->
        let pos = pos_of_lsp_pos pos in
        Log.debugf 1
          (fun k->k"lookup for def in idx (size %d) at pos %a"
              (TA.Index.size idx) T.Position.pp pos);
        let r =
          match TA.Index.find idx pos with
          | [] -> None
          | q :: _ ->
            match q#def_loc with
            | None -> None
            | Some loc ->
              Log.debugf 5 (fun k->k"found def at %a" T.Loc.pp q#loc);
              let loc =
                Location.create ~uri:loc.T.Loc.file ~range:(lsp_range_of_loc loc) in
              let r = `Location [loc] in
              Log.debugf 5 (fun k->k"response: %a" Yojson.Safe.pp (Locations.yojson_of_t r));
              Some r
        in
        Lwt.return r
  end

let setup_logger_ () =
  if true || Sys.getenv_opt "LSPLOG"=Some"1" then (
    let oc = open_out "/tmp/lsp.log" in
    at_exit (fun () -> flush oc; close_out_noerr oc);
    let out = Format.formatter_of_out_channel oc in
    Log.set_debug_out out;
    Log.set_level 50;
  )

let () =
  setup_logger_ ();
  let s = new trustee_server in
  (* TODO: the task is the LSP server *)
  let task =
    Task.start ~descr:"top task"
      (fun _top_task ->
         Log.debugf 1 (fun k->k"start lsp");
         let server = Jsonrpc2.create_stdio s in
         let* () =
           Task.run_sub ~descr:"lsp server"
             ~parent:_top_task (fun _ -> Jsonrpc2.run server _top_task)
           >>= Task.unwrap
         in
         Task.return ()
      )
  in
  match Task.run task with
  | Error e ->
    let e = Printexc.to_string e in
    Log.debugf 1 (fun k->k"error: %s" e);
    Printf.eprintf "error: %s\n%!" e;
    exit 1
  | Ok () -> ()
