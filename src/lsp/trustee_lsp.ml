
module T = Trustee_core

module Log = T.Log
module K = T.Kernel
module PA = T.Parse_ast
module TA = T.Type_ast

open Task.Infix
type 'a m = 'a Task.m

open Lsp.Types

let lsp_pos_of_pos (p:T.Position.t) : Position.t =
  Position.create ~line:(p.line-1) ~character:p.col

let lsp_range_of_loc (l:T.Loc.t) : Range.t =
  Range.create ~start:(lsp_pos_of_pos l.start) ~end_:(lsp_pos_of_pos l.end_)

class trustee_server =
  let _ctx = K.Ctx.create () in
  object(self)
    inherit Jsonrpc2.server

    (* one env per document *)
    val envs: (DocumentUri.t, PA.Env.t * TA.Env.t) Hashtbl.t = Hashtbl.create 32

    method private _on_doc ~(notify_back:Jsonrpc2.notify_back) (d:DocumentUri.t) (content:string) =
      (* TODO: use penv/env from dependencies, if any, once we have import *)

      let penv = PA.Env.create _ctx in
      let stmts =
        T.Syntax.parse_top_l_process
          ~file:(Filename.basename d) ~env:penv
          (T.Syntax.Lexer.create content)
      in
      Log.debugf 3 (fun k->k "for %s: parsed %d statements" d (List.length stmts));

      let diags = ref [] in
      let env = TA.Env.create _ctx in
      let env = List.fold_left
          (TA.process_stmt
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
          env stmts
      in

      Hashtbl.replace envs d (penv, env);

      let diags = List.rev !diags in
      Log.debugf 2 (fun k->k"send back %d diagnostics" (List.length diags));
      notify_back#send_diagnostic diags

    method on_notif_doc_did_open ~notify_back d ~content : unit m =
      Log.debugf 2 (fun k->k "did open %s (%d bytes)" d.uri (String.length content));
      self#_on_doc ~notify_back d.uri content

    method on_notif_doc_did_close ~notify_back:_ d : unit m =
      Log.debugf 2 (fun k->k "did close %s" d.uri);
      Hashtbl.remove envs d.uri;
      Lwt.return ()

    method on_notif_doc_did_change ~notify_back d _c ~old_content:_old ~new_content : unit m =
      Log.debugf 5 (fun k->k "did update %s (%d bytes -> %d bytes)" d.uri
                   (String.length _old) (String.length new_content));
      self#_on_doc ~notify_back d.uri new_content
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
