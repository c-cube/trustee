
module T = Trustee_core

module Log = T.Log
module K = T.Kernel
module TA = T.Type_ast

open Task.Infix
type 'a m = 'a Task.m

class trustee_server =
  let _ctx = K.Ctx.create () in
  object
    inherit Jsonrpc2.server
    val env = TA.Env.create _ctx

    method on_request
    : type r. r Lsp.Client_request.t -> r m
    = fun (_r:_ Lsp.Client_request.t) ->
      Log.debugf 5 (fun k->k "lsp: got request");
      Lwt.fail_with "TODO: on request"
      (*
    Jsonrpc.Response
    { Lsp.Server.Handler.
      on_request=fun (_server:t Lsp.Server.t) _r : _ result Fiber.t ->
        Lsp.Logger.log
          ~section:"trustee" ~title:Lsp.Logger.Title.Debug
          "got request";
        Fiber.return (Error (reply_err ~msg:"not implemented" ()));
    }
         *)

    method on_notification ~notify_back:_ (n:Lsp.Client_notification.t) : unit m =
      Log.debugf 5 (fun k->k"got notification");
      let open Lsp.Types in
      begin match n with
        | Lsp.Client_notification.TextDocumentDidOpen
            {DidOpenTextDocumentParams.textDocument=doc} ->
          Log.debugf 5
            (fun k->k"open document %s" doc.TextDocumentItem.uri);
          () (* TODO *)
        | Lsp.Client_notification.TextDocumentDidClose _
        | Lsp.Client_notification.TextDocumentDidChange _
        | Lsp.Client_notification.DidSaveTextDocument _
        | Lsp.Client_notification.WillSaveTextDocument _
        | Lsp.Client_notification.ChangeWorkspaceFolders _
        | Lsp.Client_notification.ChangeConfiguration _
        | Lsp.Client_notification.Initialized|Lsp.Client_notification.Exit
        | Lsp.Client_notification.Unknown_notification _ ->
          ()
      end;
      Lwt.return () (* TODO *)
  end

let setup_logger_ () =
  if true || Sys.getenv_opt "LSPLOG"=Some"1" then (
    let oc = open_out "/tmp/lsp.log" in
    at_exit (fun () -> flush oc; close_out_noerr oc);
    let out = Format.formatter_of_out_channel oc in
    Log.set_debug_out out;
    Log.set_level 50;
  )

(*
let task_io self =
  if Task.is_cancelled self then Task.return ()
  else (
    Jsonrpc2.run 
    Lsp.Io.read

  )
   *)

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
