
module T = Trustee_core

module Log = T.Log
module K = T.Kernel
module TA = T.Type_ast

open Task.Infix
type 'a m = 'a Task.m

module MkServer() : Jsonrpc2.SERVER = struct
  type t = {
    ctx: K.Ctx.t;
    mutable env: TA.env;
    (* TODO: set of documents *)
  }

  let make () : t =
    let ctx = K.Ctx.create() in
    { ctx;
      env=TA.Env.create ctx;
    }

  let st : t = make()

  let on_request
    : type r. r Lsp.Client_request.t -> r m
    = fun (_r:_ Lsp.Client_request.t) ->
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

  let on_notification
    ~notify (_n:Lsp.Client_notification.t) : unit m =
    Lwt.return () (* TODO *)
end

let lsp_logger_ oc (s,title,msg) =
  Format.fprintf oc "@[<2>%s[%s]:@ %s@]."
    s (Lsp.Logger.Title.to_string title) msg;
  ()

let setup_logger_ () =
  if true || Sys.getenv_opt "LSPLOG"=Some"1" then (
    let oc = open_out "/tmp/lsp.log" in
    at_exit (fun () -> flush oc; close_out_noerr oc);
    let out = Format.formatter_of_out_channel oc in
    Log.set_debug_out out;
    Log.set_level 50;
    Lsp.Logger.register_consumer (lsp_logger_ out);
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
  let module Server = MkServer() in
  (* TODO: the task is the LSP server *)
  let task =
    Task.start ~descr:"top task"
      (fun _top_task ->
         Log.debugf 1 (fun k->k"start lsp");
         let server = Jsonrpc2.create_stdio (module Server) in
         let* () =
           Task.run_sub ~descr:"lsp server"
             ~parent:_top_task (fun _ -> Jsonrpc2.run server _top_task)
           >>= Task.unwrap
         in
         Task.return ()
      )
  in
  (* TODO
  let rpc =
    Lsp.Rpc.Stream_io.make sched (Lsp.Io.make stdin stdout) in
  let handle =
    Lsp.Server.Handler.make
      ~on_request:St.on_request
      ~on_notification:St.on_notification
      ()
  in
  let server = Lsp.Server.make handle rpc (St.make ()) in
  Lsp.Logger.log
    ~section:"trustee" ~title:Lsp.Logger.Title.Debug
    "start";
  let fib = Lsp.Server.start server in
  *)
  match Task.run task with
  | Error e ->
    let e = Printexc.to_string e in
    Log.debugf 1 (fun k->k"error: %s" e);
    Printf.eprintf "error: %s\n%!" e;
    exit 1
  | Ok () -> ()
