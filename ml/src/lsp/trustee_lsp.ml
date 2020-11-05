
module T = Trustee_core

module K = T.Kernel
module TA = T.Type_ast

module St = struct
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

  let reply_err
      ?(code=Jsonrpc.Response.Error.Code.InternalError)
      ~msg:message () =
    Jsonrpc.Response.Error.make ~code ~message ()

  let on_request
    : type r. t -> r Lsp.Client_request.t -> r
    = fun (_self:t) (_r:_ Lsp.Client_request.t) ->
    assert false
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
      (self:t) (_n:Lsp.Client_notification.t) : _ =
    () (* TODO *)
end

let logger oc (s,title,msg) =
  Format.fprintf oc "@[<2>%s[%s]:@ %s@]."
    s (Lsp.Logger.Title.to_string title) msg;
  ()

let () =
  if Sys.getenv_opt "LSPLOG"=Some"1" then (
    let oc = open_out "/tmp/lsp.log" in
    at_exit (fun () -> flush oc; close_out_noerr oc);
    Lsp.Logger.register_consumer (logger (Format.formatter_of_out_channel oc));
  );
  (* TODO: the task is the LSP server *)
  let task = Task.start (fun _tsk -> assert false) in
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
    Printf.eprintf "error: %s\n%!" (Printexc.to_string e);
    exit 1
  | Ok () -> ()
