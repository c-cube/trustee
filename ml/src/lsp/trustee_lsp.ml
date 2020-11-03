
module T = Trustee_core

module K = T.Kernel
module TA = T.Type_ast

module St = struct
  open Fiber.O

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
      ?(code=Lsp.Jsonrpc.Response.Error.Code.InternalError)
      ~msg:message () =
    Lsp.Jsonrpc.Response.Error.make ~code ~message ()

  let on_request =
    { Lsp.Server.Handler.
      on_request=fun (_server:t Lsp.Server.t) _r : _ result Fiber.t ->
        Lsp.Logger.log
          ~section:"trustee" ~title:Lsp.Logger.Title.Debug
          "got request";
        Fiber.return (Error (reply_err ~msg:"not implemented" ()));
    }

  let on_notification
      (server:t Lsp.Server.t) (_n:Lsp.Client_notification.t) : _ =
    (* TODO *)
    Fiber.return (Lsp.Server.state server)
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
  let sched = Lsp.Scheduler.create() in
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
  match Fiber.run fib with
  | None ->
    failwith "return none"
  | Some () -> ()
