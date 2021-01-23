
(** {1 Simple JSON-RPC2 implementation}
    See {{: https://www.jsonrpc.org/specification} the spec} *)

module J = Yojson.Safe
module Err = Jsonrpc.Response.Error
open Task.Infix

module IO = struct
  type 'a t = 'a Lwt.t
  let (let+) = Lwt.(>|=)
  let (let*) = Lwt.(>>=)
  let (and+) a b =
    let open Lwt in
    a >>= fun x -> b >|= fun y -> x,y
  type in_channel = Lwt_io.input Lwt_io.channel
  type out_channel = Lwt_io.output Lwt_io.channel
end

include Lsp_server.Make(IO)

type json = J.t
type 'a m = 'a Task.m

let spf = Printf.sprintf

module ErrorCode = Lsp.Types.ErrorCodes
(*
module Err = struct
  type code = int
  let code_parse_error : code = (-32700)
  let code_invalid_request : code = (-32600)
  let code_method_not_found : code = (-32601)
  let code_invalid_param : code = (-32602)
  let code_internal_error : code = (-32603)
end

               *)
exception E of ErrorCode.t * string

type t = {
  ic: Lwt_io.input Lwt_io.channel;
  oc: Lwt_io.output Lwt_io.channel;
  s: server;
}

let create ~ic ~oc server : t = {ic; oc; s=server}

let create_stdio server : t =
  create ~ic:Lwt_io.stdin ~oc:Lwt_io.stdout server

(* bind on IO+result *)
let ( let*? ) x f =
  let open Lwt.Infix in
  x >>= function
  | Error _ as err -> Lwt.return err
  | Ok x -> f x

(* send a single message *)
let send_json_ (self:t) (j:json) : unit m =
  let json = J.to_string j in
  let full_s =
    Printf.sprintf "Content-Length: %d\r\n\r\n%s"
      (String.length json) json
  in
  Lwt_io.write self.oc full_s

let send_response (self:t) (m:Jsonrpc.Response.t) : unit m =
  let json = Jsonrpc.Response.yojson_of_t m in
  send_json_ self json

let send_server_notif (self:t) (m:Jsonrpc.Message.notification) : unit m =
  let json = Jsonrpc.Message.yojson_of_notification m in
  send_json_ self json

let try_ f =
  Lwt.catch
    (fun () -> let+ x = f() in Ok x)
    (fun e -> Lwt.return (Error e))

let log_lsp_ msg =
  Fmt.kasprintf
    (fun s ->
      Lsp.Logger.log ~title:Lsp.Logger.Title.Debug ~section:"jsonrpc2"
      "%s" s)
    msg

(* read a full message *)
let read_msg (self:t) : (Jsonrpc.Message.either, exn) result m =
  let rec read_headers acc =
    let*? line =
      try_ @@ fun () -> Lwt_io.read_line self.ic
    in
    match String.trim line with
    | "" -> Lwt.return (Ok acc) (* last separator *)
    | line ->
      begin match
          let i = String.index line ':' in
          if i<0 || String.get line (i+1) <> ' ' then raise Not_found;
          let key = String.lowercase_ascii @@ String.sub line 0 i in
          let v =
            String.lowercase_ascii @@
            String.trim (String.sub line (i+1) (String.length line-i-1))
          in
          key, v
        with
        | pair -> read_headers (pair :: acc)
        | exception _ ->
          Lwt.return (Error (E(ErrorCode.ParseError, spf "invalid header: %S" line)))
      end
  in
  let*? headers = read_headers [] in
  log_lsp_ "headers: %a" Fmt.Dump.(list @@ pair string string) headers;
  let ok = match List.assoc "content-type" headers with
    | "utf8" | "utf-8" -> true
    | _ -> false
    | exception Not_found -> true
  in
  if ok then (
    match int_of_string (List.assoc "content-length" headers) with
    | n ->
      log_lsp_ "read %d bytes..." n;
      let buf = Bytes.make n '\000' in
      let*? () =
        try_ @@ fun () -> Lwt_io.read_into_exactly self.ic buf 0 n
      in
      (* log_lsp_ "got bytes %S" (Bytes.unsafe_to_string buf); *)
      let*? j =
        try_ @@ fun () ->
        Lwt.return @@ J.from_string (Bytes.unsafe_to_string buf)
      in
      begin match Jsonrpc.Message.either_of_yojson j with
        | m -> Lwt.return @@ Ok m
        | exception _ ->
          Lwt.return (Error (E(ErrorCode.ParseError, "cannot decode json")))
      end
    | exception _ ->
      Lwt.return @@
      Error (E(ErrorCode.ParseError, "missing content-length' header"))
  ) else (
    Lwt.return @@
    Error (E(ErrorCode.InvalidRequest, "content-type must be 'utf-8'"))
  )

let run (self:t) (task:_ Task.t) : unit m =
  let process_msg r =
    let module M = Jsonrpc.Message in
    match r.M.id with
    | None ->
      (* notification *)
      begin match Lsp.Client_notification.of_jsonrpc {r with M.id=()} with
        | Ok n ->
          (self.s)#on_notification n
            ~notify_back:(fun n ->
                let msg =
                  Lsp.Server_notification.to_jsonrpc n
                in
                send_server_notif self msg)
        | Error e ->
          Lwt.fail_with (spf "cannot decode notification: %s" e)
      end
    | Some id ->
      (* request, so we need to reply *)
      Lwt.catch
        (fun () ->
          begin match Lsp.Client_request.of_jsonrpc {r with M.id} with
            | Ok (Lsp.Client_request.E r) ->
              let* reply = self.s#on_request r in
              let reply_json = Lsp.Client_request.yojson_of_result r reply in
              let response = Jsonrpc.Response.ok id reply_json in
              send_response self response
            | Error e ->
              Lwt.fail_with (spf "cannot decode request: %s" e)
          end)
      (fun e ->
        let r =
          Jsonrpc.Response.error id
            (Jsonrpc.Response.Error.make
               ~code:Jsonrpc.Response.Error.Code.InternalError
               ~message:(Printexc.to_string e) ())
        in
        send_response self r)
  in
  let rec loop () =
    if Task.is_cancelled task then Lwt.return ()
    else (
      let* r = read_msg self >>= Task.unwrap in
      Lwt.async (fun () -> process_msg r);
      loop()
    )
  in
  loop()

(*
module Make(IO : Jsonrpc2_intf.IO)
    : Jsonrpc2_intf.S with module IO = IO
= struct
  module IO = IO
  module Id = Protocol.Id
  type json = J.t

  type t = {
    proto: Protocol.t;
    methods: (string, method_) Hashtbl.t;
    reponse_promises:
      (json, code*string) result IO.Future.promise Id.Tbl.t; (* promises to fullfill *)
    ic: IO.in_channel;
    oc: IO.out_channel;
    send_lock: IO.lock; (* avoid concurrent writes *)
  }

  and method_ =
    (t -> params:json option -> return:((json, string) result -> unit) -> unit)
  (** A method available through JSON-RPC *)

  let create ~ic ~oc () : t =
    { ic; oc; reponse_promises=Id.Tbl.create 32; methods=Hashtbl.create 16;
      send_lock=IO.create_lock(); proto=Protocol.create(); }

  let declare_method (self:t) name meth : unit =
    Hashtbl.replace self.methods name meth

  let declare_method_with self ~decode_arg ~encode_res name f : unit =
    declare_method self name
      (fun self ~params ~return ->
         match params with
         | None ->
           (* pass [return] as a continuation to {!f} *)
           f self ~params:None ~return:(fun y -> return (Ok (encode_res y)))
         | Some p ->
           match decode_arg p with
           | Error e -> return (Error e)
           | Ok x ->
             (* pass [return] as a continuation to {!f} *)
             f self ~params:(Some x) ~return:(fun y -> return (Ok (encode_res y))))

  let declare_blocking_method_with self ~decode_arg ~encode_res name f : unit =
    declare_method self name
      (fun _self ~params ~return ->
         match params with
         | None -> return (Ok (encode_res (f None)))
         | Some p ->
           match decode_arg p with
           | Error e -> return (Error e)
           | Ok x -> return (Ok (encode_res (f (Some x)))))

  (** {2 Client side} *)

  exception Jsonrpc2_error of int * string
  (** Code + message *)

  type message = json

  let request (self:t) ~meth ~params : message * _ IO.Future.t =
    let msg, id = Protocol.request self.proto ~meth ~params in
    (* future response, with sender associated to ID *)
    let future, promise =
      IO.Future.make
        ~on_cancel:(fun () -> Id.Tbl.remove self.reponse_promises id)
        ()
    in
    Id.Tbl.add self.reponse_promises id promise;
    msg, future

  (* Notify the remote server *)
  let notify (self:t) ~meth ~params : message =
    Protocol.notify self.proto ~meth ~params

  let send_msg_ (self:t) (s:string) : _ IO.t =
    IO.with_lock self.send_lock
      (fun () -> IO.write_string self.oc s)

  (* send a single message *)
  let send (self:t) (m:message) : _ result IO.t =
    let json = J.to_string m in
    let full_s =
      Printf.sprintf "Content-Length: %d\r\n\r\n%s"
        (String.length json) json
    in
    send_msg_ self full_s

  let send_request self ~meth ~params : _ IO.t =
    let open IO.Infix in
    let msg, res = request self ~meth ~params in
    send self msg >>= function
    | Error e -> IO.return (Error e)
    | Ok () ->
      IO.Future.wait res >|= fun r ->
      match r with
      | Ok x -> Ok x
      | Error (code,e) -> Error (Jsonrpc2_error (code,e))

  let send_notify self ~meth ~params : _ IO.t =
    let msg = notify self ~meth ~params in
    send self msg

  let send_request_with ~encode_params ~decode_res self ~meth ~params : _ IO.t =
    let open IO.Infix in
    send_request self ~meth ~params:(opt_map_ encode_params params)
    >>= function
    | Error _ as e -> IO.return e
    | Ok x ->
      let r = match decode_res x with
        | Ok x -> Ok x
        | Error s -> Error (Jsonrpc2_error (code_invalid_request, s))
      in
      IO.return r

  let send_notify_with ~encode_params self ~meth ~params : _ IO.t =
    send_notify self ~meth ~params:(opt_map_ encode_params params)

  (* send a batch message *)
  let send_batch (self:t) (l:message list) : _ result IO.t =
    let json = J.to_string (`List l) in
    let full_s =
      Printf.sprintf "Content-Length: %d\r\n\r\n%s"
        (String.length json) json
    in
    send_msg_ self full_s

  (* bind on IO+result *)
  let (>>=?) x f =
    let open IO.Infix in
    x >>= function
    | Error _ as err -> IO.return err
    | Ok x -> f x

  (* read a full message *)
  let read_msg (self:t) : ((string * string) list * json, exn) result IO.t =
    let rec read_headers acc =
      IO.read_line self.ic >>=? function
      | "\r" -> IO.return (Ok acc) (* last separator *)
      | line ->
        begin match
            if String.get line (String.length line-1) <> '\r' then raise Not_found;
            let i = String.index line ':' in
            if i<0 || String.get line (i+1) <> ' ' then raise Not_found;
            String.sub line 0 i, String.trim (String.sub line (i+1) (String.length line-i-2))
          with
          | pair -> read_headers (pair :: acc)
          | exception _ ->
            IO.return (Error (Jsonrpc2_error (code_parse_error, "invalid header: " ^ line)))
        end
    in
    read_headers [] >>=? fun headers ->
    let ok = match List.assoc "Content-Type" headers with
      | "utf8" | "utf-8" -> true
      | _ -> false
      | exception Not_found -> true
    in
    if ok then (
      match int_of_string (List.assoc "Content-Length" headers) with
      | n ->
        let buf = Bytes.make n '\000' in
        IO.read_exact self.ic buf n >>=? fun () ->
        begin match J.from_string (Bytes.unsafe_to_string buf) with
          | j -> IO.return @@ Ok (headers, j)
          | exception _ ->
            IO.return (Error (Jsonrpc2_error (code_parse_error, "cannot decode json")))
        end
      | exception _ ->
        IO.return @@ Error (Jsonrpc2_error(code_parse_error, "missing Content-Length' header"))
    ) else (
      IO.return @@ Error (Jsonrpc2_error(code_invalid_request, "content-type must be 'utf-8'"))
    )

  (* execute actions demanded by the protocole *)
  let rec exec_actions (self:t) l : _ result IO.t =
    let open IO.Infix in
    match l with
    | [] -> IO.return (Ok ())
    | a :: tl ->
      begin match a with
        | Protocol.Send msg -> send self msg
        | Protocol.Send_batch l -> send_batch self l
        | Protocol.Start_call (id, name, params) ->
          begin match Hashtbl.find self.methods name with
            | m ->
              let fut, promise = IO.Future.make () in
              m self ~params
                ~return:(fun r -> IO.Future.fullfill promise r);
              (* now wait for the method's response, and reply to protocol *)
              IO.Future.wait fut >>= fun res ->
              let acts' = Protocol.process_call_reply self.proto id res in
              exec_actions self acts'
            | exception Not_found ->
              send self
                (Protocol.error self.proto code_method_not_found "method not found")
          end
        | Protocol.Notify (name,params) ->
          begin match Hashtbl.find self.methods name with
            | m ->
              (* execute notification, do not process response *)
              m self ~params ~return:(fun _ -> ());
              IO.return (Ok ())
            | exception Not_found ->
              send self
                (Protocol.error self.proto code_method_not_found "method not found")
          end
        | Protocol.Fill_request (id, res) ->
          begin match Id.Tbl.find self.reponse_promises id with
            | promise ->
              IO.Future.fullfill promise res;
              IO.return (Ok ())
            | exception Not_found ->
              send self @@ Protocol.error self.proto code_internal_error "no such request"
          end
        | Protocol.Error_without_id (code,msg) ->
          IO.return (Error (Jsonrpc2_error (code,msg)))
      end
      >>=? fun () ->
      exec_actions self tl

  let run (self:t) : _ IO.t =
    let open IO.Infix in
    let rec loop() : _ IO.t =
      read_msg self >>= function
      | Error End_of_file ->
        IO.return (Ok ()) (* done! *)
      | Error (Jsonrpc2_error (code, msg)) ->
        send self (Protocol.error self.proto code msg) >>=? fun () -> loop ()
      | Error _ as err -> IO.return err (* exit now *)
      | Ok (_hd, msg) ->
        begin match Protocol.process_msg self.proto msg with
          | Ok actions ->
            exec_actions self actions
          | Error (code,msg) ->
            send self (Protocol.error self.proto code msg)
        end
        >>=? fun () -> loop ()
    in
    loop ()
end
   *)
