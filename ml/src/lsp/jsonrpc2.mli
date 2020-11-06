
module IO : sig
  type 'a t = 'a Task.m
  type in_channel = Lwt_io.input Lwt_io.channel
  type out_channel = Lwt_io.output Lwt_io.channel
end

type json = Yojson.Safe.t

type t
(** A jsonrpc2 connection. *)

module type SERVER = sig
  val on_notification :
    notify:(Lsp.Server_notification.t -> unit IO.t) ->
    Lsp.Client_notification.t ->
    unit IO.t

  val on_request :
    'a Lsp.Client_request.t ->
    'a IO.t
end

val create :
  ic:IO.in_channel ->
  oc:IO.out_channel ->
  (module SERVER) ->
  t
(** Create a connection from the pair of channels *)

val create_stdio :
  (module SERVER) ->
  t

val run : t -> unit Task.t -> unit Task.m
(** Listen for incoming messages and responses *)

(** {3 Send requests and notifications to the other side} *)

(* TODO:
exception Jsonrpc2_error of int * string
(** Code + message *)

type message
(** Message sent to the other side *)

val request :
  t -> meth:string -> params:json option ->
  message * (json, int * string) result IO.Future.t
(** Create a request message, for which an answer is expected. *)

val notify : t -> meth:string -> params:json option -> message
(** Create a notification message, ie. no response is expected. *)

val send : t -> message -> (unit, exn) result IO.t
(** Send the message. *)

val send_batch : t -> message list -> (unit, exn) result IO.t
(** Send a batch of messages. *)

val send_request :
  t -> meth:string -> params:json option ->
  (json, exn) result IO.t
(** Combination of {!send} and {!request} *)

val send_notify:
  t -> meth:string -> params:json option ->
  (unit, exn) result IO.t
(** Combination of {!send} and {!notify} *)

val send_request_with :
  encode_params:('a -> json) ->
  decode_res:(json -> ('b,string) result) ->
  t -> meth:string -> params:'a option ->
  ('b, exn) result IO.t
(** Decoders + {!send_request} *)

val send_notify_with :
  encode_params:('a -> json) ->
  t -> meth:string -> params:'a option ->
  (unit, exn) result IO.t
(** Encoder + {!send_notify} *)

   *)
