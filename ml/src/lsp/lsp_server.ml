
module type IO = sig
  type 'a t
  val (let+) : 'a t -> ('a -> 'b) -> 'b t
  val (let*) : 'a t -> ('a -> 'b t) -> 'b t
  val (and+) : 'a t -> 'b t -> ('a * 'b) t
  type in_channel
  type out_channel
end

module Make(IO : IO) = struct
  (** The server baseclass *)
  class virtual server = object
    method virtual on_notification :
      notify_back:(Lsp.Server_notification.t -> unit IO.t) ->
      Lsp.Client_notification.t ->
      unit IO.t

    method virtual on_request : 'a.
      'a Lsp.Client_request.t ->
      'a IO.t

    (** Set to true if the client requested to exit *)
    method must_quit = false
  end
end
