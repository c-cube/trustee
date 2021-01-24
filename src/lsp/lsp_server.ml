
module type IO = sig
  type 'a t
  val return : 'a -> 'a t
  val failwith : string -> 'a t
  val (let+) : 'a t -> ('a -> 'b) -> 'b t
  val (let*) : 'a t -> ('a -> 'b t) -> 'b t
  val (and+) : 'a t -> 'b t -> ('a * 'b) t
  type in_channel
  type out_channel
end

module Make(IO : IO) = struct
  open Lsp.Types

  module Position = Position
  module Range = Range

  (** The server baseclass *)
  class virtual base_server = object
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

  (** A wrapper to more easily reply to notifications *)
  class notify_back ~notify_back ?version ~(uri:DocumentUri.t) () = object
    (** Send a log message to the editor *)
    method send_log_msg ~type_ msg : unit IO.t =
      let params = ShowMessageParams.create ~type_ ~message:msg in
      notify_back (Lsp.Server_notification.LogMessage params)

    (** Send diagnostics for the current document *)
    method send_diagnostic (l:Diagnostic.t list) : unit IO.t =
      let params = PublishDiagnosticsParams.create
          ~uri ?version ~diagnostics:l () in
      notify_back (Lsp.Server_notification.PublishDiagnostics params)

    (** Send a notification (general purpose method) *)
    method send_notification (n:Lsp.Server_notification.t) =
      notify_back n
  end

  (** Current state of a document. *)
  type doc_state = {
    uri: DocumentUri.t;
    languageId: string;
    version: int;
    content: string;
  }

  (** An easily overloadable class. Pick the methods you want to support.
      The user must provide at least the callbacks for document lifecycle:
      open, close, update. The most basic LSP server should check documents
      when they're updated and report diagnostics back to the editor. *)
  class virtual server = object(self)
    inherit base_server
    val mutable _quit = false
    val docs : (DocumentUri.t, doc_state) Hashtbl.t = Hashtbl.create 16

    method! must_quit = _quit

    (** Find current state of the given document, if present. *)
    method find_doc (uri:DocumentUri.t) : doc_state option =
      try Some (Hashtbl.find docs uri)
      with Not_found -> None

    (** Overload to process other requests *)
    method on_request_unhandled
      : type r. r Lsp.Client_request.t -> r IO.t
      = fun _r ->
        IO.failwith "TODO: handle this request"

    method on_request
    : type r. r Lsp.Client_request.t -> r IO.t
    = fun (r:_ Lsp.Client_request.t) ->
      begin match r with
        | Lsp.Client_request.Shutdown -> _quit <- true; IO.return ()
        | _ -> self#on_request_unhandled r
      end

    (** Called when a document is opened *)
    method virtual on_notif_doc_did_open :
      notify_back:notify_back ->
      TextDocumentItem.t ->
      content:string ->
      unit IO.t

    method virtual on_notif_doc_did_close :
      notify_back:notify_back ->
      TextDocumentIdentifier.t ->
      unit IO.t

    (** Called when the document changes. *)
    method virtual on_notif_doc_did_change :
      notify_back:notify_back ->
      VersionedTextDocumentIdentifier.t ->
      TextDocumentContentChangeEvent.t list ->
      old_content:string ->
      new_content:string ->
      unit IO.t

    method on_notification
        ~notify_back (n:Lsp.Client_notification.t) : unit IO.t =
      let open Lsp.Types in
      begin match n with
        | Lsp.Client_notification.TextDocumentDidOpen
            {DidOpenTextDocumentParams.textDocument=doc} ->
          let notify_back =
            new notify_back ~uri:doc.uri ~version:doc.version ~notify_back () in
          let st = {
            uri=doc.uri; version=doc.version; content=doc.text;
            languageId=doc.languageId;
          } in
          Hashtbl.replace docs doc.uri st;
          self#on_notif_doc_did_open ~notify_back doc ~content:st.content
        | Lsp.Client_notification.TextDocumentDidClose {textDocument=doc} ->
          let notify_back = new notify_back ~uri:doc.uri ~notify_back () in
          self#on_notif_doc_did_close ~notify_back doc
        | Lsp.Client_notification.TextDocumentDidChange {textDocument=doc; contentChanges=c} ->
          let notify_back = new notify_back ~uri:doc.uri ~notify_back () in
          begin match Hashtbl.find docs doc.uri with
            | exception Not_found -> IO.failwith "unknown document"
            | st ->
              let old_content = st.content in
              let new_doc: Lsp.Text_document.t =
                let doc = Lsp.Text_document.make
                    (DidOpenTextDocumentParams.create
                       ~textDocument:(
                         TextDocumentItem.create ~languageId:st.languageId
                           ~uri:doc.uri ~version:st.version ~text:st.content))
                in
                List.fold_left
                  (fun d ev -> Lsp.Text_document.apply_content_change ev d)
                  doc c
              in
              let new_st = {
                st with
                content=Lsp.Text_document.text new_doc;
                version=Lsp.Text_document.version new_doc;
              } in
              Hashtbl.replace docs doc.uri new_st;
              self#on_notif_doc_did_change ~notify_back doc c ~old_content
                ~new_content:new_st.content
          end
        | Lsp.Client_notification.Exit -> _quit <- true; IO.return ()
        | Lsp.Client_notification.DidSaveTextDocument _
        | Lsp.Client_notification.WillSaveTextDocument _
        | Lsp.Client_notification.ChangeWorkspaceFolders _
        | Lsp.Client_notification.ChangeConfiguration _
        | Lsp.Client_notification.Initialized
        | Lsp.Client_notification.Unknown_notification _ ->
          IO.return () (* TODO: method for each of these *)
      end
  end
end
