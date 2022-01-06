use anyhow::{anyhow, Result};
pub use lsp_types::{
    self as lsp, notification::Notification, request::Request, TextDocumentIdentifier as DocID,
};
use serde_json::{json, Value as JsonValue};
use std::{
    collections::HashMap,
    io::{BufRead, Read, Write},
    sync::{Arc, Mutex},
    thread,
};

/// A single, versioned, document.
#[derive(Debug)]
pub struct Doc {
    pub id: DocID,
    pub version: i64,
    pub content: String,
}

/// State shared among threads.
#[derive(Clone)]
pub struct State(Arc<Mutex<StateImpl>>);

/// Content of the state.
#[derive(Debug)]
pub struct StateImpl {
    pub docs: HashMap<lsp_types::Url, Doc>,
}

impl std::ops::Deref for State {
    type Target = Mutex<StateImpl>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Handler for LSP messages.
pub trait Handler: Send {
    /// Diagnostics when a document is added/updated.
    fn on_doc_update(&mut self, id: DocID, txt: &str) -> Result<Vec<lsp::Diagnostic>>;

    /// Called when a document is removed.
    fn on_remove_doc(&mut self, _id: DocID) {}

    /// Handle hover requests.
    fn handle_hover(
        &mut self,
        _st: &mut State,
        _p: lsp::HoverParams,
    ) -> Result<Option<lsp::Hover>> {
        Ok(None)
    }

    /// Handle completion requests.
    fn handle_completion(
        &mut self,
        _st: &mut State,
        _p: lsp::CompletionParams,
    ) -> Option<lsp::CompletionResponse> {
        None
    }

    /// Handle jump-to-definition.
    fn handle_goto_def(
        &mut self,
        _st: &mut State,
        _p: lsp::GotoDefinitionParams,
    ) -> Option<lsp::GotoDefinitionResponse> {
        None
    }

    /// Handle message and optionally return a reply.
    fn handle_other_msg(&mut self, _st: &mut State, msg: IncomingMsg) -> Result<Option<String>> {
        Err(anyhow!("lsp: method not implemented: '{}'", msg.m))
    }
}

/// Produce a handler for each incoming message.
pub struct HandlerFactory(pub Box<dyn (FnMut() -> Box<dyn Handler>)>);

/// The server.
pub struct Server {
    st: State,
    handler: HandlerFactory,
}

impl State {
    /// New state.
    pub fn new() -> Self {
        Self(Arc::new(Mutex::new(StateImpl {
            docs: Default::default(),
        })))
    }
}

impl StateImpl {
    /// Access document by URI.
    pub fn get_doc(&self, id: &DocID) -> Option<&Doc> {
        self.docs.get(&id.uri)
    }
}

/// A jsonrpc message, as read.
#[derive(Debug)]
pub struct IncomingMsg {
    pub m: String,
    pub params: JsonValue,
    pub id: JsonValue,
}

mod server {
    use super::*;

    fn write_msg_(out: &mut dyn Write, s: &str) -> Result<()> {
        let bytes = s.as_bytes();
        write!(out, "Content-Length: {}\r\n\r\n", bytes.len())
            .map_err(|e| anyhow!("cannot write header on stdout: {}", e))?;
        let mut bytes = bytes;
        while bytes.len() > 0 {
            let n = out
                .write(bytes)
                .map_err(|e| anyhow!("cannot write content ({}B) on stdout: {}", bytes.len(), e))?;
            bytes = &bytes[n..];
        }
        out.flush()
            .map_err(|e| anyhow!("cannot flush stdout: {}", e))?;
        Ok(())
    }

    /*
    fn write_thread_loop_(s: chan::Receiver<String>) -> Result<()> {
        let stdout = std::io::stdout();
        let mut stdout = stdout.lock();

        while let Ok(x) = s.recv() {
            log::debug!("send-thr: write {:?}", x);

            // try several times
            if let Err(e) = write_msg_(&mut stdout, &x) {
                log::error!("error when writing message: {}", e);
                return Err(anyhow!("cannot write to stdout"));
            }
        }
        Ok(())
    }

    /// Thread that writes on stdout.
    fn write_thread(s: chan::Receiver<String>) {
        let r = write_thread_loop_(s);
        log::info!("writer thread quits with {:?}", r);
        r.expect("writer thread failed")
    }
    */

    fn read_until_pos<I, F>(
        chars: &mut std::iter::Peekable<I>,
        pos: &mut lsp::Position,
        until: lsp::Position,
        mut f: F,
    ) -> Result<()>
    where
        F: FnMut(char),
        I: Iterator<Item = char>,
    {
        // catch up in `chars`
        while *pos < until {
            let c = chars.peek().ok_or_else(|| anyhow!("peek"))?;
            if *c == '\n' {
                pos.line += 1;
                pos.character = 0;
            } else {
                pos.character += 1;
            }
            f(*c);
            chars.next();
        }
        Ok(())
    }

    fn handle_msg_(
        mut st: State,
        mut h: Box<dyn Handler>,
        msg: IncomingMsg,
    ) -> Result<Option<String>> {
        use lsp::notification::*;
        use lsp::request::*;
        use lsp::*;

        macro_rules! mk_reply {
            ($j: expr) => {
                serde_json::to_string(&json!({
                    "id": msg.id,
                    "result": $j,
                }))?
            }
        }
        macro_rules! mk_notif {
            ($m: expr, $params: expr) => {{
                serde_json::to_string(&json!({
                    "jsonrpc": "2.0",
                    "method": $m,
                    "params": $params,
                }))?
            }}
        }

        // NOTE: ugh. we need to reserialize before we can deserialize from Value?
        let params = msg.params.to_string();

        if msg.m == lsp::request::Initialize::METHOD {
            log::debug!("got initialize");
            let _init: InitializeParams = serde_json::from_str(&params)?;
            let mut capabilities = ServerCapabilities::default();

            // require incremental updates
            capabilities.text_document_sync = Some(lsp::TextDocumentSyncCapability::Options(
                lsp::TextDocumentSyncOptions {
                    open_close: Some(false),
                    change: Some(lsp::TextDocumentSyncKind::Incremental),
                    will_save: Some(false),
                    will_save_wait_until: Some(false),
                    save: None,
                },
            ));

            // TODO: declare more actual capabilities
            let reply = InitializeResult {
                capabilities,
                server_info: Some(ServerInfo {
                    name: "trustee".to_string(), // TODO ask the handler?
                    version: None,
                }),
            };

            Ok(Some(mk_reply!(reply)))
        } else if msg.m == lsp::notification::DidOpenTextDocument::METHOD {
            log::debug!("got text open {:?}", msg.params);
            let d: DidOpenTextDocumentParams = serde_json::from_str(&params)?;
            let td = d.text_document;
            let id = DocID::new(td.uri.clone());

            // update doc
            let mut st = st
                .lock()
                .map_err(|_| anyhow!("cannot lock state in text/open"))?;
            let doc = Doc {
                id: id.clone(),
                version: td.version.clone(),
                content: td.text.clone(),
            };
            st.docs.insert(td.uri.clone(), doc);

            // get diagnostics
            let diagnostics = h.on_doc_update(id, &td.text)?;

            let reply = PublishDiagnosticsParams {
                uri: td.uri,
                version: Some(td.version),
                diagnostics,
            };
            drop(st); // unlock
            Ok(Some(mk_notif!(PublishDiagnostics::METHOD, reply)))
        } else if msg.m == DidCloseTextDocument::METHOD {
            log::debug!("got text close {:?}", params);

            let d: DidCloseTextDocumentParams = serde_json::from_str(&params)?;
            let td = d.text_document;
            let id = DocID::new(td.uri.clone());

            {
                let mut st = st
                    .lock()
                    .map_err(|_| anyhow!("cannot lock state in text/close"))?;
                st.docs.remove(&td.uri);
            }

            h.on_remove_doc(id);
            Ok(None)
        } else if msg.m == lsp::notification::DidChangeTextDocument::METHOD {
            log::debug!("got text change {:?}", params);

            let mut d: DidChangeTextDocumentParams = serde_json::from_str(&params)?;
            let td = d.text_document;
            let id = DocID::new(td.uri.clone());

            // update doc
            let mut st = st.lock().expect("cannot lock state");
            let doc = st
                .docs
                .get_mut(&td.uri)
                .ok_or_else(|| anyhow!("unknown document"))?;

            // update version
            if let Some(v) = td.version {
                doc.version = v;
            }
            let version = doc.version.clone();

            // update content
            if d.content_changes.len() == 1 && d.content_changes[0].range.is_none() {
                let change = &mut d.content_changes[0];
                log::debug!("consider full-text change {:?}", change);
                // directly update
                std::mem::swap(&mut doc.content, &mut change.text);
            } else {
                log::debug!("process {} individual changes", d.content_changes.len());
                // sanity check
                for change in &d.content_changes {
                    if change.range.is_none() {
                        return Err(anyhow!("change without a range"));
                    }
                }

                // apply patches, but in reverse position order
                d.content_changes.sort_by_key(|c| c.range.unwrap().start);

                let mut new_text = String::new();

                // state in text.
                let mut chars = doc.content.chars().peekable();
                let mut pos = Position {
                    line: 0,
                    character: 0,
                };

                for change in d.content_changes {
                    log::debug!("consider change {:?}", change);

                    let range = change
                        .range
                        .ok_or_else(|| anyhow!("change must have a range"))?;

                    // catch up in `chars`
                    read_until_pos(&mut chars, &mut pos, range.start, |c| new_text.push(c))?;
                    // insert change
                    new_text.push_str(&change.text);
                    // skip replaced content
                    read_until_pos(&mut chars, &mut pos, range.end, |_| ())?;
                }
                doc.content = new_text;
            }

            let diagnostics = h.on_doc_update(id, &doc.content)?;
            log::debug!("return diagnostics: {:#?}", diagnostics);
            let reply = PublishDiagnosticsParams {
                uri: td.uri,
                version: Some(version),
                diagnostics,
            };
            drop(st); // unlock
            Ok(Some(mk_notif!("textDocument/publishDiagnostics", reply)))
        } else if msg.m == lsp::request::HoverRequest::METHOD {
            log::debug!("got hover request {:?}", params);
            let d: HoverParams = serde_json::from_str(&params)?;
            let r = h.handle_hover(&mut st, d)?;
            match r {
                Some(r) => Ok(Some(mk_reply!(r))),
                None => Ok(Some(mk_reply!(Hover {
                    contents: HoverContents::Scalar(lsp::MarkedString::String(
                        "<no information>".to_string()
                    )),
                    range: None
                }))),
            }
        } else if msg.m == lsp::request::Completion::METHOD {
            log::debug!("got completion request {:?}", params);
            let d: CompletionParams = serde_json::from_str(&params)?;
            let r = h
                .handle_completion(&mut st, d)
                .unwrap_or_else(|| lsp::CompletionResponse::Array(vec![]));
            Ok(Some(mk_reply!(r)))
        } else if msg.m == lsp::request::GotoDefinition::METHOD {
            log::debug!("got goto-def request {:?}", params);
            let d: GotoDefinitionParams = serde_json::from_str(&params)?;
            let r = h
                .handle_goto_def(&mut st, d)
                .unwrap_or_else(|| lsp::GotoDefinitionResponse::Array(vec![]));
            Ok(Some(mk_reply!(r)))
        } else {
            // fallback
            h.handle_other_msg(&mut st, msg)
        }
    }

    /// Handle incoming message.
    fn handle_msg(st: State, h: Box<dyn Handler>, msg: IncomingMsg) {
        log::trace!("handle msg {:?}", msg);
        let mid = msg.id.clone();

        let r = handle_msg_(st, h, msg);
        let reply = match r {
            Ok(r) => r,
            Err(e) => {
                if !mid.is_null() {
                    let r = json!({
                        "id": mid,
                        "error": {
                            "code": -32603,
                            "message": e.to_string(),
                        }
                    });
                    log::error!("error with reply: {}", e);
                    Some(r.to_string())
                } else {
                    // must be a notification, can't reply with an error
                    log::error!("error with no reply: {}", e);
                    None
                }
            }
        };

        // send reply back
        if let Some(r_s) = reply {
            log::debug!("reply with {:?}", r_s);

            let stdout = std::io::stdout();
            let mut stdout = stdout.lock();
            let rsend = write_msg_(&mut stdout, &r_s);

            // log error
            if let Err(e) = rsend {
                log::error!("handle-thr: cannot send to writer: {}", e);
            }
        } else {
            log::debug!("no reply");
        }
    }

    impl Server {
        /// Create the state.
        ///
        /// The function `h` is called to create a new handler for every incoming
        /// request.
        pub fn new(h: HandlerFactory) -> Self {
            let st = State::new();
            Self { st, handler: h }
        }

        fn serve_loop(&mut self) -> Result<()> {
            log::info!("start serving");
            let stdin = std::io::stdin();
            let mut stdin = stdin.lock();
            let mut stdin = std::io::BufReader::new(&mut stdin);

            let mut s = String::new();
            let mut buf = vec![];
            loop {
                // read headers until we get length
                let mut len = 0;
                loop {
                    s.clear();
                    stdin.read_line(&mut s)?;
                    if s.trim().is_empty() {
                        break;
                    }
                    s.make_ascii_lowercase();
                    log::trace!("got header {}", &s);
                    if s.starts_with("content-length:") {
                        let i = s.find(':').ok_or_else(|| anyhow!("invalid length"))?;
                        len = s[i + 1..].trim().parse()?;
                    }
                }
                log::debug!("need to read {} bytes", len);
                buf.clear();
                buf.resize(len, b'\x00');
                stdin
                    .read_exact(&mut buf[..])
                    .map_err(|e| anyhow!("trying to read {} bytes, but:\n{}", len, e))?;
                log::trace!("read: {:?}", &buf);

                // parse as json
                let j: JsonValue = serde_json::from_slice::<JsonValue>(&buf)
                    .map_err(|e| anyhow!("invalid json payload: {}", e))?;
                log::trace!("got json payload: {:?}", j);

                let j2_0 = json!("2.0");
                if j.get("jsonrpc") != Some(&j2_0) {
                    log::error!("invalid `jsonrpc` field in {:?}", j);
                }

                let m = j
                    .get("method")
                    .and_then(|x| x.as_str())
                    .ok_or_else(|| anyhow!("no `method` field"))?
                    .to_string();
                let params = j.get("params").cloned().unwrap_or(json!(null));
                let id = j.get("id").cloned().unwrap_or(json!(null));

                let raw_msg = IncomingMsg { m, params, id };
                {
                    let st = self.st.clone();
                    let h = (self.handler.0)();
                    thread::spawn(move || handle_msg(st, h, raw_msg));
                }
            }
        }

        /// Serve on stdin/stdout.
        pub fn serve(mut self) -> Result<()> {
            let r = self.serve_loop();
            log::debug!("serve-loop exited with {:?}", &r);
            r
        }
    }
}
