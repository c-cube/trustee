use anyhow::{anyhow, Result};
pub use lsp_types::{self as lsp, TextDocumentIdentifier as DocID};
use serde::Deserialize;
use serde_json::{json, Value as JsonValue};
use std::{
    collections::HashMap,
    io::{BufRead, Read, Write},
    sync::{atomic, mpsc as chan, Arc, Mutex},
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
    pub nid: atomic::AtomicU32,
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
    fn handle_hover(&mut self, _p: lsp::HoverParams) -> Result<Option<lsp::Hover>> {
        Ok(None)
    }

    /// Handle completion requests.
    fn handle_completion(&mut self, _p: lsp::CompletionParams) -> Option<lsp::CompletionResponse> {
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
    write_th: thread::JoinHandle<()>,
    /// Send serialized replies
    send: chan::Sender<String>,
}

impl State {
    /// New state.
    pub fn new() -> Self {
        Self(Arc::new(Mutex::new(StateImpl {
            nid: atomic::AtomicU32::new(0),
            docs: Default::default(),
        })))
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

    /// Thread that writes on stdout.
    fn write_thread(s: chan::Receiver<String>) {
        let stdout = std::io::stdout();
        let mut stdout = stdout.lock();
        let mut stdout = std::io::BufWriter::new(&mut stdout);
        while let Ok(x) = s.recv() {
            let bytes = x.as_bytes();
            write!(&mut stdout, "Content-Length: {}\r\n\r\n", bytes.len())
                .expect("cannot write on stdout");
            stdout.write(bytes).expect("cannot write on stdout");
            stdout.flush().expect("cannot flush stdout");
        }
        log::info!("writer thread quits");
    }

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
        };
        macro_rules! mk_notif {
            ($m: expr, $params: expr) => {{
                let st = st.0.lock().map_err(|_| anyhow!("cannot lock state in mk_notif"))?;
                serde_json::to_string(&json!({
                    "jsonrpc": "2.0",
                    "id": st.nid.fetch_add(1, atomic::Ordering::SeqCst),
                    "method": $m,
                    "params": $params,
                }))?
            }}
        };

        // NOTE: ugh. we need to reserialize before we can deserialize from Value?
        let params = msg.params.to_string();

        if msg.m == lsp::request::Initialize::METHOD {
            log::debug!("got initialize");
            let _init: InitializeParams = serde_json::from_str(&params)?;
            let mut capabilities = ServerCapabilities::default();

            // require incremental updates
            capabilities.text_document_sync = Some(lsp::TextDocumentSyncCapability::Kind(
                lsp::TextDocumentSyncKind::Incremental,
            ));

            // TODO: declare more actual capabilities
            let reply = InitializeResult {
                capabilities,
                server_info: None, // TODO ask the handler?
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
            Ok(Some(mk_notif!("textDocument/publishDiagnostics", reply)))
        } else if msg.m == lsp::notification::DidCloseTextDocument::METHOD {
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
            let r = h.handle_hover(d)?;
            Ok(match r {
                Some(r) => Some(mk_reply!(r)),
                None => None,
            })
        } else {
            // fallback
            h.handle_other_msg(&mut st, msg)
        }
    }

    /// Handle incoming message.
    fn handle_msg(st: State, send: chan::Sender<String>, h: Box<dyn Handler>, msg: IncomingMsg) {
        log::trace!("handle msg {:?}", msg);
        let mid = msg.id.clone();

        let r = handle_msg_(st, h, msg);
        let reply = match r {
            Ok(r) => r,
            Err(e) => {
                let r = json!({
                    "id": mid,
                    "error": {
                        "code": -32603,
                        "message": e.to_string(),
                    }
                });
                Some(r.to_string())
            }
        };

        // send reply back
        if let Some(r_s) = reply {
            log::debug!("reply with {:?}", r_s);
            send.send(r_s).expect("cannot send to writer");
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
            let (send, recv) = chan::channel();
            let write_th = thread::spawn(move || write_thread(recv));
            Self {
                st,
                handler: h,
                send,
                write_th,
            }
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
                    let send = self.send.clone();
                    let st = self.st.clone();
                    let h = (self.handler.0)();
                    thread::spawn(move || handle_msg(st, send, h, raw_msg));
                }
            }
        }

        /// Serve on stdin/stdout.
        pub fn serve(mut self) -> Result<()> {
            let r = self.serve_loop();
            log::debug!("serve-loop exited with {:?}", &r);
            self.write_th
                .join()
                .map_err(|_| anyhow!("cannot join writer thread"))?;
            r
        }
    }
}
