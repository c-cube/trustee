use anyhow::{anyhow, Result};
use lsp_types::{
    self as lsp, request::GotoDefinition, InitializeParams, ServerCapabilities,
    TextDocumentIdentifier as DocID,
};
use serde::Deserialize;
use serde_json::{json, Value as JsonValue};
use std::{
    collections::HashMap,
    io::BufRead,
    io::Read,
    io::Write,
    sync::{mpsc as chan, Arc, Mutex},
    thread,
};
use trustee::{self, kernel_of_trust as k, meta};

/// A single, versioned, document.
#[derive(Debug)]
struct Doc {
    id: DocID,
    version: u64,
    content: String,
}

/// State shared among threads.
#[derive(Clone)]
struct State(Arc<Mutex<StateImpl>>);

#[derive(Debug)]
struct StateImpl {
    docs: HashMap<lsp_types::Url, Doc>,
}

/// The server.
struct Server {
    st: State,
    write_th: thread::JoinHandle<()>,
    /// Send serialized replies
    send: chan::Sender<String>,
}

impl State {
    /// New state.
    pub fn new() -> Self {
        Self(Arc::new(Mutex::new(StateImpl {
            docs: Default::default(),
        })))
    }
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
    }

    /// A jsonrpc message, as read.
    #[derive(Debug)]
    struct IncomingMsg {
        m: String,
        params: JsonValue,
        id: JsonValue,
    }

    /// Handle incoming message.
    fn handle_msg(send: chan::Sender<String>, msg: IncomingMsg) {
        log::debug!("handle incoming msg {:?}", msg);
        todo!()
    }

    impl Server {
        /// Create the state.
        pub fn new() -> Self {
            let st = State::new();
            let (send, recv) = chan::channel();
            let write_th = thread::spawn(move || write_thread(recv));
            Self { st, send, write_th }
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
                    thread::spawn(move || handle_msg(send, raw_msg));
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

/*
fn main_loop(
    _params: InitializeParams,
    receiver: &Receiver<RawMessage>,
    sender: &Sender<RawMessage>,
) -> Result<(), failure::Error> {
    let mut st = State::new();
    for msg in receiver {
        match msg {
            RawMessage::Request(req) => {
                let req = match handle_shutdown(req, sender) {
                    None => return Ok(()),
                    Some(req) => req,
                };
                let req = match req.cast::<GotoDefinition>() {
                    Ok((id, _params)) => {
                        let resp = RawResponse::ok::<GotoDefinition>(
                            id,
                            &Some(GotoDefinitionResponse::Array(Vec::new())),
                        );
                        sender.send(RawMessage::Response(resp))?;
                        continue;
                    }
                    Err(req) => req,
                };
                // ...
            }
            RawMessage::Response(_resp) => (),
            RawMessage::Notification(_not) => {}
        }
    }
    st.Ok(())
}
*/

fn main() -> Result<()> {
    use {simplelog::*, std::fs::File};
    WriteLogger::init(
        LevelFilter::Debug,
        Config::default(),
        File::create("/tmp/trustee_lsp.log")?,
    )
    .map_err(|e| anyhow!("failed to init logger: {}", e))?;
    let server = Server::new();
    server.serve()?;
    Ok(())
}
