use crossbeam_channel::{Receiver, Sender};
use gen_lsp_server::{handle_shutdown, stdio_transport, RawMessage, RawResponse};
use lsp_types::{
    self as lsp,
    request::{GotoDefinition, GotoDefinitionResponse},
    InitializeParams, ServerCapabilities,
};
use std::collections::HashMap;
use trustee::{self, kernel_of_trust as k};

#[derive(Debug)]
struct Doc {
    id: lsp::TextDocumentIdentifier,
    version: u64,
    content: String,
}

struct State {
    docs: HashMap<lsp_types::Url, Doc>,
}

impl State {
    pub fn new() -> Self {
        Self {
            docs: Default::default(),
        }
    }
}

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
    Ok(())
}

fn main() -> Result<(), failure::Error> {
    flexi_logger::Logger::with_env_or_str("trustee=info,sync_lsp_server=debug")
        .log_to_file()
        .directory("/tmp")
        .start()
        .unwrap();
    let (receiver, sender, io_threads) = stdio_transport();
    gen_lsp_server::run_server(ServerCapabilities::default(), receiver, sender, main_loop)?;
    io_threads.join()?;
    Ok(())
}
