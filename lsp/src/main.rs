use anyhow::{anyhow, Result};
use lsp_types::{self as lsp, notification::Notification, request::Request};
use serde::Deserialize;
use serde_json::{json, Value as JsonValue};
use std::collections::HashMap;
use trustee::{self, kernel_of_trust as k, meta};

pub mod server;
use lsp::InitializeResult;
pub use server::{Doc, DocID, Server, State};

struct TrusteeSt;

impl server::Handler for TrusteeSt {
    fn handle_msg(&mut self, st: &mut State, msg: server::IncomingMsg) -> Result<Option<String>> {
        use lsp::notification::*;
        use lsp::request::*;
        use lsp::*;

        // NOTE: ugh. we need to reserialize before we can deserialize from Value?
        let params = msg.params.to_string();
        if msg.m == lsp::request::Initialize::METHOD {
            log::debug!("got initialize");
            let _init: InitializeParams = serde_json::from_str(&params)?;
            let capabilities = ServerCapabilities::default();
            // TODO: declare some capabilities
            let reply = InitializeResult {
                capabilities,
                server_info: None,
            };

            Ok(Some(serde_json::to_string(&reply)?))
        } else if msg.m == lsp::notification::DidOpenTextDocument::METHOD {
            log::debug!("got text open {:?}", msg.params);
            let d: DidOpenTextDocumentParams = serde_json::from_str(&params)?;
            let mut st = st.lock().unwrap();
            let td = d.text_document;
            let doc = Doc {
                id: DocID::new(td.uri.clone()),
                version: td.version,
                content: td.text,
            };

            st.docs.insert(td.uri, doc);
            Ok(None)
        } else if msg.m == lsp::notification::DidCloseTextDocument::METHOD {
            log::debug!("got text close {:?}", params);
            let mut st = st.lock().unwrap();
            let d: DidCloseTextDocumentParams = serde_json::from_str(&params)?;
            st.docs.remove(&d.text_document.uri);
            Ok(None)
        } else if msg.m == lsp::notification::DidChangeTextDocument::METHOD {
            log::debug!("got text change {:?}", params);
            // TODO
            Ok(None)
        } else {
            Err(anyhow!("not implemented"))
        }
    }
}

fn main() -> Result<()> {
    use {simplelog::*, std::fs::File};
    WriteLogger::init(
        LevelFilter::Debug,
        Config::default(),
        File::create("/tmp/trustee_lsp.log")?,
    )
    .map_err(|e| anyhow!("failed to init logger: {}", e))?;
    let factory = server::HandlerFactory(Box::new(|| Box::new(TrusteeSt)));
    let server = Server::new(factory);
    server.serve()?;
    Ok(())
}
