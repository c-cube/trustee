use anyhow::{anyhow, Result};
use lsp_types::{self as lsp};
use trustee::{self, kernel_of_trust as k, meta, meta::Position};
use trustee_utils as utils;

pub mod server;
pub use server::{Doc, DocID, Server, State};

struct TrusteeSt;

/// Translate a position to a LSP position
fn pos_to_lsp(p: Position) -> lsp::Position {
    lsp::Position {
        line: p.line as u64 - 1,
        character: p.col as u64 - 1,
    }
}

/// Translate back.
fn pos_of_lsp(p: lsp::Position) -> Position {
    Position {
        line: p.line as usize + 1,
        col: p.character as usize + 1,
    }
}

impl server::Handler for TrusteeSt {
    fn on_doc_update(&mut self, _id: DocID, txt: &str) -> Result<Vec<lsp::Diagnostic>> {
        let mut ctx = k::Ctx::new();

        let mut r = utils::eval(&mut ctx, txt, None);
        log::debug!("eval: got {} results in {:?}", r.res.len(), r.duration);

        macro_rules! mk_diag {
            ($sev: expr, $range: expr, $msg: expr) => {
                lsp::Diagnostic {
                    range: $range,
                    severity: Some($sev),
                    code: None,
                    source: None,
                    message: $msg,
                    related_information: None,
                    tags: None,
                }
            };
        }

        let mut diags = vec![];
        for mut r in r.res.drain(..) {
            let range = lsp::Range {
                start: pos_to_lsp(r.start),
                end: pos_to_lsp(r.end),
            };

            // stdout
            if let Some(s) = r.stdout {
                diags.push(mk_diag!(lsp::DiagnosticSeverity::Hint, range, s.clone()));
            }

            // tracing events
            for (pos, v) in r.traces.drain(..) {
                let range = lsp::Range {
                    start: pos_to_lsp(pos),
                    end: pos_to_lsp(pos),
                };
                let s = format!("trace: {}", v);
                diags.push(mk_diag!(lsp::DiagnosticSeverity::Hint, range, s));
            }

            let severity = if r.res.is_ok() {
                lsp::DiagnosticSeverity::Information
            } else {
                lsp::DiagnosticSeverity::Error
            };

            let message = match r.res {
                Ok(meta::Value::Nil) => continue,
                Ok(v) => format!("yield value {}", v),
                Err(e) => format!("error: {}", e),
            };
            diags.push(mk_diag!(severity, range, message));
        }

        Ok(diags)
    }

    fn handle_hover(&mut self, st: &mut State, p: lsp::HoverParams) -> Result<Option<lsp::Hover>> {
        let d = p.text_document_position_params.text_document;
        let pos = pos_of_lsp(p.text_document_position_params.position);
        let st = st.lock().unwrap();
        if let Some(doc) = st.get_doc(&d) {
            log::debug!("inspect in document {:?} at {:?}", &d, pos);
            let mut ctx = k::Ctx::new();

            // FIXME: redirect stdout
            // ignore errors here!
            let _ = meta::run_code(&mut ctx, &doc.content, None);

            if let Some((s, start, end)) = utils::inspect(&mut ctx, &doc.content, pos) {
                let contents = lsp::HoverContents::Scalar(lsp::MarkedString::String(s));
                let start = pos_to_lsp(start.pos);
                let end = pos_to_lsp(end.pos);
                let rep = lsp::Hover {
                    contents,
                    range: Some(lsp::Range { start, end }),
                };
                Ok(Some(rep))
            } else {
                Ok(None)
            }
        } else {
            log::debug!("no known document for {:?}", &d);
            Ok(None)
        }
    }

    fn handle_completion(
        &mut self,
        st: &mut State,
        p: lsp::CompletionParams,
    ) -> Option<lsp::CompletionResponse> {
        let d = p.text_document_position.text_document;
        let pos = pos_of_lsp(p.text_document_position.position);
        let st = st.lock().unwrap();
        if let Some(doc) = st.get_doc(&d) {
            log::debug!("complete in document {:?} at {:?}", &d, pos);
            let mut ctx = k::Ctx::new();

            // FIXME: redirect stdout
            // ignore errors here!
            let _ = meta::run_code(&mut ctx, &doc.content, None);

            let mut c = vec![];
            if let Some(res) = utils::completion(&mut ctx, &doc.content, pos) {
                for x in res.matches {
                    let item = lsp::CompletionItem::new_simple(x, "".to_string());
                    c.push(item)
                }
            }
            let rep = lsp::CompletionResponse::Array(c);
            Some(rep)
        } else {
            log::debug!("no known document for {:?}", &d);
            None
        }
    }
}

fn main() -> Result<()> {
    use {simplelog::*, std::fs::File};
    WriteLogger::init(
        LevelFilter::Warn,
        Config::default(),
        File::create("/tmp/trustee_lsp.log")?,
    )
    .map_err(|e| anyhow!("failed to init logger: {}", e))?;
    let factory = server::HandlerFactory(Box::new(|| Box::new(TrusteeSt)));
    let server = Server::new(factory);
    server.serve()?;
    Ok(())
}
