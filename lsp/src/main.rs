use anyhow::{anyhow, Result};
use lsp_types::{self as lsp};
use trustee::{self, kernel_of_trust as k, meta, meta::Position};
use trustee_utils as utils;

pub mod server;
pub use server::{Doc, DocID, Server, State};

struct TrusteeSt;

fn pos(p: Position) -> lsp::Position {
    // translate back
    lsp::Position {
        line: p.line as u64 - 1,
        character: p.col as u64 - 1,
    }
}

impl server::Handler for TrusteeSt {
    fn on_doc_update(&mut self, _id: DocID, txt: &str) -> Result<Vec<lsp::Diagnostic>> {
        let mut ctx = k::Ctx::new();
        meta::load_prelude_hol(&mut ctx)?;

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
        for r in r.res.drain(..) {
            let range = lsp::Range {
                start: pos(r.start),
                end: pos(r.end),
            };

            if let Some(s) = r.stdout {
                diags.push(mk_diag!(lsp::DiagnosticSeverity::Hint, range, s.clone()));
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
