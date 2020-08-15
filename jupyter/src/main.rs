use anyhow::{anyhow, Result};
use jupyter_kernel as jy;
use std::{collections::HashMap, time};
use trustee::{
    kernel_of_trust as k,
    meta::{self, lexer::Tok},
};

struct EvalTrustee {
    ctx: k::Ctx,
}

/// Find identifier the cursor is on (or just after)
fn find_tok(s: &str, cursor_pos: usize) -> Option<(String, usize, usize)> {
    let mut lexer = meta::lexer::Lexer::new(s, None);
    loop {
        let t = lexer.cur().clone();
        if t == Tok::Eof {
            break;
        }

        let start = lexer.token_start_offset();
        let end = lexer.token_end_offset();

        if start <= cursor_pos && end >= cursor_pos {
            // here is where we want to complete
            if let Tok::Id(s) = lexer.cur() {
                log::debug!("relevant token is {:?} (range {}--{})", s, start, end);
                return Some((s.to_string(), start, end));
            } else {
                log::debug!("outside any identifier");
                return None;
            }
        } else {
            // go to next token
            lexer.next();
        }
    }
    None
}

impl jy::EvalContextImpl for EvalTrustee {
    fn meta(&self) -> jy::MetaData {
        jy::MetaData {
            language_name: "trustee".to_string(),
            codemirror_mode: "trustee".to_string(),
            pygment_lexer: "trustee".to_string(),
            file_extension: "trustee".to_string(),
            mimetype: "text/plain".to_string(),
        }
    }

    fn eval(&mut self, code: &str, execution_count: usize) -> Result<jy::EvalOutputs> {
        log::debug!("eval code=`{}`, execution_cout={}", code, execution_count);

        let src = format!("cell {}", execution_count);
        let start = time::Instant::now();
        match meta::run_code(&mut self.ctx, code, Some(src.into())) {
            Ok(v) => {
                let dur = time::Instant::now().duration_since(start);
                // TODO: capture `print` output for stdout as an option
                // in trustee::meta (allow redirection)

                // TODO: mimetypes
                let mut outs = jy::EvalOutputs {
                    content_by_mime_type: HashMap::new(),
                    timing: if dur.as_millis() > 500 {
                        Some(dur)
                    } else {
                        None
                    },
                    raw_stderr: None,
                    raw_stdout: None,
                };
                if v != meta::Value::Nil {
                    outs.content_by_mime_type
                        .insert("text/plain".to_string(), format!("{}", v));
                }

                Ok(outs)
            }
            Err(e) => Err(anyhow!("evaluation failed:\n{}", e)),
        }
    }

    fn inspect(&mut self, code: &str, cursor_pos: usize) -> Option<String> {
        log::debug!(
            "inspect request for code=`{}`, cursor_pos={}",
            code,
            cursor_pos
        );

        if let Some((tok, _start, _end)) = find_tok(code, cursor_pos) {
            if let Some(v) = self.ctx.find_meta_value(&tok) {
                return Some(format!("value: {}", v));
            } else if let Some((v, hlp)) = meta::all_builtin_names_and_help().find(|v| v.0 == tok) {
                return Some(format!("builtin {}:\n{}", v, hlp));
            }
        }
        None
    }

    fn completion(&mut self, code: &str, cursor_pos: usize) -> Option<jy::CompletionRes> {
        log::debug!(
            "completion request for code=`{}`, cursor_pos={}",
            code,
            cursor_pos
        );

        if let Some((tok, start, end)) = find_tok(code, cursor_pos) {
            let mut compls: Vec<String> = vec![];

            let mut add_compl = |s: &str| compls.push(s.to_string());

            for (s, _e) in self.ctx.iter_meta_values() {
                if s.starts_with(&tok) {
                    add_compl(s)
                }
            }
            for s in meta::all_builtin_names() {
                if s.starts_with(&tok) {
                    add_compl(s)
                }
            }

            if compls.len() > 0 {
                log::info!("found {} completions", compls.len());
                log::debug!("completions: {:#?}", compls);
                return Some(jy::CompletionRes {
                    cursor_start: start,
                    cursor_end: end,
                    matches: compls,
                });
            }
        }
        log::debug!("no completion found");
        None
    }
}

impl EvalTrustee {
    fn new() -> Result<Self> {
        let mut ctx = k::Ctx::new();
        meta::load_prelude_hol(&mut ctx)?;
        Ok(Self { ctx })
    }
}

fn main() -> Result<()> {
    // setup logging
    use {simplelog::*, std::fs::File};
    WriteLogger::init(
        LevelFilter::Debug,
        Config::default(),
        File::create("/tmp/trustee_jupyter.log")?,
    )
    .map_err(|e| anyhow!("failed to init logger: {}", e))?;

    let ev = Box::new(EvalTrustee::new()?);
    let e = jy::EvalContext::new(move || ev);
    jy::run_main(e)
}
