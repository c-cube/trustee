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
                outs.content_by_mime_type
                    .insert("text/plain".to_string(), format!("{}", v));

                Ok(outs)
            }
            Err(e) => Err(anyhow!("evaluation failed:\n{}", e)),
        }
    }

    fn inspect(&mut self, code: &str, cursor_pos: usize) -> Option<String> {
        let mut last_tok = None;

        {
            let mut lexer = meta::lexer::Lexer::new(code, None);
            loop {
                let t = lexer.cur().clone();
                if t == Tok::Eof {
                    break;
                }
                last_tok = Some(t);
                lexer.next();
                if lexer.offset() >= cursor_pos {
                    break;
                }
            }
        }

        let token = match last_tok {
            Some(Tok::Id(pre)) => pre,
            _ => return None,
        };

        if let Some(v) = self.ctx.find_meta_value(token) {
            Some(format!("value: {}", v))
        } else if let Some((v, hlp)) = meta::all_builtin_names_and_help().find(|v| v.0 == token) {
            Some(format!("builtin {}:\n{}", v, hlp))
        } else {
            None
        }
    }

    fn completion(&mut self, code: &str, cursor_pos: usize) -> Option<jy::CompletionRes> {
        let mut last_tok = None;
        let mut off1 = 0; // offset at which last_tok starts
        let mut off2 = 0; // offset at which last_tok ends

        {
            let mut lexer = meta::lexer::Lexer::new(code, None);
            loop {
                let t = lexer.cur().clone();
                if t == Tok::Eof {
                    off2 = lexer.offset();
                    break;
                }
                last_tok = Some(t);
                off1 = lexer.offset();
                lexer.next();
                if lexer.offset() >= cursor_pos {
                    off2 = lexer.offset();
                    break;
                }
            }
        }

        let mut compls: Vec<String> = vec![];

        let token = match last_tok {
            Some(Tok::Id(pre)) => pre,
            _ => return None,
        };

        let mut add_compl = |s: &str| compls.push(s.to_string());

        for (s, _e) in self.ctx.iter_meta_values() {
            if s.starts_with(token) {
                add_compl(s)
            }
        }
        for s in meta::all_builtin_names() {
            if s.starts_with(token) {
                add_compl(s)
            }
        }

        if compls.len() > 0 {
            log::info!("found {} completions", compls.len());
            log::debug!("completions: {:#?}", compls);
            Some(jy::CompletionRes {
                cursor_start: off1,
                cursor_end: off2,
                matches: compls,
            })
        } else {
            None
        }
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
