use anyhow::{anyhow, Result};
use jupyter_kernel as jy;
use std::{collections::HashMap, io::Write, time};
use trustee::{
    kernel_of_trust as k,
    meta::{self, lexer::Tok},
};

struct EvalTrustee {
    _ctx: Option<k::Ctx>,
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
        let mut vm = meta::VM::new(self.ctx());
        let mut stdout = vec![];
        vm.set_stdout(&mut stdout);
        match vm.run(code, Some(src.into())) {
            Ok(v) => {
                let dur = time::Instant::now().duration_since(start);

                let raw_stdout = match std::string::String::from_utf8(stdout) {
                    Ok(s) => {
                        log::debug!("stdout: {:?}", s);
                        if s.len() > 0 {
                            Some(s)
                        } else {
                            None
                        }
                    }
                    _ => None,
                };

                // TODO: mimetypes
                let mut outs = jy::EvalOutputs {
                    content_by_mime_type: HashMap::new(),
                    timing: if dur.as_millis() > 500 {
                        Some(dur)
                    } else {
                        None
                    },
                    raw_stderr: None,
                    raw_stdout,
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
            if let Some(v) = self.ctx().find_meta_value(&tok) {
                let help = match v {
                    meta::Value::Closure(c) => c
                        .docstring()
                        .map(|s| format!("\n\n{}", s))
                        .unwrap_or("".to_string()),
                    _ => "".to_string(),
                };
                return Some(format!("[value]: {}{}", v, help));
            } else if let Some((v, hlp)) = meta::all_builtin_names_and_help().find(|v| v.0 == tok) {
                return Some(format!("[builtin]: {}\n\n{}", v, hlp));
            }
        }
        None
    }

    fn code_is_complete(&mut self, code: &str) -> Option<bool> {
        let mut lex = meta::lexer::Lexer::new(code, None);
        let mut depth: isize = 0;

        loop {
            match lex.cur() {
                Tok::Eof => return Some(depth <= 0),
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen | Tok::RBracket | Tok::RBrace => depth -= 1,
                Tok::Id(..)
                | Tok::ColonId(..)
                | Tok::QuotedString(..)
                | Tok::QuotedExpr(..)
                | Tok::Int(..) => (),
                Tok::Invalid(_) => return None,
            }
            lex.next();
        }
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

            for (s, _e) in self.ctx().iter_meta_values() {
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
        Ok(Self { _ctx: None })
    }

    /// Access the inner context.
    fn ctx(&mut self) -> &mut k::Ctx {
        if let None = &mut self._ctx {
            let mut ctx = k::Ctx::new();
            meta::load_prelude_hol(&mut ctx).expect("failed to load prelude");
            self._ctx = Some(ctx);
        }
        self._ctx.as_mut().unwrap()
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
