use anyhow::{anyhow, Result};
use jupyter_kernel as jy;
use std::{collections::HashMap, time};
use trustee::{
    self, kernel_of_trust as k,
    meta::{self, lexer::Tok, Value},
    Error,
};

/// Builtins specific to jupyter.
const BUILTINS: &'static [&'static meta::InstrBuiltin] = &[&trustee::defbuiltin!(
    "import_ot",
    "`import_ts \"file\"+` imports theorems from the opentheory file(s)",
    |ctx, _out, args| {
        trustee::check_arity!("import_ot", args, >= 1);
        let mut vm = trustee_opentheory::VM::new(ctx);
        for file in args {
            let file = file.as_str().ok_or_else(|| Error::new("expect a string"))?;
            log::info!("parse opentheory file '{}'", file);
            vm.parse_file(file)?;
        }
        let art = vm.into_article();
        log::debug!("got article: {:#?}", &art);
        let l: Value = art.theorems.into();
        Ok(l)
    }
)];

/// The core structure for the jupyter kernel.
struct EvalTrustee {
    _ctx: Option<k::Ctx>,
}

#[derive(Debug, Copy, Clone)]
enum TokKind {
    Id,
    QuotedStr,
}

/// Find identifier the cursor is on (or just after)
fn find_tok(s: &str, cursor_pos: usize) -> Option<(String, TokKind, usize, usize)> {
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
            match lexer.cur() {
                Tok::Id(s) => {
                    log::debug!("relevant token is {:?} (range {}--{})", s, start, end);
                    return Some((s.to_string(), TokKind::Id, start, end));
                }
                Tok::QuotedString(s) => {
                    log::debug!("relevant token is {:?} (range {}--{})", s, start, end);
                    return Some((s.to_string(), TokKind::QuotedStr, start, end));
                }
                _ => {
                    log::debug!("outside any identifier");
                    return None;
                }
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
            codemirror_mode: "text/x-trustee".to_string(),
            pygment_lexer: "trustee".to_string(),
            file_extension: "trustee".to_string(),
            mimetype: "text/plain".to_string(),
        }
    }

    fn eval(&mut self, code: &str, execution_count: usize) -> jy::EvalResult {
        log::debug!("eval code=`{}`, execution_cout={}", code, execution_count);

        let src = format!("cell {}", execution_count);
        let start = time::Instant::now();
        let mut vm = meta::VM::new(self.ctx());
        let mut stdout = vec![];
        vm.set_stdout(&mut stdout);

        // evaluate `code`
        let eval_res = vm.run(code, Some(src.into()));

        let dur = time::Instant::now().duration_since(start);
        let timing = if dur.as_millis() > 500 {
            Some(dur)
        } else {
            None
        };

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

        // TODO: more mimetypes? return some html when we can
        let mut res = jy::EvalResult {
            res: Ok(()),
            content_by_mime_type: HashMap::new(),
            timing,
            raw_stderr: None,
            raw_stdout,
        };

        match eval_res {
            Ok(v) => {
                if v != meta::Value::Nil {
                    res.content_by_mime_type
                        .insert("text/plain".to_string(), format!("{}", v));
                }
            }
            Err(e) => {
                res.res = Err(anyhow!("evaluation failed:\n{}", e));
            }
        };

        res
    }

    fn inspect(&mut self, code: &str, cursor_pos: usize) -> Option<String> {
        log::debug!(
            "inspect request for code=`{}`, cursor_pos={}",
            code,
            cursor_pos
        );

        if let Some((tok, TokKind::Id, _start, _end)) = find_tok(code, cursor_pos) {
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

        let mut compls: Vec<String> = vec![];
        let mut add_compl = |s: &str| compls.push(s.to_string());

        let tok = find_tok(code, cursor_pos); // find token of interest
        if let Some((tok, TokKind::Id, start, end)) = tok {
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
        } else if let Some((tok, TokKind::QuotedStr, start, end)) = tok {
            // complete file names
            use std::path::Path;
            let path = Path::new(&tok);
            log::info!("complete quoted string as path '{:?}'", path);
            let dir = if path.is_file() { path.parent()? } else { path };
            for x in dir.read_dir().ok()? {
                let path2 = dir.join(x.ok()?.path());
                if let Some(p2) = path2.to_str() {
                    add_compl(p2);
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
            // add our custom builtins
            for x in BUILTINS {
                ctx.set_meta_value(x.name, Value::Builtin(x))
            }
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
