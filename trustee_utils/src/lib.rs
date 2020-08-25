use std::time;
use trustee::{
    self, kernel_of_trust as k,
    meta::{self, lexer, lexer::Tok, Value},
    Error,
};

#[derive(Debug, Copy, Clone)]
enum TokKind {
    Id,
    QuotedStr,
}

// TODO: also be able to find token by position
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

pub type Position = meta::Position;

/// Results of evaluation.
#[derive(Debug, Clone)]
pub struct EvalResults {
    pub res: Vec<EvalResult>,
    pub duration: time::Duration,
}

/// Individual result of evaluation.
#[derive(Debug, Clone)]
pub struct EvalResult {
    pub start: Position,
    pub end: Position,
    pub res: std::result::Result<Value, String>,
    pub stdout: Option<String>,
}

/// Evaluate `code`.
pub fn eval(
    ctx: &mut k::Ctx,
    code: &str,
    src: impl Into<Option<trustee::rstr::RStr>>,
) -> EvalResults {
    use std::cell::RefCell;
    log::debug!("eval code=`{}`", code);

    let start = time::Instant::now();
    let mut vm = meta::VM::new(ctx);
    let mut lexer = lexer::Lexer::new(code, src.into());

    let stdout = RefCell::new(String::new());
    let mut fout = |s: &str| {
        let mut out = stdout.borrow_mut();
        out.push_str(&s)
    };
    vm.set_stdout(&mut fout);

    // evaluate `code`
    let mut res = vec![];
    loop {
        let start = lexer.loc();
        // evaluate
        let v = vm.run_lexer_one(&mut lexer);

        let end = lexer.loc();
        let stdout = {
            let mut out = stdout.borrow_mut();
            let mut s = String::new();
            if out.len() > 0 {
                std::mem::swap(&mut s, &mut *out); // consume `out`
                log::debug!("stdout: {:?}", s);
                Some(s)
            } else {
                None
            }
        };

        match v {
            Ok(None) => break,
            Ok(Some(r)) => {
                res.push(EvalResult {
                    start,
                    end,
                    res: Ok(r),
                    stdout,
                });
            }
            Err(e) => {
                let end = lexer.loc();
                res.push(EvalResult {
                    start,
                    end,
                    res: Err(e.to_string()),
                    stdout,
                });
                break;
            }
        }
    }

    let duration = time::Instant::now().duration_since(start);
    EvalResults { res, duration }
}

/// Inspect wht's at this location.
pub fn inspect(ctx: &mut k::Ctx, code: &str, cursor_pos: usize) -> Option<String> {
    log::debug!(
        "inspect request for code=`{}`, cursor_pos={}",
        code,
        cursor_pos
    );

    if let Some((tok, TokKind::Id, _start, _end)) = find_tok(code, cursor_pos) {
        if let Some((v, hlp)) = meta::all_builtin_names_and_help().find(|v| v.0 == tok) {
            return Some(format!("[builtin]: {}\n\n{}", v, hlp));
        } else if let Some(v) = ctx.find_meta_value(&tok) {
            let help = match v {
                meta::Value::Closure(c) => {
                    let doc = c.docstring().unwrap_or("");
                    let bytecode = c.chunk();
                    format!("\n\n{}\n\n\n{:#?}", doc, bytecode)
                }
                _ => "".to_string(),
            };
            return Some(format!("[value]: {}{}", v, help));
        }
    }
    None
}

/// Is this code sufficient for evaluation, or is more needed?
pub fn code_is_complete(code: &str) -> Option<bool> {
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

#[derive(Debug)]
pub struct CompletionRes {
    pub cursor_start: usize,
    pub cursor_end: usize,
    pub matches: Vec<String>,
}

/// Find completions at the given location.
pub fn completion(ctx: &mut k::Ctx, code: &str, cursor_pos: usize) -> Option<CompletionRes> {
    log::debug!(
        "completion request for code=`{}`, cursor_pos={}",
        code,
        cursor_pos
    );

    let mut compls: Vec<String> = vec![];
    let mut add_compl = |s: &str| compls.push(s.to_string());

    let tok = find_tok(code, cursor_pos); // find token of interest
    if let Some((tok, TokKind::Id, start, end)) = tok {
        for (s, _e) in ctx.iter_meta_values() {
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
            return Some(CompletionRes {
                cursor_start: start,
                cursor_end: end,
                matches: compls,
            });
        }
    } else if let Some((tok, TokKind::QuotedStr, start, end)) = tok {
        // complete file names
        use std::path::Path;
        let path = Path::new(&tok);
        log::info!("complete quoted string as path {:?}", path);
        let (dir, file) = match path.parent() {
            Some(p) => {
                let p = if p.to_str() == Some("") {
                    Path::new(".")
                } else {
                    p
                };
                (p, path.file_name().map(|x| Path::new(x)))
            }
            None => (Path::new("."), Some(path)),
        };
        log::debug!("split into dir={:?}, file={:?}", dir, file);
        for x in dir.read_dir().ok()? {
            log::debug!("in dir, examine path {:?}", x);
            let x = x.ok()?.path();
            match (
                file.and_then(|s| s.to_str()),
                x.file_name().and_then(|s| s.to_str()),
            ) {
                (Some(""), _) => (),
                (Some(f), Some(x)) if !x.starts_with(f) => {
                    log::debug!("reject path {:?}", x);
                    continue;
                }
                _ => (),
            }
            let path2 = dir.join(x);
            if let Some(p2) = path2.to_str() {
                add_compl(&format!("\"{}\"", p2));
            }
        }

        if compls.len() > 0 {
            log::info!("found {} completions", compls.len());
            log::debug!("completions: {:#?}", compls);
            return Some(CompletionRes {
                cursor_start: start,
                cursor_end: end,
                matches: compls,
            });
        }
    }
    log::debug!("no completion found");
    None
}
