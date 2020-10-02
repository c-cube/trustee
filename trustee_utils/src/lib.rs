use std::{fmt::Write, time};
use trustee::{
    self, kernel_of_trust as k,
    meta::{self, lexer, lexer::Tok, Value},
    Error as TrError,
};

#[derive(Debug, Copy, Clone)]
enum TokKind {
    Id,
    QuotedStr,
    QuotedExpr,
    ColonId,
}

pub type Position = meta::Position;

/// An offset, or a position, in a file.
#[derive(Clone, Copy, Debug)]
pub enum PosOrOffset {
    Pos(Position),
    Offset(usize),
}

/// An offset, *and* a position.
#[derive(Clone, Copy, Debug)]
pub struct PosAndOffset {
    pub pos: Position,
    pub offset: usize,
}

mod utils {
    use super::*;

    impl From<Position> for PosOrOffset {
        fn from(p: Position) -> Self {
            Self::Pos(p)
        }
    }
    impl From<usize> for PosOrOffset {
        fn from(x: usize) -> Self {
            Self::Offset(x)
        }
    }
}

/// Find identifier the cursor is on (or just after)
fn find_tok(s: &str, pos: PosOrOffset) -> Option<(String, TokKind, PosAndOffset, PosAndOffset)> {
    let mut lexer = meta::lexer::Lexer::new(s, None);
    loop {
        let t = lexer.cur().clone();
        if t == Tok::Eof {
            break;
        }

        let start = lexer.token_start_offset();
        let pstart = lexer.token_start_pos().prev_col(); // a bit of slack here
        let end = lexer.token_end_offset();
        let pend = lexer.loc();

        let is_in = match pos {
            PosOrOffset::Offset(x) => start <= x && end >= x,
            PosOrOffset::Pos(p) => pstart <= p && pend > p,
        };
        //log::debug!( "is_in={}, pos={:?}, pstart={:?}, pend={:?}", is_in, pos, pstart, pend);

        if is_in {
            // here is where we want to complete
            let start = PosAndOffset {
                pos: pstart,
                offset: start,
            };
            let end = PosAndOffset {
                pos: pend,
                offset: end,
            };

            let tok = lexer.cur();
            log::debug!("relevant token is {:?} (range {:?}-{:?})", tok, start, end);
            match tok {
                Tok::Id(s) => {
                    return Some((s.to_string(), TokKind::Id, start, end));
                }
                Tok::QuotedString(s) => {
                    return Some((s.to_string(), TokKind::QuotedStr, start, end));
                }
                Tok::ColonId(s) => {
                    return Some((s.to_string(), TokKind::ColonId, start, end));
                }
                Tok::QuotedExpr(s) => {
                    return Some((s.to_string(), TokKind::QuotedExpr, start, end));
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
    pub res: std::result::Result<Value, TrError>,
    pub traces: Vec<(Position, Value)>,
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

    let ts_start = time::Instant::now();
    let mut vm = meta::VM::new(ctx);
    let mut lexer = lexer::Lexer::new(code, src.into());

    let stdout = RefCell::new(String::new());
    let traces = RefCell::new(vec![]);

    let mut fout = |s: &str| {
        let mut out = stdout.borrow_mut();
        out.push_str(&s)
    };
    vm.set_stdout(&mut fout);

    let mut ftrace = |pos: &Position, v| {
        let mut tr = traces.borrow_mut();
        tr.push((pos.clone(), v))
    };
    vm.set_on_trace(&mut ftrace);

    // evaluate `code`
    let mut res = vec![];
    loop {
        lexer.cur(); // make sure to parse first token before capturing `start`
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

        let mut traces2 = vec![];
        {
            let mut tr = traces.borrow_mut();
            std::mem::swap(&mut *tr, &mut traces2);
        }

        match v {
            Ok(None) => break,
            Ok(Some(r)) => {
                res.push(EvalResult {
                    start,
                    end,
                    res: Ok(r),
                    traces: traces2,
                    stdout,
                });
            }
            Err(e) => {
                let end = lexer.loc();
                res.push(EvalResult {
                    start,
                    end,
                    res: Err(e),
                    traces: traces2,
                    stdout,
                });
                break;
            }
        }
    }

    let duration = time::Instant::now().duration_since(ts_start);
    EvalResults { res, duration }
}

// TODO: put a trace there, somehow (modify lexer?) and report its result
// automatically
/// Inspect what's at this postion.
pub fn inspect(
    ctx: &mut k::Ctx,
    code: &str,
    pos: impl Into<PosOrOffset>,
) -> Option<(String, PosAndOffset, PosAndOffset)> {
    let pos = pos.into();
    log::debug!("inspect request for code=`{}`, pos={:?}", code, pos);

    let tok = find_tok(code, pos);
    if let Some((tok, TokKind::Id, start, end)) = tok {
        if let Some((v, hlp)) = meta::all_builtin_names_and_help().find(|v| v.0 == tok) {
            return Some((format!("[builtin]: {}\n\n{}", v, hlp), start, end));
        } else if let Some(v) = ctx.find_meta_value(&tok) {
            let (pval, help) = match v {
                meta::Value::Closure(c) => {
                    let doc = c.docstring().unwrap_or("");
                    let bytecode = c.chunk();
                    (true, format!("\n\n{}\n\n```\n{:#?}```", doc, bytecode))
                }
                meta::Value::Thm(th) => {
                    let mut s = "[theorem]\n\n```\n".to_string();
                    for h in th.hyps() {
                        write!(s, " {}\n", h).unwrap();
                    }
                    write!(s, "|------------------------------\n").unwrap();
                    write!(s, " {}\n```\n", th.concl()).unwrap();

                    // print proof, if available
                    if let Some(spr) = trustee::proof::print_proof::proof_to_string(&th) {
                        writeln!(s, "").unwrap();
                        writeln!(s, "{}", spr).unwrap();
                    }
                    (false, s)
                }
                _ => (true, "".to_string()),
            };

            if pval {
                return Some((format!("[value]: {:#}{}", v, help), start, end));
            } else {
                return Some((help, start, end));
            }
        }
    } else if let Some((_tok, TokKind::QuotedStr, start, end)) = tok {
        return Some((format!("[string]"), start, end));
    } else if let Some((_tok, TokKind::ColonId, start, end)) = tok {
        return Some((format!("[atom]"), start, end));
    } else if let Some((tok, TokKind::QuotedExpr, start, end)) = tok {
        let info = match trustee::parse_expr(ctx, &tok) {
            Ok(e) if e.is_kind() => format!("> root of type hierarchy"),
            Ok(e) => format!("type: `{}`", e.ty()),
            Err(e) => format!("ERR: could not parse: {}", e),
        };
        return Some((format!("[expr]\n`{}`\n\n{}", tok, info), start, end));
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
            | Tok::Trace
            | Tok::Int(..) => (),
            Tok::Invalid(_) => return None,
        }
        lex.next();
    }
}

#[derive(Debug)]
pub struct CompletionRes {
    pub start: PosAndOffset,
    pub end: PosAndOffset,
    pub matches: Vec<String>,
}

/// Find completions at the given location.
pub fn completion(
    ctx: &mut k::Ctx,
    code: &str,
    pos: impl Into<PosOrOffset>,
) -> Option<CompletionRes> {
    let pos = pos.into();
    log::debug!("completion request for code=`{}`, pos={:?}", code, pos);

    let mut compls: Vec<String> = vec![];
    let mut add_compl = |s: &str| compls.push(s.to_string());

    let tok = find_tok(code, pos); // find token of interest
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
                start,
                end,
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
                start,
                end,
                matches: compls,
            });
        }
    }
    log::debug!("no completion found");
    None
}

/// Find definition of symbol at given position, if any.
pub fn find_definition(
    code: &str,
    pos: PosOrOffset,
) -> Option<(String, PosAndOffset, PosAndOffset)> {
    let pos = pos.into();
    log::debug!("find-definition request for code=`{}`, pos={:?}", code, pos);

    // find token under the cursor
    let (name, kind, _, tokend) = find_tok(code, pos)?;
    if let TokKind::Id = kind {
    } else {
        return None;
    }

    // now find last defining occurrence of code that comes before `tokend`
    let mut lexer = meta::lexer::Lexer::new(code, None);
    let mut is_defining = false;
    let mut res = None;

    loop {
        let t = lexer.cur().clone();
        if t == Tok::Eof {
            break;
        }

        let start = lexer.token_start_offset();
        let pstart = lexer.token_start_pos().prev_col(); // a bit of slack here
        let end = lexer.token_end_offset();
        let pend = lexer.loc();

        if pstart > tokend.pos {
            break; // gone past the original query position
        }

        if let Tok::Id(s) = t {
            if s == &name && is_defining {
                // found!

                // here is where we want to complete
                let start = PosAndOffset {
                    pos: pstart,
                    offset: start,
                };
                let end = PosAndOffset {
                    pos: pend,
                    offset: end,
                };

                // update `res`.
                res = Some((start, end))
            } else if s == "def" || s == "defn" || s == "set" {
                is_defining = true; // for the next token
            } else {
                is_defining = false
            }
        } else {
            is_defining = false
        }

        // go to next token
        lexer.next();
    }

    let (start, end) = res?;
    Some((name, start, end))
}
