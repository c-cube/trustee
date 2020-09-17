//! # Parser for LLProof

use super::{
    proof::{LLProofBuilder, LLStatement},
    *,
};
use crate::Ctx;
use std::u8;

/// A parser for a series of `LLProof`.
pub struct Parser<'a> {
    ctx: &'a mut Ctx,
    lexer: Lexer<'a>,
}

/// Basic lexer.
struct Lexer<'b> {
    /// Buffer to parse.
    bytes: &'b [u8],
    /// Current offset in `bytes`.
    i: usize,
    /// Current line.
    line: usize,
    cur_: Option<Tok<'b>>,
}

/// A token for the meta-language syntax.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Tok<'b> {
    Eof,
    Id(&'b str),           // identifier
    Int(i64),              // integer
    QuotedString(&'b str), // "some string"
    LParen,                // '('
    RParen,                // ')'
    Invalid(char),         // to report an error
}

// TODO: eval statements

impl<'a> Parser<'a> {
    /// New parser from the given string.
    pub fn new(ctx: &'a mut Ctx, s: &'a str) -> Self {
        Self {
            ctx,
            lexer: Lexer::new(s),
        }
    }

    /// Parse a series of steps, and returns the stack size after executing them.
    fn parse_steps(&mut self, n_args: u8) -> Result<(LLProofBuilder, isize)> {
        self.lexer.eat(Tok::LParen, "proof steps start with '('")?;

        let mut n_st_size = n_args as isize;
        let mut pb = LLProofBuilder::new();
        while self.lexer.cur() != Tok::RParen {
            match self.lexer.cur() {
                Tok::LParen => {
                    self.lexer.next();
                    let id = self.lexer.parse_id("expect step instruction")?;

                    let mut found = false;
                    for st in STEPS {
                        if st.name == id {
                            let step = match &st.mk_step {
                                StepBuild::Step0(..) => {
                                    return Err(Error::new("step requires no argument"));
                                }
                                StepBuild::StepInt(f) => {
                                    let i = match self.lexer.cur() {
                                        Tok::Int(i) => i,
                                        _ => return Err(Error::new("argument must be an int")),
                                    };
                                    self.lexer.next();
                                    f(i)
                                }
                            };
                            pb.add_step(step);
                            n_st_size -= st.n_in as isize;
                            n_st_size += st.n_out as isize;
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return Err(Error::new("no such instruction"));
                    }
                    self.lexer.eat(Tok::RParen, "expect ')' to finish step")?;
                }
                Tok::Id(id) => {
                    self.lexer.next();

                    let mut found = false;
                    for st in STEPS {
                        if st.name == id {
                            let step = match &st.mk_step {
                                StepBuild::Step0(s) => s.clone(),
                                StepBuild::StepInt(..) => {
                                    return Err(Error::new("step has no argument"));
                                }
                            };
                            pb.add_step(step);
                            n_st_size -= st.n_in as isize;
                            n_st_size += st.n_out as isize;
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return Err(Error::new("no such instruction"));
                    }
                }
                _ => {
                    return Err(Error::new(
                        "expect identifier or '(' when parsing a proof step",
                    ));
                }
            }
        }

        self.lexer
            .eat(Tok::RParen, "missing closing ')' after proof steps")?;
        Ok((pb, n_st_size))
    }

    fn parse_(&mut self) -> Result<Option<LLStatement<'a>>> {
        if self.lexer.eof() {
            return Ok(None);
        }

        self.lexer
            .eat(Tok::LParen, "expect a '(' to start a statement")?;

        let st = match self.lexer.parse_id("expect statement")? {
            "set" => {
                let name = self.lexer.parse_id("expect a name after 'set'")?;

                let (pb, n_out) = self.parse_steps(0)?;
                if n_out != 1 {
                    return Err(Error::new("set: requires result stack to have size 1"));
                }
                let proof = pb.into_proof();
                LLStatement::Set(name, proof)
            }
            "defrule" => {
                // parse name+arity
                let name = self.lexer.parse_id("expect name of rule")?;
                let n = match self.lexer.cur() {
                    Tok::Int(i) => {
                        self.lexer.next();
                        i
                    }
                    _ => return Err(Error::new("expect arity (integer)")),
                };
                if n < 0 || n > u8::MAX as i64 {
                    return Err(Error::new("arity is not a valid u8"));
                }
                let n_args = n as u8;

                // parse steps
                let (pb, n_out) = self.parse_steps(n_args)?;

                if n_out != 1 {
                    return Err(Error::new("defrule: require output stack to have size 1"));
                }

                let rule = pb.into_proof_rule(name, n_args);
                LLStatement::DefRule(rule)
            }
            _ => return Err(Error::new("unknown statement")),
        };

        self.lexer
            .eat(Tok::RParen, "expect a closing ')' after statement")?;
        Ok(Some(st))
    }

    pub fn parse(&mut self) -> Result<Option<LLStatement<'a>>> {
        self.parse_()
            .map_err(|e| e.with_source(Error::new_string(format!("at line {}", self.lexer.line))))
    }
}

/// Step description.
struct StepDescr {
    name: &'static str,
    /// Number of arguments pop'd from the stack.
    n_in: u8,
    /// Number of arguments pushed on the stack.
    n_out: u8,
    /// How to build the step.
    mk_step: StepBuild,
}

enum StepBuild {
    Step0(LLProofStep),
    StepInt(&'static dyn Fn(i64) -> LLProofStep),
}

const STEPS: &[StepDescr] = &[
    StepDescr {
        name: "asm",
        n_in: 1,
        n_out: 1,
        mk_step: StepBuild::Step0(LLProofStep::ThAssume),
    },
    StepDescr {
        name: "cut",
        n_in: 2,
        n_out: 1,
        mk_step: StepBuild::Step0(LLProofStep::ThCut),
    },
];

mod lexer {
    use super::*;

    #[inline]
    fn is_id_char(c: u8) -> bool {
        match c {
            b'a'..=b'z' | b'A'..=b'Z' | b'_' | b'-' | b'.' => true,
            _ => false,
        }
    }

    impl<'b> Lexer<'b> {
        #[inline]
        pub fn eof(&self) -> bool {
            self.i >= self.bytes.len()
        }

        fn skip_white_(&mut self) {
            while self.i < self.bytes.len() {
                let c = self.bytes[self.i];
                if c == b';' {
                    // eat rest of line
                    while self.i < self.bytes.len() && self.bytes[self.i] != b'\n' {
                        self.i += 1
                    }
                } else if c == b' ' || c == b'\t' {
                    self.i += 1;
                } else if c == b'\n' {
                    self.i += 1;
                    self.line += 1;
                } else {
                    return;
                }
            }
        }

        /// Parse identifier.
        pub fn parse_id(&mut self, errmsg: &'static str) -> Result<&'b str> {
            match self.cur() {
                Tok::Id(s) => {
                    self.next();
                    Ok(s)
                }
                _ => Err(Error::new(errmsg)),
            }
        }

        /// Expect the token `t`, and consume it; or return an error.
        pub fn eat(&mut self, t: Tok, errmsg: &'static str) -> Result<()> {
            if self.cur() == t {
                self.next();
                Ok(())
            } else {
                Err(Error::new(errmsg))
            }
        }

        /// Next token.
        pub fn next(&mut self) -> Tok<'b> {
            self.skip_white_();
            if self.eof() {
                self.cur_ = Some(Tok::Eof);
                return Tok::Eof;
            }

            let tok = match self.bytes[self.i] {
                b'(' => {
                    self.i += 1;
                    Tok::LParen
                }
                b')' => {
                    self.i += 1;
                    Tok::RParen
                }
                b'"' => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && {
                        let c = self.bytes[j];
                        c != b'"'
                    } {
                        j += 1;
                    }
                    let tok = std::str::from_utf8(&self.bytes[self.i + 1..j])
                        .expect("invalid utf8 slice");
                    self.i = j + 1;
                    Tok::QuotedString(tok)
                }
                c if c.is_ascii_digit() => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && {
                        let c = self.bytes[j];
                        c.is_ascii_digit()
                    } {
                        j += 1;
                    }
                    let n = {
                        let s = std::str::from_utf8(&self.bytes[self.i..j])
                            .expect("invalid utf8 slice");
                        s.parse().expect("cannot parse integer")
                    };
                    self.i = j;
                    Tok::Int(n)
                }
                c if is_id_char(c) => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && {
                        let c = self.bytes[j];
                        is_id_char(c) || c.is_ascii_digit()
                    } {
                        j += 1;
                    }
                    let tok =
                        std::str::from_utf8(&self.bytes[self.i..j]).expect("invalid utf8 slice");
                    self.i = j;
                    Tok::Id(tok)
                }
                c => Tok::Invalid(std::char::from_u32(c as u32).unwrap()),
            };
            self.cur_ = Some(tok);
            tok
        }

        /// Current token.
        pub fn cur(&mut self) -> Tok<'b> {
            if let Some(c) = self.cur_ {
                c
            } else {
                self.next()
            }
        }

        /// New lexer.
        pub fn new(s: &'b str) -> Self {
            Self {
                i: 0,
                line: 1,
                bytes: s.as_bytes(),
                cur_: None,
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! lex_test {
        ($a:expr) => {
            for (s, v) in $a {
                let mut p = Lexer::new(s);
                let mut toks = vec![];
                loop {
                    let t = p.cur().clone();
                    toks.push(t);
                    if matches!(t, Tok::Eof) || matches!(t, Tok::Invalid(..)) {
                        break;
                    }
                    p.next();
                }
                assert_eq!(toks, v)
            }
        };
    }

    #[test]
    fn test_lexer() {
        use Tok as T;
        let a = vec![(
            r#" ("a" "b"(mul 2220)"d" ) b3 - 1 ) def) fejg2  "#,
            vec![
                T::LParen,
                T::QuotedString("a"),
                T::QuotedString("b"),
                T::LParen,
                T::Id("mul"),
                T::Int(2220),
                T::RParen,
                T::QuotedString("d"),
                T::RParen,
                T::Id("b3"),
                T::Id("-"),
                T::Int(1),
                T::RParen,
                T::Id("def"),
                T::RParen,
                T::Id("fejg2"),
                T::Eof,
            ],
        )];
        lex_test!(a)
    }

    #[test]
    fn test_parser() {
        let s = r#"
            (defrule cut2 3 (cut cut))
            "#;
        let mut ctx = Ctx::new();
        let mut p = Parser::new(&mut ctx, s);
        let r1 = p.parse().expect("cannot parse r1");
        assert!(r1.is_some());
        // TODO: eval

        let r2 = p.parse().expect("cannot parse r2");
        assert!(r2.is_none());
    }
}
