//! Lexer for the meta-language.

pub use crate::position::Position;
use {
    crate::rstr::RStr,
    crate::{Error, Result},
    std::u8,
};

#[macro_export]
macro_rules! perror {
    ($loc: expr, $fmt: literal) => {
        Error::new_string(format!(
                concat!( "parse error at {:?}: ", $fmt), $loc))
    };
    ($loc: expr, $fmt: literal, $($arg:expr ),*) => {
        Error::new_string(format!(
                concat!( "parse error at {:?}: ", $fmt), $loc,
                $($arg),*))
    };
}

/// Basic lexer.
pub struct Lexer<'b> {
    /// Current position.
    pos: Position,
    /// Position at the start of current token.
    tok_start_pos: Position,
    /// Offset at the start of current token.
    tok_start_off: usize,
    /// Current offset.
    i: usize,
    bytes: &'b [u8],
    pub(crate) file_name: Option<RStr>,
    cur_: Option<Tok<'b>>,
}

/// A token for the meta-language syntax.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Tok<'b> {
    Eof,
    ColonId(&'b str),      // :foo
    Id(&'b str),           // identifier
    QuotedString(&'b str), // "some string"
    QuotedExpr(&'b str),   // $some expr$
    Trace,                 // '>>'
    Int(i64),
    LParen,        // '('
    RParen,        // ')'
    LBracket,      // '['
    RBracket,      // ']'
    LBrace,        // '{'
    RBrace,        // '}'
    Invalid(char), // to report an error
}

#[inline]
fn is_id_char(c: u8) -> bool {
    match c {
        b'a'..=b'z'
        | b'A'..=b'Z'
        | b'_'
        | b'='
        | b'+'
        | b'-'
        | b'.'
        | b'@'
        | b'!'
        | b'%'
        | b'^'
        | b'&'
        | b'*'
        | b'|'
        | b'/'
        | b'>'
        | b'<'
        | b'\\'
        | b'?'
        | b';' => true,
        _ => false,
    }
}

impl<'b> Lexer<'b> {
    #[inline]
    pub fn eof(&self) -> bool {
        self.i >= self.bytes.len()
    }

    /// Current `(line, column)`.
    pub fn loc(&self) -> Position {
        self.pos
    }

    /// `(line,column)` at the beginning of the token.
    pub fn token_start_pos(&self) -> Position {
        self.tok_start_pos
    }

    /// Current offset in the string.
    pub fn offset(&self) -> usize {
        self.i
    }

    pub fn token_start_offset(&self) -> usize {
        self.tok_start_off
    }

    pub fn token_end_offset(&self) -> usize {
        self.i
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
                self.pos.col += 1;
            } else if c == b'\n' {
                self.i += 1;
                self.pos.line += 1;
                self.pos.col = 1
            } else {
                return;
            }
        }
    }

    /// Expect the token `t`, and consume it; or return an error.
    pub fn eat_(&mut self, t: Tok, errmsg: &str) -> Result<()> {
        if self.cur() == t {
            self.next();
            Ok(())
        } else {
            Err(perror!(self.loc(), "{}", errmsg))
        }
    }

    /// Next token.
    pub fn next(&mut self) -> Tok<'b> {
        self.skip_white_();
        if self.eof() {
            self.cur_ = Some(Tok::Eof);
            return Tok::Eof;
        }
        self.tok_start_off = self.i;
        self.tok_start_pos = self.loc();
        let tok = match self.bytes[self.i] {
            b'(' => {
                self.i += 1;
                self.pos.col += 1;
                Tok::LParen
            }
            b'{' => {
                self.i += 1;
                self.pos.col += 1;
                Tok::LBrace
            }
            b'[' => {
                self.i += 1;
                self.pos.col += 1;
                Tok::LBracket
            }
            b')' => {
                self.i += 1;
                self.pos.col += 1;
                Tok::RParen
            }
            b'}' => {
                self.i += 1;
                self.pos.col += 1;
                Tok::RBrace
            }
            b']' => {
                self.i += 1;
                self.pos.col += 1;
                Tok::RBracket
            }
            b'$' => {
                let mut j = self.i + 1;
                while j < self.bytes.len() && self.bytes[j] != b'$' {
                    j += 1;
                }
                let src_expr =
                    std::str::from_utf8(&self.bytes[self.i + 1..j]).expect("invalid utf8 slice");
                self.pos.col += (j - self.i + 1) as u32;
                self.i = j + 1;
                Tok::QuotedExpr(src_expr)
            }
            c if c.is_ascii_digit() => {
                let mut j = self.i + 1;
                while j < self.bytes.len() && self.bytes[j].is_ascii_digit() {
                    j += 1;
                }
                let tok = std::str::from_utf8(&self.bytes[self.i..j]).expect("invalid utf8 slice");
                let n = str::parse(tok).expect("cannot parse int");
                self.pos.col += (j - self.i) as u32;
                self.i = j;
                Tok::Int(n)
            }
            b':' => {
                let mut j = self.i + 1;
                while j < self.bytes.len() && {
                    let c = self.bytes[j];
                    is_id_char(c) || (j > self.i + 1 && c.is_ascii_digit())
                } {
                    j += 1;
                }
                let tok =
                    std::str::from_utf8(&self.bytes[self.i + 1..j]).expect("invalid utf8 slice");
                self.pos.col += (j - self.i) as u32;
                self.i = j;
                Tok::ColonId(tok)
            }
            b'"' => {
                let mut j = self.i + 1;
                while j < self.bytes.len() && {
                    let c = self.bytes[j];
                    c != b'"'
                } {
                    j += 1;
                }
                let tok =
                    std::str::from_utf8(&self.bytes[self.i + 1..j]).expect("invalid utf8 slice");
                self.pos.col += (j - self.i + 1) as u32;
                self.i = j + 1;
                Tok::QuotedString(tok)
            }
            c if is_id_char(c) => {
                let mut j = self.i + 1;
                while j < self.bytes.len() && {
                    let c = self.bytes[j];
                    is_id_char(c) || c.is_ascii_digit()
                } {
                    j += 1;
                }
                let tok = std::str::from_utf8(&self.bytes[self.i..j]).expect("invalid utf8 slice");
                self.pos.col += (j - self.i) as u32;
                self.i = j;
                match str::parse(tok) {
                    Ok(n) => Tok::Int(n), // if all numerics
                    Err(_) if tok == ">>" => Tok::Trace,
                    Err(_) => Tok::Id(tok),
                }
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
    pub fn new(s: &'b str, file_name: Option<RStr>) -> Self {
        let pos = Position { line: 1, col: 1 };
        Self {
            pos,
            i: 0,
            bytes: s.as_bytes(),
            tok_start_off: 0,
            tok_start_pos: pos,
            cur_: None,
            file_name,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! lex_test {
        ($a:expr) => {
            for (s, v) in $a {
                let mut p = Lexer::new(s, None);
                let mut toks = vec![];
                loop {
                    let t = p.cur().clone();
                    toks.push(t);
                    if matches!(t, Tok::Eof) {
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
            r#" ("a" "b"[mul 2}"d" { 3 - 1 } def) 2  "#,
            vec![
                T::LParen,
                T::QuotedString("a"),
                T::QuotedString("b"),
                T::LBracket,
                T::Id("mul"),
                T::Int(2),
                T::RBrace,
                T::QuotedString("d"),
                T::LBrace,
                T::Int(3),
                T::Id("-"),
                T::Int(1),
                T::RBrace,
                T::Id("def"),
                T::RParen,
                T::Int(2),
                T::Eof,
            ],
        )];
        lex_test!(a)
    }

    #[test]
    fn test_lexer2() {
        use Tok as T;
        let a = vec![(
            r#"(print {1 + 1})"#,
            vec![
                T::LParen,
                T::Id("print"),
                T::LBrace,
                T::Int(1),
                T::Id("+"),
                T::Int(1),
                T::RBrace,
                T::RParen,
                T::Eof,
            ],
        )];
        lex_test!(a)
    }

    #[test]
    fn test_lexer3() {
        use Tok as T;
        let a = vec![(
            r#"(print (>> 1 + >>(1)})"#,
            vec![
                T::LParen,
                T::Id("print"),
                T::LParen,
                T::Trace,
                T::Int(1),
                T::Id("+"),
                T::Trace,
                T::LParen,
                T::Int(1),
                T::RParen,
                T::RBrace,
                T::RParen,
                T::Eof,
            ],
        )];
        lex_test!(a)
    }

    #[test]
    fn test_lexer4() {
        use Tok as T;
        let a = vec![(
            r#"(match $T/\F$ ($?a /\ ?b$ (def l [a b]) l) (else 1))"#,
            vec![
                T::LParen,
                T::Id("match"),
                T::QuotedExpr("T/\\F"),
                T::LParen,
                T::QuotedExpr("?a /\\ ?b"),
                T::LParen,
                T::Id("def"),
                T::Id("l"),
                T::LBracket,
                T::Id("a"),
                T::Id("b"),
                T::RBracket,
                T::RParen,
                T::Id("l"),
                T::RParen,
                T::LParen,
                T::Id("else"),
                T::Int(1),
                T::RParen,
                T::RParen,
                T::Eof,
            ],
        )];
        lex_test!(a)
    }
}
