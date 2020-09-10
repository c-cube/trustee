//! # Lexing for the core syntax

pub use crate::meta::Position;
use crate::{Error, Result};

/// A token of the language. This is zero-copy.
#[allow(non_camel_case_types)]
#[derive(Debug, Copy, Clone, PartialEq)]
pub(super) enum Tok<'a> {
    LPAREN,
    RPAREN,
    COLON,
    DOT,
    WILDCARD,
    QUESTION_MARK,
    QUESTION_MARK_STR(&'a str),
    SYM(&'a str),
    QUOTED_STR(&'a str),
    LET,
    IN,
    DOLLAR_SYM(&'a str),
    NUM(&'a str),
    ERROR(u8),
    EOF,
}

/// Lexer for expressions.
pub(super) struct Lexer<'a> {
    src: &'a str,
    /// Index in `src`
    i: usize,
    /// Position is `src`
    pos: Position,
    is_done: bool,
    cur_: Option<Tok<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self {
            src,
            i: 0,
            pos: Position { line: 1, col: 1 },
            is_done: false,
            cur_: None,
        }
    }

    /// Current position.
    pub fn cur_pos(&self) -> Position {
        self.pos
    }

    /// Read the rest of the line.
    fn rest_of_line(&mut self) -> &'a str {
        assert!(!self.is_done);
        let i = self.i;
        let bytes = self.src.as_bytes();

        while self.i < bytes.len() && bytes[self.i] != b'\n' {
            self.i += 1;
        }
        let j = self.i;
        if self.i < bytes.len() && bytes[self.i] == b'\n' {
            // newline
            self.i += 1;
            self.pos.col = 1;
            self.pos.line += 1;
        }
        &self.src[i..j]
    }

    fn next_(&mut self) -> Tok<'a> {
        use Tok::*;
        assert!(!self.is_done);

        let bytes = self.src.as_bytes();

        // skip whitespace
        while self.i < bytes.len() {
            let c = bytes[self.i];
            if c == b'#' {
                self.rest_of_line();
            } else if c == b' ' || c == b'\t' {
                self.i += 1;
                self.pos.col += 1;
            } else if c == b'\n' {
                self.pos.col = 1;
                self.pos.line += 1;
                self.i += 1;
            } else {
                break;
            }
        }

        if self.i >= bytes.len() {
            self.is_done = true;
            return EOF;
        }

        let c = bytes[self.i];
        if c == b'(' {
            self.i += 1;
            self.pos.col += 1;
            return LPAREN;
        } else if c == b')' {
            self.i += 1;
            self.pos.col += 1;
            return RPAREN;
        } else if c == b':' {
            self.i += 1;
            self.pos.col += 1;
            COLON
        } else if c == b'.' {
            self.i += 1;
            self.pos.col += 1;
            DOT
        } else if c == b'_' {
            self.i += 1;
            self.pos.col += 1;
            WILDCARD
        } else if c == b'?' {
            self.i += 1;
            self.pos.col += 1;
            // might be meta-variable
            let mut j = self.i;
            while j < bytes.len() {
                let c2 = bytes[j];
                if c2.is_ascii_alphanumeric() || is_ascii_symbol(c2) {
                    j += 1
                } else {
                    break;
                }
            }

            if j == self.i {
                QUESTION_MARK
            } else {
                let slice = &self.src[self.i..j];
                self.pos.col += (j - self.i) as u32;
                self.i = j;
                QUESTION_MARK_STR(slice)
            }
        } else if c == b'$' {
            // operator but without any precedence
            let mut j = self.i + 1;
            while j < bytes.len() {
                let c2 = bytes[j];
                if c2.is_ascii_alphanumeric() || is_ascii_symbol(c2) {
                    j += 1
                } else {
                    break;
                }
            }
            let slice = &self.src[self.i + 1..j];
            self.pos.col += (j - self.i) as u32;
            self.i = j;
            return DOLLAR_SYM(slice);
        } else if c == b'"' {
            // TODO: escaping of inner '"' ?
            let mut j = self.i + 1;
            while j < bytes.len() {
                let c2 = bytes[j];
                if c2 == b'"' {
                    break;
                }
                j += 1
            }
            let s = &self.src[self.i + 1..j];
            self.i = j + 1;
            QUOTED_STR(s)
        } else if c.is_ascii_alphabetic() {
            let mut j = self.i + 1;
            while j < bytes.len() {
                let c2 = bytes[j];
                if c2.is_ascii_alphanumeric()
                    || c2 == b'_'
                    || (c.is_ascii_uppercase() && c2 == b'.')
                {
                    j += 1
                } else {
                    break;
                }
            }
            let slice = &self.src[self.i..j];
            self.pos.col += (j - self.i) as u32;
            self.i = j;
            return if slice == "let" {
                LET
            } else if slice == "in" {
                IN
            } else {
                SYM(slice)
            };
        } else if c.is_ascii_digit() {
            let mut j = self.i + 1;
            while j < bytes.len() {
                let c2 = bytes[j];
                if c2.is_ascii_digit() {
                    j += 1
                } else {
                    break;
                }
            }
            let slice = &self.src[self.i..j];
            self.i = j;
            return NUM(slice);
        } else if is_ascii_symbol(c) {
            let mut j = self.i + 1;
            while j < bytes.len() {
                let c2 = bytes[j];
                if is_ascii_symbol(c2) {
                    j += 1
                } else {
                    break;
                }
            }
            let slice = &self.src[self.i..j];
            self.pos.col += (j - self.i) as u32;
            self.i = j;
            return SYM(slice);
        } else {
            // Error token!
            ERROR(c)
        }
    }

    /// get next token.
    pub fn next(&mut self) -> Tok<'a> {
        let t = self.next_();
        self.cur_ = Some(t);
        t
    }

    /// Current token.
    pub fn cur(&mut self) -> Tok<'a> {
        if let Some(c) = self.cur_ {
            c
        } else {
            self.next()
        }
    }

    pub fn consume_cur(&mut self) -> Tok<'a> {
        let t = self.cur();
        self.next();
        t
    }

    /// Expect the token `t`, and consume it; or return an error.
    ///
    /// The error message should be a posotion in the grammar,
    /// like "after lambda"
    pub fn eat(&mut self, t: Tok, errmsg: &str) -> Result<()> {
        let t2 = self.cur();
        if t2 == t {
            self.next();
            Ok(())
        } else {
            Err(Error::new_string(format!(
                "lexing error at {:?}: expected {:?} {}, got {:?}",
                self.pos, t, errmsg, t2
            )))
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Tok<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.is_done {
            None
        } else {
            Some(self.next())
        }
    }
}

/// Symbol that can be infix or prefix or postfix
fn is_ascii_symbol(c: u8) -> bool {
    match c {
        b'=' | b',' | b';' | b'<' | b'>' | b'!' | b'/' | b'\\' | b'+' | b'-' | b'|' | b'^'
        | b'~' | b'*' | b'&' | b'%' | b'@' => true,
        _ => false,
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lexer1() {
        use Tok::*;
        let lexer = Lexer::new(" foo + _ bar13(hello! \" co co\" world) ");
        let toks = lexer.collect::<Vec<_>>();
        assert_eq!(
            toks,
            vec![
                SYM("foo"),
                SYM("+"),
                WILDCARD,
                SYM("bar13"),
                LPAREN,
                SYM("hello"),
                SYM("!"),
                QUOTED_STR(" co co"),
                SYM("world"),
                RPAREN,
                EOF
            ]
        );
    }

    #[test]
    fn test_lexer2() {
        use Tok::*;
        let lexer = Lexer::new(r#"((12+ f(x, in ?a ? ? b Y \( ))---let z)wlet)"#);
        let toks = lexer.collect::<Vec<_>>();
        assert_eq!(
            vec![
                LPAREN,
                LPAREN,
                NUM("12"),
                SYM("+"),
                SYM("f"),
                LPAREN,
                SYM("x"),
                SYM(","),
                IN,
                QUESTION_MARK_STR("a"),
                QUESTION_MARK,
                QUESTION_MARK,
                SYM("b"),
                SYM("Y"),
                SYM("\\"),
                LPAREN,
                RPAREN,
                RPAREN,
                SYM("---"),
                LET,
                SYM("z"),
                RPAREN,
                SYM("wlet"),
                RPAREN,
                EOF
            ],
            toks
        );
    }

    #[test]
    fn test_lex_empty() {
        // always at least one token
        let lexer = Lexer::new("");
        let toks: Vec<_> = lexer.collect();
        assert_eq!(vec![Tok::EOF], toks);
    }
}
