//! A basic syntax for parsing and printing terms.
//!
//! This syntax is optional and is not needed at all when using the kernel.
//! We follow https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
//! for the main parser and terminology.

use crate::{database as db, kernel_of_trust as k};
use std::{cell::RefCell, rc::Rc};

/// Reuse symbols from the kernel.
type Symbol = k::Symbol;

/// The AST used for parsing and type inference.
#[derive(Debug, Clone)]
pub struct PExpr(Rc<PExprCell>);

/// Content of an expression.
#[derive(Debug, Clone)]
pub struct PExprCell {
    view: PExprView,
    ty: RefCell<Option<k::Expr>>,
}

/// A (possibly type-annotated) variable
#[derive(Debug, Clone)]
pub struct Var {
    name: Symbol,
    ty: Option<PExpr>,
}

/// How a symbol behaves in the grammar: prefix, infix, postfix, constant.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Fixity {
    /// No arguments
    Nullary,
    /// Unary, prefix (e.g. `¬`)
    Prefix(BindingPower),
    /// Infix (e.g. `+`)
    Infix(BindingPower),
    /// Postfix (e.g. `^c`, set complement)
    Postfix(BindingPower),
    /// Binder symbol (e.g. `?`, exists)
    Binder(BindingPower),
}

/// Binding power. The higher, the stronger it tights.
///
/// It's a pair because it's left and right binding powers so we can represent
/// associativity.
/// See https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html .
pub type BindingPower = (u32, u32);

#[derive(Debug, Clone)]
pub enum PExprView {
    Var(Symbol),
    DollarVar(Symbol), // `$foo` is the non-infix version of `foo` with explicit type args
    App(PExpr, Vec<PExpr>),
    Bind { binder: Symbol, v: Var, body: PExpr },
}

// token
#[derive(Debug, PartialEq)]
enum Tok<'a> {
    LPAREN,
    RPAREN,
    SYM(&'a str),
    NUM(&'a str),
    EOF,
}

/// Lexer for expressions.
struct Lexer<'a> {
    src: &'a str,
    /// Index in `src`
    i: usize,
    /// Current line in `src`
    line: usize,
    /// Current column in `src`
    col: usize,
    is_done: bool,
}

impl<'a> Lexer<'a> {
    fn new(src: &'a str) -> Self {
        Self { src, i: 0, line: 1, col: 1, is_done: false }
    }

    pub fn cur_pos(&self) -> (usize, usize) {
        (self.line, self.col)
    }

    // get next token
    fn next_(&mut self) -> Tok<'a> {
        use Tok::*;
        assert!(!self.is_done);

        let bytes = self.src.as_bytes();

        // skip whitespace
        while self.i < bytes.len() {
            let c = bytes[self.i];
            if c == b' ' || c == b'\t' {
                self.i += 1;
                self.col += 1;
            } else if c == b'\n' {
                self.col = 1;
                self.line += 1;
                self.i += 1;
            } else {
                break;
            }
        }

        if self.i >= bytes.len() {
            self.is_done = true;
            return EOF;
        } else if bytes[self.i] == b'(' {
            self.i += 1;
            self.col += 1;
            return LPAREN;
        } else if bytes[self.i] == b')' {
            self.i += 1;
            self.col += 1;
            return RPAREN;
        }
        let c = bytes[self.i];

        let mut j = self.i + 1;
        if c.is_ascii_alphabetic() {
            while j < bytes.len() {
                let c2 = bytes[j];
                if c2.is_ascii_alphanumeric() {
                    j += 1
                } else {
                    break;
                }
            }
            let slice = &self.src[self.i..j];
            self.col += j - self.i;
            self.i = j;
            return SYM(slice);
        } else if c.is_ascii_digit() {
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
        } else if c.is_ascii_punctuation() {
            while j < bytes.len() {
                let c2 = bytes[j];
                if c2.is_ascii_punctuation() {
                    j += 1
                } else {
                    break;
                }
            }
            let slice = &self.src[self.i..j];
            self.col += j - self.i;
            self.i = j;
            return SYM(slice);
        } else {
            todo!("handle char {:?}", c) // TODO? error?
        }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Tok<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.is_done {
            None
        } else {
            Some(self.next_())
        }
    }
}

/// Parser for expressions.
///
/// It uses the precedence table provided by a `Database`, and an IO stream.
pub struct Parser<'a> {
    db: &'a db::Database,
    lexer: Lexer<'a>,
    cur: Tok<'a>,
}

impl<'a> Parser<'a> {
    /// New parser using the given string `src`.
    pub fn new(db: &'a db::Database, src: &'a str) -> Self {
        let mut lexer = Lexer::new(src);
        let cur = lexer.next_(); // parse first token
        Self { db, lexer, cur }
    }

    /// Return current `(line,column)` pair.
    pub fn cur_pos(&self) -> (usize, usize) {
        self.lexer.cur_pos()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lexer1() {
        use Tok::*;
        let lexer = Lexer::new(" foo + bar13(hello! world) ");
        let toks = lexer.collect::<Vec<_>>();
        assert_eq!(
            toks,
            vec![
                SYM("foo"),
                SYM("+"),
                SYM("bar13"),
                LPAREN,
                SYM("hello"),
                SYM("!"),
                SYM("world"),
                RPAREN,
                EOF
            ]
        );
    }

    #[test]
    fn test_lexer2() {
        use Tok::*;
        let lexer = Lexer::new("((12+ f(x, Y))--- z)");
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
                SYM("Y"),
                RPAREN,
                RPAREN,
                SYM("---"),
                SYM("z"),
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
