//! A basic syntax for parsing and printing terms.
//!
//! This syntax is optional and is not needed at all when using the kernel.
//! We follow https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
//! for the main parser and terminology.

use crate::{kernel_of_trust as k, Error, Result};
use std::{cell::RefCell, fmt, rc::Rc, u8};

/// Reuse symbols from the kernel.
type Symbol = k::Symbol;

/// The AST used for parsing and type inference.
#[derive(Clone)]
pub struct PExpr(Rc<PExprCell>);

/// Content of an expression.
#[derive(Clone)]
pub struct PExprCell {
    view: PExprView,
    loc: (usize, usize),
    ty: RefCell<Option<k::Expr>>,
}

/// The root of an expression.
#[derive(Debug, Clone)]
pub enum PExprView {
    Var(Symbol),
    Num(String),
    DollarVar(Symbol), // `$foo`: non-infix version of `foo` with explicit type args
    App(PExpr, PExpr),
    Bind { binder: Symbol, v: Var, body: PExpr },
}

use PExprView::*;

/// A (possibly type-annotated) variable
#[derive(Clone)]
pub struct Var {
    name: Symbol,
    ty: Option<PExpr>,
}

// custom debug that prints as S-expressions
impl fmt::Debug for PExpr {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match &self.0.view {
            Var(v) => write!(fmt, "{}", v.name()),
            Num(s) => write!(fmt, "{}", s),
            DollarVar(v) => write!(fmt, "${}", v.name()),
            App(..) => {
                // print nested applications as flattened
                let (f, args) = self.unfold_app();
                write!(fmt, "({:?}", f)?;
                for x in args {
                    write!(fmt, " {:?}", x)?;
                }
                write!(fmt, ")")
            }
            Bind { binder, v, body } => {
                write!(fmt, "({}{:?}. {:?})", binder.name(), v, body)
            }
        }
    }
}

// custom debug that prints type if specified
impl fmt::Debug for Var {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match &self.ty {
            None => write!(fmt, "{}", self.name.name()),
            Some(ty) => write!(fmt, "{}: {:?}", self.name.name(), ty),
        }
    }
}

impl PExpr {
    /// Print expression as a S-expr.
    pub fn to_string(&self) -> String {
        format!("{:?}", self)
    }

    /// View of the term.
    #[inline]
    pub fn view(&self) -> &PExprView {
        &self.0.view
    }

    pub fn loc(&self) -> (usize, usize) {
        self.0.loc
    }

    fn mk_(view: PExprView, loc: (usize, usize)) -> Self {
        PExpr(Rc::new(PExprCell { view, loc, ty: RefCell::new(None) }))
    }

    /// Flatten an application.
    pub fn unfold_app(&self) -> (PExpr, Vec<PExpr>) {
        let mut t = self.clone();
        let mut args = vec![];
        while let App(f, a) = &t.0.view {
            args.push(a.clone());
            t = f.clone();
        }
        args.reverse();
        (t, args)
    }

    /// Create a variable.
    pub fn var(s: &str, loc: (usize, usize)) -> Self {
        Self::mk_(Var(Symbol::from_str(s)), loc)
    }

    /// Create a number.
    pub fn num(s: &str, loc: (usize, usize)) -> Self {
        Self::mk_(Num(s.to_string()), loc)
    }

    /// Create a variable.
    pub fn dollar_var(s: &str, loc: (usize, usize)) -> Self {
        Self::mk_(DollarVar(Symbol::from_str(s)), loc)
    }

    /// Create an application.
    pub fn apply(&self, arg: PExpr, loc: (usize, usize)) -> Self {
        Self::mk_(App(self.clone(), arg), loc)
    }

    /// Create an application from a list of arguments.
    pub fn apply_l(&self, args: &[PExpr], loc: (usize, usize)) -> Self {
        let mut t = self.clone();
        for x in args.iter() {
            t = t.apply(x.clone(), loc)
        }
        t
    }

    /// Create a binder.
    pub fn bind(b: &str, v: Var, body: PExpr, loc: (usize, usize)) -> Self {
        Self::mk_(Bind { binder: Symbol::from_str(b), v, body }, loc)
    }
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

impl Fixity {
    pub fn bp(&self) -> BindingPower {
        match self {
            Fixity::Nullary => (0, 0),
            Fixity::Prefix(p) => *p,
            Fixity::Infix(p) => *p,
            Fixity::Postfix(p) => *p,
            Fixity::Binder(p) => *p,
        }
    }
}

/// Binding power. The higher, the stronger it tights.
///
/// It's a pair because it's left and right binding powers so we can represent
/// associativity.
/// See https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html .
pub type BindingPower = (u8, u8);

// token
#[derive(Debug, Copy, Clone, PartialEq)]
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
/// It uses a fixity function, and a string to parse.
pub struct Parser<'a> {
    get_fix: &'a dyn Fn(&str) -> Option<Fixity>,
    lexer: Lexer<'a>,
    next_tok: Option<Tok<'a>>,
}

impl<'a> Parser<'a> {
    /// New parser using the given string `src`.
    pub fn new(
        get_fix: &'a dyn Fn(&str) -> Option<Fixity>,
        src: &'a str,
    ) -> Self {
        let lexer = Lexer::new(src);
        Self { get_fix, lexer, next_tok: None }
    }

    /// Return current `(line,column)` pair.
    pub fn loc(&self) -> (usize, usize) {
        self.lexer.cur_pos()
    }

    /// Peek at the current token.
    #[inline]
    fn peek_(&mut self) -> Tok<'a> {
        match self.next_tok {
            Some(t) => t,
            None => {
                let t = self.lexer.next_();
                self.next_tok = Some(t);
                t
            }
        }
    }

    #[inline]
    fn fixity_(&self, s: &str) -> Fixity {
        (*self.get_fix)(s).unwrap_or(Fixity::Nullary)
    }

    /// Consume current token and return the next one.
    #[inline]
    fn next_(&mut self) -> Tok<'a> {
        match self.next_tok {
            Some(t) => {
                self.next_tok = None;
                t
            }
            None => self.lexer.next_(),
        }
    }

    /// Consume `tok` an nothing else.
    fn eat_(&mut self, tok: Tok) -> Result<()> {
        let t = self.peek_();
        if t == tok {
            self.next_();
            Ok(())
        } else {
            Err(Error::new_string(format!("expected {:?}, got {:?}", tok, t)))
        }
    }

    /// Parse an expression, up to EOF.
    ///
    /// `bp` is the current binding power for this Pratt parser.
    pub fn parse_bp(&mut self, bp: u8) -> Result<PExpr> {
        use Tok::*;

        let mut lhs = match self.next_() {
            SYM(s) => PExpr::var(s, self.loc()), // TODO: handle prefix op
            NUM(s) => PExpr::var(s, self.loc()),
            LPAREN => {
                let t = self.parse_bp(0)?;
                self.eat_(RPAREN)?;
                t
            }
            RPAREN => return Err(Error::new("unexpected ')'")),
            EOF => return Err(Error::new("unexpected EOF")),
        };

        loop {
            let loc_op = self.loc();
            let (op, l_bp, r_bp) = match self.peek_() {
                EOF => return Ok(lhs),
                RPAREN => break,
                LPAREN => {
                    self.next_();
                    let t = self.parse_bp(0)?; // maximum binding power
                    self.eat_(RPAREN)?;
                    lhs = lhs.apply(t, loc_op);
                    continue;
                }
                SYM(s) => {
                    let v = PExpr::var(s, self.loc());
                    match self.fixity_(s) {
                        Fixity::Infix((l1, l2)) => (v, l1, l2),
                        Fixity::Nullary => {
                            // simple application
                            lhs = lhs.apply(v, self.loc());
                            self.next_();
                            continue;
                        }
                        Fixity::Prefix(..) => todo!(),
                        Fixity::Postfix(..) => todo!(),
                        Fixity::Binder(..) => todo!(),
                    }
                }
                NUM(s) => {
                    let v = PExpr::num(s, self.loc());
                    lhs = lhs.apply(v, self.loc());
                    self.next_();
                    continue;
                } // TODO: dollar var
            };

            if l_bp < bp {
                break; // binding left
            }

            self.next_();

            let rhs = self.parse_bp(r_bp)?;

            // infix apply
            dbg!("app", &op, &lhs, &rhs);
            let app = op.apply_l(&[lhs, rhs], loc_op);
            lhs = app;
        }

        Ok(lhs)
    }

    /// Parse an expression, up to EOF.
    pub fn parse(&mut self) -> Result<PExpr> {
        self.parse_bp(0)
    }
}

/// Parse the string into an expression.
pub fn parse(
    get_fix: &dyn Fn(&str) -> Option<Fixity>,
    s: &str,
) -> Result<PExpr> {
    let mut p = Parser::new(get_fix, s);
    p.parse()
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

    #[test]
    fn test_parser1() {
        let s = "foo";
        let get_fix = |_: &str| None;
        let e = parse(&get_fix, s).unwrap();
        assert_eq!("foo", e.to_string());
    }

    #[test]
    fn test_parser2() {
        let s = "(f x) = y";
        let get_fix = |s: &str| {
            if s == "=" {
                Some(Fixity::Infix((5, 5)))
            } else {
                None
            }
        };
        let e = parse(&get_fix, s).unwrap();
        assert_eq!("(= (f x) y)", e.to_string());
    }

    // test from the blog post
    #[test]
    fn test_parser3() {
        let fix = |s: &str| match s {
            "+" | "-" => Some(Fixity::Infix((1, 2))),
            "*" | "/" => Some(Fixity::Infix((3, 4))),
            "." => Some(Fixity::Infix((6, 5))),
            _ => None,
        };
        let s = parse(&fix, "1").unwrap();
        assert_eq!(s.to_string(), "1");

        let s = parse(&fix, "1 + 2 * 3").unwrap();
        assert_eq!(
            vec![
                Tok::NUM("1"),
                Tok::SYM("+"),
                Tok::NUM("2"),
                Tok::SYM("*"),
                Tok::NUM("3"),
                Tok::EOF,
            ],
            Lexer::new("1 + 2 * 3").collect::<Vec<_>>()
        );
        assert_eq!(s.to_string(), "(+ 1 (* 2 3))");

        let s = parse(&fix, "a + b * c * d + e").unwrap();
        assert_eq!(s.to_string(), "(+ (+ a (* (* b c) d)) e)");

        let s = parse(&fix, "f . g . h").unwrap();
        assert_eq!(s.to_string(), "(. f (. g h))");

        let s = parse(&fix, " 1 + 2 + f . g . h * 3 * 4").unwrap();
        assert_eq!(s.to_string(), "(+ (+ 1 2) (* (* (. f (. g h)) 3) 4))");
    }
}
