//! A basic syntax for parsing and printing terms.
//!
//! This syntax is optional and is not needed at all when using the kernel.
//! We follow https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
//! for the main parser and terminology.

use crate::{kernel_of_trust as k, CtxI, Error, Result};

/// ## Parsing
///
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
pub type BindingPower = (u16, u16);

/// A token of the language. This is zero-copy.
#[allow(non_camel_case_types)]
#[derive(Debug, Copy, Clone, PartialEq)]
enum Tok<'a> {
    LPAREN,
    RPAREN,
    COLON,
    DOT,
    QUESTION_MARK,
    SYM(&'a str),
    DOLLAR_SYM(&'a str),
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
        }

        let c = bytes[self.i];
        if c == b'(' {
            self.i += 1;
            self.col += 1;
            return LPAREN;
        } else if c == b')' {
            self.i += 1;
            self.col += 1;
            return RPAREN;
        } else if c == b':' {
            self.i += 1;
            self.col += 1;
            COLON
        } else if c == b'.' {
            self.i += 1;
            self.col += 1;
            DOT
        } else if c == b'?' {
            self.i += 1;
            QUESTION_MARK
        } else if c == b'$' {
            // operator but without any precedence
            let mut j = self.i + 1;
            while j < bytes.len() {
                let c2 = bytes[j];
                if c2.is_ascii_punctuation() {
                    j += 1
                } else {
                    break;
                }
            }
            let slice = &self.src[self.i + 1..j];
            self.col += j - self.i;
            self.i = j;
            return DOLLAR_SYM(slice);
        } else if c.is_ascii_alphabetic() {
            let mut j = self.i + 1;
            while j < bytes.len() {
                let c2 = bytes[j];
                if c2.is_ascii_alphanumeric()
                    || (c.is_ascii_uppercase() && c2 == b'.')
                {
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
        } else if c.is_ascii_punctuation() {
            let mut j = self.i + 1;
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

/// An interpolation argument.
///
/// This is used to fill in "gaps" in the parsed expression, represented
/// by a "?", similar to SQL parametrized queries.
#[derive(Clone, Copy, Debug)]
pub enum InterpolationArg<'a> {
    Thm(&'a k::Thm),
    Expr(&'a k::Expr),
}

impl<'a> From<&'a k::Thm> for InterpolationArg<'a> {
    fn from(x: &'a k::Thm) -> Self {
        InterpolationArg::Thm(x)
    }
}
impl<'a> From<&'a k::Expr> for InterpolationArg<'a> {
    fn from(x: &'a k::Expr) -> Self {
        InterpolationArg::Expr(x)
    }
}

/// Parser for expressions.
///
/// It uses a fixity function, and a lexer that yields the stream of tokens
/// to parse.
pub struct Parser<'a> {
    ctx: &'a mut dyn CtxI,
    /// Local variables, from binders.
    local: Vec<k::Var>,
    lexer: Lexer<'a>,
    next_tok: Option<Tok<'a>>,
    /// Interpolation arguments.
    qargs: &'a [InterpolationArg<'a>],
    /// Index in `qargs`
    qargs_idx: usize,
}

// TODO: binders: select, with, \\, pi
// TODO: infix: =, ==>
// TODO: normal names: Bool, $=, $==>, $select, type, defined constants

macro_rules! perror {
    ($self: ident, $fmt: literal) => {
        Error::new_string(format!(
                    concat!( "parse error at {:?}: ", $fmt), $self.loc()))
    };
    ($self: ident, $fmt: literal, $($arg:expr ),*) => {
        Error::new_string(format!(
                    concat!( "parse error at {:?}: ", $fmt), $self.loc(),
                    $($arg),*))
    };
}

impl<'a> Parser<'a> {
    /// New parser using the given string `src` and interpolation arguments `qargs`.
    ///
    /// Holes in the source `src` will be filled with elements of `qargs`.
    /// A parse error will be emitted if the number of holes in `src` does not
    /// correspond to the length of `qargs`.
    pub fn new_with_args(
        ctx: &'a mut dyn CtxI,
        src: &'a str,
        qargs: &'a [InterpolationArg<'a>],
    ) -> Self {
        let lexer = Lexer::new(src);
        Self { ctx, local: vec![], lexer, next_tok: None, qargs, qargs_idx: 0 }
    }

    /// New parser using the given string `src`.
    ///
    /// The string must not contain interpolation holes `"?"`.
    pub fn new(ctx: &'a mut dyn CtxI, src: &'a str) -> Self {
        Self::new_with_args(ctx, src, &[])
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
        match s {
            "=" => Fixity::Infix((10, 11)),
            "==>" => Fixity::Infix((6, 5)),
            "with" => Fixity::Binder((1, 2)),
            "\\" => Fixity::Binder((30, 31)),
            "select" => Fixity::Binder((26, 27)),
            _ => Fixity::Nullary,
        }
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

    /// Consume `tok` and fail on anything else.
    fn eat_(&mut self, tok: Tok) -> Result<()> {
        let t = self.peek_();
        if t == tok {
            self.next_();
            Ok(())
        } else {
            Err(Error::new_string(format!("expected {:?}, got {:?}", tok, t)))
        }
    }

    /// Parse a bound variable.
    fn parse_bnd_var(
        &mut self,
        ty_expected: Option<k::Expr>,
    ) -> Result<k::Var> {
        use Tok::*;

        let v = match self.next_() {
            SYM(s) => s,
            t => {
                return Err(perror!(
                    self,
                    "unexpected token {:?} while parsing bound variable",
                    t
                ))
            }
        };

        let ty_parsed = if let COLON = self.peek_() {
            self.eat_(COLON)?;
            // the expression after `:` should have type `type`.
            let ty_ty = self.ctx.mk_ty();
            Some(self.parse_bp_(0, Some(ty_ty))?)
        } else {
            None
        };

        let ty = match (ty_parsed, ty_expected) {
            (Some(ty), _) => ty,
            (None, Some(ty)) => ty,
            (None, None) => {
                return Err(perror!(
                    self,
                    "cannot find type for variable {}",
                    v
                ));
            }
        };

        let v = k::Var { name: k::Symbol::from_str(v), ty };
        Ok(v)
    }

    fn expr_of_atom_(&mut self, s: &str) -> Result<k::Expr> {
        Ok(match s {
            "=" => self.ctx.mk_eq(),
            "==>" => self.ctx.mk_imply(),
            "select" => self.ctx.mk_select(),
            "ind" => self.ctx.mk_ind(),
            "bool" => self.ctx.mk_bool(),
            "type" => self.ctx.mk_ty(),
            _ => self
                .ctx
                .find_const(s)
                .ok_or_else(|| perror!(self, "unknown constant {:?}", s))?
                .clone(),
        })
    }

    /// Apply an infix token.
    fn apply_sym2_(
        &mut self,
        s: &str,
        e1: k::Expr,
        e2: k::Expr,
    ) -> Result<k::Expr> {
        match s {
            "=" => self.ctx.mk_app(e1, e2),
            "==>" => {
                let i = self.ctx.mk_imply();
                self.ctx.mk_app_l(i, &[e1, e2])
            }
            _ => Err(perror!(self, "todo: handle infix '{:?}'", s)),
        }
    }

    /// Apply binder `b`.
    fn mk_binder_(
        &mut self,
        _b: &str,
        _v: k::Var,
        _body: k::Expr,
    ) -> Result<k::Expr> {
        todo!() // TODO
    }

    // TODO
    /*
    fn apply_sym1_(&mut self, s: &str, k: k::Expr) -> Result<k::Expr> {
        match s {
            "=" => todo!(),
            "==>" => todo!(),
            "with" => todo!(),
        }
    }
    */

    /// Look for an interpolation argument and consume it
    fn interpol_expr_(&mut self) -> Result<k::Expr> {
        Ok(if self.qargs_idx < self.qargs.len() {
            let e = match self.qargs[self.qargs_idx] {
                InterpolationArg::Expr(e) => e.clone(),
                InterpolationArg::Thm(_) => {
                    return Err(perror!(
                    self,
                    "interpolation parameter {} is a theorem, expected a term",
                    self.qargs_idx
                ))
                }
            };
            self.qargs_idx += 1;
            e
        } else {
            return Err(perror!(self, "too many interpolation '?'"));
        })
    }

    /// Parse an expression, up to EOF.
    ///
    /// `bp` is the current binding power for this Pratt parser.
    fn parse_bp_(
        &mut self,
        bp: u16,
        ty_expected: Option<k::Expr>,
    ) -> Result<k::Expr> {
        use Tok::*;

        let mut lhs = {
            let t = self.next_();
            match t {
                SYM(s) => {
                    // TODO: get a constant for that, fail if undefined
                    match self.fixity_(s) {
                        Fixity::Prefix((_, r_bp)) => {
                            let arg = self.parse_bp_(r_bp, None)?;
                            let lhs = self.expr_of_atom_(s)?;
                            self.ctx.mk_app(lhs, arg)?
                        }
                        Fixity::Infix(..) => {
                            return Err(perror!(
                                self,
                                "unexpected infix operator {:?}",
                                s
                            ));
                        }
                        Fixity::Postfix(..) => {
                            return Err(perror!(
                                self,
                                "unexpected infix operator {:?}",
                                s
                            ));
                        }
                        Fixity::Binder((_, l2)) => {
                            // TODO: provide expected type, maybe
                            let v = self.parse_bnd_var(None)?;
                            let old_l = self.local.len();
                            self.local.push(v.clone());
                            self.eat_(DOT)?;
                            // TODO: provide expected type of body?
                            let body = self.parse_bp_(l2, None)?;
                            self.local.truncate(old_l);
                            self.mk_binder_(s, v, body)?
                        }
                        _ => self.expr_of_atom_(s)?,
                    }
                }
                DOLLAR_SYM(s) => self.expr_of_atom_(s)?,
                QUESTION_MARK => self.interpol_expr_()?,
                NUM(_s) => todo!("parse number"), // PExpr::var(s, self.loc()),
                LPAREN => {
                    let t = self.parse_bp_(0, ty_expected)?;
                    self.eat_(RPAREN)?;
                    t
                }
                RPAREN | DOT | EOF | COLON => {
                    return Err(perror!(self, "unexpected token {:?}'", t))
                }
            }
        };

        loop {
            let (op, l_bp, r_bp) = match self.peek_() {
                EOF => return Ok(lhs),
                RPAREN | COLON | DOT => break,
                LPAREN => {
                    // TODO: set ty_expected to `lhs`'s first argument's type.
                    self.next_();
                    let t = self.parse_bp_(0, None)?; // maximum binding power
                    self.eat_(RPAREN)?;
                    lhs = self.ctx.mk_app(lhs, t)?;
                    continue;
                }
                DOLLAR_SYM(s) => {
                    let arg = self.expr_of_atom_(s)?;

                    self.next_();
                    // simple application
                    lhs = self.ctx.mk_app(lhs, arg)?;
                    continue;
                }
                QUESTION_MARK => {
                    self.next_();
                    let arg = self.interpol_expr_()?;

                    // simple application
                    lhs = self.ctx.mk_app(lhs, arg)?;
                    continue;
                }
                NUM(_s) => todo!("handle numbers"),
                SYM(s) => {
                    match self.fixity_(s) {
                        Fixity::Infix((l1, l2)) => (s, l1, l2),
                        Fixity::Nullary => {
                            // simple application
                            let arg = self.expr_of_atom_(s)?;
                            lhs = self.ctx.mk_app(lhs, arg)?;
                            self.next_();
                            continue;
                        }
                        Fixity::Postfix((l_bp, _)) => {
                            if l_bp < bp {
                                break;
                            }
                            self.next_();

                            // postfix operator applied to lhs
                            let po = self.expr_of_atom_(s)?;
                            lhs = self.ctx.mk_app(po, lhs)?;
                            continue;
                        }
                        Fixity::Prefix(..) => {
                            return Err(Error::new("unexpected prefix symbol"))
                        }
                        Fixity::Binder(..) => {
                            return Err(Error::new("unexpected inder"))
                        }
                    }
                }
            };

            if l_bp < bp {
                break; // binding left
            }

            self.next_();

            let rhs = self.parse_bp_(r_bp, None)?;

            // infix apply
            let app = self.apply_sym2_(op, lhs, rhs)?;
            lhs = app;
        }

        Ok(lhs)
    }

    // TODO: parse/execute statements:
    // -``def f := expr; …`
    // - `tydef tau := thm, abs, repr; …`

    /// Parse an expression, up to EOF.
    pub fn parse(&mut self) -> Result<k::Expr> {
        let e = self.parse_bp_(0, None)?;
        if self.peek_() != Tok::EOF {
            Err(perror!(self, "expected EOF"))
        } else if self.qargs_idx < self.qargs.len() {
            Err(perror!(self,
                    "expected all {} interpolation arguments to be used, but only {} were",
                    self.qargs.len(), self.qargs_idx))
        } else {
            Ok(e)
        }
    }
}

/// Parse the string into an expression.
pub fn parse_expr(ctx: &mut dyn CtxI, s: &str) -> Result<k::Expr> {
    let mut p = Parser::new(ctx, s);
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

    /*
    #[test]
    fn test_parser1() {
        let s = "foo";
        let get_fix = |_: &str| None;
        let e = parse(&get_fix, s).unwrap();
        assert_eq!("foo", e.to_string());
    }

    #[test]
    fn test_parser2() {
        let get_fix = |s: &str| match s {
            "=" => Some(Fixity::Infix((10, 10))),
            "!" | "?" => Some(Fixity::Binder((0, 5))),
            _ => None,
        };
        let s = "?y. (!x: foo bar. f x) = y";
        let e = parse(&get_fix, s).unwrap();
        assert_eq!("(?y. (= (!x: (foo bar). (f x)) y))", e.to_string());
        assert_eq!(
            "?y. (!x: foo bar. f x) = y",
            format!("{}", PrintStr::new(&get_fix, &e))
        );
    }

    #[test]
    fn test_parser4() {
        let s = "f _";
        let get_fix = |_: &str| None;
        let e = parse(&get_fix, s).unwrap();
        assert_eq!("(f _)", e.to_string());
    }
    */

    /* FIXME
    #[test]
    fn test_infer1() {
        let mut ctx = k::Ctx::new();
        let mut db = db::Database::new();

        // test parse 2
        let get_fix = |s: &str| match s {
            "=" => Some(Fixity::Infix((10, 10))),
            "\\" => Some(Fixity::Binder((0, 5))),
            _ => None,
        };
        let s = "\\y. (\\x: foo bar. f x) = y";
        let e = parse(&get_fix, s).unwrap();
        assert_eq!("(\\y. (= (\\x: (foo bar). (f x)) y))", e.to_string());

        // now infer
        let mut ictx = TypeInferenceCtx::new(&mut ctx, &mut db);
        let e2 = ictx.infer(&e).unwrap();
        println!("{:?}", e2);
    }

    #[test]
    fn test_infer2() {
        let mut ctx = k::Ctx::new();
        let mut db = db::Database::new();

        // test parse 2
        let get_fix = |s: &str| match s {
            "=" => Some(Fixity::Infix((10, 10))),
            "!" | "?" | "\\" => Some(Fixity::Binder((0, 5))),
            _ => None,
        };
        let s = "?y. (!x: foo bar. f x) = y";
        let e = parse(&get_fix, s).unwrap();
        assert_eq!("(?y. (= (!x: (foo bar). (f x)) y))", e.to_string());

        // now infer
        let mut ictx = TypeInferenceCtx::new(&mut ctx, &mut db);
        let e2 = ictx.infer(&e).unwrap();
        println!("{:?}", e2);
    }
    */
}
