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
    QUOTED_STR(&'a str),
    LET,
    IN,
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

/// Symbol that can be infix or prefix or postfix
fn is_ascii_symbol(c: u8) -> bool {
    match c {
        b'=' | b',' | b';' | b'<' | b'>' | b'!' | b'/' | b'\\' | b'+'
        | b'-' | b'|' | b'^' | b'~' | b'*' | b'&' | b'%' | b'@' => true,
        _ => false,
    }
}

impl<'a> Lexer<'a> {
    fn new(src: &'a str) -> Self {
        Self { src, i: 0, line: 1, col: 1, is_done: false }
    }

    pub fn cur_pos(&self) -> (usize, usize) {
        (self.line, self.col)
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
            self.col = 1;
            self.line += 1;
        }
        &self.src[i..j]
    }

    /// get next token.
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
                if is_ascii_symbol(c2) {
                    j += 1
                } else {
                    break;
                }
            }
            let slice = &self.src[self.i + 1..j];
            self.col += j - self.i;
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
            self.col += j - self.i;
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
            self.col += j - self.i;
            self.i = j;
            return SYM(slice);
        } else {
            let s = &[c];
            todo!("handle char {:?} ({:?})", c, std::str::from_utf8(s)) // TODO? error?
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

/// Result of parsing a statement.
#[derive(Debug, Clone)]
pub enum ParseOutput {
    Expr(k::Expr),
    Thm(k::Thm),
    Def((k::Expr, k::Thm)),
    DefTy(k::NewTypeDef),
    SideEffect(&'static str),
    Include(Vec<ParseOutput>),
}

/// Parser for expressions.
///
/// It uses a fixity function, and a lexer that yields the stream of tokens
/// to parse.
pub struct Parser<'a> {
    ctx: &'a mut dyn CtxI,
    /// Local variables from binders.
    local: Vec<k::Var>,
    /// Let bindings (`let x = y in z`)
    let_bindings: Vec<(&'a str, k::Expr)>,
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
        Self {
            ctx,
            local: vec![],
            let_bindings: vec![],
            lexer,
            next_tok: None,
            qargs,
            qargs_idx: 0,
        }
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
            "=" => Fixity::Infix((30, 31)),
            "==>" => Fixity::Infix((46, 45)),
            "->" => Fixity::Infix((81, 80)),
            "with" => Fixity::Binder((1, 2)),
            "\\" => Fixity::Binder((20, 21)),
            "select" => Fixity::Binder((22, 23)),
            "pi" => Fixity::Binder((24, 25)),
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

    /// Parse a symbol and return it.
    fn parse_sym_(&mut self) -> Result<&'a str> {
        use Tok::*;
        match self.next_() {
            SYM(s) => Ok(s),
            t => Err(perror!(self, "expected symbol, got {:?}", t)),
        }
    }

    /// Parse a (list of) bound variable(s) of the same type.
    fn parse_bnd_var_list_(
        &mut self,
        ty_expected: Option<&k::Expr>,
    ) -> Result<usize> {
        use Tok::*;
        const MAX_NUM: usize = 16;

        // parse at most 16 of them
        let mut names: [&'a str; MAX_NUM] = [""; MAX_NUM];
        let mut i = 0;

        loop {
            match self.peek_() {
                SYM(s) => {
                    names[i] = s;
                    i += 1;
                    if i >= MAX_NUM {
                        return Err(perror!(
                            self,
                            "cannot parse more than {} variables in one binder",
                            MAX_NUM
                        ));
                    }
                    self.next_();
                }
                COLON | DOT => break,
                t => {
                    return Err(perror!(
                        self,
                        "unexpected token {:?} while parsing bound variable",
                        t
                    ))
                }
            };
        }
        if i == 0 {
            return Err(perror!(self, "expected a variable name",));
        }

        let ty_parsed = if let COLON = self.peek_() {
            self.eat_(COLON)?;
            // the expression after `:` should have type `type`.
            let ty_ty = self.ctx.mk_ty();
            Some(self.parse_expr_bp_(0, Some(ty_ty))?)
        } else {
            None
        };

        let ty = match (&ty_parsed, ty_expected) {
            (Some(ty), _) => &ty,
            (None, Some(ty)) => ty,
            (None, None) => {
                return Err(perror!(
                    self,
                    "cannot infer type for bound variable(s)",
                ));
            }
        };

        // push variables now that we have their type.
        for j in 0..i {
            let v =
                k::Var { name: k::Symbol::from_str(names[j]), ty: ty.clone() };
            self.local.push(v)
        }

        Ok(i)
    }

    /// Parse a list of bound variables and pushes them onto `self.local`.
    ///
    /// Returns the number of parsed variables.
    fn parse_bnd_vars_(
        &mut self,
        ty_expected: Option<&k::Expr>,
    ) -> Result<usize> {
        use Tok::*;

        let mut n = 0;
        loop {
            match self.peek_() {
                LPAREN => {
                    self.next_();
                    n += self.parse_bnd_var_list_(ty_expected)?;
                    self.eat_(RPAREN)?;
                },
                SYM(_) => {
                    n += self.parse_bnd_var_list_(ty_expected)?;
                    break;
                }
                DOT => break,
                t => {
                    return Err(perror!(
                        self,
                        "unexpected token {:?} while parsing a list of bound variables",
                        t))
                }

            }
        }
        if n == 0 {
            return Err(perror!(
                self,
                "expected at least one bound variable after binder",
            ));
        }

        Ok(n)
    }

    /// Resolve a single symbol into a (constant or variable) expression.
    fn expr_of_atom_(&mut self, s: &str) -> Result<k::Expr> {
        // let bindings
        if let Some((_, e)) = self.let_bindings.iter().find(|(v, _)| *v == s) {
            return Ok(e.clone());
        };
        // local variables
        if let Some(v) = self.local.iter().find(|x| x.name.name() == s) {
            let e = self.ctx.mk_var(v.clone());
            return Ok(e);
        };
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
    fn apply_expr_infix_(
        &mut self,
        s: &str,
        e1: k::Expr,
        e2: k::Expr,
    ) -> Result<k::Expr> {
        match s {
            "=" => self.ctx.mk_eq_app(e1, e2),
            "==>" => {
                let i = self.ctx.mk_imply();
                self.ctx.mk_app_l(i, &[e1, e2])
            }
            "->" => self.ctx.mk_arrow(e1, e2),
            _ => Err(perror!(self, "todo: handle infix '{:?}'", s)),
        }
    }

    /// Expected type for variables bound by `b`.
    fn binder_type_hint_(&mut self, b: &str) -> Result<Option<k::Expr>> {
        Ok(match b {
            "pi" => {
                let ty = self.ctx.mk_ty();
                Some(ty)
            }
            _ => None,
        })
    }

    /// Apply binder `b`.
    fn mk_expr_binder_(
        &mut self,
        b: &str,
        local_offset: usize,
        body: k::Expr,
    ) -> Result<k::Expr> {
        let vars = &self.local[local_offset..];
        Ok(match b {
            "with" => {
                body // not a real binder
            }
            "\\" => self.ctx.mk_lambda_l(vars, body)?,
            "pi" => self.ctx.mk_pi_l(vars, body)?,
            "select" => {
                // turn `select x. p` into `select (λx. p)`
                let mut t = body;
                for v in vars {
                    let ty_v = v.ty();
                    let sel = self.ctx.mk_select();
                    let sel = self.ctx.mk_app(sel, ty_v.clone())?;
                    let lam = self.ctx.mk_lambda(v.clone(), t)?;
                    t = self.ctx.mk_app(sel, lam)?;
                }
                t
            }
            _ => return Err(perror!(self, "TODO: mk binder {}", b)),
        })
    }

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

    /// Parse an expression.
    ///
    /// `bp` is the current binding power for this Pratt parser.
    fn parse_expr_bp_(
        &mut self,
        bp: u16,
        ty_expected: Option<k::Expr>,
    ) -> Result<k::Expr> {
        use Tok::*;

        let mut lhs = {
            let t = self.next_();
            match t {
                LET => {
                    // parse `let x = y in e`.
                    let v = self.parse_sym_()?;
                    self.eat_(SYM("="))?;
                    let e = self.parse_expr_bp_(0, None)?;
                    self.eat_(IN)?;
                    let n_let = self.let_bindings.len();
                    self.let_bindings.push((v, e));
                    let body = self.parse_expr_bp_(bp, ty_expected);
                    self.let_bindings.truncate(n_let);
                    body?
                }
                SYM(s) => {
                    // TODO: get a constant for that, fail if undefined
                    match self.fixity_(s) {
                        Fixity::Prefix((_, r_bp)) => {
                            let arg = self.parse_expr_bp_(r_bp, None)?;
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
                                "unexpected postfix operator {:?}",
                                s
                            ));
                        }
                        Fixity::Binder((_, l2)) => {
                            let local_offset = self.local.len();
                            let ty_expected_vars = self.binder_type_hint_(s)?;
                            self.parse_bnd_vars_(ty_expected_vars.as_ref())?;
                            self.eat_(DOT)?;
                            // TODO: find expected type for body, maybe
                            let body = self.parse_expr_bp_(l2, None)?;
                            let result =
                                self.mk_expr_binder_(s, local_offset, body);
                            self.local.truncate(local_offset);
                            result?
                        }
                        _ => self.expr_of_atom_(s)?,
                    }
                }
                DOLLAR_SYM(s) => self.expr_of_atom_(s)?,
                QUESTION_MARK => self.interpol_expr_()?,
                NUM(s) => {
                    let mut i: i64 = s.parse().map_err(|e| {
                        perror!(self, "cannot parse integer literal: {}", e)
                    })?;
                    if i < 0 {
                        // TODO: relative numbers
                        return Err(perror!(
                            self,
                            "cannot parse negative numbers yet"
                        ));
                    }
                    let mut t = self.ctx.find_const("Zero")
                        .ok_or_else(||
                        perror!(self, "cannot find constant `Zero` to encode number `{}`", i)
                    )?.clone();
                    while i > 0 {
                        let b = i % 2 == 1;
                        let f = if b { "Bit1" } else { "Bit0" };
                        let f =
                            self.ctx.find_const(f)
                                .ok_or_else(||
                                    perror!(self, "cannot find constant `{}` to encode number `{}`", f, i)
                                )?.clone();
                        t = self.ctx.mk_app(f, t).map_err(|e| {
                            perror!(
                                self,
                                "type error when encoding number `{}`: {}",
                                i,
                                e
                            )
                        })?;
                        i = i / 2;
                    }
                    t
                }
                LPAREN => {
                    let t = self.parse_expr_bp_(0, ty_expected)?;
                    self.eat_(RPAREN)?;
                    t
                }
                RPAREN | DOT | EOF | COLON | IN | QUOTED_STR(..) => {
                    return Err(perror!(self, "unexpected token {:?}", t))
                }
            }
        };

        loop {
            let (op, l_bp, r_bp) = match self.peek_() {
                EOF => return Ok(lhs),
                RPAREN | COLON | DOT | IN | LET | QUOTED_STR(..) => break,
                LPAREN => {
                    // TODO: set ty_expected to `lhs`'s first argument's type.
                    self.next_();
                    let t = self.parse_expr_bp_(0, None)?; // maximum binding power
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
                NUM(_s) => return Err(perror!(self, "handle numbers")),
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
                            return Err(perror!(
                                self,
                                "unexpected prefix symbol {:?}",
                                s
                            ))
                        }
                        Fixity::Binder(..) => {
                            return Err(perror!(
                                self,
                                "unexpected binder {:?}",
                                s
                            ))
                        }
                    }
                }
            };

            if l_bp < bp {
                break; // binding left
            }

            self.next_();

            let rhs = self.parse_expr_bp_(r_bp, None)?;

            // infix apply
            let app = self.apply_expr_infix_(op, lhs, rhs)?;
            lhs = app;
        }

        Ok(lhs)
    }

    // TODO: parse/execute statements:
    // - `tydef tau := thm, abs, repr; …`

    /// Parse an expression, up to EOF.
    pub fn parse_expr(&mut self) -> Result<k::Expr> {
        let e = self.parse_expr_bp_(0, None)?;
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
    p.parse_expr()
}

/// Parse the string into an expression with a set of parameters.
pub fn parse_expr_with_args(
    ctx: &mut dyn CtxI,
    s: &str,
    qargs: &[InterpolationArg],
) -> Result<k::Expr> {
    let mut p = Parser::new_with_args(ctx, s, qargs);
    p.parse_expr()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lexer1() {
        use Tok::*;
        let lexer = Lexer::new(" foo + bar13(hello! \" co co\" world) ");
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
        let lexer = Lexer::new(r#"((12+ f(x, in Y \( ))---let z)wlet)"#);
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

    #[test]
    fn test_parser_expr() -> Result<()> {
        let pairs = [
            (
                "with a:bool. select x:bool. x=a",
                "(select bool (λx0 : bool. (= bool x0 a)))",
            ),
            (r#"(\x:bool. x= x) "#, "(λx0 : bool. (= bool x0 x0))"),
            (
                r#"(\x y:bool. x= y) "#,
                "(λx0 : bool. (λx1 : bool. (= bool x0 x1)))",
            ),
            (
                "with a:bool. with b:bool. (a=b) = (b=a)",
                "(= bool (= bool a b) (= bool b a))",
            ),
            (
                "with (a b:bool). (a=b) = (b=a)",
                "(= bool (= bool a b) (= bool b a))",
            ),
            (
                "let t=bool in with (a b:t). (let y = b in (a=y)) = let y = a in (b=y)",
                "(= bool (= bool a b) (= bool b a))",
            ),
        ];

        for (x, y) in &pairs {
            let mut ctx = k::Ctx::new();
            let r = parse_expr(&mut ctx, x).map_err(|e| {
                e.set_source(Error::new_string(format!("parsing {:?}", x)))
            })?;
            let r2 = format!("{:?}", r);
            assert_eq!(&r2, *y);
        }
        Ok(())
    }

    #[test]
    fn test_parser_expr_interpol() -> Result<()> {
        let cases: Vec<(
            &'static str,
            &'static str,
            &'static dyn Fn(&mut dyn CtxI) -> Result<Vec<k::Expr>>,
        )> = vec![
            (
                "with a:?. select x:?. x=a",
                "(select bool (λx0 : bool. (= bool x0 a)))",
                &|ctx: &mut dyn CtxI| Ok(vec![ctx.mk_bool(), ctx.mk_bool()]),
            ),
            (
                r#"(\x:bool. ?= x) "#,
                "(λx0 : bool. (= bool x0 x0))",
                &|ctx: &mut dyn CtxI| {
                    let b = ctx.mk_bool();
                    Ok(vec![ctx.mk_var_str("x", b)])
                },
            ),
            /*
            (
                r#"(\x y:bool. x= y) "#,
                "(λx0 : bool. (λx1 : bool. (= bool x0 x1)))",
            ),
            (
                "with a:bool. with b:bool. (a=b) = (b=a)",
                "(= bool (= bool a b) (= bool b a))",
            ),
            (
                "with (a b:bool). (a=b) = (b=a)",
                "(= bool (= bool a b) (= bool b a))",
            ),
             */
        ];

        for (x, y, f) in &cases {
            let mut ctx = k::Ctx::new();
            let args: Vec<_> = f(&mut ctx)?;
            let qargs: Vec<InterpolationArg> =
                args.iter().map(|x| x.into()).collect();
            let r = parse_expr_with_args(&mut ctx, x, &qargs).map_err(|e| {
                e.set_source(Error::new_string(format!("parsing {:?}", x)))
            })?;
            let r2 = format!("{:?}", r);
            assert_eq!(&r2, *y);
        }
        Ok(())
    }
}
