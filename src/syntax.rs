//! A basic syntax for parsing and printing terms.
//!
//! This syntax is optional and is not needed at all when using the kernel.
//! We follow https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
//! for the main parser and terminology.

use crate::{database as db, fnv, kernel_of_trust as k, utils, Error, Result};
use std::{cell::RefCell, fmt, rc::Rc, sync::atomic, u16};

/// ## Definition of the AST
///
/// The AST used for parsing and type inference.
#[derive(Clone)]
pub struct PExpr(Rc<PExprCell>);

/// Content of an expression.
#[derive(Clone)]
pub struct PExprCell {
    /// View of the expression
    view: PExprView,
    /// Location in the input (start location)
    loc: (usize, usize),
    /// The expression this resolves into after type inference
    resolved: RefCell<Option<k::Expr>>,
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

/// Reuse symbols from the kernel.
type Symbol = k::Symbol;

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
        PExpr(Rc::new(PExprCell { view, loc, resolved: RefCell::new(None) }))
    }

    /// Flatten an application.
    pub fn unfold_app(&self) -> (&PExpr, Vec<&PExpr>) {
        let mut t = self;
        let mut args = vec![];
        while let App(f, a) = &t.0.view {
            args.push(a);
            t = f;
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

// token
#[derive(Debug, Copy, Clone, PartialEq)]
#[allow(non_camel_case_types)]
enum Tok<'a> {
    LPAREN,
    RPAREN,
    COLON,
    DOT,
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

    /// Parse a bound variable.
    fn parse_var(&mut self) -> Result<Var> {
        use Tok::*;

        let v = match self.next_() {
            SYM(s) => s,
            t => {
                return Err(Error::new_string(format!(
                    "unexpected token {:?} while parsing bound variable",
                    t
                )))
            }
        };

        let ty = if let COLON = self.peek_() {
            self.eat_(COLON)?;
            Some(self.parse_bp(0)?)
        } else {
            None
        };
        Ok(Var { name: Symbol::from_str(v), ty })
    }

    /// Parse an expression, up to EOF.
    ///
    /// `bp` is the current binding power for this Pratt parser.
    pub fn parse_bp(&mut self, bp: u16) -> Result<PExpr> {
        use Tok::*;

        let mut lhs = {
            let t = self.next_();
            match t {
                SYM(s) => {
                    let t_loc = self.loc();
                    let t = PExpr::var(s, t_loc);
                    match self.fixity_(s) {
                        Fixity::Prefix((_, r_bp)) => {
                            let arg = self.parse_bp(r_bp)?;
                            t.apply(arg, t_loc)
                        }
                        Fixity::Infix(..) => {
                            return Err(Error::new(
                                "unexpected infix operator",
                            ));
                        }
                        Fixity::Postfix(..) => {
                            return Err(Error::new(
                                "unexpected infix operator",
                            ));
                        }
                        Fixity::Binder((_, l2)) => {
                            let v = self.parse_var()?;
                            self.eat_(DOT)?;
                            let body = self.parse_bp(l2)?;
                            PExpr::bind(s, v, body, t_loc)
                        }
                        _ => t,
                    }
                }
                DOLLAR_SYM(s) => PExpr::dollar_var(s, self.loc()), // TODO: handle prefix op
                NUM(s) => PExpr::var(s, self.loc()),
                LPAREN => {
                    let t = self.parse_bp(0)?;
                    self.eat_(RPAREN)?;
                    t
                }
                RPAREN | DOT | EOF | COLON => {
                    return Err(Error::new_string(format!(
                        "unexpected token {:?}'",
                        t
                    )))
                }
            }
        };

        loop {
            let loc_op = self.loc();
            let (op, l_bp, r_bp) = match self.peek_() {
                EOF => return Ok(lhs),
                RPAREN | COLON | DOT => break,
                LPAREN => {
                    self.next_();
                    let t = self.parse_bp(0)?; // maximum binding power
                    self.eat_(RPAREN)?;
                    lhs = lhs.apply(t, loc_op);
                    continue;
                }
                DOLLAR_SYM(s) => {
                    let v = PExpr::dollar_var(s, self.loc());
                    // simple application
                    lhs = lhs.apply(v, self.loc());
                    self.next_();
                    continue;
                }
                NUM(s) => {
                    let v = PExpr::num(s, self.loc());
                    lhs = lhs.apply(v, self.loc());
                    self.next_();
                    continue;
                }
                SYM(s) => {
                    let loc_op = self.loc();
                    let v = PExpr::var(s, loc_op);
                    match self.fixity_(s) {
                        Fixity::Infix((l1, l2)) => (v, l1, l2),
                        Fixity::Nullary => {
                            // simple application
                            lhs = lhs.apply(v, self.loc());
                            self.next_();
                            continue;
                        }
                        Fixity::Postfix((l_bp, _)) => {
                            if l_bp < bp {
                                break;
                            }
                            self.next_();

                            // postfix operator applied to lhs
                            lhs = v.apply(lhs, loc_op);
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

            let rhs = self.parse_bp(r_bp)?;

            // infix apply
            let app = op.apply_l(&[lhs, rhs], loc_op);
            lhs = app;
        }

        Ok(lhs)
    }

    fn parse_top_(&mut self) -> Result<PExpr> {
        let e = self.parse_bp(0)?;
        if self.peek_() != Tok::EOF {
            Err(Error::new("expected EOF"))
        } else {
            Ok(e)
        }
    }

    /// Parse an expression, up to EOF.
    pub fn parse(&mut self) -> Result<PExpr> {
        self.parse_top_().map_err(|e| {
            e.set_source(Error::new_string(format!(
                "parse expression, at {:?}",
                self.loc()
            )))
        })
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

/// ## Pretty printing
///
/// This struct captures an expression to print and a fixity function used
/// to properly display infix symbols and insert parenthesis.
#[derive(Copy, Clone)]
pub struct PrintStr<'a> {
    e: &'a PExpr,
    get_fixity: &'a dyn Fn(&str) -> Option<Fixity>,
    min_bp: u16,
}

impl<'a> PrintStr<'a> {
    /// New printer for the given expression.
    pub fn new(
        get_fixity: &'a dyn Fn(&str) -> Option<Fixity>,
        e: &'a PExpr,
    ) -> Self {
        Self { e, get_fixity, min_bp: 0 }
    }

    fn set_e_(&self, e2: &'a PExpr) -> Self {
        PrintStr { e: e2, ..*self }
    }

    fn set_bp_(&self, bp: u16) -> Self {
        PrintStr { min_bp: bp, ..*self }
    }

    /// Pretty print into the given formatter.
    fn pp_bp(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self.e.view() {
            DollarVar(v) => write!(fmt, "${}", v.name()),
            Var(v) => write!(fmt, "{}", v.name()),
            Num(s) => write!(fmt, "{}", s),
            App(..) => {
                let (f, args) = self.e.unfold_app();
                debug_assert!(args.len() > 0);

                if let Var(s) = f.view() {
                    match (*self.get_fixity)(s.name()) {
                        Some(Fixity::Infix((lp, rp))) if args.len() == 2 => {
                            // TODO: remove implicit args? or use a dollar
                            let need_paren = self.min_bp >= lp;
                            if need_paren {
                                write!(fmt, "(")?;
                            }
                            write!(
                                fmt,
                                "{} {} {}",
                                self.set_e_(&args[0]).set_bp_(lp),
                                self.set_e_(f).set_bp_(u16::MAX),
                                self.set_e_(&args[1]).set_bp_(rp),
                            )?;

                            if need_paren {
                                write!(fmt, ")")?;
                            }
                            return Ok(());
                        }
                        Some(Fixity::Prefix((_, rp))) if args.len() == 1 => {
                            let need_paren = self.min_bp >= rp;
                            if need_paren {
                                write!(fmt, "(")?;
                            }
                            write!(
                                fmt,
                                "{} {}",
                                self.set_e_(f),
                                self.set_e_(&args[0]).set_bp_(rp)
                            )?;
                            if need_paren {
                                write!(fmt, ")")?;
                            }
                            return Ok(());
                        }
                        Some(Fixity::Postfix((lp, _))) if args.len() == 1 => {
                            let need_paren = self.min_bp >= lp;
                            if need_paren {
                                write!(fmt, "(")?;
                            }
                            write!(
                                fmt,
                                "{} {}",
                                self.set_e_(&args[0]).set_bp_(lp),
                                self.set_e_(f),
                            )?;
                            if need_paren {
                                write!(fmt, ")")?;
                            }
                            return Ok(());
                        }
                        Some(Fixity::Binder(..)) => panic!(
                            "unexpected binder fixity for symbol {:?}",
                            s
                        ),
                        Some(..) | None => (),
                    }
                }

                let need_paren = self.min_bp == u16::MAX;
                if need_paren {
                    write!(fmt, "(")?;
                }
                let sub_bp = u16::MAX; // application binds tightly
                self.set_e_(f).set_bp_(sub_bp).pp_bp(fmt)?;
                for x in args {
                    write!(fmt, " {}", self.set_e_(x).set_bp_(sub_bp))?;
                }

                if need_paren {
                    write!(fmt, ")")?;
                }
                Ok(())
            }
            Bind { binder, v, body } => {
                let r_bp = match (*self.get_fixity)(binder.name()) {
                    Some(Fixity::Binder((_, x))) => x,
                    None => 1,
                    _ => panic!(
                        "expected binder {:?} to have binder fixity",
                        binder
                    ),
                };
                if self.min_bp > r_bp {
                    write!(fmt, "(")?;
                }
                write!(fmt, "{}{}", binder.name(), v.name.name())?;
                if let Some(ty) = &v.ty {
                    write!(fmt, ": {}", self.set_e_(ty).set_bp_(0))?;
                }
                write!(fmt, ". ")?;
                self.set_e_(body).set_bp_(r_bp).pp_bp(fmt)?;

                if self.min_bp > r_bp {
                    write!(fmt, ")")?;
                }
                Ok(())
            }
        }
    }
}

impl<'a> fmt::Display for PrintStr<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.pp_bp(fmt)
    }
}

pub fn print(get_fix: &dyn Fn(&str) -> Option<Fixity>, e: &PExpr) -> String {
    let pp = PrintStr::new(get_fix, e);
    format!("{}", pp)
}

/// ## Type inference.
///
/// Type inference allows us to turn syntactic terms of type `PExpr`
/// into fully resolved `kernel_of_trust::Expr`.
/// It might fail if the input term is not well typed or not inferrable.
pub struct TypeInferenceCtx<'a> {
    ctx: &'a mut k::Ctx,
    db: &'a mut db::Database,
    gen_vars: Vec<k::Expr>, // freshly allocated variables
    vmap: fnv::FnvHashMap<Symbol, k::Expr>, // variables
}

// used to allocate fresh variables
static GENSYM: atomic::AtomicUsize = atomic::AtomicUsize::new(0);

impl<'a> TypeInferenceCtx<'a> {
    /// New type inference context.
    pub fn new(ctx: &'a mut k::Ctx, db: &'a mut db::Database) -> Self {
        Self { ctx, db, gen_vars: vec![], vmap: fnv::new_table_with_cap(16) }
    }

    fn new_name_(&mut self, s: &str) -> String {
        let n = GENSYM.fetch_add(1, atomic::Ordering::Relaxed);
        format!("{}{}", s, n)
    }

    fn new_ty_var_(&mut self) -> k::Expr {
        let ty = self.ctx.mk_ty();
        let name = self.new_name_("'a");
        let v = self.ctx.mk_var_str(&name, ty);
        self.gen_vars.push(v.clone());
        v
    }

    fn infer_var_(&mut self, v: &Symbol, is_dollar: bool) -> Result<k::Expr> {
        match self.vmap.get(v) {
            Some(e2) => {
                Ok(e2.clone()) // cached
            }
            None => {
                // lookup in database
                if let Some(c) = self.db.def_by_name(v.name()) {
                    Ok(c.expr.clone())
                } else if is_dollar {
                    Err(Error::new(
                        "dollar symbols can only be used for defined constants",
                    ))
                } else {
                    // allocate new var
                    let ty_v = self.new_ty_var_();
                    let ev = self.ctx.mk_var(k::Var::new(v.clone(), ty_v));
                    self.vmap.insert(v.clone(), ev.clone());
                    Ok(ev)
                }
            }
        }
    }

    fn infer_lam_(&mut self, v: &Var, body: &PExpr) -> Result<k::Expr> {
        // type of `v`
        let ty_v = match &v.ty {
            None => self.new_ty_var_(),
            Some(ty) => self.infer_(ty)?,
        };
        if self.vmap.contains_key(&v.name) {
            return Err(Error::new("shadowing of variables is forbidden"));
        }
        // locally insert a variable `v` with given type.
        let local_v = k::Var::new(v.name.clone(), ty_v);
        let local_ev = self.ctx.mk_var(local_v.clone());
        self.vmap.insert(v.name.clone(), local_ev.clone());
        // infer body
        let body = self.infer_(body);
        self.vmap.remove(&v.name);
        let e = self.ctx.mk_lambda(local_v, body?)?;
        Ok(e)
    }

    fn infer_(&mut self, e: &PExpr) -> Result<k::Expr> {
        // cached
        if let Some(e) = &*e.0.resolved.borrow() {
            return Ok(e.clone());
        }

        let e2 = match &e.0.view {
            Var(v) if v.name() == "_" => {
                // wildcard: generative variable. Do not cache.
                let ty_v = self.new_ty_var_();
                let name = self.new_name_("$x");
                self.ctx.mk_var_str(&name, ty_v)
            }
            Var(v) => self.infer_var_(v, false)?,
            DollarVar(v) => self.infer_var_(v, true)?,
            App(f, a) => {
                let f = self.infer_(f)?;
                let a = self.infer_(a)?;

                self.ctx.mk_app(f, a).map_err(|err| {
                    err.set_source(Error::new_string(format!(
                        "inferring {:?} at {:?}",
                        e, e.0.loc
                    )))
                })?

                // TODO: unify types, in case `f` is a variable
                /*
                match ty_f.view() {
                    k::EPi(..) => {
                        // direct apply

                    },
                    _ => {
                        let b =
                    }

                }
                utils::unify(f.ty(),
                */
            }
            Num(_) => todo!("type inference for numbers"),
            Bind { binder, v, body } if binder.name() == "\\" => {
                // pure lambda
                self.infer_lam_(v, body)?
            }
            Bind { binder, v, body } => {
                // `binder x. body` is sugar for `binder (λx. body)`
                let binder = self
                    .db
                    .def_by_name(binder.name())
                    .ok_or_else(|| {
                        Error::new_string(format!(
                            "cannot find binder {:?}",
                            &binder
                        ))
                    })?
                    .expr
                    .clone();
                let lam = self.infer_lam_(v, body)?;
                self.ctx.mk_app(binder, lam)?
            }
        };
        *e.0.resolved.borrow_mut() = Some(e2.clone());
        Ok(e2)
    }

    /// Perform type inference to turn `e` into a proper expression.
    pub fn infer(&mut self, e: &PExpr) -> Result<k::Expr> {
        self.gen_vars.clear();
        self.infer_(e)
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

    // test adapted from the blog post
    #[test]
    fn test_parser3() {
        let fix = |s: &str| match s {
            "+" | "-" => Some(Fixity::Infix((1, 2))),
            "*" | "/" => Some(Fixity::Infix((3, 4))),
            "o" => Some(Fixity::Infix((10, 9))),
            "~" => Some(Fixity::Prefix((0, 5))), // prefix -
            "!" => Some(Fixity::Postfix((7, 0))),
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

        let s = parse(&fix, "f o g o h").unwrap();
        assert_eq!(s.to_string(), "(o f (o g h))");

        let s = parse(&fix, " 1 + 2 + f o g o h * 3 * 4").unwrap();
        assert_eq!(s.to_string(), "(+ (+ 1 2) (* (* (o f (o g h)) 3) 4))");

        let s = parse(&fix, "~ ~1 * 2").unwrap();
        assert_eq!(s.to_string(), "(* (~ (~ 1)) 2)");

        let s = parse(&fix, "~ ~f o g").unwrap();
        assert_eq!(s.to_string(), "(~ (~ (o f g)))");

        let s = parse(&fix, "~9!").unwrap();
        assert_eq!(s.to_string(), "(~ (! 9))");

        let s = parse(&fix, "f o g !").unwrap();
        assert_eq!(s.to_string(), "(! (o f g))");

        let s = parse(&fix, "(((0)))").unwrap();
        assert_eq!(s.to_string(), "0");
    }

    #[test]
    fn test_parser4() {
        let s = "f _";
        let get_fix = |_: &str| None;
        let e = parse(&get_fix, s).unwrap();
        assert_eq!("(f _)", e.to_string());
    }

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
