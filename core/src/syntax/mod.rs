//! A basic syntax for parsing and printing terms.
//!
//! This syntax is optional and is not needed at all when using the kernel.
//! We follow https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
//! for the main parser and terminology.

use {
    crate::{kernel_of_trust as k, Ctx, Error, Result},
    std::fmt,
};

pub mod fixity;
pub mod lexer;

pub use fixity::Fixity;
use lexer::{Lexer, Tok};

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
    ctx: &'a mut Ctx,
    /// Local variables from binders.
    local: Vec<k::Var>,
    /// Let bindings (`let x = y in z`)
    let_bindings: Vec<(&'a str, k::Expr)>,
    lexer: Lexer<'a>,
    next_tok: Option<Tok<'a>>,
    /// Interpolation arguments.
    qargs: &'a [k::Expr],
    /// Index in `qargs`
    qargs_idx: usize,
}

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
    pub fn new_with_args(ctx: &'a mut Ctx, src: &'a str, qargs: &'a [k::Expr]) -> Self {
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
    pub fn new(ctx: &'a mut Ctx, src: &'a str) -> Self {
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
            "=" => k::FIXITY_EQ,
            "->" => k::FIXITY_ARROW,
            "with" => Fixity::Binder((1, 2)),
            "\\" => k::FIXITY_LAM,
            "pi" => k::FIXITY_PI,
            _ => {
                // lookup in context
                if let Some((_, f)) = self.ctx.find_const(s) {
                    f
                } else {
                    Fixity::Nullary
                }
            }
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
            Err(Error::new_string(format!(
                "expected {:?}, got {:?}",
                tok, t
            )))
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
    fn parse_bnd_var_list_(&mut self, ty_expected: Option<&k::Expr>) -> Result<usize> {
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
                return Err(perror!(self, "cannot infer type for bound variable(s)",));
            }
        };

        // push variables now that we have their type.
        for j in 0..i {
            let v = k::Var {
                name: k::Symbol::from_str(names[j]),
                ty: ty.clone(),
            };
            self.local.push(v)
        }

        Ok(i)
    }

    /// Parse a list of bound variables and pushes them onto `self.local`.
    ///
    /// Returns the number of parsed variables.
    fn parse_bnd_vars_(&mut self, ty_expected: Option<&k::Expr>) -> Result<usize> {
        use Tok::*;

        let mut n = 0;
        loop {
            match self.peek_() {
                LPAREN => {
                    self.next_();
                    n += self.parse_bnd_var_list_(ty_expected)?;
                    self.eat_(RPAREN)?;
                }
                SYM(_) => {
                    n += self.parse_bnd_var_list_(ty_expected)?;
                    break;
                }
                DOT => break,
                t => {
                    return Err(perror!(
                        self,
                        "unexpected token {:?} while parsing a list of bound variables",
                        t
                    ))
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
            "bool" => self.ctx.mk_bool(),
            "type" => self.ctx.mk_ty(),
            _ => self
                .ctx
                .find_const(s)
                .ok_or_else(|| perror!(self, "unknown constant {:?}", s))?
                .0
                .clone(),
        })
    }

    /// Apply an infix token.
    fn apply_expr_infix_(&mut self, s: &str, e1: k::Expr, e2: k::Expr) -> Result<k::Expr> {
        match s {
            "=" => self.ctx.mk_eq_app(e1, e2),
            "->" => self.ctx.mk_arrow(e1, e2),
            _ => {
                if let Some((c, _)) = self.ctx.find_const(s) {
                    let c = c.clone();
                    self.ctx.mk_app_l(c, &[e1, e2])
                } else {
                    return Err(perror!(self, "unknown infix '{:?}'", s));
                }
            }
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
    fn mk_expr_binder_(&mut self, b: &str, local_offset: usize, body: k::Expr) -> Result<k::Expr> {
        let vars = &self.local[local_offset..];
        Ok(match b {
            "with" => {
                body // not a real binder
            }
            "\\" => self.ctx.mk_lambda_l(vars, body)?,
            "pi" => self.ctx.mk_pi_l(vars, body)?,
            _ => {
                if let Some((c, Fixity::Binder(..))) = self.ctx.find_const(b) {
                    // turn `b x:ty. p` into `b ty (λx:ty. p)`
                    let c = c.clone();
                    let mut t = body;
                    for v in vars {
                        let ty = v.ty().clone();
                        let c = self.ctx.mk_app(c.clone(), ty)?;
                        let lam = self.ctx.mk_lambda(v.clone(), t)?;
                        t = self.ctx.mk_app(c, lam)?;
                    }
                    t
                } else {
                    return Err(perror!(self, "unknown binder {:?}", b));
                }
            }
        })
    }

    /// Look for an interpolation argument and consume it
    fn interpol_expr_(&mut self) -> Result<k::Expr> {
        Ok(if self.qargs_idx < self.qargs.len() {
            let e = self.qargs[self.qargs_idx].clone();
            self.qargs_idx += 1;
            e
        } else {
            return Err(perror!(self, "too many interpolation '?'"));
        })
    }

    fn parse_nullary_(&mut self, s: &str) -> Result<k::Expr> {
        use Tok::*;

        if let COLON = self.peek_() {
            // inline variable decl, parse type with high precedence.
            self.eat_(COLON)?;
            let ty_ty = self.ctx.mk_ty();
            let ty = self.parse_expr_bp_(u16::MAX, Some(ty_ty))?;
            let v = k::Var::new(k::Symbol::from_str(s), ty);
            self.local.push(v.clone());
            Ok(self.ctx.mk_var(v))
        } else {
            self.expr_of_atom_(s)
        }
    }

    /// Parse an expression.
    ///
    /// `bp` is the current binding power for this Pratt parser.
    fn parse_expr_bp_(&mut self, bp: u16, ty_expected: Option<k::Expr>) -> Result<k::Expr> {
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
                    match self.fixity_(s) {
                        Fixity::Prefix((_, r_bp)) => {
                            let arg = self.parse_expr_bp_(r_bp, None)?;
                            let lhs = self.expr_of_atom_(s)?;
                            self.ctx.mk_app(lhs, arg)?
                        }
                        Fixity::Infix(..) => {
                            return Err(perror!(self, "unexpected infix operator {:?}", s));
                        }
                        Fixity::Postfix(..) => {
                            return Err(perror!(self, "unexpected postfix operator {:?}", s));
                        }
                        Fixity::Binder((_, l2)) => {
                            let local_offset = self.local.len();
                            let ty_expected_vars = self.binder_type_hint_(s)?;
                            self.parse_bnd_vars_(ty_expected_vars.as_ref())?;
                            self.eat_(DOT)?;
                            // TODO: find expected type for body, maybe
                            let body = self.parse_expr_bp_(l2, None)?;
                            let result = self.mk_expr_binder_(s, local_offset, body);
                            self.local.truncate(local_offset);
                            result?
                        }
                        Fixity::Nullary => self.parse_nullary_(s)?,
                    }
                }
                DOLLAR_SYM(s) => self.expr_of_atom_(s)?,
                QUESTION_MARK => self.interpol_expr_()?,
                NUM(s) => {
                    let mut i: i64 = s
                        .parse()
                        .map_err(|e| perror!(self, "cannot parse integer literal: {}", e))?;
                    if i < 0 {
                        // TODO: relative numbers
                        return Err(perror!(self, "cannot parse negative numbers yet"));
                    }
                    let mut t = self
                        .ctx
                        .find_const("Zero")
                        .ok_or_else(|| {
                            perror!(self, "cannot find constant `Zero` to encode number `{}`", i)
                        })?
                        .0
                        .clone();
                    while i > 0 {
                        let b = i % 2 == 1;
                        let f = if b { "Bit1" } else { "Bit0" };
                        let f = self
                            .ctx
                            .find_const(f)
                            .ok_or_else(|| {
                                perror!(
                                    self,
                                    "cannot find constant `{}` to encode number `{}`",
                                    f,
                                    i
                                )
                            })?
                            .0
                            .clone();
                        t = self.ctx.mk_app(f, t).map_err(|e| {
                            perror!(self, "type error when encoding number `{}`: {}", i, e)
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
                            let arg = self.parse_nullary_(s)?;
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
                            return Err(perror!(self, "unexpected prefix symbol {:?}", s))
                        }
                        Fixity::Binder(..) => {
                            return Err(perror!(self, "unexpected binder {:?}", s))
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

    /// Parse an expression, up to EOF.
    pub fn parse_expr(&mut self) -> Result<k::Expr> {
        let e = self.parse_expr_bp_(0, None)?;
        if self.peek_() != Tok::EOF {
            Err(perror!(self, "expected EOF"))
        } else if self.qargs_idx < self.qargs.len() {
            Err(perror!(
                self,
                "expected all {} interpolation arguments to be used, but only {} were",
                self.qargs.len(),
                self.qargs_idx
            ))
        } else {
            Ok(e)
        }
    }
}

/// Parse the string into an expression.
pub fn parse_expr(ctx: &mut Ctx, s: &str) -> Result<k::Expr> {
    let mut p = Parser::new(ctx, s);
    p.parse_expr()
}

/// Parse the string into an expression with a set of parameters.
pub fn parse_expr_with_args(ctx: &mut Ctx, s: &str, qargs: &[k::Expr]) -> Result<k::Expr> {
    let mut p = Parser::new_with_args(ctx, s, qargs);
    p.parse_expr()
}

struct Printer {
    scope: Vec<k::Var>, // variable in scope
}

impl Printer {
    fn new() -> Self {
        Self { scope: vec![] }
    }

    fn pp_var_ty_(&self, v: &k::Var, k: isize, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "({} : ", v.name.name())?;
        self.pp_expr(&v.ty, k, 0, 0, out)?;
        write!(out, ")")
    }

    /// pretty print `e`.
    ///
    /// - `k` is the number of surroundings binders, used to print bound
    ///     variables using on-the-fly conversion to De Bruijn level
    /// - `pl` is the surrounding precedence on the left.
    /// - `pr` is the surrounding precedence on the right.
    fn pp_expr(
        &self,
        e: &k::Expr,
        k: isize,
        pl: u16,
        pr: u16,
        out: &mut fmt::Formatter,
    ) -> fmt::Result {
        use k::ExprView as EV;
        const P_MAX: u16 = u16::MAX;

        match e.view() {
            EV::EKind => write!(out, "kind")?,
            EV::EType => write!(out, "type")?,
            EV::EVar(v) => {
                if self.scope.iter().any(|v2| v == v2) {
                    write!(out, "{}", v.name.name())?;
                } else {
                    self.pp_var_ty_(&v, k, out)?
                }
            }
            EV::EBoundVar(v) => write!(out, "x{}", k - v.idx() as isize - 1)?,
            EV::EConst(c) => match c.fixity() {
                Fixity::Infix(..) | Fixity::Prefix(..) | Fixity::Binder(..) => {
                    // must escape that.
                    write!(out, "${}", c.name.name())?
                }
                _ => write!(out, "{}", c.name.name())?,
            },
            EV::EApp(_, _) => {
                let (f, args) = e.unfold_app();
                let fv = match f.as_const() {
                    Some(fv) => fv,
                    _ => {
                        // prefix. Print sub-members with maximum binding power.
                        if pl > 0 || pr > 0 {
                            return self.pp_expr_paren_(e, k, out);
                        }
                        self.pp_expr(f, k, P_MAX, P_MAX, out)?;
                        for x in &args {
                            write!(out, " ")?;
                            self.pp_expr(x, k, P_MAX, P_MAX, out)?;
                        }
                        return Ok(());
                    }
                };
                let f_name = fv.name.name();
                match fv.fixity() {
                    Fixity::Infix((l, r)) if args.len() >= 2 && !e.ty().is_fun_type() => {
                        let n = args.len();
                        if (pl > 0 && pl >= l) || (pr > 0 && pr >= r) {
                            return self.pp_expr_paren_(e, k, out);
                        }
                        self.pp_expr(&args[n - 2], k, pl, l, out)?;
                        write!(out, " {} ", f_name)?;
                        self.pp_expr(&args[n - 1], k, r, pr, out)?;
                    }
                    Fixity::Binder((_, r))
                        if args.len() > 0
                            && args[args.len() - 1].as_lambda().is_some()
                            && args[0..args.len() - 1].iter().all(|x| x.ty().is_type()) =>
                    {
                        // `binder ty…ty (\x:ty. body)` printed as `binder x:ty. body`
                        let (ty_x, body) = args[args.len() - 1].as_lambda().unwrap();
                        if r > 0 && pr >= r {
                            return self.pp_expr_paren_(e, k, out);
                        }
                        write!(out, "{} x{}:", f_name, k)?;
                        self.pp_expr(ty_x, k, 0, 0, out)?;
                        write!(out, ". ")?;
                        self.pp_expr(body, k + 1, r, pr, out)?;
                    }
                    Fixity::Prefix((_, r)) if args.len() == 1 => {
                        let arg = &args[0];
                        if pr > 0 && pr >= r {
                            return self.pp_expr_paren_(e, k, out);
                        }
                        write!(out, "{} ", f_name)?;
                        self.pp_expr(arg, k, r, pr, out)?;
                    }
                    Fixity::Infix(..)
                    | Fixity::Binder(..)
                    | Fixity::Prefix(..)
                    | Fixity::Postfix(..) => {
                        // default, safe case: print `f` independently,
                        // it'll have `$` as prefix.
                        write!(out, "(")?;
                        self.pp_expr(f, k, P_MAX, P_MAX, out)?;
                        for x in &args {
                            write!(out, " ")?;
                            self.pp_expr(x, k, P_MAX, P_MAX, out)?;
                        }
                        write!(out, ")")?;
                    }
                    Fixity::Nullary => {
                        // prefix
                        if pl > 0 || pr > 0 {
                            return self.pp_expr_paren_(e, k, out);
                        }
                        self.pp_expr(f, k, P_MAX, P_MAX, out)?;
                        for x in &args {
                            write!(out, " ")?;
                            self.pp_expr(x, k, P_MAX, P_MAX, out)?;
                        }
                    }
                }
            }
            EV::ELambda(ty_v, body) => {
                let p_lam = k::FIXITY_LAM.bp().1;
                if (pr > 0 && pl >= p_lam) || (pr > 0 && pr >= p_lam) {
                    return self.pp_expr_paren_(e, k, out);
                }
                write!(out, r#"\x{} : "#, k)?;
                self.pp_expr(&ty_v, k, 0, 0, out)?;
                write!(out, ". ")?;
                // no binding power on the left because of '.'
                self.pp_expr(&body, k + 1, 0, p_lam, out)?;
            }
            EV::EPi(ty_v, body) => {
                let is_arrow = body.is_closed();
                let (mypl, mypr) = if is_arrow {
                    let p = k::FIXITY_ARROW.bp();
                    (p.0, p.1)
                } else {
                    (0, k::FIXITY_PI.bp().1)
                };
                if (pl > 0 && pl >= mypl) || (pr > 0 && pr >= mypr) {
                    return self.pp_expr_paren_(e, k, out);
                }
                if is_arrow {
                    // just print a lambda
                    self.pp_expr(&ty_v, k, pl, mypl, out)?;
                    write!(out, " -> ")?;
                    self.pp_expr(&body, k + 1, mypr, pr, out)?;
                } else {
                    write!(out, r#"pi x{}."#, k)?;
                    self.pp_expr(&body, k + 1, 0, mypr, out)?;
                }
            }
        }
        Ok(())
    }

    /// Same as `pp_expr` but between "()".
    fn pp_expr_paren_(&self, e: &k::Expr, k: isize, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "(")?;
        self.pp_expr(e, k, 0, 0, out)?;
        write!(out, ")")
    }

    fn pp_expr_top(&mut self, e: &k::Expr, out: &mut fmt::Formatter) -> fmt::Result {
        // to print a self-contained expression, we declare all free
        // variables using `with a b:ty1. with c: ty2. <the expr>`.
        let mut fvars: Vec<_> = e.free_vars().collect();

        // group by type first, then name
        fvars.sort_by_key(|v| (v.ty.clone(), v.name.name()));
        fvars.dedup();

        let mut i = 0;
        while i < fvars.len() {
            write!(out, "with")?;

            // gather all the variables with the same type
            let mut j = i + 1;
            while j < fvars.len() {
                if &fvars[i].ty != &fvars[j].ty {
                    break;
                }

                j += 1;
            }

            assert!(fvars[i..j].iter().all(|v2| &v2.ty == &fvars[i].ty));

            for v in &fvars[i..j] {
                write!(out, " {}", v.name.name())?;
            }
            write!(out, ":")?;
            self.pp_expr(&fvars[i].ty, 0, 0, 0, out)?;
            write!(out, ". ")?;

            i = j;
        }

        let n_scope = self.scope.len();
        self.scope.extend(fvars.into_iter().cloned());
        let r = self.pp_expr(e, 0, 0, 0, out);
        self.scope.truncate(n_scope);

        r
    }
}

/// Pretty print this expression according to the existing precedence rules.
pub fn print_expr(e: &k::Expr, out: &mut fmt::Formatter) -> fmt::Result {
    let mut pp = Printer::new();
    pp.pp_expr_top(e, out)
}

#[cfg(test)]
mod test {
    use super::*;

    fn mkctx() -> Result<k::Ctx> {
        let mut ctx = k::Ctx::new();
        {
            // declare a binder
            let ty = parse_expr(&mut ctx, "pi a. (a -> bool) -> a")?;
            ctx.mk_new_const(k::Symbol::from_str("myb"), ty)?;
            ctx.set_fixity("myb", Fixity::Binder((20, 21)))?;
        }
        Ok(ctx)
    }

    #[test]
    fn test_parser_expr() -> Result<()> {
        let pairs = [
            (
                "with a:bool. myb x:bool. x=a",
                "(myb bool (\\x0 : bool. (= bool x0 a)))",
            ),
            (
                r#"with a:bool. $myb bool (\x:bool. x=a)"#,
                "(myb bool (\\x0 : bool. (= bool x0 a)))",
            ),
            (r#"(\x:bool. x= x) "#, "(\\x0 : bool. (= bool x0 x0))"),
            (
                r#"(\x y:bool. x= y) "#,
                "(\\x0 : bool. (\\x1 : bool. (= bool x0 x1)))",
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
            let mut ctx = mkctx()?;
            let r = parse_expr(&mut ctx, x)
                .map_err(|e| e.with_source(Error::new_string(format!("parsing {:?}", x))))?;
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
            &'static dyn Fn(&mut Ctx) -> Result<Vec<k::Expr>>,
        )> = vec![
            (
                "with a:?. myb x:?. x=a",
                "(myb bool (\\x0 : bool. (= bool x0 a)))",
                &|ctx: &mut Ctx| Ok(vec![ctx.mk_bool(), ctx.mk_bool()]),
            ),
            (
                r#"(\x:bool. ?= x) "#,
                "(\\x0 : bool. (= bool x0 x0))",
                &|ctx: &mut Ctx| {
                    let b = ctx.mk_bool();
                    Ok(vec![ctx.mk_var_str("x", b)])
                },
            ),
        ];

        for (x, y, f) in &cases {
            let mut ctx = mkctx()?;
            let qargs: Vec<k::Expr> = f(&mut ctx)?;
            let r = parse_expr_with_args(&mut ctx, x, &qargs)
                .map_err(|e| e.with_source(Error::new_string(format!("parsing {:?}", x))))?;
            let r2 = format!("{:?}", r);
            assert_eq!(&r2, *y);
        }
        Ok(())
    }

    #[test]
    fn test_parse_with_prelude() -> Result<()> {
        let pairs = [
            (
                "forall x:bool. F ==> ~ ~ x",
                r#"(forall bool (\x0 : bool. (==> F (~ (~ x0)))))"#,
            ),
            (
                "with a: bool. a ==> T ==> (a ==> T) ==> T",
                "(==> a (==> T (==> (==> a T) T)))",
            ),
            (
                r#" with a: (bool).  a /\ T ==>  ~ ~ T"#,
                r#"(==> (/\ a T) (~ (~ T)))"#,
            ),
        ];

        for (x, y) in &pairs {
            let mut ctx = Ctx::new();
            crate::meta::load_prelude_hol(&mut ctx)?;
            let r = parse_expr(&mut ctx, x)
                .map_err(|e| e.with_source(Error::new_string(format!("parsing {:?}", x))))?;
            let r2 = format!("{:?}", r);
            assert_eq!(&r2, *y);
        }
        Ok(())
    }

    #[test]
    fn test_printer() -> Result<()> {
        let pairs = [
            ("with a: type. (a -> a) -> a", "with a:type. (a -> a) -> a"),
            ("$~", "$~"),
            (
                // test that /\ is printed as right-assoc
                r#"with a b : bool. a /\ (a/\ T) /\ b"#,
                r#"with a b:bool. a /\ (a /\ T) /\ b"#,
            ),
            (
                r#"with a b : bool. (a /\ (a/\ T)) /\ b"#,
                r#"with a b:bool. (a /\ a /\ T) /\ b"#,
            ),
            (
                r#"with a b : bool. (a ==> T /\ (T ==> a ==> (b/\ ~T))) /\ b"#,
                r#"with a b:bool. (a ==> T /\ (T ==> a ==> b /\ ~ T)) /\ b"#,
            ),
            (
                "forall x:bool. F ==> ~ ~ x",
                r#"forall x0:bool. F ==> ~ ~ x0"#,
            ),
            (
                "(forall x:bool. x ==> x) ==> (forall y:bool. T = F ==> ~ ~ y)",
                r#"(forall x0:bool. x0 ==> x0) ==> forall x0:bool. T = F ==> ~ ~ x0"#,
            ),
        ];

        for (x, s) in &pairs {
            let mut ctx = Ctx::new();
            crate::meta::load_prelude_hol(&mut ctx)?;
            let r = parse_expr(&mut ctx, x)
                .map_err(|e| e.with_source(Error::new_string(format!("parsing {:?}", x))))?;
            // use pretty printer
            let r2 = format!("{}", r);
            assert_eq!(&r2, *s, "left: actual, right: expected");
        }
        Ok(())
    }

    #[test]
    fn test_infix_pp_eq() -> Result<()> {
        let mut ctx = Ctx::new();
        let a = parse_expr(&mut ctx, "x:bool")?;
        let b = parse_expr(&mut ctx, "y:bool")?;
        let e = ctx.mk_eq_app(a, b)?;
        let s = format!("{}", e);
        assert_eq!(s, "with x y:bool. x = y");
        let e1 = e.as_app().ok_or_else(|| Error::new("is not app"))?.0;
        let s1 = format!("{}", e1);
        assert_eq!(s1, "with x:bool. ($= bool x)");
        Ok(())
    }
}
