//! # Expression parser
//!
//! This parses an expression from a string directly, without intermediate AST.
//! New constants can be declared with infix/prefix fixity.
//!
//! We follow https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
//! quite closely :-)

use {
    super::fixity,
    crate::{
        errorstr, kernel as k,
        syntax::Fixity,
        syntax::{lexer::Position, Lexer, Tok},
        Ctx, Error, Result,
    },
    smallvec::smallvec,
};

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
    pub fn loc(&self) -> Position {
        self.lexer.cur_pos()
    }

    #[inline]
    fn fixity_(&self, s: &str) -> Fixity {
        match s {
            "=" => fixity::FIXITY_EQ,
            "->" => fixity::FIXITY_ARROW,
            "with" => Fixity::Binder((1, 2)),
            "\\" => fixity::FIXITY_LAM,
            "pi" => fixity::FIXITY_PI,
            _ => {
                // lookup in context
                if let Some(f) = self.ctx.find_const(s).and_then(|c| self.ctx.find_fixity(c)) {
                    *f
                } else {
                    Fixity::Nullary
                }
            }
        }
    }

    /// Parse a symbol and return it.
    fn parse_sym_(&mut self) -> Result<&'a str> {
        use Tok::*;
        match self.lexer.consume_cur() {
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
            match self.lexer.cur() {
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
                    self.lexer.next();
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

        let ty_parsed = if let COLON = self.lexer.cur() {
            self.lexer.eat(COLON, "type signature")?;
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
            match self.lexer.cur() {
                LPAREN => {
                    self.lexer.next();
                    n += self.parse_bnd_var_list_(ty_expected)?;
                    self.lexer.eat(RPAREN, "after list of variables")?;
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
            "=" => {
                let ty = self.parse_expr()?;
                self.ctx.mk_eq(ty)
            }
            "bool" => self.ctx.mk_bool(),
            "type" => self.ctx.mk_ty(),
            _ => {
                // parse constant, then as many arguments as needed
                let c = self
                    .ctx
                    .find_const(s)
                    .ok_or_else(|| perror!(self, "unknown constant {:?}", s))?
                    .clone();
                let mut args = smallvec![];
                for _ in 0..c.arity {
                    args.push(self.parse_expr()?);
                }
                self.ctx.mk_const(c, args)?
            }
        })
    }

    /// Apply an infix token.
    fn apply_expr_infix_(&mut self, s: &str, e1: k::Expr, e2: k::Expr) -> Result<k::Expr> {
        match s {
            "=" => self.ctx.mk_eq_app(e1, e2),
            "->" => self.ctx.mk_arrow(e1, e2),
            _ => {
                if let Some(c) = self.ctx.find_const(s) {
                    // FIXME: type inference to fill vars, if any
                    if c.arity > 0 {
                        return Err(errorstr!(
                            "cannot use constant `{}` as infix",
                            c.name.name()
                        ));
                    }
                    let c = c.clone();
                    let c = self.ctx.mk_const(c, smallvec![])?;
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
            _ => {
                let c = self
                    .ctx
                    .find_const(b)
                    .cloned()
                    .ok_or_else(|| errorstr!("`{}` is not a constant", b))?;
                if let Some(Fixity::Binder(..)) = self.ctx.find_fixity(&c) {
                    // turn `b x:ty. p` into `b ty (λx:ty. p)`
                    // FIXME: type inference
                    if c.arity != 1 {
                        return Err(errorstr!(
                            "cannot use `{}` as binder, it needs to have exactly 1 type argument",
                            c.name.name()
                        ));
                    }
                    let mut t = body;
                    for v in vars {
                        let ty = v.ty().clone();
                        let c_expr = self.ctx.mk_const(c.clone(), smallvec![ty])?;
                        let lam = self.ctx.mk_lambda(v.clone(), t)?;
                        t = self.ctx.mk_app(c_expr, lam)?;
                    }
                    t
                } else {
                    return Err(perror!(
                        self,
                        "constant `{}` is not a binder",
                        c.name.name()
                    ));
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

        if let COLON = self.lexer.cur() {
            // inline variable decl, parse type with high precedence.
            self.lexer.next();
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
            let t = self.lexer.consume_cur();
            match t {
                ERROR(c) => {
                    return Err(perror!(
                        self,
                        "invalid char {:?} (utf8: {:?})",
                        c,
                        std::str::from_utf8(&[c])
                    ));
                }
                LET => {
                    // parse `let x = y in e`.
                    let v = self.parse_sym_()?;
                    self.lexer.eat(SYM("="), "after let-bound variable")?;
                    let e = self.parse_expr_bp_(0, None)?;
                    self.lexer.eat(IN, "after let binding")?;
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
                            self.lexer.eat(DOT, "before binder's body")?;
                            // TODO: find expected type for body, maybe
                            let body = self.parse_expr_bp_(l2, None)?;
                            let result = self.mk_expr_binder_(s, local_offset, body);
                            self.local.truncate(local_offset);
                            result?
                        }
                        Fixity::Nullary => self.parse_nullary_(s)?,
                    }
                }
                AT_SYM(s) => self.expr_of_atom_(s)?,
                QUESTION_MARK => self.interpol_expr_()?,
                WILDCARD | QUESTION_MARK_STR(..) => {
                    return Err(perror!(self, "invalid token in expression: {:?}", t))
                }
                NUM(s) => {
                    let mut i: i64 = s
                        .parse()
                        .map_err(|e| perror!(self, "cannot parse integer literal: {}", e))?;
                    if i < 0 {
                        // TODO: relative numbers
                        return Err(perror!(self, "cannot parse negative numbers yet"));
                    }
                    let zero = self.ctx.find_const("Zero").cloned().ok_or_else(|| {
                        perror!(self, "cannot find constant `Zero` to encode number `{}`", i)
                    })?;
                    if zero.arity > 0 {
                        return Err(Error::new("Zero should not be polymorphic"));
                    }
                    let mut t = self.ctx.mk_const(zero, smallvec![])?;
                    while i > 0 {
                        let b = i % 2 == 1;
                        let name = if b { "Bit1" } else { "Bit0" };
                        let f = self
                            .ctx
                            .find_const(name)
                            .ok_or_else(|| {
                                perror!(
                                    self,
                                    "cannot find constant `{}` to encode number `{}`",
                                    name,
                                    i
                                )
                            })?
                            .clone();
                        if f.arity > 0 {
                            return Err(errorstr!("`{}` should not be polymorphic", name));
                        }
                        let f = self.ctx.mk_const(f, smallvec![])?;
                        t = self.ctx.mk_app(f, t).map_err(|e| {
                            perror!(self, "type error when encoding number `{}`: {}", i, e)
                        })?;
                        i = i / 2;
                    }
                    t
                }
                LPAREN => {
                    let t = self.parse_expr_bp_(0, ty_expected)?;
                    self.lexer.eat(RPAREN, "after '('-prefixed expression")?;
                    t
                }
                RPAREN | DOT | EOF | COLON | IN | QUOTED_STR(..) => {
                    return Err(perror!(
                        self,
                        "unexpected token {:?} at {}",
                        t,
                        self.lexer.cur_pos()
                    ))
                }
            }
        };

        loop {
            let (op, l_bp, r_bp) = match self.lexer.cur() {
                EOF => return Ok(lhs),
                RPAREN | WILDCARD | COLON | DOT | IN | LET | QUOTED_STR(..) => break,
                LPAREN => {
                    // TODO: set ty_expected to `lhs`'s first argument's type.
                    self.lexer.next();
                    let t = self.parse_expr_bp_(0, None)?; // maximum binding power
                    self.lexer.eat(RPAREN, "after '('-prefixed expression")?;
                    lhs = self.ctx.mk_app(lhs, t)?;
                    continue;
                }
                AT_SYM(s) => {
                    let arg = self.expr_of_atom_(s)?;

                    self.lexer.next();
                    // simple application
                    lhs = self.ctx.mk_app(lhs, arg)?;
                    continue;
                }
                QUESTION_MARK => {
                    self.lexer.next();
                    let arg = self.interpol_expr_()?;

                    // simple application
                    lhs = self.ctx.mk_app(lhs, arg)?;
                    continue;
                }
                QUESTION_MARK_STR(..) => return Err(perror!(self, "cannot handle meta-variable")),
                NUM(_s) => return Err(perror!(self, "handle numbers")),
                SYM(s) => {
                    match self.fixity_(s) {
                        Fixity::Infix((l1, l2)) => (s, l1, l2),
                        Fixity::Nullary => {
                            // simple application
                            let arg = self.parse_nullary_(s)?;
                            lhs = self.ctx.mk_app(lhs, arg)?;
                            self.lexer.next();
                            continue;
                        }
                        Fixity::Postfix((l_bp, _)) => {
                            if l_bp < bp {
                                break;
                            }
                            self.lexer.next();

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
                ERROR(c) => {
                    return Err(perror!(
                        self,
                        "invalid char {:?} (utf8: {:?})",
                        c,
                        std::str::from_utf8(&[c])
                    ));
                }
            };

            if l_bp < bp {
                break; // binding left
            }

            self.lexer.next();

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
        if self.lexer.cur() != Tok::EOF {
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::{kernel as k, Ctx, Error, Result};

    fn mkctx() -> Result<k::Ctx> {
        let mut ctx = k::Ctx::new();
        {
            // declare a binder
            let ty = parse_expr(&mut ctx, "pi a. (a -> bool) -> a")?;
            ctx.mk_new_const(k::Symbol::from_str("myb"), ty, None)?;
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
                r#"with a:bool. @myb bool (\x:bool. x=a)"#,
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
                r#"(\x:bool. ? = x) "#,
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
    fn test_fvars() -> Result<()> {
        let mut ctx = Ctx::new();
        let s = "with b:type. with t u:(a : type). with f g:(a : type) -> b. (f t) = (g u)";
        let e = parse_expr(&mut ctx, s)?;
        let mut fvars: Vec<_> = e.free_vars().map(|v| v.name.name()).collect();
        fvars.sort();

        assert_eq!(fvars, vec!["a", "b", "f", "g", "t", "u",]);
        Ok(())
    }
}
