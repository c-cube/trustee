//! Pretty-printing terms.

use {
    crate::{
        kernel::{Expr, ExprView, FixityTbl, Var},
        syntax::{fixity, Fixity},
    },
    std::fmt,
};

struct Printer<'a> {
    fixities: &'a FixityTbl,
    scope: Vec<Var>, // variable in scope
}

/// Pretty print this expression according to the existing precedence rules.
pub fn print_expr(ftbl: &FixityTbl, e: &Expr, out: &mut fmt::Formatter) -> fmt::Result {
    let mut pp = Printer::new(ftbl);
    pp.pp_expr_top(e, out)
}

impl<'a> Printer<'a> {
    fn new(fixities: &'a FixityTbl) -> Self {
        Self {
            scope: vec![],
            fixities,
        }
    }

    fn pp_var_ty_(&self, v: &Var, k: isize, out: &mut fmt::Formatter) -> fmt::Result {
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
        e: &Expr,
        k: isize,
        pl: u16,
        pr: u16,
        out: &mut fmt::Formatter,
    ) -> fmt::Result {
        use ExprView as EV;
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
            EV::EConst(c, _args) => {
                let f = self
                    .fixities
                    .find_fixity(c)
                    .cloned()
                    .unwrap_or(Fixity::Nullary);
                match f {
                    Fixity::Infix(..) | Fixity::Prefix(..) | Fixity::Binder(..) => {
                        // must escape that.
                        write!(out, "@{}", c.name.name())?
                    }
                    _ => write!(out, "{}", c.name.name())?,
                }
            }
            EV::EApp(_, _) => {
                let (f, args) = e.unfold_app();
                let fv = match f.as_const() {
                    Some((fv, _)) => fv,
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
                let fv_fixity = self
                    .fixities
                    .find_fixity(&fv)
                    .cloned()
                    .unwrap_or(Fixity::Nullary);
                match fv_fixity {
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
                        // it'll have `@` as prefix.
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
                let p_lam = fixity::FIXITY_LAM.bp().1;
                if (pr > 0 && pl >= p_lam) || (pr > 0 && pr >= p_lam) {
                    return self.pp_expr_paren_(e, k, out);
                }
                write!(out, r#"\x{} : "#, k)?;
                self.pp_expr(&ty_v, k, 0, 0, out)?;
                write!(out, ". ")?;
                // no binding power on the left because of '.'
                self.pp_expr(&body, k + 1, 0, p_lam, out)?;
            }
            EV::EArrow(a, b) => {
                let (mypl, mypr) = {
                    let p = fixity::FIXITY_ARROW.bp();
                    (p.0, p.1)
                };
                if (pl > 0 && pl >= mypl) || (pr > 0 && pr >= mypr) {
                    return self.pp_expr_paren_(e, k, out);
                }
                // just print an arrow
                self.pp_expr(&a, k, pl, mypl, out)?;
                write!(out, " -> ")?;
                self.pp_expr(&b, k + 1, mypr, pr, out)?;
            }
        }
        Ok(())
    }

    /// Same as `pp_expr` but between "()".
    fn pp_expr_paren_(&self, e: &Expr, k: isize, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "(")?;
        self.pp_expr(e, k, 0, 0, out)?;
        write!(out, ")")
    }

    fn pp_expr_top(&mut self, e: &Expr, out: &mut fmt::Formatter) -> fmt::Result {
        // to print a self-contained expression, we declare all free
        // variables using `with a b:ty1. with c: ty2. <the expr>`.
        let mut fvars: Vec<_> = e.free_vars().collect();

        // put type variables first.
        fvars.sort_by_key(|v| {
            let isty = 1 - ((v.ty.is_type() || v.ty.is_kind()) as u8);
            (isty, v.ty.clone(), v.name.name())
        });
        fvars.dedup();

        let n_scope = self.scope.len(); // save `scope`

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
                self.scope.push((*v).clone());
            }
            write!(out, ":")?;
            self.pp_expr(&fvars[i].ty, 0, 0, 0, out)?;
            write!(out, ". ")?;

            i = j;
        }

        let r = self.pp_expr(e, 0, 0, 0, out);
        self.scope.truncate(n_scope);

        r
    }
}

#[cfg(test)]
mod test {
    use super::super::parse_expr;
    use crate::{Ctx, Error, Result};

    #[test]
    fn test_printer() -> Result<()> {
        let pairs = [
            ("with a: type. (a -> a) -> a", "with a:type. (a -> a) -> a"),
            ("@~", "@~"),
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
            (
                "with (a b:type) (f g:a->b). f = g",
                r#"with a b:type. with f g:a -> b. f = g"#,
            ),
        ];

        for (x, s) in &pairs {
            let mut ctx = Ctx::new();
            crate::meta::load_prelude_hol(&mut ctx)?;
            let r = parse_expr(&mut ctx, x)
                .map_err(|e| e.with_source(Error::new_string(format!("parsing {:?}", x))))?;
            // use pretty printer
            let r2 = format!("{:?}", r);
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
        let s = format!("{:?}", e);
        assert_eq!(s, "with x y:bool. x = y");
        let e1 = e.as_app().ok_or_else(|| Error::new("is not app"))?.0;
        let s1 = format!("{:?}", e1);
        assert_eq!(s1, "with x:bool. (@= bool x)");
        Ok(())
    }
}
