//! Algorithms that are outside the kernel of trust itself.

use crate::{kernel as k, *};

pub mod ac_rw;
pub mod cc;
pub mod conv;
pub mod kbo;
pub mod pattern;
pub mod rw;
pub mod rw_rule;
pub mod unif;

pub use ac_rw::{ACConv, ACConvList};
pub use cc::{prove_cc, CC};
pub use conv::{thm_conv_concl, BetaReduce, BetaReduceRepeat, Converter};
use k::expr::Vars;
use k::Const;
pub use pattern::{Pattern, PatternIdx, PatternSubst, PatternView};
pub use rw::rewrite_bottom_up;
pub use rw_rule::{RewriteRule, RewriteRuleSet};
pub use unif::{match_, unify, RenamingData, UnifySubst};

/// Result of the definition of a new polymorphic constant.
#[derive(Debug, Clone)]
pub struct NewPolyDef {
    /// Constant being defined
    pub c: Const,
    /// Theorem defining `c` (as `|- c = rhs`)
    pub thm: Thm,
    /// Type variables, in the order they are abstracted on
    pub ty_vars: Vars,
    /// `c` applied to `ty_vars`
    pub c_applied: Expr,
}

/// Make a definition from a polymorphic term.
///
/// `ExprManager::thm_new_basic_definition` requires the term to be closed,
/// so we must gather type variables and close over them.
///
/// Returns a tuple `(thm_def, c, vars)` where `thm_def` is the theorem
/// defining the new constant `c`, and `vars` is the set of type variables
/// closed over.
pub fn thm_new_poly_definition(ctx: &mut Ctx, c: &str, rhs: Expr) -> Result<NewPolyDef> {
    /*
    let mut vars_ty_rhs: Vec<Var> = rhs.ty().free_vars().cloned().collect();
    //eprintln!("vars_of_ty({:?}) = {:?}", &rhs, &vars_ty_rhs);
    vars_ty_rhs.sort_unstable();
    vars_ty_rhs.dedup();
    */

    if rhs.ty().free_vars().any(|v| !v.ty.is_type()) {
        return Err(errorstr!(
            "thm_new_poly_definition: cannot make a polymorphic \
        definition for {}\nusing rhs = {:?}\nrhs contains non-type free variables",
            c,
            rhs
        ));
    }

    let eqn = {
        let v = ctx.mk_var_str(c, rhs.ty().clone());
        ctx.mk_eq_app(v, rhs)?
    };
    let (thm, c, ty_vars) = ctx.thm_new_basic_definition(eqn)?;

    let c_applied = {
        let ty_vars_as_exprs: ConstArgs = ty_vars.iter().map(|v| ctx.mk_var(v.clone())).collect();
        ctx.mk_const(c.clone(), ty_vars_as_exprs)?
    };

    Ok(NewPolyDef {
        thm,
        c,
        ty_vars,
        c_applied,
    })
}

/* TODO?
/// Prove modus ponens, assuming `==>` and `def_imply` are in the context.
pub fn thm_mp(ctx: &mut Ctx, th1: Thm, th2: Thm) -> Result<Thm> {
    todo!()
}
*/

/// Prove symmetry of equality as an equation.
///
/// Goes from `t=u` to `|- (t=u) = (u=t)`.
pub fn thm_sym_conv(ctx: &mut Ctx, e: Expr) -> Result<Thm> {
    // start with `t=u |- t=u`.
    // apply thm_sym to get `t=u |- u=t`.
    let (t, u) = e
        .unfold_eq()
        .ok_or_else(|| Error::new("sym: expect an equation"))?;
    let th1 = {
        let hyp = ctx.thm_assume(e.clone())?;
        ctx.thm_sym(hyp)?
    };

    let th2 = {
        let eq = ctx.mk_eq_app(u.clone(), t.clone())?;
        let hyp = ctx.thm_assume(eq)?;
        ctx.thm_sym(hyp)?
    };

    ctx.thm_bool_eq_intro(th1, th2)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_sym() {
        let mut ctx = Ctx::new();
        let bool = ctx.mk_bool();
        let x = ctx.mk_var_str("x", bool.clone());
        let y = ctx.mk_var_str("y", bool.clone());
        let x_eq_y = ctx.mk_eq_app(x.clone(), y.clone()).unwrap();
        let y_eq_x = ctx.mk_eq_app(y.clone(), x.clone()).unwrap();
        let th = ctx.thm_assume(x_eq_y).unwrap();
        println!("th: {:?}", th);
        let th2 = ctx.thm_sym(th).unwrap();
        assert_eq!(th2.concl(), &y_eq_x);
    }

    #[test]
    fn test_sym_conv() {
        let mut ctx = Ctx::new();
        let bool = ctx.mk_bool();
        let x = ctx.mk_var_str("x", bool.clone());
        let y = ctx.mk_var_str("y", bool.clone());
        let x_eq_y = ctx.mk_eq_app(x.clone(), y.clone()).unwrap();
        let y_eq_x = ctx.mk_eq_app(y.clone(), x.clone()).unwrap();
        let eq_b = ctx.mk_eq_app(x_eq_y.clone(), y_eq_x.clone()).unwrap();
        let th = thm_sym_conv(&mut ctx, x_eq_y.clone()).unwrap();
        assert_eq!(th.concl(), &eq_b);
    }

    #[test]
    fn test_beta_conv_repeat() -> Result<()> {
        let mut ctx = Ctx::new();
        let e = syntax::parse_expr(
            &mut ctx,
            r#"with (tau:type) (p:tau->tau->bool) (h:tau->tau) (a:tau).
            let f1 = \(x:tau). h x in
            let f2 = \(x:tau). f1 x in
            let f3 = \(x:tau). f2 x in
            p (h (f3 a)) (f3 a)"#,
        )?;

        let th1 = ctx.thm_assume(e.clone())?;
        let th2 = conv::thm_conv_concl(
            &mut ctx,
            th1,
            &conv::Congr(&conv::BetaReduceRepeat, &conv::BetaReduceRepeat),
        )?;
        let exp = syntax::parse_expr(
            &mut ctx,
            r#"with (tau:type) (p:tau->tau->bool) (h:tau->tau) (a:tau).
            let f1 = \(x:tau). h x in
            let f2 = \(x:tau). f1 x in
            let f3 = \(x:tau). f2 x in
            p (h (f3 a)) (h a)"#,
        )?;
        assert_eq!(exp, th2.concl().clone(), "\n\ninitial: {:?}", e);
        Ok(())
    }

    #[test]
    fn test_rw_beta_conv() -> Result<()> {
        let mut ctx = Ctx::new();
        let e = syntax::parse_expr(
            &mut ctx,
            r#"with (tau:type) (g1 h:tau->tau) (a:tau).
            let f2 = \(f:tau->tau) (x:tau). f (f x) in
            h (f2 g1 a) = f2 (f2 g1) a"#,
        )?;
        println!("e: {:?}", e);

        let th1 = ctx.thm_assume(e)?;
        let rw = rw::BottomUpRwConv(&conv::BetaReduce);
        let th2 = conv::thm_conv_concl(&mut ctx, th1, &rw)?;
        let exp = syntax::parse_expr(
            &mut ctx,
            r#"with (tau:type) (h g1:tau->tau) (a:tau). h (g1 (g1 a)) = (g1 (g1 (g1 (g1 a))))"#,
        )?;
        assert_eq!(exp, th2.concl().clone());
        Ok(())
    }
}
