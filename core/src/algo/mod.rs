//! Algorithms that are outside the kernel of trust itself.

use crate::{kernel_of_trust as k, *};

pub mod cc;
pub mod rw;
pub mod unif;

pub use cc::{prove_cc, CC};
pub use rw::{
    rewrite_bottom_up, thm_rw_concl, RewriteCombine, RewriteRule, RewriteRuleSet, Rewriter,
    RewriterBetaConv,
};
pub use unif::{match_, unify, RenamingData, UnifySubst};

/// Result of the definition of a new polymorphic constant.
#[derive(Debug, Clone)]
pub struct NewPolyDef {
    /// Constant being defined
    pub c: Expr,
    /// Theorem defining `c` (as `c = …`)
    pub thm: Thm,
    /// Type variables, in the order they are abstracted on
    pub ty_vars: Vec<Var>,
    /// `c` applied to `ty_vars`
    pub c_applied: Expr,
    /// `thm_c` applied to `ty_vars`
    pub thm_applied: Thm,
}

/// Make a definition from a polymorphic term, by closing it first.
///
/// `ExprManager::thm_new_basic_definition` requires the term to be closed,
/// so we must gather type variables and close over them.
///
/// Returns a tuple `(thm_def, c, vars)` where `thm_def` is the theorem
/// defining the new constant `c`, and `vars` is the set of type variables
/// closed over.
pub fn thm_new_poly_definition(ctx: &mut Ctx, c: &str, rhs: Expr) -> Result<NewPolyDef> {
    let mut vars_ty_rhs: Vec<Var> = rhs.ty().free_vars().cloned().collect();
    //eprintln!("vars_of_ty({:?}) = {:?}", &rhs, &vars_ty_rhs);
    vars_ty_rhs.sort_unstable();
    vars_ty_rhs.dedup();

    if vars_ty_rhs.iter().any(|v| !v.ty.is_type()) {
        return Err(Error::new_string(format!(
            "thm_new_poly_definition: cannot make a polymorphic \
        definition for {}\nusing rhs = {:?}\nrhs contains non-type free variables",
            c, rhs
        )));
    }

    let ty_closed = ctx.mk_pi_l(&vars_ty_rhs, rhs.ty().clone())?;
    let eqn = {
        let rhs_closed = ctx.mk_lambda_l(&vars_ty_rhs, rhs.clone())?;
        let v = ctx.mk_var_str(c, ty_closed);
        ctx.mk_eq_app(v, rhs_closed)?
    };
    let (thm, c) = ctx.thm_new_basic_definition(eqn)?;

    // type variables as expressions
    let e_vars: Vec<_> = vars_ty_rhs.iter().cloned().map(|v| ctx.mk_var(v)).collect();

    let c_applied = ctx.mk_app_l(c.clone(), &e_vars)?;

    // apply `thm` to the type variables
    let thm_applied = {
        let mut thm = thm.clone();
        for v in e_vars.iter() {
            thm = ctx.thm_congr_ty(thm, &v)?;
            // now replace `(λa:type. …) v` with its beta reduced version
            let thm_rhs = thm
                .concl()
                .unfold_eq()
                .ok_or_else(|| Error::new("rhs must be an equality"))?
                .1;
            let thm_beta = ctx.thm_beta_conv(thm_rhs)?;
            thm = ctx.thm_trans(thm, thm_beta)?;
        }
        thm
    };

    Ok(NewPolyDef {
        thm,
        c,
        ty_vars: vars_ty_rhs,
        thm_applied,
        c_applied,
    })
}

/// Prove symmetry of equality.
///
/// Goes from `A |- t=u` to `A |- u=t`.
pub fn thm_sym(em: &mut Ctx, th: Thm) -> Result<Thm> {
    // start with `F |- t=u`.
    // now by left-congruence with `refl(=)`, `F |- ((=) t) = ((=) u)`.
    // by right-congruence with `refl(t)`, `F |- (((=) t) t) = (((=) u) t)`.
    // in other words, `F |- (t=t)=(u=t)`.
    // Just do bool_eq_elim with `|- t=t` (refl(t)) and we're done.
    let (t, u) = th
        .concl()
        .unfold_eq()
        .ok_or_else(|| Error::new("sym: expect an equation"))?;
    let refl_t = em.thm_refl(t.clone());
    let th_tequ_eq_ueqt = {
        let eq = em.mk_eq();
        let eq_u = em.mk_app(eq, u.ty().clone())?;
        let th_r = em.thm_refl(eq_u);
        let th_c_r = em.thm_congr(th_r, th)?;
        em.thm_congr(th_c_r, refl_t.clone())?
    };
    em.thm_bool_eq(refl_t, th_tequ_eq_ueqt)
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
        thm_sym(ctx, hyp)?
    };

    let th2 = {
        let eq = ctx.mk_eq_app(u.clone(), t.clone())?;
        let hyp = ctx.thm_assume(eq)?;
        thm_sym(ctx, hyp)?
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
        let th2 = thm_sym(&mut ctx, th).unwrap();
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
    fn test_rw_beta_conv() -> Result<()> {
        let mut ctx = Ctx::new();
        let e = syntax::parse_expr(
            &mut ctx,
            r#"with (tau:type) (g1 h:tau->tau) (a:tau). let f2 = \(f:tau->tau) (x:tau). f (f x) in h (f2 g1 a) = f2 (f2 g1) a"#,
        )?;

        let th1 = ctx.thm_assume(e)?;
        let th2 = thm_rw_concl(&mut ctx, th1, &RewriterBetaConv)?;
        let exp = syntax::parse_expr(
            &mut ctx,
            r#"with (tau:type) (h g1:tau->tau) (a:tau). h (g1 (g1 a)) = (g1 (g1 (g1 (g1 a))))"#,
        )?;
        assert_eq!(exp, th2.concl().clone());
        Ok(())
    }
}
