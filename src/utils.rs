//! Utils that are outside the kernel of trust itself.

use crate::*;

/// Make a definition from a polymorphic term, by closing it first.
///
/// `ExprManager::thm_new_basic_definition` requires the term to be closed,
/// so we must gather type variables and close over them.
///
/// Returns a tuple `(thm_def, c, vars)` where `thm_def` is the theorem
/// defining the new constant `c`, and `vars` is the set of type variables
/// closed over.
pub fn thm_new_poly_definition(
    em: &mut ExprManager,
    c: &str,
    rhs: Expr,
) -> Result<(Thm, Expr, Vec<Var>), String> {
    let mut vars_ty_rhs: Vec<Var> = rhs.ty().free_vars().cloned().collect();
    vars_ty_rhs.sort_unstable();
    vars_ty_rhs.dedup();

    if vars_ty_rhs.iter().any(|v| !v.ty.is_type()) {
        return Err(format!("thm_new_poly_definition: cannot make a polymorphic \
        definition for {}\nusing rhs = {:?}\nrhs contains non-type free variables",
        c, rhs));
    }

    let ty_closed = em.mk_pi_l(vars_ty_rhs.iter().cloned(), rhs.ty().clone());
    let eqn = {
        let rhs_closed =
            em.mk_lambda_l(vars_ty_rhs.iter().cloned(), rhs.clone());
        let v = em.mk_var_str(c, ty_closed);
        em.mk_eq_app(v, rhs_closed)
    };
    let (thm, c) = em.thm_new_basic_definition(eqn)?;
    Ok((thm, c, vars_ty_rhs))
}
