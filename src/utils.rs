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

// TODO: use binary search?
/// A substitution obtained by unification.
pub struct UnifySubst<'a>(Vec<(&'a Var, &'a Expr)>);

impl<'a> UnifySubst<'a> {
    /// Find a variable `v` in this substitution.
    pub fn find(&self, v: &'a Var) -> Option<&'a Expr> {
        match self.0.binary_search_by_key(&v, |pair| pair.0) {
            Ok(i) => Some(&self.0[i].1),
            Err(_) => None,
        }
    }

    /// Combination of `find` and `deref`.
    pub fn find_rec(&self, v: &'a Var) -> Option<&'a Expr> {
        match self.find(v) {
            None => None,
            Some(e) => Some(self.deref(e)),
        }
    }

    /// if `e` is a bound variable, follow the binding, recursively.
    pub fn deref(&self, e: &'a Expr) -> &'a Expr {
        match e.view() {
            EVar(v) => match self.find(v) {
                None => e,
                Some(u) => self.deref(u),
            },
            _ => e,
        }
    }

    fn add_(&mut self, v: &'a Var, e: &'a Expr) {
        debug_assert!(self.find(v).is_none());
        self.0.push((v, e));
        // the implementation is pattern-defeating quicksort, which is linear
        // on already sorted slices of input. I therefore expect that this
        // should be linear.
        self.0.sort_unstable();
    }
}

struct UnifySt<'a> {
    solved: fnv::FnvHashSet<(&'a Expr, &'a Expr)>,
    subst: UnifySubst<'a>,
    to_solve: Vec<(&'a Expr, &'a Expr)>,
}

impl<'a> UnifySt<'a> {
    fn new() -> Self {
        UnifySt {
            solved: fnv::new_set_with_cap(16),
            subst: UnifySubst(Vec::with_capacity(16)),
            to_solve: Vec::with_capacity(16),
        }
    }

    // make sure `e1 = e2` holds
    fn add_pair(&mut self, e1: &'a Expr, e2: &'a Expr) {
        if e1 != e2 && !self.solved.contains(&(e1, e2)) {
            self.to_solve.push((e1, e2))
        }
    }

    /// Does `v` occur in `e`?
    fn occur_check(&self, v: &'a Var, e: &'a Expr) -> bool {
        let e = self.subst.deref(e);
        match e.ty_opt() {
            Some(ty) if self.occur_check(v, ty) => return true,
            _ => (),
        }
        match e.view() {
            EType | EKind | EConst(..) => false,
            EVar(v2) => v == v2,
            EBoundVar(_) => false,
            EApp(f, arg) => self.occur_check(v, f) || self.occur_check(v, arg),
            ELambda(_, body) | EPi(_, body) => self.occur_check(v, body),
        }
    }

    // solve and consume
    fn solve(mut self) -> Option<UnifySubst<'a>> {
        let sat = loop {
            let (e1, e2) = match self.to_solve.pop() {
                None => break true, // done
                Some(tup) => tup,
            };
            let e1 = self.subst.deref(e1);
            let e2 = self.subst.deref(e2);

            // trivial cases: syntactic eq, or already cached
            if e1 == e2 || self.solved.contains(&(e1, e2)) {
                continue;
            }

            // assume we solved this pair
            self.solved.insert((e1, e2));

            // unify types
            match (e1.ty_opt(), e2.ty_opt()) {
                (Some(ty1), Some(ty2)) if ty1 == ty2 => (),
                (Some(ty1), Some(ty2)) => self.add_pair(ty1, ty2),
                (None, Some(_)) => break false,
                (Some(_), None) => break false,
                (None, None) => (),
            }

            match (e1.view(), e2.view()) {
                (EType, _) => break false,
                (EKind, _) => break false,
                (EConst(..), _) => break false, // closed types: equal or incompatible
                (EBoundVar(v1), EBoundVar(v2)) => {
                    if v1.idx() != v2.idx() {
                        break false;
                    }
                    self.add_pair(v1.ty(), v2.ty())
                }
                (EVar(v), _) => {
                    if self.occur_check(v, e2) {
                        break false;
                    }
                    self.subst.add_(v, e2);
                }
                (_, EVar(v)) => {
                    if self.occur_check(v, e1) {
                        break false;
                    }
                    self.subst.add_(v, e1)
                }
                (EApp(f1, a1), EApp(f2, a2)) => {
                    self.add_pair(f1, f2);
                    self.add_pair(a1, a2);
                }
                (EPi(tyv1, body1), EPi(tyv2, body2)) => {
                    self.add_pair(tyv1, tyv2);
                    self.add_pair(body1, body2);
                }
                (ELambda(tyv1, body1), ELambda(tyv2, body2)) => {
                    self.add_pair(tyv1, tyv2);
                    self.add_pair(body1, body2);
                }
                (EBoundVar(..), _) => break false,
                (EApp(..), _) => break false,
                (ELambda(..), _) => break false,
                (EPi(..), _) => break false,
            }
        };
        if sat {
            Some(self.subst)
        } else {
            None
        }
    }
}

// TODO: when we have a parser, write some tests
/// Unify the two expressions.
pub fn unify<'a>(e1: &'a Expr, e2: &'a Expr) -> Option<UnifySubst<'a>> {
    let mut st = UnifySt::new();
    st.add_pair(e1, e2);
    st.solve()
}

/// Prove symmetry of equality.
///
/// Goes from `A |- t=u` to `A |- u=t`.
pub fn thm_sym(em: &mut ExprManager, th: &Thm) -> Result<Thm, String> {
    // start with `F |- t=u`.
    // now by left-congruence with `refl(=)`, `F |- ((=) t) = ((=) u)`.
    // by right-congruence with `refl(t)`, `F |- (((=) t) t) = (((=) u) t)`.
    // in other words, `F |- (t=t)=(u=t)`.
    // Just do bool_eq_elim with `|- t=t` (refl(t)) and we're done.
    let (t, u) = th
        .concl()
        .unfold_eq()
        .ok_or_else(|| format!("sym: expect an equation in {:?}", th))?;
    let refl_t = em.thm_refl(t.clone());
    let th_tequ_eq_ueqt = {
        let eq = em.mk_eq();
        let eq_u = em.mk_app(eq, u.ty().clone());
        let th_r = em.thm_refl(eq_u);
        let th_c_r = em.thm_congr(&th_r, th)?;
        em.thm_congr(&th_c_r, &refl_t)?
    };
    em.thm_bool_eq(&refl_t, &th_tequ_eq_ueqt)
}
