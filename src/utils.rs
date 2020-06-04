//! Utils that are outside the kernel of trust itself.

use crate::*;

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
pub fn thm_new_poly_definition(
    em: &mut dyn CtxI,
    c: &str,
    rhs: Expr,
) -> Result<NewPolyDef> {
    let mut vars_ty_rhs: Vec<Var> = rhs.ty().free_vars().cloned().collect();
    //eprintln!("vars_of_ty({:?}) = {:?}", &rhs, &vars_ty_rhs);
    vars_ty_rhs.sort_unstable();
    vars_ty_rhs.dedup();

    if vars_ty_rhs.iter().any(|v| !v.ty.is_type()) {
        return Err(Error::new_string(format!("thm_new_poly_definition: cannot make a polymorphic \
        definition for {}\nusing rhs = {:?}\nrhs contains non-type free variables",
        c, rhs)));
    }

    let ty_closed = em.mk_pi_l(&vars_ty_rhs, rhs.ty().clone())?;
    let eqn = {
        let rhs_closed = em.mk_lambda_l(&vars_ty_rhs, rhs.clone())?;
        let v = em.mk_var_str(c, ty_closed);
        em.mk_eq_app(v, rhs_closed)?
    };
    let (thm, c) = em.thm_new_basic_definition(eqn)?;

    // type variables as expressions
    let e_vars: Vec<_> =
        vars_ty_rhs.iter().cloned().map(|v| em.mk_var(v)).collect();

    let c_applied = em.mk_app_l(c.clone(), &e_vars)?;

    // apply `thm` to the type variables
    let thm_applied = {
        let mut thm = thm.clone();
        for v in e_vars.iter() {
            thm = em.thm_congr_ty(thm, &v)?;
            // now replace `(λa:type. …) v` with its beta reduced version
            let thm_rhs = thm
                .concl()
                .unfold_eq()
                .ok_or_else(|| Error::new("rhs must be an equality"))?
                .1;
            let thm_beta = em.thm_beta_conv(thm_rhs)?;
            thm = em.thm_trans(thm, thm_beta)?;
        }
        thm
    };

    Ok(NewPolyDef { thm, c, ty_vars: vars_ty_rhs, thm_applied, c_applied })
}

/// Data used to rename variables, if needed, prior to implementation.
pub struct RenamingData {
    v2: fnv::FnvHashSet<Var>,
    var_count: usize,
    buf: String,
    renaming: fnv::FnvHashMap<Var, Var>,
}

impl RenamingData {
    pub fn rename_var(&mut self, v: &Var) -> Var {
        use std::fmt::Write;

        match self.renaming.get(&v) {
            Some(v2) => v2.clone(),
            None => {
                // allocate a new variable that isn't in `v2`
                let ty = v.ty.clone();
                let v2 = loop {
                    self.buf.clear();
                    write!(&mut self.buf, "_x_{}", self.var_count)
                        .expect("cannot print temporary variable name");
                    let new_v = Var::from_str(&self.buf[..], ty.clone());
                    if !self.v2.contains(&new_v) {
                        break new_v;
                    }
                };
                self.var_count += 1;
                self.renaming.insert(v.clone(), v2.clone());
                v2
            }
        }
    }
}

/// Do we need to rename `e1`prior to unification?
///
/// The answer is `Some(data)` if there are shared variables, where `data`
/// can be used to perform the renaming, `None` otherwise.
pub fn need_to_rename_before_unif(
    e1: &Expr,
    e2: &Expr,
) -> Option<RenamingData> {
    let v1: fnv::FnvHashSet<Var> = e1.free_vars().cloned().collect();
    if v1.is_empty() {
        return None;
    }

    let v2: fnv::FnvHashSet<Var> = e2.free_vars().cloned().collect();

    let inter = v1.intersection(&v2);
    if inter.take(1).count() > 0 {
        Some(RenamingData {
            v2,
            var_count: 0,
            buf: String::with_capacity(16),
            renaming: fnv::new_table_with_cap(8),
        })
    } else {
        None
    }
}

// TODO: use binary search?
/// A substitution obtained by unification.
#[derive(Debug, Clone)]
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

#[derive(Copy, Clone, Eq, PartialEq)]
enum UnifOp {
    Match,
    Unify,
}
struct UnifySt<'a> {
    op: UnifOp,
    solved: fnv::FnvHashSet<(&'a Expr, &'a Expr)>,
    subst: UnifySubst<'a>,
    to_solve: Vec<(&'a Expr, &'a Expr)>,
}

impl<'a> UnifySt<'a> {
    fn new(op: UnifOp) -> Self {
        UnifySt {
            op,
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
                    if !e2.is_closed() || self.occur_check(v, e2) {
                        break false;
                    }
                    self.subst.add_(v, e2);
                }
                (_, EVar(v)) if self.op == UnifOp::Unify => {
                    if !e1.is_closed() || self.occur_check(v, e1) {
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

// TODO: a function for variable renaming

// TODO: when we have a parser, write some tests
/// Unify the two expressions.
pub fn unify<'a>(e1: &'a Expr, e2: &'a Expr) -> Option<UnifySubst<'a>> {
    let mut st = UnifySt::new(UnifOp::Unify);
    st.add_pair(e1, e2);
    st.solve()
}

/// Match the LHS (pattern) against the RHS.
pub fn match_<'a>(e1: &'a Expr, e2: &'a Expr) -> Option<UnifySubst<'a>> {
    let mut st = UnifySt::new(UnifOp::Match);
    st.add_pair(e1, e2);
    st.solve()
}

/// Prove symmetry of equality.
///
/// Goes from `A |- t=u` to `A |- u=t`.
pub fn thm_sym(em: &mut dyn CtxI, th: Thm) -> Result<Thm> {
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
