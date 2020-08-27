///! ## Rewriting
///!
///! Rewriting algorithms.
use super::*;

/// Result of a rewrite step.
pub enum Res {
    /// No rewrite step.
    RwSame,
    /// A theorem `A |- a=b` where `a` is the initial term, and `b` the result.
    RwStep(Thm),
}

use Res::*;

/// A term rewriter that operates at the root of a term.
pub trait Rewriter {
    /// `rewriter.step(ctx, e)` is called on a term `e` and can trigger a rewrite step.
    ///
    /// If it returns `Some(A |- e=e2)`, then the term rewrites into `e2`
    /// with the given proof.
    fn step(&self, ctx: &mut Ctx, e: &Expr) -> Option<Thm>;
}

/// Rewrite `e` using the rewriter `rw`.
///
/// The rewriter is called on every non-type subterm, starting from the leaves.
pub fn rewrite_bottom_up(ctx: &mut Ctx, rw: &dyn Rewriter, e0: Expr) -> Result<Res> {
    let mut th_eq = None; // stores proof for `e0 = e`
    let mut e = e0;

    macro_rules! update_th {
        ($res: expr, $els: block) => {
            match $res {
                None => $els,
                Some(th2) => {
                    e = {
                        let (_, b) = th2.concl().unfold_eq().ok_or_else(|| {
                            Error::new("rewrite function must return an equation")
                        })?;
                        b.clone()
                    };
                    th_eq = match th_eq {
                        None => Some(th2),
                        Some(th1) => Some(ctx.thm_trans(th1, th2)?),
                    }
                }
            }
        };
    };

    loop {
        match e.view() {
            EType | EKind | EVar(..) | EBoundVar(..) | EPi(..) => break,
            _ if e.ty().is_type() => break,
            EConst(..) => {
                let r = rw.step(ctx, &e);
                update_th!(r, { break });
            }
            EApp(hd, a) => {
                let r1 = rewrite_bottom_up(ctx, rw, hd.clone())?;
                let r2 = rewrite_bottom_up(ctx, rw, a.clone())?;
                let step = match (r1, r2) {
                    (RwSame, RwSame) => None,
                    (RwStep(th), RwSame) => {
                        if a.ty().is_type() {
                            Some(ctx.thm_congr_ty(th, a)?)
                        } else {
                            let th2 = ctx.thm_refl(a.clone());
                            Some(ctx.thm_congr(th, th2)?)
                        }
                    }
                    (RwSame, RwStep(th)) => {
                        let th_hd = ctx.thm_refl(hd.clone());
                        Some(ctx.thm_congr(th_hd, th)?)
                    }
                    (RwStep(th1), RwStep(th2)) => Some(ctx.thm_congr(th1, th2)?),
                };
                update_th!(step, {});
                let step2 = rw.step(ctx, &e);
                update_th!(step2, { break });
            }
            // TODO: rewrite under lambdas?
            //
            // But then we need either:
            // - introduce variable `x`, turn `λbody` into `x, body[0\x]`,
            //   rewrite, then use `thm_abs(x, norm(body))`
            ELambda(..) => break,
        };
    }
    Ok(match th_eq {
        Some(th) => RwStep(th),
        None => RwSame,
    })
}

/// A rewrite rule.
pub struct RewriteRule {
    lhs: Expr,
    th: Thm,
}

impl RewriteRule {
    fn new_(th: &Thm, oriented: bool) -> Result<Self> {
        let (lhs, rhs) = th
            .concl()
            .unfold_eq()
            .ok_or_else(|| Error::new("rewrite rule conclusion must be an equation"))?;
        let vl: Vec<_> = lhs.free_vars().collect();
        let vr: Vec<_> = rhs.free_vars().collect();
        if th.hyps().len() > 0 {
            // TODO: if there are hypothesis, we need a `prove` procedure
            // to dischard the guard upon matching
            return Err(Error::new("rewrite rule must have no hypothesis"));
        }
        match vr.iter().find(|v| !vl.contains(v)) {
            None => (),
            Some(v) => {
                return Err(Error::new_string(format!(
                    "variable {:?} occurs freely in RHS of rule but not LHS",
                    v
                )))
            }
        };
        // TODO: not used for now?
        if !oriented {
            match vl.iter().find(|v| !vr.contains(v)) {
                None => (),
                Some(v) => {
                    return Err(Error::new_string(format!(
                        "variable {:?} occurs freely in LHS of non-oriented rule but not in RHS",
                        v
                    )))
                }
            };
        }
        Ok(Self {
            lhs: lhs.clone(),
            th: th.clone(),
        })
    }

    /// Create a rewrite rule from a theorem `|- lhs=rhs`.
    ///
    /// Will fail if the theorem is not an equation, or if some
    /// free variables of `rhs` are not in `lhs`, or if the theorem has
    /// assumptions.
    pub fn new(th: &Thm) -> Result<Self> {
        Self::new_(th, true)
    }

    // TODO
    /// Create an unordered rewrite rule from a theorem `|- t1=t2`.
    ///
    /// This can rewrite both `t1σ` into `t2σ`, or `t2σ` into `t1σ`
    /// for a substitution `σ`, depending on which is the bigger term.
    ///
    /// Will fail if the theorem is not an equation, or if `t1` and `t2`
    /// do not have the same set of free `t1` and `t2`
    /// do not have the same set of free variables.
    /// free variables of `rhs` are not in `lhs`.
    pub fn new_non_oriented(th: &Thm) -> Result<Self> {
        Self::new_(th, false)
    }
}

/// A combinator of rewriters.
pub struct RewriteCombine<'a> {
    rw: Vec<&'a dyn Rewriter>,
}

impl<'a> RewriteCombine<'a> {
    /// New combinator of rewriters.
    pub fn new() -> Self {
        RewriteCombine { rw: vec![] }
    }

    /// Add a sub-rewriter.
    pub fn add(&mut self, rw: &'a dyn Rewriter) {
        self.rw.push(rw);
    }

    /// Add a slice of sub-rewriters.
    pub fn add_slice(&mut self, rw: &[&'a dyn Rewriter]) {
        for x in rw.iter().copied() {
            self.rw.push(x)
        }
    }

    /// Add a list of sub-rewriters.
    pub fn extend<I>(&mut self, rw: I)
    where
        I: IntoIterator<Item = &'a dyn Rewriter>,
    {
        for x in rw {
            self.rw.push(x)
        }
    }
}

impl<'a> Rewriter for RewriteCombine<'a> {
    fn step(&self, ctx: &mut Ctx, e: &Expr) -> Option<Thm> {
        for rw in self.rw.iter() {
            match rw.step(ctx, e) {
                x @ Some(..) => return x,
                None => (),
            }
        }
        None
    }
}

/// A set of rewrite rules.
///
/// Implementation details are hidden, but this implements `Rewriter`.
pub struct RewriteRuleSet {
    // TODO: use a better kind of indexing
    rules: Vec<RewriteRule>,
}

impl Rewriter for RewriteRuleSet {
    fn step(&self, ctx: &mut Ctx, e: &Expr) -> Option<Thm> {
        for r in &self.rules {
            match match_(&r.lhs, e) {
                None => (),
                Some(subst) => {
                    // match happened.
                    let th = ctx
                        .thm_instantiate(r.th.clone(), &subst.to_k_subst())
                        .expect("invalid instantiation");
                    return Some(th);
                }
            }
        }
        None
    }
}

impl RewriteRuleSet {
    /// New rule set.
    pub fn new() -> Self {
        Self { rules: vec![] }
    }

    /// Add a single rule.
    pub fn add_rule(&mut self, r: RewriteRule) {
        self.rules.push(r)
    }

    /// Add a set of rules.
    pub fn add_rules<I>(&mut self, i: I)
    where
        I: Iterator<Item = RewriteRule>,
    {
        for r in i {
            self.rules.push(r)
        }
    }

    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    pub fn size(&self) -> usize {
        self.rules.len()
    }
}

impl std::iter::FromIterator<RewriteRule> for RewriteRuleSet {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = RewriteRule>,
    {
        let mut s = Self::new();
        s.add_rules(iter.into_iter());
        s
    }
}

/// Rewriter implementation using the `beta_conv` rule.
#[derive(Clone, Copy)]
pub struct RewriterBetaConv;

impl Rewriter for RewriterBetaConv {
    fn step(&self, ctx: &mut Ctx, e: &Expr) -> Option<Thm> {
        match ctx.thm_beta_conv(&e) {
            Ok(th) => Some(th),
            Err(..) => None,
        }
    }
}

/// Normalize the conclusion of `th` using the given rewriter.
pub fn thm_rw_concl(ctx: &mut Ctx, th: Thm, rw: &dyn Rewriter) -> Result<Thm> {
    let c = th.concl().clone();
    match rewrite_bottom_up(ctx, rw, c)? {
        rw::Res::RwSame => Ok(th.clone()),
        rw::Res::RwStep(th2) => {
            let th3 = ctx.thm_bool_eq(th, th2)?;
            Ok(th3)
        }
    }
}
