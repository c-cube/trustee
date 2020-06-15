//! # Rewriting
//!
//! Rewriting algorithms.

use crate::{utils, CtxI, Error, Expr, ExprView::*, Result, Thm};

/// Result of a rewrite step.
pub enum RewriteResult {
    /// No rewrite step.
    RwSame,
    /// A theorem `A |- a=b` where `a` is the initial term, and `b` the result.
    RwStep(Thm),
}

use RewriteResult::*;

/* TODO: remove
fn trans_opt(
    ctx: &mut dyn CtxI,
    th1: Option<Thm>,
    th2: Option<Thm>,
) -> Result<Option<Thm>> {
    match (th1, th2) {
        (Some(th1), Some(th2)) => Ok(Some(ctx.thm_trans(th1, th2)?)),
        (Some(th), None) => Ok(Some(th)),
        (None, Some(th)) => Ok(Some(th)),
        (None, None) => Ok(None),
    }
}
*/

/// A term rewriter that operates at the root of a term.
pub trait Rewriter {
    /// `rewriter.step(ctx, e)` is called on a term `e` and can trigger a rewrite step.
    ///
    /// If it returns `Some(A |- e=e2)`, then the term rewrites into `e2`
    /// with the given proof.
    fn step(&mut self, ctx: &mut dyn CtxI, e: &Expr) -> Option<Thm>;
}

/// Rewrite `e` using the rewriter `rw`.
///
/// The rewriter is called on every non-type subterm, starting from the leaves.
pub fn rewrite_bottom_up<RW>(
    ctx: &mut dyn CtxI,
    rw: &mut RW,
    e: Expr,
) -> Result<RewriteResult>
where
    RW: Rewriter,
{
    let r = match e.view() {
        EType | EKind | EVar(..) | EBoundVar(..) | EPi(..) => RwSame,
        _ if e.ty().is_type() => RwSame,
        EConst(..) => match rw.step(ctx, &e) {
            None => RwSame,
            Some(th2) => {
                let e2 = {
                    let (_, b) = th2.concl().unfold_eq().ok_or_else(|| {
                        Error::new("rewrite function must return an equation")
                    })?;
                    b.clone()
                };
                match rewrite_bottom_up(ctx, rw, e2)? {
                    RwSame => RwStep(th2),
                    RwStep(th3) => RwStep(ctx.thm_trans(th2, th3)?),
                }
            }
        },
        EApp(hd, a) => {
            let r1 = rewrite_bottom_up(ctx, rw, hd.clone())?;
            let r2 = rewrite_bottom_up(ctx, rw, a.clone())?;
            match (r1, r2) {
                (RwSame, RwSame) => RwSame,
                (RwStep(th), RwSame) => {
                    if a.ty().is_type() {
                        RwStep(ctx.thm_congr_ty(th, a)?)
                    } else {
                        let th2 = ctx.thm_refl(a.clone());
                        RwStep(ctx.thm_congr(th, th2)?)
                    }
                }
                (RwSame, RwStep(th)) => {
                    let th_hd = ctx.thm_refl(hd.clone());
                    RwStep(ctx.thm_congr(th_hd, th)?)
                }
                (RwStep(th1), RwStep(th2)) => RwStep(ctx.thm_congr(th1, th2)?),
            }
        }
        // TODO: rewrite under lambdas?
        //
        // But then we need either:
        // - introduce variable `x`, turn `λbody` into `x, body[0\x]`,
        //   rewrite
        //   then use `abs(x,
        ELambda(..) => RwSame,
    };
    Ok(r)
}

/// A rewrite rule.
pub struct Rule {
    lhs: Expr,
    th: Thm,
    ordered: bool, // only works if `lhs>rhs`.
}

impl Rule {
    fn new_(th: &Thm, ordered: bool) -> Result<Self> {
        let (lhs, rhs) = th.concl().unfold_eq().ok_or_else(|| {
            Error::new("rewrite rule conclusion must be an equation")
        })?;
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
        if !ordered {
            match vl.iter().find(|v| !vr.contains(v)) {
                None => (),
                Some(v) => {
                    return Err(Error::new_string(format!(
                        "variable {:?} occurs freely in LHS of unordered rule but not RHS",
                        v
                    )))
                }
            };
        }
        Ok(Rule { lhs: lhs.clone(), th: th.clone(), ordered })
    }

    /// Create a rewrite rule from a theorem `|- lhs=rhs`.
    ///
    /// Will fail if the theorem is not an equation, or if some
    /// free variables of `rhs` are not in `lhs`, or if the theorem has
    /// assumptions.
    pub fn new(th: &Thm) -> Result<Self> {
        Self::new_(th, false)
    }

    /// Create an unordered rewrite rule from a theorem `|- t1=t2`.
    ///
    /// This can rewrite both `t1σ` into `t2σ`, or `t2σ` into `t1σ`
    /// for a substitution `σ`, depending on which is the bigger term.
    ///
    /// Will fail if the theorem is not an equation, or if `t1` and `t2`
    /// do not have the same set of free `t1` and `t2`
    /// do not have the same set of free variables.
    /// free variables of `rhs` are not in `lhs`.
    pub fn new_unordered(th: &Thm) -> Result<Self> {
        Self::new_(th, true)
    }
}

/// A set of rewrite rules.
///
/// Implementation details are hidden, but this implements `Rewriter`.
pub struct RuleSet {
    // TODO: use a better kind of indexing
    rules: Vec<Rule>,
}

impl Rewriter for RuleSet {
    fn step(&mut self, ctx: &mut dyn CtxI, e: &Expr) -> Option<Thm> {
        for r in &self.rules {
            match utils::match_(&r.lhs, e) {
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

impl RuleSet {
    /// New rule set.
    pub fn new() -> Self {
        Self { rules: vec![] }
    }

    /// Add a single rule.
    pub fn add_rule(&mut self, r: Rule) {
        self.rules.push(r)
    }

    /// Add a set of rules.
    pub fn add_rules<I>(&mut self, i: I)
    where
        I: Iterator<Item = Rule>,
    {
        for r in i {
            self.rules.push(r)
        }
    }
}

impl std::iter::FromIterator<Rule> for RuleSet {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = Rule>,
    {
        let mut s = Self::new();
        s.add_rules(iter.into_iter());
        s
    }
}
