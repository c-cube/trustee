//! Equations seen as rewrite rules.

use super::{conv::Converter, unif};
use crate::{Ctx, Error, Expr, Result, Thm};

/// A simple rewrite rule.
#[derive(Debug, Clone)]
pub struct RewriteRule {
    /// the LHS of the theorem's conclusion.
    lhs: Expr,
    /// A theorem `A |- lhs = rhs`
    th: Thm,
}

impl Converter for RewriteRule {
    fn try_conv(&self, ctx: &mut Ctx, e: &Expr) -> Result<Option<Thm>> {
        crate::logtrace!("rw-rule.try-conv {:?} with rule {:?}", e, self);
        match unif::match_(&self.lhs, e) {
            None => Ok(None),
            Some(subst) => {
                // match happened, substitute to get an equality.
                let th = ctx.thm_instantiate(self.th.clone(), &subst.to_k_subst())?;
                Ok(Some(th))
            }
        }
    }
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

/// A set of rewrite rules.
///
/// Implementation details are hidden, but this implements `Converter`.
#[derive(Debug, Clone)]
pub struct RewriteRuleSet {
    // TODO(perf): use a better kind of indexing
    rules: Vec<RewriteRule>,
}

impl Converter for RewriteRuleSet {
    fn try_conv(&self, ctx: &mut Ctx, e: &Expr) -> Result<Option<Thm>> {
        // at some point, implement indexing. for now, just try rules one by one.
        for r in &self.rules {
            if let Some(th) = r.try_conv(ctx, e)? {
                return Ok(Some(th));
            }
        }
        Ok(None)
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
    ///
    /// For now it is unspecified whether deduplication is performed.
    pub fn add_rules<I>(&mut self, i: I)
    where
        I: Iterator<Item = RewriteRule>,
    {
        for r in i {
            self.rules.push(r)
        }
    }

    /// Is the set of rules empty?
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }

    /// Number of rules in the set.
    pub fn size(&self) -> usize {
        self.rules.len()
    }
}

/// Allow to collect rewrite rules into a set.
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
