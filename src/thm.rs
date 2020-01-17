//! The main type of theorems, with a LCF style kernel.
//!
//! This is the trusted part of the system, where axioms need to be carefully
//! reviewed.

use crate::expr::{self, Expr};
use std::sync::Arc;

/// The main theorem type.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Thm(Arc<ThmCell>);

#[derive(Clone, Debug, Eq, PartialEq)]
struct ThmCell {
    concl: Expr,
    hyps: Vec<Expr>,
}

impl Thm {
    /// Access the conclusion and hypothesis.
    #[inline]
    pub fn get(&self) -> (&Expr, &[Expr]) {
        (&self.0.concl, self.0.hyps.as_slice())
    }

    /// Access conclusion.
    pub fn concl(&self) -> &Expr {
        &self.0.concl
    }

    /// Access hypotheses.
    pub fn hyps(&self) -> &[Expr] {
        &self.0.hyps
    }

    /// Implementation of the rules.

    fn mk_(concl: Expr, hyps: Vec<Expr>) -> Self {
        Thm(Arc::new(ThmCell { concl, hyps }))
    }

    /// Builds `e |- e`.
    pub fn assume(e: &Expr) -> Self {
        Self::mk_(e.clone(), vec![e.clone()])
    }

    /// Builds `|- e=e`.
    pub fn refl(e: &Expr) -> Self {
        let concl = Expr::eq(e.ty()).app(e).app(e);
        Self::mk_(concl, vec![])
    }
}
