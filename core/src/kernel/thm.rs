//! # Theorems.
//!
//! Theorems are proved correct by construction.

use super::{Expr, Ref, Var};
use std::fmt;

/// A theorem.
#[derive(Clone)]
pub struct Thm(pub(super) Ref<ThmImpl>);

#[derive(Clone)]
pub(super) struct ThmImpl {
    /// Conclusion of the theorem.
    pub concl: Expr,
    /// Hypothesis of the theorem.
    pub hyps: Vec<Expr>,
    /// Unique ID of the `Ctx`
    pub ctx_uid: u32,
    /// Proof of the theorem, if any.
    pub proof: Option<Ref<Proof>>,
}

/// The proof step for a theorem, if proof recording is enabled.
pub enum Proof {
    Assume(Expr),
    Refl(Expr),
    Trans(Thm, Thm),
    Congr(Thm, Thm),
    CongrTy(Thm, Expr),
    Instantiate(Thm, Box<[(Var, Expr)]>),
    Abs(Var, Thm),
    /// Point to self as an axiom.
    Axiom(Expr),
    Cut(Thm, Thm),
    BoolEq(Thm, Thm),
    BoolEqIntro(Thm, Thm),
    BetaConv(Expr),
    NewDef(Expr),
    NewTyDef(Expr, Thm),
    // TODO: custom rules
}

impl Thm {
    pub(super) fn make_(
        concl: Expr,
        em_uid: u32,
        hyps: Vec<Expr>,
        proof: Option<Ref<Proof>>,
    ) -> Self {
        // TODO: remove
        //if hyps.len() >= 2 {
        //    hyps.sort_unstable();
        //    hyps.dedup();
        //    hyps.shrink_to_fit();
        //}
        Thm(Ref::new(ThmImpl {
            concl,
            ctx_uid: em_uid,
            hyps,
            proof: None,
        }))
    }

    /// Conclusion of the theorem
    #[inline]
    pub fn concl(&self) -> &Expr {
        &self.0.concl
    }

    /// Access the proof of this theorem, if it was recorded.
    pub fn proof(&self) -> Option<&Proof> {
        match self.0.proof {
            None => None,
            Some(ref p) => Some(p),
        }
    }

    /// Hypothesis of the theorem
    #[inline]
    pub fn hyps(&self) -> &[Expr] {
        self.0.hyps.as_slice()
    }

    #[inline]
    pub fn hyps_vec(&self) -> &Vec<Expr> {
        &self.0.hyps
    }
}

mod impls {
    use super::*;

    impl fmt::Display for Thm {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            if self.hyps().len() == 0 {
                write!(out, "$|- {}$", self.concl())
            } else {
                let mut first = true;
                for h in self.hyps() {
                    if out.alternate() {
                        write!(out, "    {}\n", h)?;
                    } else {
                        if first {
                            first = false;
                            write!(out, "$")?;
                        } else {
                            write!(out, ", ")?;
                        }
                        write!(out, "{}", h)?;
                    }
                }
                write!(out, " |- {}$", self.concl())
            }
        }
    }

    impl fmt::Debug for Thm {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            if self.hyps().len() == 0 {
                write!(out, "|- {:?}", self.concl())
            } else {
                for h in self.hyps() {
                    write!(out, "    {:?}\n", h)?;
                }
                write!(out, " |- {:?}", self.concl())
            }
        }
    }

    impl PartialEq for Thm {
        fn eq(&self, other: &Self) -> bool {
            std::ptr::eq(self.0.as_ref() as *const _, other.0.as_ref() as *const _)
        }
    }
}
