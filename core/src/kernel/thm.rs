//! # Theorems.
//!
//! Theorems are proved correct by construction.

use super::{Expr, Proof, Ref};
use smallvec::SmallVec;
use std::fmt;

/// A theorem.
#[derive(Clone)]
pub struct Thm(pub(super) Ref<ThmImpl>);

pub type Exprs = SmallVec<[Expr; 3]>;

#[derive(Clone)]
pub(super) struct ThmImpl {
    /// Conclusion of the theorem.
    pub concl: Expr,
    /// Hypothesis of the theorem.
    pub hyps: Exprs,
    /// Unique ID of the `Ctx`
    pub ctx_uid: u32,
    /// Proof of the theorem, if any.
    pub proof: Option<Proof>,
}

impl Thm {
    pub(super) fn make_(concl: Expr, em_uid: u32, hyps: Exprs, proof: Option<Proof>) -> Self {
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
            proof,
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
    pub fn hyps_vec(&self) -> &Exprs {
        &self.0.hyps
    }

    // TODO: something to replace the proof of a theorem with a named
    // proof, called from the context (`pub(super)`) so we can
    // change the proof of `th` to `"foo"` when `(set "foo" th)` is emitted.

    /// Forget the proof of this theorem, if any.
    pub fn forget_proof(mut self) -> Self {
        let r = Ref::make_mut(&mut self.0); // no copy if single use
        r.proof = None;
        self
    }

    /// Make a copy of the theorem with a different proof.
    ///
    /// This is sound, per se, but if the proof is wrong it can be misleading
    /// because it will not be reproducible from the proof itself.
    pub fn set_proof(mut self, pr: Proof) -> Self {
        let r = Ref::make_mut(&mut self.0); // no copy if single use
        r.proof = Some(pr);
        self
    }
}

mod impls {
    use super::*;

    impl fmt::Debug for Thm {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            if self.hyps().len() == 0 {
                write!(out, "|- {:?}", self.concl())
            } else {
                for h in self.hyps() {
                    writeln!(out, "    {:?}", h)?;
                }
                write!(out, " |- {:?}", self.concl())
            }
        }
    }

    impl PartialEq for Thm {
        fn eq(&self, other: &Self) -> bool {
            self.concl() == other.concl() && self.hyps() == other.hyps()
        }
    }

    impl Eq for Thm {}

    impl std::hash::Hash for Thm {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.concl().hash(state);
            for x in self.hyps() {
                x.hash(state)
            }
        }
    }
}
