//! # Theorems.
//!
//! Theorems are proved correct by construction.

use super::{Expr, Proof, ProofView, Ref, Result};
use crate::fnv::FnvHashMap as HM;
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
    pub proof: Option<Proof>,
}

impl Thm {
    pub(super) fn make_(concl: Expr, em_uid: u32, hyps: Vec<Expr>, proof: Option<Proof>) -> Self {
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
    pub fn hyps_vec(&self) -> &Vec<Expr> {
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

    // recursive implementation of `print_proof`
    fn print_proof_(&self, seen: &mut HM<Thm, usize>, out: &mut dyn std::io::Write) -> Result<()> {
        if seen.contains_key(&self) {
            return Ok(());
        }

        let pr = match self.proof() {
            None => return Ok(()),
            Some(pr) => pr,
        };

        {
            // explore parents first
            let mut e = Ok(());
            pr.premises(|th2| match th2.print_proof_(seen, out) {
                Ok(()) => (),
                Err(e2) => e = Err(e2),
            });
            e?;
        }

        let n = seen.len();
        seen.insert(self.clone(), n);
        write!(out, " ({} ", n)?;

        match &**pr {
            ProofView::Assume(e) => {
                writeln!(out, "assume ${}$)", e)?;
            }
            ProofView::Refl(e) => {
                writeln!(out, "refl ${}$)", e)?;
            }
            ProofView::Trans(th1, th2) => {
                let n1 = seen.get(&th1).unwrap();
                let n2 = seen.get(&th2).unwrap();
                writeln!(out, "trans {} {})", n1, n2)?;
            }
            ProofView::Congr(th1, th2) => {
                let n1 = seen.get(&th1).unwrap();
                let n2 = seen.get(&th2).unwrap();
                writeln!(out, "congr {} {})", n1, n2)?;
            }
            ProofView::CongrTy(th1, ty) => {
                let n1 = seen.get(&th1).unwrap();
                writeln!(out, "congr_ty {} ${}$)", n1, ty)?;
            }
            ProofView::Instantiate(th1, _) => {
                // TODO: print subst
                let n1 = seen.get(&th1).unwrap();
                writeln!(out, "instantiate {})", n1,)?;
            }
            ProofView::Abs(v, th1) => {
                let n1 = seen.get(&th1).unwrap();
                writeln!(out, "abs ${:?}$ {})", v, n1,)?;
            }
            ProofView::Axiom(e) => {
                writeln!(out, "axiom ${}$)", e,)?;
            }
            ProofView::Cut(th1, th2) => {
                let n1 = seen.get(&th1).unwrap();
                let n2 = seen.get(&th2).unwrap();
                writeln!(out, "cut {} {})", n1, n2)?;
            }
            ProofView::BoolEq(th1, th2) => {
                let n1 = seen.get(&th1).unwrap();
                let n2 = seen.get(&th2).unwrap();
                writeln!(out, "bool_eq {} {})", n1, n2)?;
            }
            ProofView::BoolEqIntro(th1, th2) => {
                let n1 = seen.get(&th1).unwrap();
                let n2 = seen.get(&th2).unwrap();
                writeln!(out, "bool_eq_intro {} {})", n1, n2)?;
            }
            ProofView::BetaConv(e) => {
                writeln!(out, "beta_conv ${}$)", e)?;
            }
            ProofView::NewDef(e) => {
                writeln!(out, "new_def ${}$)", e)?;
            }
            ProofView::NewTyDef(e, _) => {
                writeln!(out, "new_ty_def ${}$)", e)?;
            }
            ProofView::GetThm(r) => {
                writeln!(out, "get {})", r)?;
            }
            ProofView::CallRule1(r, th1) => {
                let n1 = seen.get(&th1).unwrap();
                writeln!(out, "call1 {} {})", r, n1)?;
            }
            ProofView::CallRule2(r, th1, th2) => {
                let n1 = seen.get(&th1).unwrap();
                let n2 = seen.get(&th2).unwrap();
                writeln!(out, "call2 {} {} {})", r, n1, n2)?;
            }
            ProofView::CallRuleN(r, a) => {
                write!(out, "calln {}", r)?;
                for th in a.iter() {
                    let n = seen.get(&th).unwrap();
                    write!(out, " {}", n)?;
                }
                writeln!(out, ")")?;
            }
        }
        Ok(())
    }

    /// Print proof of this theorem and its parents, recursively.
    pub fn print_proof(&self, out: &mut dyn std::io::Write) -> Result<()> {
        let mut seen = HM::default();
        writeln!(out, "(proof ")?;
        self.print_proof_(&mut seen, out)?;
        writeln!(out, ")")?;
        Ok(())
    }

    /// Print proof into stirng, if present.
    pub fn proof_to_string(&self) -> Option<String> {
        let mut v = vec![];
        if let Err(_e) = self.print_proof(&mut v) {
            return None;
        }
        std::string::String::from_utf8(v).ok()
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

    // TODO: use structural equality instead?
    impl PartialEq for Thm {
        fn eq(&self, other: &Self) -> bool {
            std::ptr::eq(self.0.as_ref() as *const _, other.0.as_ref() as *const _)
        }
    }

    impl Eq for Thm {}

    impl std::hash::Hash for Thm {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            let p = self.0.as_ref();
            std::ptr::hash(p, state)
        }
    }
}
