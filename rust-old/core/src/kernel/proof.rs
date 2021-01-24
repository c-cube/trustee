//! # A low-level proof step.
//!
//! Such proofs are direct justifications for theorem (see `thm.rs`).

use {
    super::*,
    crate::{rptr::RPtr, rstr::RStr},
    std::fmt,
};

/// The proof step for a theorem, if proof recording is enabled.
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct Proof(RPtr<ProofView>);

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ProofView {
    Assume(Expr),
    Refl(Expr),
    Trans(Thm, Thm),
    Congr(Thm, Thm),
    CongrTy(Thm, Expr),
    Instantiate(Thm, Subst),
    Abs(Var, Thm),
    /// Point to self as an axiom.
    Axiom(Expr),
    Cut(Thm, Thm),
    BoolEq(Thm, Thm),
    BoolEqIntro(Thm, Thm),
    BetaConv(Expr),
    NewDef(Expr),
    NewTyDef(Expr, Thm),
    /// Get existing theorem by its name
    GetThm(RStr),
    /// Call rule with one argument
    CallRule1(RStr, Thm),
    /// Call rule with two argument
    CallRule2(RStr, Thm, Thm),
    /// Call rule with three argument
    CallRuleN(RStr, Box<[Thm]>),
    // TODO: custom rules
}

mod impls {
    use super::*;

    impl std::ops::Deref for Proof {
        type Target = ProofView;

        #[inline]
        fn deref(&self) -> &Self::Target {
            &*self.0
        }
    }

    impl Proof {
        /// Call `f` on immediate premises of this proof.
        pub fn premises<FThm, FE>(&self, mut fe: FE, mut f: FThm)
        where
            FE: FnMut(&Expr),
            FThm: FnMut(&Thm),
        {
            use ProofView as PV;
            match &*self.0 {
                PV::Assume(e) | PV::Refl(e) => fe(e),
                PV::Trans(a, b) => {
                    f(a);
                    f(b)
                }
                PV::Congr(a, b) => {
                    f(a);
                    f(b)
                }
                PV::CongrTy(a, e) => {
                    f(a);
                    fe(&e)
                }
                PV::Instantiate(a, subst) => {
                    f(a);
                    for (v, e) in &**subst {
                        fe(v.ty());
                        fe(e);
                    }
                }
                PV::Abs(v, a) => {
                    fe(v.ty());
                    f(a)
                }
                PV::Axiom(e) => fe(e),
                PV::Cut(a, b) => {
                    f(a);
                    f(b);
                }
                PV::BoolEq(a, b) => {
                    f(a);
                    f(b)
                }
                PV::BoolEqIntro(a, b) => {
                    f(a);
                    f(b)
                }
                PV::BetaConv(e) => fe(e),
                PV::NewDef(e) => {
                    fe(e);
                }
                PV::NewTyDef(ty, th) => {
                    fe(ty);
                    f(th)
                }
                PV::GetThm(_) => {}
                PV::CallRule1(_, th) => f(th),
                PV::CallRule2(_, th1, th2) => {
                    f(th1);
                    f(th2)
                }
                PV::CallRuleN(_, a) => {
                    for th in a.iter() {
                        f(th)
                    }
                }
            }
        }

        #[inline]
        pub fn new(v: ProofView) -> Self {
            Proof(RPtr::new(v))
        }
    }

    impl fmt::Debug for Proof {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.0.fmt(f)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_size() {
        let s1 = std::mem::size_of::<Proof>();
        assert_eq!(s1, std::mem::size_of::<*const ()>(), "size of ptr: {}", s1);
        let s2 = std::mem::size_of::<Option<Proof>>();
        assert_eq!(
            s2,
            std::mem::size_of::<*const ()>(),
            "size of ptr option {}",
            s2
        );
    }
}
