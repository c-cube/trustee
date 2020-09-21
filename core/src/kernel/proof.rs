//! # A low-level proof step.
//!
//! Such proofs are direct justifications for theorem (see `thm.rs`).

use super::*;

/// The proof step for a theorem, if proof recording is enabled.
#[derive(Clone)]
pub enum Proof {
    Assume(Expr),
    Refl(Expr),
    Trans(Thm, Thm),
    Congr(Thm, Thm),
    CongrTy(Thm, Expr),
    // FIXME: use a Rc<[…]> when I find how to turn a Vec into it
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
    // TODO: custom rules
}

mod impls {
    use super::*;

    impl Proof {
        /// Call `f` on immediate premises of this proof.
        pub fn premises<F>(&self, mut f: F)
        where
            F: FnMut(&Thm),
        {
            match self {
                Proof::Assume(_) | Proof::Refl(_) => {}
                Proof::Trans(a, b) => {
                    f(a);
                    f(b)
                }
                Proof::Congr(a, b) => {
                    f(a);
                    f(b)
                }
                Proof::CongrTy(a, _) => {
                    f(a);
                }
                Proof::Instantiate(a, _) => f(a),
                Proof::Abs(_, a) => f(a),
                Proof::Axiom(_) => {}
                Proof::Cut(a, b) => {
                    f(a);
                    f(b);
                }
                Proof::BoolEq(a, b) => {
                    f(a);
                    f(b)
                }
                Proof::BoolEqIntro(a, b) => {
                    f(a);
                    f(b)
                }
                Proof::BetaConv(_) => {}
                Proof::NewDef(_) => {}
                Proof::NewTyDef(_, th) => f(th),
            }
        }
    }
}
