//! # Low Level Proofs.
//!

use crate::{
    algo::conv, pattern::PatternSubst, rptr::RPtr, rstr::RStr, Error, Expr, Pattern, Result, Thm,
};

/// A low-level proof, composed of a series of steps.
pub struct LLProof(pub(super) LLProofSteps);

/// A low-level proof rule, with a name and an arity.
///
/// It can take some arguments.
pub struct LLProofRule {
    /// Number of arguments that will be consumed from the stack.
    pub n_args: u8,
    /// Name of the proof rule.
    pub name: RStr,
    pub(super) steps: LLProofSteps,
}

/// A series of steps, used in other structures.
pub struct LLProofSteps {
    /// Successive steps.
    pub(super) steps: Box<[LLProofStep]>,
    /// Local values.
    pub(super) locals: Box<[LocalValue]>,
}

/// A local value, serializable, and parametrizing some instructions.
#[derive(Clone, Debug)]
pub enum LocalValue {
    Expr(Expr),
    Str(RStr),
    Pat(Pattern),
    Rule(RPtr<LLProofRule>),
}

/// ## LL Values
///
/// A value of the low-level value language.
#[derive(Debug, Clone)]
pub enum StackValue {
    /// A string, of any kind.
    Str(RStr),
    Expr(Expr),
    /// A theorem.
    Thm(Thm),
    /// A converter.
    Conv(RPtr<conv::BasicConverter>),
    /// A pattern.
    Pattern(Pattern),
    /// Substitution obtained from a pattern.
    PatSubst(RPtr<PatternSubst>),
    /// A proof rule.
    Rule(RPtr<LLProofRule>),
}

/// Index in `locals`
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct LocalIdx(pub(super) u8);

/// A single step in a proof; an instruction of the proof virtual machine.
#[derive(Debug, Clone)]
pub enum LLProofStep {
    /// Load `locals[$0]` onto the stack
    LoadLocal(LocalIdx),
    /// Parse expression from string
    /// `s -- e`
    ParseExpr,
    /// Copy `st[-i]` to the top.
    /// `st -- st st[-i]`
    LoadDeep(u8),
    /// Push `type` on the stack.
    /// `-- type`
    EMkType,
    /// `e -- e.ty`
    EGetType,
    /// Push `=` on the stack.
    /// `-- =`
    EEq,
    /// `a b -- (a = b)`
    EMkEq,
    /// `a b -- (app a b)`
    EApp,
    /// `th1 th2 -- cut(th1, th2)`
    ThCut,
    /// `e -- assume(e)`
    ThAssume,
    /// Call rule `locals[$0]`.
    CallRule(LocalIdx),
    /// Pop value and set `ctx[locals[$0]]` to it.
    /// `v --`
    SetByName(LocalIdx),
    /// Get lemma with name `local[$0]` and push it on the stack.
    GetByname(LocalIdx),
}

/// A toplevel statement for the language of proofs.
#[derive(Debug)]
pub enum LLStatement<'a> {
    /// Define a rule.
    DefRule(LLProofRule),
    /// Declare a lemma in the context, using the proof's result.
    Set(&'a str, LLProof),
}

/// Builder for a proof.
pub struct LLProofBuilder {
    steps: Vec<LLProofStep>,
    locals: Vec<LocalValue>,
}

mod impls {
    use super::*;
    use std::{fmt, u8};

    impl std::cmp::PartialEq for LocalValue {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (LocalValue::Expr(e1), LocalValue::Expr(e2)) => return e1 == e2,
                (LocalValue::Str(s1), LocalValue::Str(s2)) => return s1 == s2,
                (LocalValue::Rule(r1), LocalValue::Rule(r2)) => return r1.name == r2.name,
                _ => false,
            }
        }
    }

    impl fmt::Debug for LocalIdx {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "loc({})", self.0)
        }
    }

    // print series of steps
    fn pp_steps(steps: &LLProofSteps, out: &mut fmt::Formatter) -> fmt::Result {
        for s in &*steps.steps {
            write!(out, "  {:?}", s)?;
            if let Some(lix) = s.get_lix() {
                write!(out, "  // {:?}", &steps.locals[lix.0 as usize])?;
            }
            writeln!(out, "")?;
        }
        Ok(())
    }

    impl fmt::Debug for LLProof {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            writeln!(out, "llproof[")?;
            pp_steps(&self.0, out)?;
            writeln!(out, "]")?;
            Ok(())
        }
    }

    impl fmt::Debug for LLProofRule {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            writeln!(
                out,
                "llproofrule (n-args={}, name={}) [",
                self.n_args, &*self.name
            )?;
            pp_steps(&self.steps, out)?;
            writeln!(out, "]")?;
            Ok(())
        }
    }

    impl StackValue {
        pub fn as_thm(self) -> Option<Thm> {
            match self {
                StackValue::Thm(th) => Some(th),
                _ => None,
            }
        }
    }

    impl LLProofStep {
        /// Access local index, if any.
        fn get_lix(&self) -> Option<LocalIdx> {
            match self {
                LLProofStep::SetByName(lix) => Some(*lix),
                LLProofStep::GetByname(lix) => Some(*lix),
                LLProofStep::CallRule(lix) => Some(*lix),
                LLProofStep::LoadLocal(lix) => Some(*lix),
                LLProofStep::LoadDeep(..)
                | LLProofStep::ParseExpr
                | LLProofStep::EMkType
                | LLProofStep::EGetType
                | LLProofStep::EEq
                | LLProofStep::EMkEq
                | LLProofStep::EApp
                | LLProofStep::ThCut
                | LLProofStep::ThAssume => None,
            }
        }
    }

    impl LLProofSteps {
        #[inline]
        pub fn steps(&self) -> &[LLProofStep] {
            &*self.steps
        }

        #[inline]
        pub fn locals(&self) -> &[LocalValue] {
            &*self.locals
        }
    }

    impl LLProofRule {
        /// Constructor.
        pub fn new(name: RStr, n_args: u8, steps: LLProofSteps) -> Self {
            // TODO: arity check.
            Self {
                name,
                n_args,
                steps,
            }
        }
    }

    impl LLProofBuilder {
        /// New proof builder.
        pub fn new() -> Self {
            Self {
                steps: vec![],
                locals: vec![],
            }
        }

        /// Allocate a local for the given value.
        pub fn alloc_local(&mut self, v: LocalValue) -> Result<LocalIdx> {
            for (i, v2) in self.locals.iter().enumerate() {
                if v == *v2 {
                    return Ok(LocalIdx(i as u8));
                }
            }

            let i = self.locals.len();
            if i == u8::MAX as usize {
                return Err(Error::new("too many locals"));
            }
            self.locals.push(v);
            Ok(LocalIdx(i as u8))
        }

        /// Add a step to the proof.
        pub fn add_step(&mut self, st: LLProofStep) {
            self.steps.push(st)
        }

        /// Convert into a proper set of steps.
        pub fn into_proof(self) -> LLProof {
            let LLProofBuilder { steps, locals } = self;
            let steps = steps.into_boxed_slice();
            let locals = locals.into_boxed_slice();
            LLProof(LLProofSteps { steps, locals })
        }

        /// Convert into a proper set of steps.
        pub fn into_proof_rule(self, name: impl Into<RStr>, n_args: u8) -> LLProofRule {
            let LLProofBuilder { steps, locals } = self;
            let steps = steps.into_boxed_slice();
            let locals = locals.into_boxed_slice();
            LLProofRule {
                n_args,
                name: name.into(),
                steps: LLProofSteps { steps, locals },
            }
        }
    }

    impl From<LocalValue> for StackValue {
        fn from(v: LocalValue) -> Self {
            match v {
                LocalValue::Expr(e) => StackValue::Expr(e),
                LocalValue::Str(s) => StackValue::Str(s),
                LocalValue::Pat(p) => StackValue::Pattern(p),
                LocalValue::Rule(r) => StackValue::Rule(r),
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_size() {
        let sz = std::mem::size_of::<LLProofStep>();
        println!("size of llproofstep is {}", sz);
        assert!(sz <= 8);

        let sz = std::mem::size_of::<StackValue>();
        println!("size of llvalue is {}", sz);
        assert!(sz <= 16); // at most 2 words

        let sz = std::mem::size_of::<LocalValue>();
        println!("size of localvalue is {}", sz);
        assert!(sz <= 16); // at most 2 words
    }
}
