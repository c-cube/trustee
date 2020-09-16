//! # Low Level Proofs
//!
//! Definition of derived rules, and proof format for the kernel.

use crate::{
    algo::conv, pattern::PatternSubst, rptr::RPtr, rstr::RStr, syntax, Ctx, Error, Expr, Pattern,
    Result, Thm,
};

mod eval;

/// A low-level proof, composed of a series of steps.
///
/// It can take some arguments.
pub struct LLProof {
    /// Number of arguments that will be consumed from the stack.
    pub n_args: u8,
    /// Name of the proof rule, if any.
    pub name: Option<RStr>,
    /// Successive steps.
    steps: Box<[LLProofStep]>,
    /// Local values.
    locals: Box<[LLValue]>,
}

/// Index in `locals`
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LocalIdx(u8);

#[derive(Debug)]
pub enum LLProofStep {
    /// Parse expression in `locals[$0]`
    /// `-- e`
    ParseExpr(LocalIdx),
    /// Copy `st[-i]` to the top.
    /// `st -- st st[-i]`
    LoadDeep(u8),
    /// Push `type` on the stack.
    /// `-- type`
    EType,
    /// `e -- e.ty`
    EGetType,
    /// Push `=` on the stack.
    /// `-- =`
    EEq,
    /// `a b -- (a = b)`
    EMkEq,
    /// `a b -- (app a b)`
    EApp,
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

/// Builder for a proof.
pub struct LLProofBuilder {
    n_args: u8,
    name: Option<RStr>,
    steps: Vec<LLProofStep>,
    locals: Vec<LLValue>,
}

/// ## LL Values
///
/// A value of the low-level value language.
#[derive(Debug, Clone)]
pub enum LLValue {
    /// A string, of any kind.
    Str(RStr),
    Expr(Expr),
    /// A theorem.
    Thm(Thm),
    /// A converter.
    Conv(RPtr<conv::BasicConverter>),
    /// A pattern.
    Pattern(RPtr<Pattern>),
    /// Substitution obtained from a pattern.
    PatSubst(RPtr<PatternSubst>),
    /// A proof rule.
    Rule(RPtr<LLProof>),
}

const INIT_ST_SIZE: usize = 256;

/// Evaluate proof in the given context.
pub fn eval_proof(ctx: &mut Ctx, p: &LLProof) -> Result<Thm> {
    let mut st = Vec::with_capacity(INIT_ST_SIZE);
    let ev = eval::Eval {
        st: &mut st,
        ctx,
        err: None,
    };
    let th = ev
        .eval(p)?
        .as_thm()
        .ok_or_else(|| Error::new("llproof must return a theorem"))?;
    Ok(th)
}

// TODO: add a syntax file to parse the proofs

mod impls {
    use super::*;
    use std::{fmt, u8};

    impl std::cmp::PartialEq for LLValue {
        fn eq(&self, other: &Self) -> bool {
            match (self, other) {
                (LLValue::Expr(e1), LLValue::Expr(e2)) => return e1 == e2,
                (LLValue::Thm(t1), LLValue::Thm(t2)) => return t1 == t2,
                (LLValue::Str(s1), LLValue::Str(s2)) => return s1 == s2,
                _ => false,
            }
        }
    }

    impl fmt::Debug for LLProof {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            let name = self.name.as_ref().map(|s| &**s).unwrap_or("<anon>");
            writeln!(out, "llproof (n-args={}, name={}) [", self.n_args, name)?;
            for s in &*self.steps {
                write!(out, "  {:?}", s)?;
                if let Some(lix) = s.get_lix() {
                    write!(out, "  // {:?}", &self.locals[lix.0 as usize])?;
                }
                writeln!(out, "")?;
            }
            writeln!(out, "]")?;
            Ok(())
        }
    }

    impl LLValue {
        pub fn as_thm(self) -> Option<Thm> {
            match self {
                LLValue::Thm(th) => Some(th),
                _ => None,
            }
        }
    }

    impl LLProofStep {
        /// Access local index, if any.
        fn get_lix(&self) -> Option<LocalIdx> {
            match self {
                LLProofStep::ParseExpr(lix) => Some(*lix),
                LLProofStep::SetByName(lix) => Some(*lix),
                LLProofStep::GetByname(lix) => Some(*lix),
                LLProofStep::CallRule(lix) => Some(*lix),
                LLProofStep::LoadDeep(..)
                | LLProofStep::EType
                | LLProofStep::EGetType
                | LLProofStep::EEq
                | LLProofStep::EMkEq
                | LLProofStep::EApp
                | LLProofStep::ThAssume => None,
            }
        }
    }

    impl LLProofBuilder {
        /// New proof builder.
        pub fn new(n_args: u8, name: Option<RStr>) -> Self {
            Self {
                n_args,
                name,
                steps: vec![],
                locals: vec![],
            }
        }

        /// Allocate a local for the given value.
        pub fn alloc_local(&mut self, v: LLValue) -> Result<LocalIdx> {
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

        /// Convert into a proper proof.
        pub fn into_proof(self) -> LLProof {
            let LLProofBuilder {
                steps,
                locals,
                n_args,
                name,
            } = self;
            let steps = steps.into_boxed_slice();
            let locals = locals.into_boxed_slice();
            LLProof {
                steps,
                locals,
                n_args,
                name,
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

        let sz = std::mem::size_of::<LLValue>();
        println!("size of llvalue is {}", sz);
        assert!(sz <= 16); // at most 2 words
    }

    #[test]
    fn test_eval1() {
        let mut pr = LLProofBuilder::new(0, None);
        let lix = pr
            .alloc_local(LLValue::Str("with a b:bool. a = b".into()))
            .unwrap();
        pr.add_step(LLProofStep::ParseExpr(lix));
        pr.add_step(LLProofStep::ThAssume);
        let pr = pr.into_proof();

        let mut ctx = Ctx::new();
        let th = eval_proof(&mut ctx, &pr).unwrap();
        println!("th: {:?}", th);
    }
}
