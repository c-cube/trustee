//! # Low Level Proofs
//!
//! Definition of derived rules, and proof format for the kernel.

use crate::{syntax, Ctx, Error, Result, Thm};

// TODO: proof generation for opentheory, with a small CLI tool

mod eval;
pub mod parser;
pub mod printer;
pub mod proof;

pub use parser::Parser;
pub use printer::{print_defrule, print_set};
pub use proof::{LLProof, LLProofBuilder, LLProofRule, LLProofStep, StackValue};

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

#[cfg(test)]
mod test {
    use super::*;
    use proof::*;

    #[test]
    fn test_eval1() {
        let mut pr = LLProofBuilder::new();
        let lix = pr
            .alloc_local(LocalValue::Str("with a b:bool. a = b".into()))
            .unwrap();
        pr.add_step(LLProofStep::LoadLocal(lix));
        pr.add_step(LLProofStep::ParseExpr);
        pr.add_step(LLProofStep::ThAssume);
        let pr = pr.into_proof();

        let mut ctx = Ctx::new();
        let th = eval_proof(&mut ctx, &pr).unwrap();
        println!("th: {:?}", th);
    }
}
