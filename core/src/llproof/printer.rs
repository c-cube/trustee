//! # Print proofs

use super::{
    proof::{LLProofSteps, LLStatement, LocalValue},
    *,
};
use crate::rstr::RStr;
use std::io;

pub fn print_set(name: &str, p: &LLProof, out: &mut dyn io::Write) -> Result<()> {
    write!(out, "(set {} ", name)?;
    print_steps(&p.0, out)?;
    write!(out, ")")?;
    Ok(())
}

pub fn print_defrule(p: &LLProofRule, out: &mut dyn io::Write) -> Result<()> {
    write!(out, "(defrule {} {} ", p.name, p.n_args)?;
    print_steps(&p.steps, out)?;
    write!(out, ")")?;
    Ok(())
}

/// Print a series of steps, in `()`.
pub fn print_steps(p: &LLProofSteps, out: &mut dyn io::Write) -> Result<()> {
    write!(out, "(")?;
    for (i, s) in p.steps.iter().enumerate() {
        if i > 0 {
            write!(out, " ")?;
        }
        match s {
            LLProofStep::LoadLocal(lix) => match &p.locals[lix.0 as usize] {
                LocalValue::Str(s) => {
                    write!(out, "\"{}\"", s)?;
                }
                LocalValue::Expr(e) => {
                    let s = format!("${}", e);
                    write!(out, "{}", s)?;
                }
                LocalValue::Rule(r) => write!(out, "{}", r.name)?,
                LocalValue::Pat(_) => todo!("print pattern"),
            },
            LLProofStep::ParseExpr => todo!(),
            LLProofStep::LoadDeep(_) => {}
            LLProofStep::EMkType => {}
            LLProofStep::EGetType => {}
            LLProofStep::EEq => {}
            LLProofStep::EMkEq => {}
            LLProofStep::EApp => {}
            LLProofStep::ThCut => write!(out, "cut")?,
            LLProofStep::ThAssume => {}
            LLProofStep::CallRule(_) => {}
            LLProofStep::SetByName(_) => {}
            LLProofStep::GetByname(_) => {}
        }
    }
    write!(out, ")")?;
    Ok(())
}

/// Print proofs of the given theorems, if present, in low-level proof format.
pub fn print_thm_proofs(
    thms: impl Iterator<Item = (RStr, Thm)>,
    out: &mut dyn io::Write,
) -> Result<()> {
    // TODO: print each theorem as a "set", store it in a hashset
    // so that next steps can use refer to it by name.
    //
    // Locally, also use the hashset for a graph traversal and use stack operations
    // to re-use proofs.
    // Test on opentheory with fake names.

    /*
    impl fmt::Debug for Proof {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Proof::Axiom(_) => write!(out, "<axiom ø>"),
                Proof::Assume(e) => write!(out, "(assume ${}$)", e),
                Proof::Refl(e) => write!(out, "(refl ${}$)", e),
                Proof::Trans(th1, th2) => {}
                Proof::Congr(_, _) => {}
                Proof::CongrTy(_, _) => {}
                Proof::Instantiate(_, _) => {}
                Proof::Abs(_, _) => {}
                Proof::Cut(_, _) => {}
                Proof::BoolEq(_, _) => {}
                Proof::BoolEqIntro(_, _) => {}
                Proof::BetaConv(_) => {}
                Proof::NewDef(_) => {}
                Proof::NewTyDef(_, _) => {}
            }
        }
    }
    */

    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_printer() {
        let s = r#"
            (defrule cut2    3 (cut cut))
            "#;
        let mut ctx = Ctx::new();
        let mut p = Parser::new(&mut ctx, s);
        let r1 = p
            .parse()
            .expect("cannot parse r1")
            .expect("must be present");

        let p = match r1 {
            LLStatement::DefRule(r) => r,
            _ => panic!("must be a rule"),
        };

        let mut s = vec![];
        print_defrule(&p, &mut s).expect("print");
        let s = std::str::from_utf8(&s).expect("print: invalid utf8");

        assert_eq!(s, "(defrule cut2 3 (cut cut))");
    }
}
