//! # Evaluation.

use super::{
    proof::{LLProofSteps, LocalValue},
    *,
};

/// Evaluator.
pub struct Eval<'a> {
    pub ctx: &'a mut Ctx,
    pub st: &'a mut Vec<StackValue>,
    pub err: Option<Error>,
}

/// Specialized version of `?`
macro_rules! tryev {
    ($self: expr, $e: expr) => {
        match $e {
            Ok(x) => x,
            Err(e) => {
                $self.err = Some(e);
                return false;
            }
        }
    };
}

/// Pop a value from the stack.
macro_rules! popst {
    ($self: expr) => {
        match $self.st.pop() {
            Some(v) => v,
            None => {
                $self.err = Some(Error::new("stack underflow"));
                return false;
            }
        }
    };
}

macro_rules! getv {
    ($name: ident, $pat: pat, $rhs: expr, $what:literal) => {
        macro_rules! $name {
            ($self: expr, $e: expr) => {
                match $e {
                    $pat => $rhs,
                    _ => {
                        $self.err = Some(Error::new($what));
                        return false;
                    }
                }
            };
        }
    };
}

getv!(lgetstr, LocalValue::Str(ref v), v, "expected string");
getv!(lgetexpr, LocalValue::Expr(ref e), e, "expected expression");
getv!(getstr, StackValue::Str(v), v, "expected string");
getv!(getexpr, StackValue::Expr(e), e, "expected expression");
getv!(getthm, StackValue::Thm(th), th, "expected theorem");
getv!(lgetrule, LocalValue::Rule(r), &*r, "expected proof rule");

impl<'a> Eval<'a> {
    /// Evaluate the given proof.
    pub fn eval(mut self, p: &LLProof) -> Result<StackValue> {
        // TODO: also add an entrypoint with some args
        self.eval_loop_(&p.0);

        if let Some(e) = self.err {
            Err(e) // execution failed
        } else if self.st.len() == 1 {
            let v = self.st.pop().unwrap();
            Ok(v)
        } else {
            return Err(Error::new("llproof.eval: stack should have size 1"));
        }
    }

    /// Evaluate current proof.
    /// Returns `true` if evaluation was successful, otherwise set
    /// `err` to `Some(e)` and return `false`.
    fn eval_loop_(&mut self, p: &LLProofSteps) -> bool {
        // linear execution
        for step in p.steps.iter() {
            match step {
                LLProofStep::LoadLocal(lix) => {
                    let v = p.locals[lix.0 as usize].clone().into();
                    self.st.push(v)
                }
                LLProofStep::ParseExpr => {
                    let v = popst!(self);
                    let s = &*getstr!(self, v);
                    let e = tryev!(self, syntax::parse_expr(self.ctx, s));
                    self.st.push(StackValue::Expr(e))
                }
                LLProofStep::LoadDeep(i) => {
                    let n = self.st.len();
                    debug_assert!((*i as usize) < n);
                    let v = self.st[n - (*i as usize)].clone();
                    self.st.push(v)
                }
                LLProofStep::EMkType => {
                    let v = self.ctx.mk_ty();
                    self.st.push(StackValue::Expr(v))
                }
                LLProofStep::EGetType => {
                    let v = popst!(self);
                    let e = getexpr!(self, v);
                    self.st.push(StackValue::Expr(e.ty().clone()));
                }
                LLProofStep::EEq => {
                    let e = self.ctx.mk_eq();
                    self.st.push(StackValue::Expr(e));
                }
                LLProofStep::EMkEq => {
                    let v = popst!(self);
                    let e2 = getexpr!(self, v);
                    let v = popst!(self);
                    let e1 = getexpr!(self, v);
                    let e = tryev!(self, self.ctx.mk_eq_app(e1, e2));
                    self.st.push(StackValue::Expr(e));
                }
                LLProofStep::EApp => {
                    let v = popst!(self);
                    let e2 = getexpr!(self, v);
                    let v = popst!(self);
                    let e1 = getexpr!(self, v);
                    let e = tryev!(self, self.ctx.mk_app(e1, e2));
                    self.st.push(StackValue::Expr(e));
                }
                LLProofStep::ThAssume => {
                    let v = popst!(self);
                    let e = getexpr!(self, v);
                    let th = tryev!(self, self.ctx.thm_assume(e));
                    self.st.push(StackValue::Thm(th));
                }
                LLProofStep::ThCut => {
                    let v = popst!(self);
                    let th2 = getthm!(self, v);
                    let v = popst!(self);
                    let th1 = getthm!(self, v);
                    let th = tryev!(self, self.ctx.thm_cut(th1, th2));
                    self.st.push(StackValue::Thm(th));
                }
                LLProofStep::CallRule(lix) => {
                    let p2 = lgetrule!(self, &p.locals[lix.0 as usize]);
                    crate::logtrace!("call proof rule {:?}", p2.name);

                    if p2.n_args as usize > self.st.len() {
                        self.err = Some(Error::new("not enough arguments"));
                        return false;
                    }

                    let ok = self.eval_loop_(&p2.steps);
                    if !ok {
                        return false;
                    }
                }
                LLProofStep::SetByName(_lix) => {
                    // TODO: store llvalues in ctx, not meta::Value
                    todo!("set by name")
                }
                LLProofStep::GetByname(_lix) => {
                    // TODO: store llvalues in ctx, not meta::Value
                    todo!("get by name");
                }
            }
        }
        true
    }
}
