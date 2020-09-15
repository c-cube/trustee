//! Basic ground rewriting modulo AC.
//!
//! The purpose is simply to normalize some AC-operators such as `\/` or `/\`.

use crate::{
    algo::{self, conv, kbo},
    kernel::{Ctx, Error, Expr, Result, Thm},
    syntax,
};

// TODO: from the E paper: prove these and use them.
// {f (x, y) = f (y, x),
// f (f (x, y), z) = f (x, f (y, z)),
// f (x, f (y, z)) = f (z, f (x, y)),
// f (x, f (y, z)) = f (y, f (x, z)),
// f (x, f (y, z)) = f (z, f (y, x))}

// TODO: optionally take an idempotent axiom (and ground-complete it?)
// TODO: optionally handle neutral elements (/\ + T,  \/ + F)

/// AC-conversion rule for one symbol.
///
/// Use functions from `conv` and `rw` to normalize deeply.
#[derive(Debug, Clone)]
pub struct ACConv {
    /// A binary function.
    pub f: Expr,
    /// Theorem `|- f (f x y) z = f x (f y z)`
    pub assoc: Thm,
    /// Theorem `|- f x y = f y x`
    pub comm: Thm,
    // prevent users from creating this directly.
    _hidden: (),
}

impl ACConv {
    fn new_(ctx: &mut Ctx, assoc: Thm, comm: Thm) -> Result<Self> {
        let pat_assoc = syntax::parse_pattern(ctx, r#"= _ (?f (?f ?x ?y) ?z) (?f ?x (?f ?y ?z))"#)
            .map_err(|e| e.with_source(Error::new("parsing pattern for associativity")))?;
        let pat_comm = syntax::parse_pattern(ctx, r#"= _ (?f ?x ?y) (?f ?y ?x)"#)
            .map_err(|e| e.with_source(Error::new("parsing pattern for commutativity")))?;

        let s1 = pat_assoc.match_(assoc.concl()).ok_or_else(|| {
            Error::new_string(format!("theorem `{:?}` doesn't match associativity", assoc))
        })?;
        let s2 = pat_comm.match_(comm.concl()).ok_or_else(|| {
            Error::new_string(format!("theorem `{:?}` doesn't match commutativity", comm))
        })?;

        crate::logtrace!("match assoc: {:?}, match comm: {:?}", s1, s2);

        let f1 = s1.get_by_name("f").ok_or(Error::new("pattern bug"))?;
        let f2 = s2.get_by_name("f").ok_or(Error::new("pattern bug"))?;

        if f1 != f2 {
            return Err(Error::new_string(format!(
                "ac_rw: incompatible axioms: assoc is for function {:?}, comm is for {:?}",
                f1, f2
            )));
        }
        let f = f1.clone();

        Ok(ACConv {
            assoc,
            comm,
            f,
            _hidden: (),
        })
    }

    /// Create a new AC-conversion rule from the given associativity
    /// and commutativity axioms.
    ///
    /// Fails if the axioms do not have the expected shape.
    pub fn new(ctx: &mut Ctx, assoc: Thm, comm: Thm) -> Result<Self> {
        Self::new_(ctx, assoc, comm).map_err(|e| {
            e.with_source(Error::new(
                "ACConv::new: expected associativity and commutativity axioms",
            ))
        })
    }
}

/// A set of AC-conversion rules.
#[derive(Debug, Clone)]
pub struct ACConvList<'a>(pub &'a [&'a ACConv]);

impl conv::Converter for ACConv {
    fn try_conv(&self, ctx: &mut Ctx, e: &Expr) -> Result<Option<Thm>> {
        let mut e = e.clone();
        let mut res = None;

        let rw_assoc = algo::rw_rule::RewriteRule::new(&self.assoc)?;
        let rw_comm = algo::rw_rule::RewriteRule::new(&self.comm.clone())?;

        loop {
            crate::logtrace!("ac rw: try to rewrite {:?}", e);
            if let Some(th) = rw_assoc.try_conv(ctx, &e)? {
                e = th
                    .concl()
                    .unfold_eq()
                    .ok_or_else(|| Error::new("rw assoc yielded a non-equational theorem"))?
                    .1
                    .clone();

                res = conv::chain_res(ctx, res, Some(th))?;
            } else if let Some(th) = rw_comm.try_conv(ctx, &e)? {
                let (a, b) = th
                    .concl()
                    .unfold_eq()
                    .expect("rw-comm matches implies is-eq");
                if let Some(std::cmp::Ordering::Greater) = kbo::kbo_compare(&a, &b) {
                    // effectively rewrite, by term ordering, if `a >_kbo b`.
                    let e2 = th
                        .concl()
                        .unfold_eq()
                        .ok_or_else(|| Error::new("rw conv yielded a non-equational theorem"))?
                        .1
                        .clone();
                    crate::logtrace!("rewrite {:?} into {:?}", e, e2);
                    e = e2;
                    res = conv::chain_res(ctx, res, Some(th))?;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
        Ok(res)
    }
}

impl<'a> conv::Converter for ACConvList<'a> {
    fn try_conv(&self, ctx: &mut Ctx, e: &Expr) -> Result<Option<Thm>> {
        for r in self.0 {
            if let Some(th) = r.try_conv(ctx, e)? {
                return Ok(Some(th));
            }
        }
        Ok(None)
    }
}
