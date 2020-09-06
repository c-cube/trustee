//! Basic ground rewriting modulo AC.
//!
//! The purpose is simply to normalize some AC-operators such as `\/` or `/\`.

use crate::{
    algo::{
        self,
        conv::{self},
    },
    kernel_of_trust::{Ctx, Error, Expr, Result, Thm},
    syntax,
};

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
        let eqc = comm
            .concl()
            .unfold_eq()
            .ok_or_else(|| Error::new("commutativity axiom must be an equality"))?;
        let (f, args) = eqc.0.unfold_app();
        if args.len() < 2 {
            return Err(Error::new_string(format!(
                "{:?} must be a binary function",
                f
            )));
        }
        let f = f.clone();
        let ty = args[args.len() - 2].ty().clone();

        let t_assoc = syntax::parse_expr_with_args(
            ctx,
            "with x y z:?. let f = ? in f (f x y) z = f x (f y z)",
            &[ty, f.clone()],
        )?;

        dbg!(&t_assoc);
        if let Some(_subst) = algo::unif::match_(&t_assoc, assoc.concl()) {
            // TODO: actually check for alpha-equiv
        } else {
            return Err(Error::new_string(format!(
                "expected conclusion of {:?} to be {:?}",
                assoc, t_assoc,
            )));
        }

        // TODO: also check comm

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

// TODO: implement basic KBO for the "comm" case

impl conv::Converter for ACConv {
    fn try_conv(&self, ctx: &mut Ctx, e: &Expr) -> Result<Option<Thm>> {
        let mut e = e.clone();
        let mut res = None;

        let rw_assoc = algo::rw_rule::RewriteRule::new(&self.assoc)?;
        let rw_comm = algo::rw_rule::RewriteRule::new(&self.comm.clone())?;

        loop {
            if let Some(th) = rw_assoc.try_conv(ctx, &e)? {
                e = th
                    .concl()
                    .unfold_eq()
                    .ok_or_else(|| Error::new("rw assoc yielded a non-equational theorem"))?
                    .1
                    .clone();

                res = conv::chain_res(ctx, res, Some(th))?;
            } else if let Some(th) = rw_comm.try_conv(ctx, &e)? {
                let (a, b) = e.unfold_eq().expect("rw-comm matches implies is-eq");
                if a > b {
                    // effectively rewrite, by term ordering.
                    // TODO: use KBO as a more robust ordering.
                    e = th
                        .concl()
                        .unfold_eq()
                        .ok_or_else(|| Error::new("rw conv yielded a non-equational theorem"))?
                        .1
                        .clone();
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
