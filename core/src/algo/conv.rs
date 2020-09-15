//! Converter.
//!
//! A converter is a function taking an expression `e`, and returning
//! an `Option<Thm>`. It returns `Some(… |- e = e2)` if `e` can be converted
//! into `e2`, `None` otherwise.

use crate::{kernel as k, Ctx, Expr, Result, Thm};
use std::fmt;

/// `converter.try_conv(ctx, e)` is called on a term `e` and can trigger a rewrite step.
///
/// If it returns `Some(A |- e=e2)`, then the term rewrites into `e2`
/// with the given proof.
pub trait Converter: fmt::Debug {
    /// The core function.
    fn try_conv(&self, _: &mut Ctx, e: &Expr) -> Result<Option<Thm>>;

    /// Unconditionally produce a theorem, using `refl` to produce `|- e = e`
    /// if nothing else is found.
    fn conv(&self, ctx: &mut Ctx, e: &Expr) -> Result<Thm> {
        let th = self.try_conv(ctx, e)?;
        Ok(get_or_refl(ctx, e, th))
    }
}

/// Apply beta-reduction at root.
#[derive(Clone, Copy, Debug)]
pub struct BetaReduce;

/// Apply beta-reduction at root, repeatedly, until the root
/// is not a beta-redex anymore.
#[derive(Clone, Copy, Debug)]
pub struct BetaReduceRepeat;

/// Converter that does nothing.
#[derive(Clone, Copy, Debug)]
pub struct TrivialConv;

/// A "basic" converter. Use a as component in `SeqConverter`.
#[derive(Debug, Clone)]
pub enum BasicConverter {
    Nil,
    Beta(BetaReduce),
    BetaRepeat(BetaReduceRepeat),
    Wrapped(k::Ref<dyn Converter>),
}

/// A composite converter, made of smaller converters.
#[derive(Debug)]
pub struct SeqConverter {
    v: Vec<BasicConverter>,
    repeat: bool,
}

/// Converter2
#[derive(Debug)]
pub struct Congr<'a>(pub &'a dyn Converter, pub &'a dyn Converter);

/// Converter for the LHS.
#[derive(Debug)]
pub struct CongrLHS<'a>(pub &'a dyn Converter);

/// Converter for the RHS.
#[derive(Debug)]
pub struct CongrRHS<'a>(pub &'a dyn Converter);

/// Normalize the conclusion of `th` using the given converter.
pub fn thm_conv_concl(ctx: &mut Ctx, th: Thm, conv: &dyn Converter) -> Result<Thm> {
    let c = th.concl().clone();
    if let Some(th2) = conv.try_conv(ctx, &c)? {
        let th3 = ctx.thm_bool_eq(th, th2)?;
        Ok(th3)
    } else {
        Ok(th.clone())
    }
}

/// Return the theorem `th`, or `refl e` if `th.is_none()`.
fn get_or_refl(ctx: &mut k::Ctx, e: &Expr, th: Option<Thm>) -> Thm {
    match th {
        Some(th) => th,
        None => ctx.thm_refl(e.clone()),
    }
}

/// Chain `res1` and `res2` into a single theorem, or `None` if both are none.
pub fn chain_res(ctx: &mut k::Ctx, res1: Option<Thm>, res2: Option<Thm>) -> Result<Option<Thm>> {
    if let Some(th1) = res1 {
        if let Some(th2) = res2 {
            // transitivity here
            ctx.thm_trans(th1, th2).map(|x| Some(x))
        } else {
            Ok(Some(th1))
        }
    } else {
        Ok(res2)
    }
}

impl Converter for TrivialConv {
    fn try_conv(&self, _ctx: &mut k::Ctx, _e: &k::Expr) -> Result<Option<k::Thm>> {
        Ok(None)
    }
}

impl<'a> Converter for Congr<'a> {
    fn try_conv(&self, ctx: &mut k::Ctx, e: &k::Expr) -> Result<Option<k::Thm>> {
        if let Some((lhs, rhs)) = e.as_app() {
            let r1 = self.0.try_conv(ctx, lhs)?;
            let r2 = self.1.try_conv(ctx, rhs)?;
            eprintln!("conv {:?}: r1={:?}, r2={:?}", e, r1, r2);
            let step = match (r1, r2) {
                (None, None) => None,
                (Some(th), None) => {
                    if rhs.ty().is_type() {
                        Some(ctx.thm_congr_ty(th, rhs)?)
                    } else {
                        let th2 = ctx.thm_refl(rhs.clone());
                        Some(ctx.thm_congr(th, th2)?)
                    }
                }
                (None, Some(th)) => {
                    let th_hd = ctx.thm_refl(lhs.clone());
                    Some(ctx.thm_congr(th_hd, th)?)
                }
                (Some(th1), Some(th2)) => Some(ctx.thm_congr(th1, th2)?),
            };
            Ok(step)
        } else {
            Ok(None)
        }
    }
}

impl<'a> Converter for CongrLHS<'a> {
    fn try_conv(&self, ctx: &mut k::Ctx, e: &k::Expr) -> Result<Option<k::Thm>> {
        if let Some((lhs, rhs)) = e.as_app() {
            let r1 = self.0.try_conv(ctx, lhs)?;
            let step = match r1 {
                None => None,
                Some(th) => {
                    if rhs.ty().is_type() {
                        Some(ctx.thm_congr_ty(th, rhs)?)
                    } else {
                        let th2 = ctx.thm_refl(rhs.clone());
                        Some(ctx.thm_congr(th, th2)?)
                    }
                }
            };
            Ok(step)
        } else {
            Ok(None)
        }
    }
}

impl<'a> Converter for CongrRHS<'a> {
    fn try_conv(&self, ctx: &mut k::Ctx, e: &k::Expr) -> Result<Option<k::Thm>> {
        if let Some((lhs, rhs)) = e.as_app() {
            let r2 = self.0.try_conv(ctx, rhs)?;
            let step = match r2 {
                None => None,
                Some(th) => {
                    let th_hd = ctx.thm_refl(lhs.clone());
                    Some(ctx.thm_congr(th_hd, th)?)
                }
            };
            Ok(step)
        } else {
            Ok(None)
        }
    }
}

impl Converter for BetaReduce {
    fn try_conv(&self, ctx: &mut k::Ctx, e: &k::Expr) -> Result<Option<k::Thm>> {
        Ok(ctx.thm_beta_conv(e).ok())
    }
}

// FIXME: also go in applications to reduce `(\x. u) a b c` into `u[x\a] b c`
impl Converter for BetaReduceRepeat {
    fn try_conv(&self, ctx: &mut k::Ctx, e: &k::Expr) -> Result<Option<k::Thm>> {
        let mut e = e.clone();
        let mut r = None;

        while let Some(th2) = BetaReduce.try_conv(ctx, &e)? {
            e = th2
                .concl()
                .unfold_eq()
                .ok_or_else(|| k::Error::new("converter yielded a non-equational theorem"))?
                .1
                .clone();
            // chain step with previous step(s)
            r = chain_res(ctx, r, Some(th2))?;
        }
        Ok(r)
    }
}

impl From<BetaReduce> for BasicConverter {
    fn from(b: BetaReduce) -> Self {
        BasicConverter::Beta(b)
    }
}
impl From<BetaReduceRepeat> for BasicConverter {
    fn from(b: BetaReduceRepeat) -> Self {
        BasicConverter::BetaRepeat(b)
    }
}

impl BasicConverter {
    /// Wrap the converter in a box.
    pub fn wrap<T: Converter + 'static>(x: T) -> Self {
        BasicConverter::Wrapped(k::Ref::new(x))
    }

    /// Beta-reduce.
    pub fn beta() -> Self {
        BetaReduce.into()
    }

    /// Beta-reduce repeatedly.
    pub fn beta_repeat() -> Self {
        BetaReduceRepeat.into()
    }
}

impl Converter for BasicConverter {
    fn try_conv(&self, ctx: &mut Ctx, e: &Expr) -> Result<Option<Thm>> {
        match self {
            BasicConverter::Nil => Ok(None),
            BasicConverter::Beta(b) => b.try_conv(ctx, e),
            BasicConverter::BetaRepeat(b) => b.try_conv(ctx, e),
            BasicConverter::Wrapped(b) => b.try_conv(ctx, e),
        }
    }
}

impl Converter for SeqConverter {
    fn try_conv(&self, ctx: &mut Ctx, e: &Expr) -> Result<Option<Thm>> {
        let repeat = self.repeat;

        // in case `repeat` is true
        let mut e = e.clone();
        let mut r = None;

        loop {
            let mut did_rw = false;

            // try converters one by one
            for c in &self.v {
                if let Some(th) = c.try_conv(ctx, &e)? {
                    e = th
                        .concl()
                        .unfold_eq()
                        .ok_or_else(|| k::Error::new("converter step should return an equality"))?
                        .1
                        .clone();
                    r = chain_res(ctx, r, Some(th))?;

                    did_rw = true;
                    break;
                }
            }

            if !did_rw || !repeat {
                break;
            }
        }
        Ok(r)
    }
}

impl SeqConverter {
    /// New combinator of rewriters.
    pub fn new() -> Self {
        Self {
            v: vec![],
            repeat: false,
        }
    }

    /// Add a sub-converter.
    pub fn add(&mut self, c: BasicConverter) {
        self.v.push(c);
    }

    /// Enable the `repeat` behavior on this converter.
    ///
    /// An expression will be repeatedly rewritten using any sub-converter
    /// until it reaches a normal form.
    pub fn repeat(&mut self) {
        self.repeat = true;
    }

    /// Add a list of sub-rewriters.
    pub fn extend<I>(&mut self, i: I)
    where
        I: IntoIterator<Item = BasicConverter>,
    {
        for x in i {
            self.v.push(x)
        }
    }
}
