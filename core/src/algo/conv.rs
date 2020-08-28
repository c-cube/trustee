//! Converter.
//!
//! A converter is a function taking an expression `e`, and returning
//! an `Option<Thm>`. It returns `Some(… |- e = e2)` if `e` can be converted
//! into `e2`, `None` otherwise.

use crate::{kernel_of_trust as k, Ctx, Expr, Result, Thm};
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
fn chain_res(ctx: &mut k::Ctx, res1: Option<Thm>, res2: Option<Thm>) -> Result<Option<Thm>> {
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

/// Apply beta-reduction at root.
#[derive(Clone, Copy, Debug)]
pub struct BetaReduce;

impl Converter for BetaReduce {
    fn try_conv(&self, ctx: &mut k::Ctx, e: &k::Expr) -> Result<Option<k::Thm>> {
        Ok(ctx.thm_beta_conv(e).ok())
    }
}

/// Apply beta-reduction at root, repeatedly, until the root
/// is not a beta-redex anymore.
#[derive(Clone, Copy, Debug)]
pub struct BetaReduceRepeat;

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

/// A "basic" converter. Use a as component in `SeqConverter`.
#[derive(Debug, Clone)]
pub enum BasicConverter {
    Beta(BetaReduce),
    BetaRepeat(BetaReduceRepeat),
    Wrapped(k::Ref<dyn Converter>),
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
            BasicConverter::Beta(b) => b.try_conv(ctx, e),
            BasicConverter::BetaRepeat(b) => b.try_conv(ctx, e),
            BasicConverter::Wrapped(b) => b.try_conv(ctx, e),
        }
    }
}

/// A composite converter, made of smaller converters.
#[derive(Debug)]
pub struct SeqConverter {
    v: Vec<BasicConverter>,
    repeat: bool,
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
