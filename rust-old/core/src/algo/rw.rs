use super::conv::Converter;
///! ## Rewriting
///!
///! Rewriting algorithms.
use crate::{kernel as k, Ctx, Error, Expr, Result, Thm};

/// Rewrite `e` using the converter `conv`.
///
/// The rewriter is called on every non-type subterm, starting from the leaves.
pub fn rewrite_bottom_up(ctx: &mut Ctx, conv: &dyn Converter, e0: Expr) -> Result<Option<Thm>> {
    let mut th_eq = None; // stores proof for `e0 = e`
    let mut e = e0;

    use k::ExprView::*;

    macro_rules! update_th {
        ($res: expr, $els: block) => {
            match $res {
                None => $els,
                Some(th2) => {
                    e = {
                        let (_, b) = th2.concl().unfold_eq().ok_or_else(|| {
                            Error::new("rewrite function must return an equation")
                        })?;
                        b.clone()
                    };
                    th_eq = match th_eq {
                        None => Some(th2),
                        Some(th1) => Some(ctx.thm_trans(th1, th2)?),
                    }
                }
            }
        };
    };

    loop {
        match e.view() {
            EType | EKind | EVar(..) | EBoundVar(..) | EPi(..) => break,
            _ if e.ty().is_type() => break,
            EConst(..) => {
                let r = conv.try_conv(ctx, &e)?;
                update_th!(r, { break });
            }
            EApp(hd, a) => {
                let r1 = rewrite_bottom_up(ctx, conv, hd.clone())?;
                let r2 = rewrite_bottom_up(ctx, conv, a.clone())?;
                let step = match (r1, r2) {
                    (None, None) => None,
                    (Some(th), None) => {
                        if a.ty().is_type() {
                            Some(ctx.thm_congr_ty(th, a)?)
                        } else {
                            let th2 = ctx.thm_refl(a.clone());
                            Some(ctx.thm_congr(th, th2)?)
                        }
                    }
                    (None, Some(th)) => {
                        let th_hd = ctx.thm_refl(hd.clone());
                        Some(ctx.thm_congr(th_hd, th)?)
                    }
                    (Some(th1), Some(th2)) => Some(ctx.thm_congr(th1, th2)?),
                };
                update_th!(step, {});
                let step2 = conv.try_conv(ctx, &e)?;
                update_th!(step2, { break });
            }
            // TODO: rewrite under lambdas?
            //
            // But then we need either:
            // - introduce variable `x`, turn `λbody` into `x, body[0\x]`,
            //   rewrite, then use `thm_abs(x, norm(body))`
            ELambda(..) => break,
        };
    }
    Ok(th_eq)
}

/// A converter that uses bottom-up rewriting.
#[derive(Clone, Debug)]
pub struct BottomUpRwConv<'a>(pub &'a dyn Converter);

impl<'a> Converter for BottomUpRwConv<'a> {
    fn try_conv(&self, ctx: &mut Ctx, e: &Expr) -> Result<Option<Thm>> {
        rewrite_bottom_up(ctx, self.0, e.clone())
    }
}

impl<'a> BottomUpRwConv<'a> {
    /// New converter.
    pub fn new(c: &'a dyn Converter) -> Self {
        BottomUpRwConv(c)
    }
}
