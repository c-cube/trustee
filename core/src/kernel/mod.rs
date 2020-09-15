//! Kernel of Trust: Terms and Theorems.

pub type Ref<T> = std::rc::Rc<T>;
pub type WeakRef<T> = std::rc::Weak<T>;

pub use crate::error::{Error, Result};

pub mod ctx;
pub mod expr;
pub mod symbol;
pub mod thm;

pub use ctx::{Ctx, NewTypeDef, Subst};
pub use expr::{Expr, ExprView, Type, Var};
pub use symbol::Symbol;
pub use thm::Thm;
pub use ExprView::*;

pub type Fixity = crate::syntax::Fixity;
pub(crate) const FIXITY_EQ: Fixity = Fixity::Infix((30, 31));
pub(crate) const FIXITY_LAM: Fixity = Fixity::Binder((10, 11));
pub(crate) const FIXITY_PI: Fixity = Fixity::Binder((24, 25));
pub(crate) const FIXITY_ARROW: Fixity = Fixity::Infix((81, 80));

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_hashcons1() {
        let mut em = Ctx::new();
        let b = em.mk_bool();
        let t1 = em.mk_arrow(b.clone(), b.clone()).unwrap();
        let t2 = em.mk_arrow(b.clone(), b.clone()).unwrap();
        assert_eq!(t1, t2);
    }

    #[test]
    fn test_sym() {
        let s1 = Symbol::from_str("a");
        let s2 = Symbol::from_str("a");
        let s3 = Symbol::from_str("b");
        assert_eq!(s1, s2);
        assert_ne!(s1, s3);
        assert_eq!(s1.name(), "a");
    }

    #[test]
    #[should_panic]
    fn test_type_of_kind() {
        let em = Ctx::new();
        let k = em.mk_ty().ty().clone();
        let _ = k.ty();
    }

    #[test]
    fn test_apply() {
        let mut em = Ctx::new();
        let b = em.mk_bool();
        let b2b = em.mk_arrow(b.clone(), b.clone()).unwrap();
        let p = em.mk_var_str("p", b2b);
        let a = em.mk_var_str("a", b);
        let pa = em.mk_app(p, a).unwrap();
        assert!(match pa.view() {
            EApp(..) => true,
            _ => false,
        });
        assert!(pa.is_closed());
    }

    #[test]
    fn test_lambda() {
        let mut em = Ctx::new();
        let b = em.mk_bool();
        let b2b = em.mk_arrow(b.clone(), b.clone()).unwrap();
        let p = em.mk_var_str("p", b2b);
        let x = Var::from_str("x", b.clone());
        let ex = em.mk_var(x.clone());
        let body = em.mk_app(p, ex).unwrap();
        let f = em.mk_lambda(x, body).unwrap();
        assert!(match f.view() {
            ELambda(..) => true,
            _ => false,
        });
        assert!(f.is_closed());
        let (ty_args, ty_body) = f.ty().unfold_pi();
        assert_eq!(ty_args.len(), 1);
        assert_eq!(ty_args[0], &em.mk_bool());
        assert_eq!(ty_body, &em.mk_bool());
    }

    #[test]
    fn test_assume() {
        let mut em = Ctx::new();
        let b = em.mk_bool();
        let b2b = em.mk_arrow(b.clone(), b.clone()).unwrap();
        let p = em.mk_var_str("p", b2b);
        let a = em.mk_var_str("a", b);
        let pa2 = em.mk_app(p.clone(), a.clone()).unwrap();
        let pa = em.mk_app(p, a).unwrap();
        assert_eq!(&pa, &pa2);
        let th = em.thm_assume(pa.clone()).unwrap();
        assert_eq!(th.concl(), &pa);
        assert_eq!(th.hyps().len(), 1);
    }

    #[test]
    fn test_bool_eq_intro() -> Result<()> {
        let mut ctx = Ctx::new();
        let b = ctx.mk_bool();
        let e1 = ctx.mk_var_str("a", b.clone());
        let e2 = ctx.mk_var_str("b", b.clone());
        let th1 = ctx.thm_axiom(vec![e1.clone()], e2.clone())?;
        let th_a_a = ctx.thm_bool_eq_intro(th1.clone(), th1.clone())?;
        assert_eq!(th_a_a.concl(), &ctx.mk_eq_app(e2.clone(), e2.clone())?);
        assert_eq!(th_a_a.hyps().len(), 1);
        assert_eq!(th_a_a.hyps()[0].clone(), e1);
        Ok(())
    }
}
