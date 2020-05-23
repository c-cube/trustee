use trustee::*;

#[test]
fn test_hashcons1() {
    let mut em = ExprManager::new();
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
fn test_kind() {
    let em = ExprManager::new();
    let ty = em.mk_ty();
    let k = em.mk_kind();
    assert_eq!(&k, ty.ty());
}

#[test]
#[should_panic]
fn test_type_of_kind() {
    let em = ExprManager::new();
    let k = em.mk_kind();
    let _ = k.ty();
}

#[test]
fn test_apply() {
    let mut em = ExprManager::new();
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
    let mut em = ExprManager::new();
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
    let mut em = ExprManager::new();
    let b = em.mk_bool();
    let b2b = em.mk_arrow(b.clone(), b.clone()).unwrap();
    let p = em.mk_var_str("p", b2b);
    let a = em.mk_var_str("a", b);
    let pa2 = em.mk_app(p.clone(), a.clone()).unwrap();
    let pa = em.mk_app(p, a).unwrap();
    assert_eq!(&pa, &pa2);
    let th = em.thm_assume(&pa);
    assert_eq!(th.concl(), &pa);
    assert_eq!(th.hyps().len(), 1);
}
