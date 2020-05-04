use trustee::*;

#[test]
fn test_hashcons1() {
    let mut em = ExprManager::new();
    let b = em.mk_bool();
    let t1 = em.mk_arrow(b.clone(), b.clone());
    let t2 = em.mk_arrow(b.clone(), b.clone());
    assert_eq!(t1, t2);
}
