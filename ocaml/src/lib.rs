use ocaml::{FromValue, Pointer};
use std::sync::{Arc, Mutex};
use trustee::kernel_of_trust as k;

// ==== Expr ====

/// A wrapper around an expression.
#[derive(Debug, Clone)]
pub struct Expr(k::Expr);

unsafe extern "C" fn trustee_finalize_expr(v: ocaml::Value) {
    let ptr: Pointer<Expr> = Pointer::from_value(v);
    ptr.drop_in_place()
}

ocaml::custom_finalize!(Expr, trustee_finalize_expr);

#[ocaml::func]
pub fn trustee_expr_to_string(v: Pointer<Expr>) -> String {
    v.as_ref().0.to_string()
}

#[ocaml::func]
pub fn trustee_expr_is_type(v: Pointer<Expr>) -> bool {
    v.as_ref().0.is_type()
}

#[ocaml::func]
pub fn trustee_expr_ty(v: Pointer<Expr>) -> Pointer<Expr> {
    match v.as_ref().0.ty_opt() {
        None => ocaml::Error::raise_failure("expr has no type"),
        Some(ty) => Pointer::alloc_custom(Expr(ty.clone())),
    }
}

// ==== Thm ====

/// A wrapper around an expression.
#[derive(Debug, Clone)]
pub struct Thm(k::Thm);

unsafe extern "C" fn trustee_finalize_thm(v: ocaml::Value) {
    let ptr: Pointer<Thm> = Pointer::from_value(v);
    ptr.drop_in_place()
}

ocaml::custom_finalize!(Thm, trustee_finalize_thm);

#[ocaml::func]
pub fn trustee_thm_to_string(v: Pointer<Thm>) -> String {
    v.as_ref().0.to_string()
}

#[ocaml::func]
pub fn trustee_thm_concl(v: Pointer<Thm>) -> Pointer<Expr> {
    let e = v.as_ref().0.concl();
    Pointer::alloc_custom(Expr(e.clone()))
}

#[ocaml::func]
pub fn trustee_thm_hyps(v: Pointer<Thm>) -> Vec<Pointer<Expr>> {
    let mut res = vec![];
    for x in v.as_ref().0.hyps() {
        res.push(Pointer::alloc_custom(Expr(x.clone())))
    }
    res
}

// ==== Context ====

/// A wrapper around the context.
#[derive(Debug, Clone)]
pub struct Ctx(Arc<Mutex<k::Ctx>>);

unsafe extern "C" fn trustee_finalize_ctx(v: ocaml::Value) {
    let ptr: Pointer<Ctx> = Pointer::from_value(v);
    ptr.drop_in_place()
}

ocaml::custom_finalize!(Ctx, trustee_finalize_ctx);

/// Allocate a new context.
#[ocaml::func]
pub fn trustee_new_ctx() -> Pointer<Ctx> {
    let ctx = Ctx(Arc::new(Mutex::new(k::Ctx::new())));
    let ptr = Pointer::alloc_custom(ctx);
    ptr
}

#[ocaml::func]
pub fn trustee_mk_type(mut ctx: Pointer<Ctx>) -> Pointer<Expr> {
    let ctx = ctx.as_mut().0.lock().unwrap();
    Pointer::alloc_custom(Expr(ctx.mk_ty()))
}

#[ocaml::func]
pub fn trustee_mk_bool(mut ctx: Pointer<Ctx>) -> Pointer<Expr> {
    let ctx = ctx.as_mut().0.lock().unwrap();
    Pointer::alloc_custom(Expr(ctx.mk_bool()))
}

#[ocaml::func]
pub fn trustee_mk_var(
    mut ctx: Pointer<Ctx>,
    s: &str,
    ty: Pointer<Expr>,
) -> Result<Pointer<Expr>, ocaml::Error> {
    let mut ctx = ctx.as_mut().0.lock().unwrap();
    let t = ctx.mk_var_str(&s, ty.as_ref().0.clone());
    Ok(Pointer::alloc_custom(Expr(t)))
}

#[ocaml::func]
pub fn trustee_mk_app(
    mut ctx: Pointer<Ctx>,
    e1: Pointer<Expr>,
    e2: Pointer<Expr>,
) -> Result<Pointer<Expr>, ocaml::Error> {
    let mut ctx = ctx.as_mut().0.lock().unwrap();
    let t = ctx.mk_app(e1.as_ref().0.clone(), e2.as_ref().0.clone())?;
    Ok(Pointer::alloc_custom(Expr(t)))
}

#[ocaml::func]
pub fn trustee_mk_arrow(
    mut ctx: Pointer<Ctx>,
    e1: Pointer<Expr>,
    e2: Pointer<Expr>,
) -> Result<Pointer<Expr>, ocaml::Error> {
    let mut ctx = ctx.as_mut().0.lock().unwrap();
    let t = ctx.mk_arrow(e1.as_ref().0.clone(), e2.as_ref().0.clone())?;
    Ok(Pointer::alloc_custom(Expr(t)))
}

#[ocaml::func]
pub fn trustee_mk_eq_app(
    mut ctx: Pointer<Ctx>,
    e1: Pointer<Expr>,
    e2: Pointer<Expr>,
) -> Result<Pointer<Expr>, ocaml::Error> {
    let mut ctx = ctx.as_mut().0.lock().unwrap();
    let t = ctx.mk_eq_app(e1.as_ref().0.clone(), e2.as_ref().0.clone())?;
    Ok(Pointer::alloc_custom(Expr(t)))
}

#[ocaml::func]
pub fn trustee_thm_assume(
    mut ctx: Pointer<Ctx>,
    e: Pointer<Expr>,
) -> Result<Pointer<Thm>, ocaml::Error> {
    let mut ctx = ctx.as_mut().0.lock().unwrap();
    let t = ctx.thm_assume(e.as_ref().0.clone())?;
    Ok(Pointer::alloc_custom(Thm(t)))
}

// === OPEN THEORY ====

/// A wrapper around the context.
#[derive(Debug, Clone)]
pub struct OT(Arc<Mutex<k::Ctx>>);

unsafe extern "C" fn trustee_finalize_ot(v: ocaml::Value) {
    let ptr: Pointer<OT> = Pointer::from_value(v);
    ptr.drop_in_place()
}

ocaml::custom_finalize!(OT, trustee_finalize_ot);

/// Parse OpenTheory
#[ocaml::func]
pub fn trustee_ot_parse(
    mut ctx: Pointer<Ctx>,
    s: &str,
) -> (Vec<Pointer<Expr>>, Vec<Pointer<Thm>>, Vec<Pointer<Thm>>) {
    use trustee_opentheory as open_theory;
    let mut ctx = ctx.as_mut().0.lock().unwrap();
    let mut vm = open_theory::VM::new(&mut ctx);
    let mut buf = std::io::BufReader::new(s.as_bytes());
    eprintln!("reading string (len {})", s.as_bytes().len());
    vm.parse_str(&mut buf).unwrap_or_else(|e| {
        let msg = format!("trustee_parse_ot: {}", e);
        ocaml::Error::raise_failure(&msg)
    });
    eprintln!("got OT article");
    let open_theory::Article { defs: v1, assumptions: v2, theorems: v3 } =
        vm.into_article();
    let v1: Vec<_> =
        v1.into_iter().map(|e| Pointer::alloc_custom(Expr(e.1))).collect();
    let v2: Vec<_> =
        v2.into_iter().map(|e| Pointer::alloc_custom(Thm(e))).collect();
    let v3: Vec<_> =
        v3.into_iter().map(|e| Pointer::alloc_custom(Thm(e))).collect();
    (v1, v2, v3).into()
}

/*
/// Parse OpenTheory
#[ocaml::func]
pub fn trustee_ot_parse(
    mut ctx: Pointer<Ctx>,
    s: &str,
) -> Result<(Vec<Expr>, Vec<Thm>, Vec<Thm>), ocaml::Error> {
    let mut ctx = ctx.as_mut().0.lock().unwrap();
    let mut vm = trustee::open_theory::VM::new(&mut ctx);
    let mut buf = std::io::BufReader::new(s.as_bytes());
    eprintln!("reading string (len {})", s.as_bytes().len());
    vm.parse_str(&mut buf).unwrap_or_else(|e| {
        let msg = format!("trustee_parse_ot: {}", e);
        ocaml::Error::raise_failure(&msg)
    });
    eprintln!("got OT article");
    let article = vm.into_article();
    let (v1, v2, v3) = article.get(&mut ctx);
    /*
    ocaml::local!(a1, a2, a3);
    a1 = (ocaml::Array::alloc(v1.len()) as ocaml::Array<Value>).to_value();
    a2 = (ocaml::Array::alloc(v2.len()) as ocaml::Array<Value>).to_value();
    a3 = (ocaml::Array::alloc(v3.len()) as ocaml::Array<Value>).to_value();
    for (i, x) in v1.into_iter().enumerate() {
        ocaml::Array::from_value(a1).set(i, Pointer::alloc_custom(Expr(x)))?
    }
    for (i, x) in v2.into_iter().enumerate() {
        ocaml::Array::from_value(a2).set(i, Pointer::alloc_custom(Thm(x)))?
    }
    for (i, x) in v3.into_iter().enumerate() {
        ocaml::Array::from_value(a3).set(i, Pointer::alloc_custom(Thm(x)))?
    }
    */
    let v1: Vec<_> = v1.into_iter().map(|e| Expr(e)).collect();
    let v2: Vec<_> = v2.into_iter().map(|e| Thm(e)).collect();
    let v3: Vec<_> = v3.into_iter().map(|e| Thm(e)).collect();
    // Ok(v1.to_value(), v2.to_value(), v3.to_value())
    Ok((v1, v2, v3))
}
*/
