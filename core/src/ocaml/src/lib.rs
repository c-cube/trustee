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

// ==== Context ====

/// A wrapper around the context.
#[derive(Debug, Clone)]
pub struct Ctx(Arc<Mutex<k::ExprManager>>);

unsafe extern "C" fn trustee_finalize_ctx(v: ocaml::Value) {
    let ptr: Pointer<Ctx> = Pointer::from_value(v);
    ptr.drop_in_place()
}

ocaml::custom_finalize!(Ctx, trustee_finalize_ctx);

/// Allocate a new context.
#[ocaml::func]
pub fn trustee_new_ctx() -> Pointer<Ctx> {
    let ctx = Ctx(Arc::new(Mutex::new(k::ExprManager::new())));
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
