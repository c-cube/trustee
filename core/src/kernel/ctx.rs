//! # Context for Expressions and Theorem.
//!
//!  The proof context is responsible for creating new terms and new theorems,
//!  in a way that ensures theorems are valid.

use super::{
    expr::{
        self, BoundVarContent, Const, ConstArgs, ConstImpl, ConstKind, ConstTag, DbIndex, Var,
        Vars, WExpr,
    },
    fixity_tbl::FixityTbl,
    symbol::{BuiltinSymbol, Symbol},
    thm::Exprs,
    Expr, ExprView, Proof, ProofView, Ref, Subst, Thm, Type, WeakRef,
};
use crate::{
    error::{Error, Result},
    errorstr,
    fnv::{self, FnvHashMap as HM},
    meta,
    rstr::RStr,
};
use smallvec::{smallvec, SmallVec};
use std::{fmt, rc::Rc, sync::atomic};

use ExprView::*;

// re-export
pub type Fixity = crate::syntax::Fixity;

/// Global manager for expressions, used to implement perfect sharing, allocating
/// new terms, etc.
pub struct Ctx(Box<CtxImpl>);

struct CtxImpl {
    /// Hashconsing table, with weak semantics.
    tbl: HM<ExprView, WExpr>,
    /// The equality symbol, lazily initialized.
    c_eq: Option<Const>,
    /// The type of types, lazily initialized
    e_ty: Option<Expr>,
    /// The boolean type, lazily initialized.
    e_bool: Option<Expr>,
    /// Pretty printing of constants
    fixities: FixityTbl,
    /// Temporary used to merge sets of hypotheses
    tmp_hyps: Exprs, // (smallvec)
    /// The defined chunks of code. These comprise some user defined tactics,
    /// derived rules, etc.
    meta_values: HM<RStr, meta::Value>,
    next_cleanup: usize,
    /// All the axioms created so far.
    axioms: Vec<Thm>,
    /// Generation for constants. Each constant is tagged with a generation
    /// so that two constants with the same name are not confused with
    /// one another.
    c_gen: u32,
    uid: u32, // Unique to this ctx
    /// If false, `thm_axiom` will fail.
    allow_new_axioms: bool,
    /// Enable proof generation?
    proof_gen: bool,
}

/// Helper for defining new type.
#[derive(Debug, Clone)]
pub struct NewTypeDef {
    /// the new type constructor
    pub tau: Const,
    /// Type variables, in the order they are abstracted on.
    pub ty_vars: Vars,
    /// Function from the general type to `tau`
    pub c_abs: Const,
    /// Function from `tau` back to the general type
    pub c_repr: Const,
    /// `abs_thm` is `|- abs (repr x) = x`
    pub abs_thm: Thm,
    pub abs_x: Var,
    /// `repr_thm` is `|- Phi x <=> repr (abs x) = x`
    pub repr_thm: Thm,
    pub repr_x: Var,
}

/// Period between 2 cleanups.
///
/// The cleanup of dead entries from the hashconsing table is done
/// every time `CLEANUP_PERIOD` new terms are added.
const CLEANUP_PERIOD: usize = 5_000;

// used to allocate unique ExprManager IDs
static EM_ID: atomic::AtomicUsize = atomic::AtomicUsize::new(0);

// helpers
impl Ctx {
    /// Create a new term manager with given initial capacity.
    pub fn with_capacity(bs: &BuiltinSymbol, n: usize) -> Self {
        let tbl = fnv::new_table_with_cap(n);
        // allocate new uid
        let uid = EM_ID.fetch_add(1, atomic::Ordering::SeqCst);
        if uid > std::u32::MAX as usize {
            panic!("allocated more than u32::MAX ExprManager, cannot allocate more");
        }
        let mut ctx = Ctx(Box::new(CtxImpl {
            tbl,
            tmp_hyps: smallvec![],
            c_gen: 0,
            meta_values: fnv::new_table_with_cap(16),
            next_cleanup: CLEANUP_PERIOD,
            axioms: vec![],
            uid: uid as u32,
            c_eq: None,
            e_ty: None,
            e_bool: None,
            allow_new_axioms: true,
            proof_gen: false,
            fixities: FixityTbl::default(),
        }));

        // insert initial builtins
        let kind = ctx.hashcons_builtin_(EKind, None);
        ctx.0.tbl.insert(kind.view().clone(), kind.weak());
        let ty = ctx.hashcons_builtin_(EType, Some(kind));
        ctx.0.tbl.insert(ty.view().clone(), ty.weak());
        ctx.0.e_ty = Some(ty.clone());

        // define bool
        let e_bool = {
            let name = Symbol::from_str(bs.bool);
            let c_bool = Const(Rc::new(ConstImpl {
                name,
                kind: ConstKind::TyConst,
                arity: 0,
                gen: 0,
                tag: ConstTag::Bool,
                proof: None,
            }));
            ctx.add_const_(c_bool.clone());
            ctx.mk_const_(c_bool, smallvec![]).unwrap()
        };
        ctx.0.e_bool = Some(e_bool.clone());

        // build `=`. It needs `builtins` to be set.
        let c_eq = {
            let name = Symbol::from_str(bs.eq);

            // db0 -> (db0 -> bool)
            let db0 = ctx.mk_bound_var(0, ty.clone());
            let ty = ctx.mk_arrow(db0.clone(), e_bool).unwrap();
            let ty = ctx.mk_arrow(db0, ty).unwrap();

            Const(Rc::new(ConstImpl {
                name,
                kind: ConstKind::ExprConst { ty },
                arity: 1,
                gen: 0,
                tag: ConstTag::Eq,
                proof: None,
            }))
        };
        ctx.add_const_(c_eq.clone());
        ctx.0.c_eq = Some(c_eq);

        ctx
    }

    /// New context with the default builtin symbols.
    pub fn new() -> Self {
        Self::with_capacity(&BuiltinSymbol::default(), 2_048)
    }

    /// Enable or disable proofs.
    pub fn enable_proof_recording(&mut self, b: bool) {
        self.0.proof_gen = b;
    }

    /// Add to the internal table, return the canonical representant.
    fn hashcons_(&mut self, ev: ExprView) -> Result<Expr> {
        let CtxImpl {
            tbl, next_cleanup, ..
        } = &mut *self.0;
        if let Some(v) = tbl.get(&ev) {
            if let Some(t) = WeakRef::upgrade(&v.0) {
                return Ok(Expr(t)); // still alive!
            }
        }

        // every n new terms, do a `cleanup`
        // TODO: maybe if last cleanups were ineffective, increase n,
        // otherwise decrease n (down to some min value)
        if *next_cleanup == 0 {
            // eprintln!("expr.hashcons: cleanup");
            self.cleanup();
        } else {
            *next_cleanup -= 1;
        }

        // need to insert the term, so first we need to compute its type.
        let ty = self.compute_ty_(&ev)?;
        let key = ev.clone();
        let e = Expr::make_(ev, self.0.uid, ty);
        //#[rustfmt::skip]
        //eprintln!("insert.expr.hashcons {:?} at {:?}", &e, e.0.as_ref() as *const _);
        //eprintln!("ev mem: {}", self.tbl.contains_key(&ev2));
        //eprintln!("btw table is {:#?}", &self.tbl);

        // lock table, again, but this time we'll write to it.
        // invariant: computing the type doesn't insert `e` in the table.
        let tbl = &mut self.0.tbl;
        tbl.insert(key, e.weak());
        //eprintln!("e.ev mem: {}", self.tbl.contains_key(&e.0.view));
        Ok(e)
    }

    /// Define a constant.
    fn add_const_(&mut self, c: Const) {
        let name = c.name.clone();
        self.0.meta_values.insert(name.to_rstr(), c.into());
    }

    fn hashcons_builtin_(&mut self, ev: ExprView, ty: Option<Expr>) -> Expr {
        let CtxImpl { tbl, uid, .. } = &mut *self.0;
        debug_assert!(!tbl.contains_key(&ev));
        let e = Expr::make_(ev, *uid, ty);
        tbl.insert(e.view().clone(), e.weak());
        e
    }

    #[inline]
    fn get_eq_(&self) -> &Const {
        self.0.c_eq.as_ref().expect("`eq` not initialized")
    }

    #[inline]
    fn get_ty_(&self) -> &Expr {
        self.0.e_ty.as_ref().expect("`ty` not initialized")
    }

    #[inline]
    fn get_bool_(&self) -> &Expr {
        self.0.e_bool.as_ref().expect("`bool` not initialized")
    }

    fn mk_const_with_(
        &mut self,
        s: Symbol,
        tag: ConstTag,
        arity: u8,
        kind: ConstKind,
        pr: Option<Proof>,
    ) -> Result<Const> {
        if let ConstKind::ExprConst { ty } = &kind {
            self.check_uid_(&ty);
            if ty.db_depth() > arity as u32 {
                return Err(errorstr!(
                    "cannot create constant with type {}",
                    self.pp_expr(&ty)
                ));
            }
            if ty.free_vars().next().is_some() {
                return Err(Error::new("cannot create constant with non-ground type"));
            }
        }

        self.0.c_gen = self.0.c_gen.wrapping_add(1); // next gen
        let gen = self.0.c_gen;
        let c = Const(Rc::new(ConstImpl {
            name: s,
            gen,
            tag,
            proof: pr,
            arity,
            kind,
        }));
        self.add_const_(c.clone());
        Ok(c)
    }

    // helper to create type constants
    fn mk_new_ty_const_(
        &mut self,
        s: impl Into<Symbol>,
        arity: impl Into<usize>,
        pr: Option<Proof>,
    ) -> Result<Const> {
        let arity = arity.into();
        if arity > u8::MAX as usize {
            return Err(Error::new("arity for type constant is too high"));
        }
        let arity = arity as u8;
        self.mk_const_with_(s.into(), ConstTag::None, arity, ConstKind::TyConst, pr)
    }

    #[inline]
    fn check_uid_(&self, e: &Expr) {
        assert!(self.0.uid == e.ctx_uid()); // term should belong to this ctx
    }

    #[inline]
    fn check_thm_uid_(&self, th: &Thm) {
        assert!(self.0.uid == th.0.ctx_uid); // theorem should belong to this ctx
    }

    // compute the type for this expression. This is done at hashconsing time.
    fn compute_ty_(&mut self, e: &ExprView) -> Result<Option<Expr>> {
        Ok(match e {
            EKind => None,
            EType => Some(self.get_ty_().clone()),
            EConst(c, args) => match &c.kind {
                ConstKind::TyConst => Some(self.get_ty_().clone()),
                ConstKind::ExprConst { ty } => {
                    // check arity
                    let n_args = args.len();
                    if n_args != c.arity as usize {
                        return Err(errorstr!(
                            "constant {} requires {} arguments, got {}",
                            c.name.name(),
                            c.arity,
                            n_args
                        ));
                    }
                    // substitute arguments in `ty`
                    let ty_res = self.subst_db_(&ty, 0, &args[..])?;
                    assert!(ty_res.is_closed());
                    Some(ty_res)
                }
            },
            EVar(v) => Some(v.ty.clone()),
            EBoundVar(v) => Some(v.ty.clone()),
            ELambda(v_ty, body) => {
                // type of `λx:a. t` is `a-> typeof(b)`.
                Some(self.hashcons_(EArrow(v_ty.clone(), body.ty().clone()))?)
            }
            EArrow(..) => Some(self.get_ty_().clone()),
            EApp(f, arg) => match f.ty().view() {
                EArrow(ty_arg_f, ty_body_f) => {
                    // rule: `f: a -> b`, `arg: a` ==> `f arg : b`
                    if ty_arg_f != arg.ty() {
                        return Err(Error::new("apply: incompatible types"));
                    }
                    Some(ty_body_f.clone())
                }
                _ => return Err(Error::new("cannot apply term with a non-arrow type")),
            },
        })
    }

    /// Replace `DB_i` in `t` by `args[i]`, under `k` intermediate binders.
    fn subst_db_(&mut self, t: &Expr, k: u32, args: &[Expr]) -> Result<Expr> {
        if t.is_closed() || args.len() == 0 {
            return Ok(t.clone()); // shortcut
        }

        Ok(match t.view() {
            EKind | EType | EConst(..) => t.clone(),
            EApp(a, b) => {
                let a2 = self.subst_db_(a, k, args)?;
                let b2 = self.subst_db_(b, k, args)?;
                if a == &a2 && b == &b2 {
                    t.clone() // no need to do hashconsing
                } else {
                    self.hashcons_(EApp(a2, b2))?
                }
            }
            EArrow(a, b) => {
                let a2 = self.subst_db_(a, k, args)?;
                let b2 = self.subst_db_(b, k, args)?;
                if a == &a2 && b == &b2 {
                    t.clone() // no need to do hashconsing
                } else {
                    self.hashcons_(EArrow(a2, b2))?
                }
            }
            ELambda(v_ty, body) => {
                let v_ty2 = self.subst_db_(v_ty, k, args)?;
                let body2 = self.subst_db_(body, k + 1, args)?;
                if v_ty == &v_ty2 && body == &body2 {
                    t.clone() // no need to do hashconsing
                } else {
                    self.hashcons_(ELambda(v_ty2, body2))?
                }
            }
            EVar(v) => {
                let v2 = Var {
                    ty: self.subst_db_(&v.ty, k, args)?,
                    name: v.name().clone(),
                };
                if v2.ty == v.ty {
                    t.clone() // no need to do hashconsing
                } else {
                    self.hashcons_(EVar(v2))?
                }
            }
            EBoundVar(v) if v.idx >= k && v.idx < k + (args.len() as u32) => {
                // `v` refers to a variable in `args.
                // substitute `v` for this variable's mapping `u`,
                // but shifting `u` by `k` to
                // account for the `k` intermediate binders we just traversed.
                let u = &args[(v.idx - k) as usize];
                self.shift_(u, k, 0)?
            }
            EBoundVar(v) if v.idx > k + (args.len() as u32) => {
                // need to unshift by `args.len()`, since we remove that many
                // binders and this is a free variable
                let shift_by = args.len() as u32;
                let v2 = BoundVarContent {
                    idx: v.idx - shift_by,
                    ty: self.subst_db_(&v.ty, k, args)?,
                };
                self.hashcons_(EBoundVar(v2))?
            }
            EBoundVar(v) => {
                // variable bound within the `k` binders we traversed, only
                // modify the type.
                debug_assert!(v.idx < k);
                let v2 = BoundVarContent {
                    idx: v.idx,
                    ty: self.subst_db_(&v.ty, k, args)?,
                };
                if v2.ty == v.ty {
                    t.clone() // no need to do hashconsing
                } else {
                    self.hashcons_(EBoundVar(v2))?
                }
            }
        })
    }

    /// Shift free DB vars by `n` under `k` intermediate binders.
    ///
    /// examples:
    /// - `shift (lambda. db0 db1 = db2) 5 1` is `lambda. db0 db1 = db7`,
    /// - `shift (lambda. f db3 db1) 5 1` is `lambda. f db8 db1`.
    fn shift_(&mut self, t: &Expr, n: DbIndex, k: DbIndex) -> Result<Expr> {
        if n == 0 || t.is_closed() {
            return Ok(t.clone()); // shortcut for identity
        }

        let ev = t.view();
        Ok(match ev {
            EKind | EType | EConst(..) => t.clone(),
            EApp(..) | ELambda(..) | EArrow(..) | EVar(..) => {
                let ev2 = ev.map(|u, k| self.shift_(u, n, k), k)?;
                self.hashcons_(ev2)?
            }
            EBoundVar(v) if v.idx < k => {
                // keep `v`, as it's bound, but update its type
                let v = BoundVarContent {
                    idx: v.idx,
                    ty: self.shift_(&v.ty, n, k)?,
                };
                self.hashcons_(EBoundVar(v))?
            }
            EBoundVar(v) => {
                // shift bound var by `n`
                let ty = self.shift_(&v.ty, n, k)?;
                self.hashcons_(EBoundVar(BoundVarContent { idx: v.idx + n, ty }))?
            }
        })
    }

    /// Cleanup terms that are only referenced by the hashconsing table.
    ///
    /// This is done regularly when new terms are created, but one can
    /// also call `cleanup` manually.
    ///
    /// We also cleanup the fixity table.
    pub fn cleanup(&mut self) {
        self.0.next_cleanup = CLEANUP_PERIOD;

        self.0.tbl.retain(|_, v| {
            // if `v` is not used anywhere else, it's the only
            // references and should have a strong count of 1.
            // This is thread safe as the only way this is 1 is if it's already
            // not referenced anywhere, and we don't provide any way to produce
            // a weak ref.
            let n = WeakRef::strong_count(&v.0);
            n > 0
        });

        self.0.fixities.cleanup();
    }

    /// Make a lambda term.
    fn mk_lambda_(&mut self, ty_var: Type, body: Expr) -> Result<Expr> {
        self.check_uid_(&ty_var);
        self.check_uid_(&body);
        self.hashcons_(ELambda(ty_var, body))
    }

    /// `abs_on_(vars, e)` replaces each free variable `vars[i]` by `db_i` in `e`.
    ///
    /// The de Bruijn indices are shifted as needed when the free
    /// variable occurs under a binder.
    fn abs_on_(&mut self, vars: &[Var], body: Expr) -> Result<Expr> {
        self.check_uid_(&body);

        let n_vars = vars.len();
        if n_vars == 0 {
            return Ok(body.clone());
        } else if n_vars > u32::MAX as usize {
            return Err(Error::new("abs_on_: far too many variables"));
        }

        let mut subst: SmallVec<[(Var, Expr); 3]> = SmallVec::with_capacity(n_vars);
        for (i, v_i) in vars.iter().rev().enumerate() {
            let v_i_ty = &v_i.ty;
            self.check_uid_(v_i_ty);
            if !v_i_ty.is_closed() {
                return Err(Error::new("mk_abs: var has non-closed type"));
            }

            // replace `v_i` with `db_i` in `body` (counting from the end).
            // This should also take care of shifting the DB by `n_vars` as appropriate.
            let db_i = self.mk_bound_var(i as u32, v_i_ty.clone());
            subst.push((v_i.clone(), db_i));
        }
        let body = self.shift_(&body, n_vars as u32, 0)?;
        self.subst(&body, &subst[..])
    }

    /// Make a constant term.
    fn mk_const_(&mut self, c: Const, args: ConstArgs) -> Result<Expr> {
        for a in &args[..] {
            self.check_uid_(a);
        }
        self.hashcons_(EConst(c, args))
    }
}

// public interface
impl Ctx {
    /// Return a pretty printable object for this expression.
    pub fn pp_expr<'a>(&'a self, e: &Expr) -> impl fmt::Display + 'a {
        ExprWithCtx(e.clone(), self)
    }

    /// Get the `=` constant. It has arity 1.
    #[inline]
    pub fn mk_c_eq(&mut self) -> Const {
        self.get_eq_().clone()
    }

    /// Build the expression `=_α` for equality of type α.
    pub fn mk_eq(&mut self, ty: Type) -> Expr {
        let c = self.mk_c_eq();
        debug_assert_eq!(1, c.arity);
        self.mk_const_(c, smallvec![ty]).unwrap()
    }

    /// Build the expression `a = b`.
    ///
    /// Fails if `a` and `b` do not have the same type.
    pub fn mk_eq_app(&mut self, a: Expr, b: Expr) -> Result<Expr> {
        self.check_uid_(&a);
        self.check_uid_(&b);
        if a.ty() != b.ty() {
            return Err(Error::new("mk_eq: incompatible_types"));
        }
        let eq = self.mk_eq(a.ty().clone());
        self.mk_app_l(eq, &[a, b])
    }

    /// For each pair `(x,u)` in `subst`, replace instances of the free
    /// variable `x` by `u` in `t`.
    pub fn subst(&mut self, t: &Expr, subst: &[(Var, Expr)]) -> Result<Expr> {
        self.check_uid_(t);
        struct Replace<'a> {
            // cache, relative to depth
            ctx: &'a mut Ctx,
            subst: &'a [(Var, Expr)],
        }

        impl<'a> Replace<'a> {
            // replace in `t`, under `k` intermediate binders.
            fn replace(&mut self, t: &Expr, k: DbIndex) -> Result<Expr> {
                //eprintln!("> replace `{:?}` k={}", t, k);
                let r = match t.view() {
                    // fast cases first
                    EType | EKind | EConst(..) => t.clone(),
                    EVar(v) => {
                        // lookup `v` in `subst`
                        for (v2, u2) in self.subst.iter() {
                            if v == v2 {
                                let u3 = self.ctx.shift_(u2, k, 0)?;
                                //eprintln!(
                                //    ">> replace {:?} with {:?}, shifted[{}] into {:?}",
                                //    v, u2, k, u3
                                //);
                                return Ok(u3);
                            }
                        }
                        // otherwise just substitute in the type
                        let v2 = Var {
                            name: v.name.clone(),
                            ty: self.replace(&v.ty, k)?,
                        };
                        self.ctx.mk_var(v2)
                    }
                    ev => {
                        // shallow map + cache
                        let uv = ev.map(|sub, k| self.replace(sub, k), k)?;
                        self.ctx.hashcons_(uv)?
                    }
                };
                //eprintln!("< replace `{:?}` k={}\n  yields `{:?}`", t, k, r);
                Ok(r)
            }
        }

        subst.iter().for_each(|(v, t)| {
            self.check_uid_(&v.ty);
            self.check_uid_(t)
        });

        debug_assert!(subst.iter().all(|(v, t)| &v.ty == t.ty())); // type preservation
        let mut replace = Replace { ctx: self, subst };
        //eprintln!("### start replace\n  `{:?}`,\n  subst {:?}", t, subst);
        replace.replace(t, 0)
    }

    /// The type of types. This has type `self.mk_kind()`.
    #[inline]
    pub fn mk_ty(&self) -> Expr {
        self.get_ty_().clone()
    }

    /// The type of booleans.
    #[inline]
    pub fn mk_bool(&self) -> Expr {
        self.get_bool_().clone()
    }

    /// Apply `a` to `b`.
    pub fn mk_app(&mut self, a: Expr, b: Expr) -> Result<Expr> {
        self.check_uid_(&a);
        self.check_uid_(&b);
        self.hashcons_(EApp(a, b))
    }

    /// Apply `f` to the given arguments.
    pub fn mk_app_l(&mut self, f: Expr, args: &[Expr]) -> Result<Expr> {
        let mut e = f;
        for x in args {
            let e2 = e.clone();
            e = self.mk_app(e2, x.clone())?;
        }
        Ok(e)
    }

    /// Make a free variable.
    pub fn mk_var(&mut self, v: Var) -> Expr {
        self.check_uid_(&v.ty);
        self.hashcons_(EVar(v)).expect("mk_var can't fail")
    }

    /// Make a constant expression.
    ///
    /// This takes a constant (possibly polymorphic) and turns it into a term
    /// of a given type.
    #[inline]
    pub fn mk_const(&mut self, c: Const, args: SmallVec<[Expr; 3]>) -> Result<Expr> {
        self.mk_const_(c, args)
    }

    /// Make a free variable.
    pub fn mk_var_str(&mut self, name: &str, ty_var: Type) -> Expr {
        self.check_uid_(&ty_var);
        self.mk_var(Var::from_str(name, ty_var))
    }

    /// Make a free type variable.
    pub fn mk_ty_var_str(&mut self, name: &str) -> Expr {
        let ty = self.mk_ty();
        self.mk_var_str(name, ty)
    }

    /// Make a bound variable with given type and index.
    pub fn mk_bound_var(&mut self, idx: DbIndex, ty_var: Type) -> Expr {
        self.check_uid_(&ty_var);
        self.hashcons_(EBoundVar(BoundVarContent { idx, ty: ty_var }))
            .expect("mk_bound_var cannot fail")
    }

    /// Make a lambda term by abstracting on `v`.
    pub fn mk_lambda(&mut self, v: Var, body: Expr) -> Result<Expr> {
        self.check_uid_(&v.ty);
        self.check_uid_(&body);
        let v_ty = v.ty.clone();
        let body = self.abs_on_(&[v], body)?;
        self.mk_lambda_(v_ty, body)
    }

    /// Make a lambda term by abstracting on `vars`.
    pub fn mk_lambda_l(&mut self, vars: &[Var], body: Expr) -> Result<Expr> {
        self.check_uid_(&body);
        // do the shifting only once!
        let mut body = self.abs_on_(vars, body)?;
        for v in vars.iter().rev() {
            self.check_uid_(&v.ty);
            body = self.mk_lambda_(v.ty.clone(), body)?;
        }
        Ok(body)
    }

    /// Make a lambda term, where `body` already contains the DB index 0.
    pub fn mk_lambda_db(&mut self, ty_v: Expr, body: Expr) -> Result<Expr> {
        self.check_uid_(&ty_v);
        self.check_uid_(&body);
        self.mk_lambda_(ty_v, body)
    }

    #[inline]
    pub fn abs_on_fvars(&mut self, vars: &[Var], body: Expr) -> Result<Expr> {
        self.abs_on_(vars, body)
    }

    /*
    /// Make a pi term by abstracting on `v`.
    pub fn mk_pi(&mut self, v: Var, body: Expr) -> Result<Expr> {
        self.check_uid_(&v.ty);
        self.check_uid_(&body);
        let v_ty = v.ty.clone();
        let body = self.abs_on_(v, body)?;
        self.mk_pi_(v_ty, body)
    }

    /// Bind several variables at once.
    pub fn mk_pi_l(&mut self, vars: &[Var], body: Expr) -> Result<Expr> {
        let mut e = body;
        // TODO: substitute more efficiently (with a stack, rather than one by one)?
        // right-assoc
        for v in vars.iter().rev() {
            e = self.mk_pi(v.clone(), e)?;
        }
        Ok(e)
    }
        */

    /// Make an arrow `a -> b` term.
    pub fn mk_arrow(&mut self, ty1: Expr, ty2: Expr) -> Result<Expr> {
        // need to shift ty2 by 1 to account for the Π binder.
        self.check_uid_(&ty1);
        self.check_uid_(&ty2);
        self.hashcons_(EArrow(ty1, ty2))
    }

    /// Declare a new constant with given name and type.
    ///
    /// Fails if the type is not ground.
    /// This constant has no axiom associated to it, it is entirely opaque.
    ///
    /// Also returns the list of free variables abstracted upon,
    /// in the right order.
    pub fn mk_new_const(
        &mut self,
        s: impl Into<Symbol>,
        ty: Type,
        pr: Option<Proof>,
    ) -> Result<(Const, Vars)> {
        let arity = ty.db_depth();
        if arity > u8::MAX as u32 {
            return Err(Error::new("mk_new_const: arity is too high"));
        }
        let arity = arity as u8;

        let mut fvars: Vars = ty.free_vars().cloned().collect();
        fvars.sort_unstable();
        fvars.dedup();

        let ty = self.abs_on_(&fvars[..], ty)?;

        let c = self.mk_const_with_(
            s.into(),
            ConstTag::None,
            arity,
            ConstKind::ExprConst { ty },
            pr,
        )?;
        Ok((c, fvars))
    }

    // TODO: return a result, and only allow infix/binder if type is inferrable?
    /// Change the fixity of a given constant.
    ///
    /// Does nothing if the constant is not defined.
    pub fn set_fixity(&mut self, s: &str, f: Fixity) -> Result<()> {
        if let Some(meta::Value::Const(c)) = self.0.meta_values.get(s) {
            self.0.fixities.set_fixity(c.clone(), f);
            return Ok(());
        }
        Err(errorstr!("set_fixity: unknown constant `{}`", s))
    }

    /// Find a meta value by name. Returns `None` if the binding is absent.
    #[inline]
    pub fn find_meta_value(&self, s: &str) -> Option<&meta::Value> {
        self.0.meta_values.get(s)
    }

    /// Set a meta value by name.
    #[inline]
    pub fn set_meta_value(&mut self, s: impl Into<RStr>, v: meta::Value) {
        self.0.meta_values.insert(s.into(), v);
    }

    /// Iterate over all meta values.
    pub fn iter_meta_values(&self) -> impl Iterator<Item = (&str, &meta::Value)> {
        self.0.meta_values.iter().map(|(s, v)| (s.get(), v))
    }

    /// Find a constant by name. Returns `None` if no such constant exists.
    pub fn find_const(&self, s: &str) -> Option<&Const> {
        if let Some(meta::Value::Const(c)) = self.0.meta_values.get(s) {
            Some(c)
        } else {
            None
        }
    }

    #[inline]
    pub fn find_fixity(&self, c: &Const) -> Option<&Fixity> {
        self.0.fixities.find_fixity(c)
    }

    pub fn iter_consts(&self) -> impl Iterator<Item = (&str, &Expr)> {
        self.iter_meta_values()
            .filter_map(|(k, v)| v.as_expr().map(move |e| (k, e)))
    }

    /// Define a named lemma.
    ///
    /// If another lemma with the same name exists, it will be replaced.
    pub fn define_lemma(&mut self, name: impl Into<RStr>, th: Thm) {
        self.0.meta_values.insert(name.into(), meta::Value::Thm(th));
    }

    /// Find a lemma by name. Returns `None` if no such theorem exists.
    pub fn find_lemma(&self, s: &str) -> Option<&Thm> {
        self.0.meta_values.get(s).and_then(|v| v.as_thm())
    }

    /// Iterate over all lemmas.
    pub fn iter_lemmas(&self) -> impl Iterator<Item = (&str, &Thm)> {
        self.iter_meta_values()
            .filter_map(|(s, v)| v.as_thm().map(move |v| (s, v)))
    }

    /// `assume F` is `F |- F`.
    ///
    /// This fails if `F` is not a boolean.
    pub fn thm_assume(&mut self, e: Expr) -> Result<Thm> {
        self.check_uid_(&e);
        if e.ty() != self.get_bool_() {
            return Err(Error::new("cannot assume non-boolean expression"));
        }
        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::Assume(e.clone())))
        } else {
            None
        };

        let th = Thm::make_(e.clone(), self.0.uid, smallvec![e], pr);
        Ok(th)
    }

    /// `refl t` is `|- t=t`
    pub fn thm_refl(&mut self, e: Expr) -> Thm {
        self.check_uid_(&e);
        let t = self.mk_eq_app(e.clone(), e.clone()).expect("refl");
        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::Refl(e)))
        } else {
            None
        };
        Thm::make_(t, self.0.uid, smallvec![], pr)
    }

    /// `trans (F1 |- a=b) (F2 |- b'=c)` is `F1, F2 |- a=c`.
    ///
    /// Can fail if the conclusions don't match properly.
    pub fn thm_trans(&mut self, th1: Thm, th2: Thm) -> Result<Thm> {
        self.check_thm_uid_(&th1);
        self.check_thm_uid_(&th2);
        let (a, b) = th1
            .concl()
            .unfold_eq()
            .ok_or_else(|| Error::new("trans: th1 must be an equation"))?;
        let (b2, c) = th2
            .concl()
            .unfold_eq()
            .ok_or_else(|| Error::new("trans: th2 must be an equation"))?;
        if b != b2 {
            return Err(Error::new("trans: th1 and th2's conclusions do not align"));
        }

        let eq_a_c = self.mk_eq_app(a.clone(), c.clone())?;
        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::Trans(th1.clone(), th2.clone())))
        } else {
            None
        };
        let hyps = self.merge_hyps_th(th1, th2);
        let th = Thm::make_(eq_a_c, self.0.uid, hyps, pr);
        Ok(th)
    }

    /// `congr (F1 |- f=g) (F2 |- t=u)` is `F1, F2 |- f t=g u`
    pub fn thm_congr(&mut self, th1: Thm, th2: Thm) -> Result<Thm> {
        self.check_thm_uid_(&th1);
        self.check_thm_uid_(&th2);
        let (f, g) = th1
            .concl()
            .unfold_eq()
            .ok_or_else(|| Error::new("congr: th1.concl must be an equality"))?;
        let (t, u) = th2
            .concl()
            .unfold_eq()
            .ok_or_else(|| Error::new("congr: th2.concl must be an equality"))?;
        let ft = self.mk_app(f.clone(), t.clone())?;
        let gu = self.mk_app(g.clone(), u.clone())?;
        let eq = self.mk_eq_app(ft, gu)?;
        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::Congr(th1.clone(), th2.clone())))
        } else {
            None
        };
        let hyps = self.merge_hyps_th(th1, th2);
        Ok(Thm::make_(eq, self.0.uid, hyps, pr))
    }

    /// `congr_ty (F1 |- f=g) ty` is `F1 |- f ty=g ty`
    pub fn thm_congr_ty(&mut self, mut th: Thm, ty: &Expr) -> Result<Thm> {
        self.check_thm_uid_(&th);
        self.check_uid_(ty);
        let (f, g) =
            th.0.concl
                .unfold_eq()
                .ok_or_else(|| Error::new("congr_ty: th.concl must be an equality"))?;
        if ty.view() == &EKind || !ty.ty().is_type() {
            return Err(Error::new("congr_ty: argument must be a type"));
        }
        let ft = self.mk_app(f.clone(), ty.clone())?;
        let gu = self.mk_app(g.clone(), ty.clone())?;
        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::CongrTy(th.clone(), ty.clone())))
        } else {
            None
        };
        let eq = self.mk_eq_app(ft, gu)?;
        {
            let thref = Ref::make_mut(&mut th.0);
            thref.concl = eq;
            thref.proof = pr;
        }
        Ok(th)
    }

    /// `instantiate thm σ` produces `Fσ |- Gσ`  where `thm` is `F |- G`
    ///
    /// Returns an error if the substitution is not closed.
    pub fn thm_instantiate(&mut self, mut th: Thm, subst: Subst) -> Result<Thm> {
        self.check_thm_uid_(&th);
        if subst.iter().any(|(_, t)| !t.is_closed()) {
            return Err(Error::new(
                "instantiate: substitution contains non-closed binding",
            ));
        }

        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::Instantiate(
                th.clone(),
                subst.clone(),
            )))
        } else {
            None
        };

        {
            let thref = Ref::make_mut(&mut th.0);
            thref.concl = self.subst(&thref.concl, &subst[..])?;
            thref.proof = pr;
            for t in thref.hyps.iter_mut() {
                *t = self.subst(t, &subst[..])?;
            }
        }
        Ok(th)
    }

    /// `abs x (F |- t=u)` is `F |- (λx.t)=(λx.u)`
    ///
    /// Fails if `x` occurs freely in `F`.
    pub fn thm_abs(&mut self, v: &Var, mut thm: Thm) -> Result<Thm> {
        self.check_uid_(&v.ty);
        self.check_thm_uid_(&thm);
        if expr::free_vars_iter(thm.0.hyps.iter()).any(|v2| v == v2) {
            return Err(Error::new("abs: variable occurs in one of the hypothesis"));
        }

        let (t, u) = thm
            .0
            .concl
            .unfold_eq()
            .ok_or_else(|| Error::new("abs: thm conclusion should be an equality"))?;

        let lam_t = self.mk_lambda(v.clone(), t.clone())?;
        let lam_u = self.mk_lambda(v.clone(), u.clone())?;
        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::Abs(v.clone(), thm.clone())))
        } else {
            None
        };
        let eq = self.mk_eq_app(lam_t, lam_u)?;
        {
            let thref = Ref::make_mut(&mut thm.0); // clone or acquire
            thref.concl = eq;
            thref.proof = pr;
        }
        Ok(thm)
    }

    /// Merge sets of hypothesis in a sorted fashion.
    fn merge_hyps_iter_<I1, I2>(&mut self, mut i1: I1, mut i2: I2) -> Exprs
    where
        I1: Iterator<Item = Expr>,
        I2: Iterator<Item = Expr>,
    {
        let tmp_hyps = &mut self.0.tmp_hyps;
        tmp_hyps.clear();

        let mut cur1 = i1.next();
        let mut cur2 = i2.next();

        loop {
            match (cur1, cur2) {
                (None, None) => break,
                (Some(x), None) => {
                    tmp_hyps.push(x);
                    cur1 = i1.next();
                    cur2 = None;
                }
                (None, Some(x)) => {
                    tmp_hyps.push(x);
                    cur1 = None;
                    cur2 = i2.next();
                }
                (Some(x1), Some(x2)) => {
                    if x1 == x2 {
                        // deduplication
                        tmp_hyps.push(x1);
                        cur1 = i1.next();
                        cur2 = i2.next();
                    } else if x1 < x2 {
                        tmp_hyps.push(x1);
                        cur1 = i1.next();
                        cur2 = Some(x2);
                    } else {
                        tmp_hyps.push(x2);
                        cur1 = Some(x1);
                        cur2 = i2.next();
                    }
                }
            }
        }
        tmp_hyps.clone()
    }

    /// Merge sets of hypothesis of the two theorems.
    fn merge_hyps_th(&mut self, mut th1: Thm, mut th2: Thm) -> Exprs {
        use std::mem::swap;

        let mut v1 = smallvec![];
        let mut v2 = smallvec![];

        if th1.0.hyps.is_empty() {
            // take or copy th2.hyps
            match Ref::get_mut(&mut th2.0) {
                None => th2.0.hyps.clone(),
                Some(th) => {
                    swap(&mut v2, &mut th.hyps);
                    v2
                }
            }
        } else if th2.0.hyps.is_empty() {
            // take or copy th1.hyps
            match Ref::get_mut(&mut th1.0) {
                None => th1.0.hyps.clone(),
                Some(th) => {
                    swap(&mut v1, &mut th.hyps);
                    v1
                }
            }
        } else {
            // try to reuse th1.hyps and th2.hyps
            match (Ref::get_mut(&mut th1.0), Ref::get_mut(&mut th2.0)) {
                (Some(th1), Some(th2)) => {
                    swap(&mut v1, &mut th1.hyps);
                    swap(&mut v2, &mut th2.hyps);
                    self.merge_hyps_iter_(v1.into_iter(), v2.into_iter())
                }
                (Some(th1), None) => {
                    swap(&mut v1, &mut th1.hyps);
                    self.merge_hyps_iter_(v1.into_iter(), th2.0.hyps.iter().cloned())
                }
                (None, Some(th2)) => {
                    swap(&mut v2, &mut th2.hyps);
                    self.merge_hyps_iter_(th1.0.hyps.iter().cloned(), v2.into_iter())
                }
                (None, None) => {
                    self.merge_hyps_iter_(th1.0.hyps.iter().cloned(), th2.0.hyps.iter().cloned())
                }
            }
        }
    }

    /// `cut (F1 |- b) (F2, b |- c)` is `F1, F2 |- c`
    ///
    /// This fails if `b` does not occur _syntactically_ in the hypothesis
    /// of the second theorem.
    ///
    /// NOTE: this is not strictly necessary, as it's not an axiom in HOL light,
    /// but we include it here anyway.
    pub fn thm_cut(&mut self, th1: Thm, th2: Thm) -> Result<Thm> {
        self.check_thm_uid_(&th1);
        self.check_thm_uid_(&th2);
        let th1_c = th1.0.concl.clone();
        if !th2.0.hyps.contains(&th1_c) {
            return Err(Error::new(
                "cut: th2's hyps do not contain th1's conclusion",
            ));
        }
        let th2_c = th2.0.concl.clone();

        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::Cut(th1.clone(), th2.clone())))
        } else {
            None
        };

        let hyps = {
            self.merge_hyps_iter_(
                th1.0.hyps.iter().cloned(),
                th2.0.hyps.iter().filter(|u| **u != th1_c).cloned(),
            )
        };
        let th_res = Thm::make_(th2_c, self.0.uid, hyps, pr);
        Ok(th_res)
    }

    /// `bool_eq (F1 |- a) (F2 |- a=b)` is `F1, F2 |- b`.
    /// This is the boolean equivalent of transitivity.
    pub fn thm_bool_eq(&mut self, th1: Thm, th2: Thm) -> Result<Thm> {
        self.check_thm_uid_(&th1);
        self.check_thm_uid_(&th2);
        let th2_c = &th2.0.concl;
        let (a, b) = th2_c
            .unfold_eq()
            .filter(|(a, _)| a.ty() == self.get_bool_())
            .ok_or_else(|| {
                //Some((a, b)) if a.ty() == &self.builtins_().bool => (a, b),
                Error::new("bool-eq: th2 should have a boleean equality as conclusion")
            })?;

        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::BoolEq(th1.clone(), th2.clone())))
        } else {
            None
        };

        if a != &th1.0.concl {
            return Err(Error::new_string(format!(
                "bool-eq: the conclusion of th1, `{}` is not compatible with th2's concl LHS `{}`",
                self.pp_expr(&th1.0.concl),
                self.pp_expr(a)
            )));
        }
        let b = b.clone();

        let hyps = self.merge_hyps_th(th1, th2);
        Ok(Thm::make_(b, self.0.uid, hyps, pr))
    }

    /// `bool_eq_intro (F1, a |- b) (F2, b |- a)` is `F1, F2 |- b=a`.
    /// This is a way of building a boolean `a=b` from proofs of
    ///  `a|-b` and `b|-a`.
    pub fn thm_bool_eq_intro(&mut self, th1: Thm, th2: Thm) -> Result<Thm> {
        self.check_thm_uid_(&th1);
        self.check_thm_uid_(&th2);
        let eq = self.mk_eq_app(th2.0.concl.clone(), th1.0.concl.clone())?;

        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::BoolEqIntro(th1.clone(), th2.clone())))
        } else {
            None
        };

        let hyps = self.merge_hyps_iter_(
            th1.0.hyps.iter().filter(|x| *x != &th2.0.concl).cloned(),
            th2.0.hyps.iter().filter(|x| *x != &th1.0.concl).cloned(),
        );
        let th = Thm::make_(eq, self.0.uid, hyps, pr);
        Ok(th)
    }

    /// `beta_conv ((λx.u) a)` is `|- (λx.u) a = u[x:=a]`.
    /// Fails if the term is not a beta-redex.
    pub fn thm_beta_conv(&mut self, e: &Expr) -> Result<Thm> {
        self.check_uid_(e);
        let (f, arg) = e
            .as_app()
            .ok_or_else(|| Error::new("beta-conv: expect an application"))?;
        let (ty, bod) = f
            .as_lambda()
            .ok_or_else(|| Error::new("beta-conv: expect a lambda in the application"))?;
        debug_assert_eq!(ty, arg.ty()); // should already be enforced by typing.

        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::BetaConv(e.clone())))
        } else {
            None
        };

        let lhs = e.clone();
        let rhs = self.subst_db_(bod, 0, &[arg.clone()])?;
        let eq = self.mk_eq_app(lhs, rhs)?;
        Ok(Thm::make_(eq, self.0.uid, smallvec![], pr))
    }

    /// `new_basic_definition (x=t)` where `x` is a variable and `t` a term
    /// with a closed type,
    /// returns a theorem `|- x=t` where `x` is now a constant, along with
    /// the constant `x`, and the set of free variables of the type of `t`
    /// that the constant is parametrized with.
    pub fn thm_new_basic_definition(&mut self, e: Expr) -> Result<(Thm, Const, Vars)> {
        self.check_uid_(&e);
        let (x, rhs) = e
            .unfold_eq()
            .and_then(|(x, rhs)| x.as_var().map(|x| (x, rhs)))
            .ok_or_else(|| {
                Error::new("new definition: expr should be an equation `x = rhs` with rhs closed")
            })?;
        assert_eq!(x.ty(), rhs.ty());
        // checks that the type of `x` is closed
        if !rhs.is_closed() {
            return Err(Error::new("RHS of equation should be closed"));
        }

        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::NewDef(e.clone())))
        } else {
            None
        };

        let (c, ty_vars) = self.mk_new_const(x.name.clone(), x.ty.clone(), pr.clone())?;
        let ty_vars_as_exprs: Exprs = ty_vars.iter().map(|v| self.mk_var(v.clone())).collect();
        let lhs = self.mk_const(c.clone(), ty_vars_as_exprs)?;
        let eqn = self.mk_eq_app(lhs, rhs.clone())?;
        let thm = Thm::make_(eqn, self.0.uid, smallvec![], pr);
        Ok((thm, c, ty_vars))
    }

    /// Create a new axiom `|- concl`.
    /// **use with caution**
    ///
    /// Fails if `pledge_no_new_axiom` was called earlier on this context.
    pub fn thm_axiom(&mut self, concl: Expr) -> Result<Thm> {
        if !self.0.allow_new_axioms {
            return Err(Error::new(
                "this context has pledged to not take new axioms",
            ));
        }
        self.check_uid_(&concl);

        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::Axiom(concl.clone())))
        } else {
            None
        };

        let thm = Thm::make_(concl, self.0.uid, smallvec![], pr);
        self.0.axioms.push(thm.clone());
        Ok(thm)
    }

    /// Pledge that no new call to `thm_axiom` will occur.
    ///
    /// This freezes the logical theory to the consequences of the builtin
    /// rules and the already created axioms.
    pub fn pledge_no_new_axiom(&mut self) {
        self.0.allow_new_axioms = false;
    }

    /// Introduce a new type operator.
    ///
    /// Here, too, we follow HOL light:
    /// `new_basic_type_definition(tau, abs, repr, inhabited)`
    /// where `inhabited` is the theorem `|- Phi x` with `x : ty`,
    /// defines a new type operator named `tau` and two functions,
    /// `abs : ty -> tau` and `repr: tau -> ty`.
    ///
    /// It returns a struct `NewTypeDef` containing `tau, absthm, reprthm`, where:
    /// - `tau` is the new (possibly parametrized) type operator
    /// - `absthm` is `|- abs (repr x) = x`
    /// - `reprthm` is `|- Phi x <=> repr (abs x) = x`
    pub fn thm_new_basic_type_definition(
        &mut self,
        name_tau: Symbol,
        abs: Symbol,
        repr: Symbol,
        thm_inhabited: Thm,
    ) -> Result<NewTypeDef> {
        self.check_thm_uid_(&thm_inhabited);
        if thm_inhabited.hyps().len() > 0 {
            return Err(Error::new(
                "new_basic_type_def: theorem must not have hypotheses",
            ));
        }
        let (phi, witness) = thm_inhabited
            .concl()
            .as_app()
            .ok_or_else(|| Error::new("conclusion of theorem must be `(Phi x)`"))?;
        // the concrete type
        let ty = witness.ty().clone();
        // check that all free variables are type variables
        let mut fvars: Vars = thm_inhabited.concl().free_vars().cloned().collect();
        fvars.sort_unstable();
        fvars.dedup();

        if fvars.iter().any(|v| !v.ty.is_type()) {
            return Err(Error::new(
                "new_basic_type_def: definition contains \
                a free variable that does not have type `type`",
            ));
        }
        let ty_vars = fvars;

        // free vars, as expressions
        let ty_vars_as_exprs: SmallVec<_> =
            ty_vars.iter().map(|v| self.mk_var(v.clone())).collect();

        let pr = if self.0.proof_gen {
            Some(Proof::new(ProofView::NewTyDef(
                ty.clone(),
                thm_inhabited.clone(),
            )))
        } else {
            None
        };

        // construct new type and mapping functions
        let tau: Const = { self.mk_new_ty_const_(name_tau, ty_vars.len(), pr.clone())? };

        // `tau` applied to `fvars`
        let tau_vars = self.mk_const(tau.clone(), ty_vars_as_exprs.clone())?;

        let c_abs = {
            let ty = self.mk_arrow(ty.clone(), tau_vars.clone())?;
            let ty = self.abs_on_(&ty_vars[..], ty)?;
            self.mk_new_const(abs, ty, pr.clone())?.0
        };
        assert_eq!(ty_vars.len(), c_abs.arity as usize);
        let c_repr = {
            let ty = self.mk_arrow(tau_vars.clone(), ty.clone())?;
            let ty = self.abs_on_(&ty_vars[..], ty)?;
            self.mk_new_const(repr, ty, pr.clone())?.0
        };
        assert_eq!(ty_vars.len(), c_repr.arity as usize);

        let abs_x = self.mk_var_str("x", tau_vars.clone());
        let abs_thm = {
            // `|- abs (repr x) = x`
            let repr = self.mk_const(c_repr.clone(), ty_vars_as_exprs.clone())?;
            let t = self.mk_app(repr, abs_x.clone())?;
            let abs = self.mk_const(c_abs.clone(), ty_vars_as_exprs.clone())?;
            let abs_t = self.mk_app(abs, t)?;
            let eqn = self.mk_eq_app(abs_t.clone(), abs_x.clone())?;
            Thm::make_(eqn, self.0.uid, smallvec![], pr.clone())
        };
        let repr_x = self.mk_var_str("x", ty.clone());
        let repr_thm = {
            // `|- Phi x <=> repr (abs x) = x`
            let abs = self.mk_const(c_abs.clone(), ty_vars_as_exprs.clone())?;
            let t1 = self.mk_app(abs, repr_x.clone())?;
            let repr = self.mk_const(c_repr.clone(), ty_vars_as_exprs.clone())?;
            let t2 = self.mk_app(repr, t1)?;
            let eq_t2_x = self.mk_eq_app(t2, repr_x.clone())?;
            let phi_x = self.mk_app(phi.clone(), repr_x.clone())?;
            Thm::make_(
                self.mk_eq_app(phi_x, eq_t2_x)?,
                self.0.uid,
                smallvec![],
                pr.clone(),
            )
        };

        let c = NewTypeDef {
            tau,
            c_repr,
            c_abs,
            ty_vars,
            repr_x: repr_x.as_var().unwrap().clone(),
            abs_thm,
            abs_x: abs_x.as_var().unwrap().clone(),
            repr_thm,
        };
        Ok(c)
    }
}

pub struct ExprWithCtx<'a>(Expr, &'a Ctx);

impl<'a> fmt::Display for ExprWithCtx<'a> {
    // use the pretty-printer from `syntax`
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        crate::syntax::print_expr(&self.1 .0.fixities, &self.0, out)
    }
}

mod impls {
    use super::*;

    impl std::default::Default for Ctx {
        fn default() -> Self {
            Ctx::new()
        }
    }

    impl fmt::Debug for Ctx {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "<logical context>")
        }
    }
}
