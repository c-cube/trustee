//! Kernel of Trust: Terms and Theorems

use crate::fnv;
use std::{fmt, ops::Deref, sync::Arc, sync::Mutex};

///! ## Symbols.

#[derive(Debug, Clone, Ord, PartialOrd, Hash, Eq, PartialEq)]
pub struct Symbol(Arc<str>);

impl Symbol {
    /// New symbol from this string.
    ///
    /// ```
    /// # use trustee::*;
    /// let s1 = Symbol::from_str("a");
    /// let s2 = Symbol::from_str("a");
    /// let s3 = Symbol::from_str("b");
    /// assert_eq!(s1, s2);
    /// assert_ne!(s1, s3);
    /// assert_eq!(s1.name(), "a");
    /// ```
    pub fn from_str(s: &str) -> Self {
        let a = Arc::from(s);
        Symbol(a)
    }

    pub fn name(&self) -> &str {
        &*self.0
    }
}

/// De Buijn indices.
pub type DbIndex = u32;

///! ## Expressions (and types)

/// An expression.
#[derive(Clone)]
pub struct Expr(Arc<ExprImpl>);

/// Types and Terms are the same, but this is helpful for documentation.
pub type Type = Expr;

/// The public view of an expression's root.
#[derive(Clone, Eq, PartialEq, Hash)]
pub enum ExprView {
    EType,
    EKind,
    EConst(ConstContent),
    EVar(Var),
    EBoundVar(BoundVarContent),
    EApp(Expr, Expr),
    ELambda(Type, Expr),
    EPi(Type, Expr),
}

pub use ExprView::*;

/// A free variable.
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Var {
    name: Symbol,
    ty: Expr,
}

/// The content of an expression.
struct ExprImpl {
    /// The view of the expression.
    view: ExprView,
    /// Number of DB indices missing. 0 means the term is closed.
    db_depth: DbIndex,
    /// Type of the expression. Always present except for `Kind`.
    ty: Option<Expr>,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct ConstContent {
    name: Symbol,
    ty: Expr,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct BoundVarContent {
    idx: DbIndex,
    ty: Expr,
}

impl Eq for Expr {}
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        // simple pointer equality
        std::ptr::eq(
            self.0.deref() as *const ExprImpl,
            other.0.deref() as *const _,
        )
    }
}

impl PartialOrd for Expr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        // simple pointer comparison
        std::cmp::PartialOrd::partial_cmp(
            &(self.0.deref() as *const ExprImpl),
            &(other.0.deref() as *const _),
        )
    }
}
impl Ord for Expr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // simple pointer comparison
        std::cmp::Ord::cmp(
            &(self.0.deref() as *const ExprImpl),
            &(other.0.deref() as *const _),
        )
    }
}

impl std::hash::Hash for Expr {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        // hash pointer
        std::ptr::hash(&(self.0.deref() as *const ExprImpl), h)
    }
}

impl std::borrow::Borrow<ExprView> for Expr {
    fn borrow(&self) -> &ExprView {
        &self.0.view
    }
}

impl Var {
    #[inline]
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    #[inline]
    pub fn ty(&self) -> &Type {
        &self.ty
    }

    #[inline]
    pub fn new(name: Symbol, ty: Type) -> Var {
        Var { name, ty }
    }

    /// Make a free variable.
    pub fn from_str(name: &str, ty: Type) -> Var {
        Var { name: Symbol::from_str(name), ty }
    }

    /// Transform the type using `f`.
    pub fn map_ty<F>(&self, f: F) -> Self
    where
        F: FnOnce(&Expr) -> Expr,
    {
        Var { name: self.name.clone(), ty: f(&self.ty) }
    }
}

impl BoundVarContent {
    fn map_ty<F>(&self, f: F) -> Self
    where
        F: FnOnce(&Expr) -> Expr,
    {
        BoundVarContent { idx: self.idx, ty: f(&self.ty) }
    }
}

#[inline]
fn pred_db_idx(n: DbIndex) -> DbIndex {
    if n == 0 {
        0
    } else {
        n - 1
    }
}

// compute the deepest DB index
fn compute_db_depth(e: &ExprView) -> DbIndex {
    match e {
        EKind | EType => 0u32,
        EConst(c) => c.ty.db_depth(),
        EVar(v) => v.ty.db_depth(),
        EBoundVar(v) => v.ty.db_depth(),
        EApp(a, b) => a.db_depth().max(b.db_depth()),
        ELambda(v_ty, e) | EPi(v_ty, e) => {
            // `e`'s depth is decremented here
            v_ty.db_depth().max(pred_db_idx(e.db_depth()))
        }
    }
}

impl ExprView {
    /// Shallow map, with a depth parameter.
    pub fn map<F>(&self, mut f: F, k: DbIndex) -> Self
    where
        F: FnMut(&Expr, DbIndex) -> Expr,
    {
        match self {
            EType | EKind => self.clone(),
            EConst(c) => EConst(ConstContent { ty: f(&c.ty, k), ..c.clone() }),
            EVar(v) => EVar(Var { ty: f(&v.ty, k), ..v.clone() }),
            EBoundVar(v) => {
                EBoundVar(BoundVarContent { ty: f(&v.ty, k), ..v.clone() })
            }
            EApp(a, b) => EApp(f(a, k), f(b, k)),
            EPi(ty_a, b) => EPi(f(ty_a, k), f(b, k + 1)),
            ELambda(ty_a, b) => ELambda(f(ty_a, k), f(b, k + 1)),
        }
    }
}

impl Expr {
    /// View the expression's root.
    #[inline]
    pub fn view(&self) -> &ExprView {
        &self.0.view
    }

    /// Is this the representation of `Kind`?
    #[inline]
    pub fn is_kind(&self) -> bool {
        match self.0.view {
            EKind => true,
            _ => false,
        }
    }

    /// Is this the representation of `Type`?
    #[inline]
    pub fn is_type(&self) -> bool {
        match self.0.view {
            EType => true,
            _ => false,
        }
    }

    /// Type of the expression. Panics if `self.is_kind()`.
    #[inline]
    pub fn ty(&self) -> &Expr {
        match self.0.ty {
            Some(ref ty) => &ty,
            None => {
                debug_assert!(self.is_kind());
                panic!("cannot return type of expr (must be `kind`)")
            }
        }
    }

    /// `e.unfold_app()` returns a tuple `(f, args)` where `args`
    /// iterates over arguments.
    pub fn unfold_app(&self) -> (&Expr, Vec<&Expr>) {
        let mut e = self;
        let mut v = vec![];
        while let EApp(f, a) = e.view() {
            e = f;
            v.push(a);
        }
        v.reverse();
        (e, v)
    }

    /// `e.unfold_pi()` returns a tuple `(ty_args, body)` such
    /// that `e == pi 0:a1. pi 1:a2. …. body` with `ty_args = (a1,a2,…)`.
    ///
    /// The length of `ty_args` indicates how many pi abstractions have been done.
    pub fn unfold_pi(&self) -> (Vec<&Type>, &Expr) {
        let mut e = self;
        let mut v = vec![];
        while let EPi(ty_arg, body) = e.view() {
            e = body;
            v.push(ty_arg);
        }
        (v, e)
    }

    /// Deepest bound variable in the expr.
    ///
    /// 0 means it's a closed term.
    #[inline]
    fn db_depth(&self) -> DbIndex {
        self.0.db_depth
    }

    /// Is this a closed term?
    #[inline]
    pub fn is_closed(&self) -> bool {
        self.db_depth() == 0
    }

    // helper for building expressions
    fn make_(v: ExprView, ty: Option<Expr>) -> Self {
        let db_depth = compute_db_depth(&v);
        Expr(Arc::new(ExprImpl { view: v, ty, db_depth }))
    }

    // pretty print
    fn pp_(&self, k: DbIndex, out: &mut fmt::Formatter) -> fmt::Result {
        match self.view() {
            EKind => write!(out, "kind"),
            EType => write!(out, "type"),
            EConst(c) => write!(out, "{}", c.name.name()),
            EVar(v) => write!(out, "{}", v.name.name()),
            EBoundVar(v) => write!(out, "x{}", (k - v.idx)),
            EApp(..) => {
                let (f, args) = self.unfold_app();
                write!(out, "(")?;
                f.pp_(k, out)?;
                for x in args {
                    x.pp_(k, out)?;
                }
                write!(out, ")")
            }
            ELambda(ty_x, body) => {
                write!(out, "(%x{} : ", k)?;
                ty_x.pp_(k, out)?;
                write!(out, ". ")?;
                body.pp_(k + 1, out)?;
                write!(out, ")")
            }
            EPi(_x, body) => {
                debug_assert!(_x.is_type());
                write!(out, "(Πx{}. ", k)?;
                body.pp_(k + 1, out)?;
                write!(out, ")")
            }
        }
    }
}

impl fmt::Debug for Expr {
    // printer
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        self.pp_(0, out)
    }
}

impl fmt::Debug for Var {
    // printer
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "{}", self.name.name())
    }
}

/// Global manager for expressions, used to implement perfect sharing, allocating
/// new terms, etc.
pub struct ExprManager {
    tbl: fnv::FnvHashMap<Expr, Expr>,
    builtins: Option<ExprBuiltins>,
    consts: fnv::FnvHashMap<Symbol, Expr>,
}

struct ExprBuiltins {
    kind: Expr,
    ty: Expr,
    bool: Expr,
}

impl ExprManager {
    /// Create a new term manager with given initial capacity.
    pub fn with_capacity(n: usize) -> Self {
        let tbl = fnv::new_table_with_cap(n);
        let mut tm = ExprManager {
            tbl,
            builtins: None,
            consts: fnv::new_table_with_cap(n),
        };
        // insert initial builtins
        let kind = tm.hashcons_builtin_(EKind, None);
        let ty = tm.hashcons_builtin_(EType, Some(kind.clone()));
        let s_bool = Symbol::from_str("Bool");
        let bool = tm.hashcons_builtin_(
            EConst(ConstContent { name: s_bool.clone(), ty: ty.clone() }),
            Some(ty.clone()),
        );
        tm.add_const_(s_bool, bool.clone());
        let builtins = ExprBuiltins { bool, kind, ty };
        tm.builtins = Some(builtins);
        tm
    }

    pub fn new() -> Self {
        Self::with_capacity(2_048)
    }

    /// Add to the internal table, return the canonical representant.
    fn hashcons_(&mut self, ev: ExprView) -> Expr {
        let tbl = &mut self.tbl; // lock tbl
        match tbl.get(&ev) {
            Some(v) => v.clone(),
            None => {
                // TODO: every n cycles, do a `cleanup`?
                // maybe if last cleanups were ineffective, increase n,
                // otherwise decrease n (down to some min value)

                // need to insert the term, so first we need to compute its type.
                drop(tbl);
                let ty = self.compute_ty_(&ev);
                let e = Expr::make_(ev, ty);
                // lock table, again, but this time we'll write to it.
                // invariant: computing the type doesn't insert `e` in the table.
                let tbl = &mut self.tbl;
                tbl.insert(e.clone(), e.clone());
                e
            }
        }
    }

    fn add_const_(&mut self, c: Symbol, e: Expr) {
        let consts = &mut self.consts;
        consts.insert(c, e);
    }

    fn hashcons_builtin_(&mut self, ev: ExprView, ty: Option<Expr>) -> Expr {
        let tbl = &mut self.tbl;
        debug_assert!(!tbl.contains_key(&ev));
        let e = Expr::make_(ev, ty);
        tbl.insert(e.clone(), e.clone());
        e
    }

    #[inline]
    fn builtins_(&self) -> &ExprBuiltins {
        match self.builtins {
            None => panic!("term manager should have builtins"),
            Some(ref b) => &b,
        }
    }

    // compute the type for this expression
    fn compute_ty_(&mut self, e: &ExprView) -> Option<Expr> {
        match e {
            EKind => None,
            EType => Some(self.builtins_().ty.clone()),
            EConst(c) => Some(c.ty.clone()),
            EVar(v) => Some(v.ty.clone()),
            EBoundVar(v) => Some(v.ty.clone()),
            ELambda(v_ty, e) => {
                // type of `λx:a. t` is `Πx:a. typeof(b)`.
                Some(self.hashcons_(EPi(v_ty.clone(), e.ty().clone())))
            }
            EPi(v_ty, e) => {
                if !v_ty.is_type() && !v_ty.ty().is_type() {
                    panic!(
                        "pi: variable must be a type or be of type `type`, not {:?}",
                        v_ty
                    );
                };
                if !e.ty().is_type() {
                    panic!("pi: body must have type `type`, not {:?}", e.ty());
                };
                Some(self.builtins_().ty.clone())
            }
            EApp(f, arg) => match &f.ty().0.view {
                EPi(ty_var_f, ref ty_body_f) => {
                    // rule: `f: Πx:tya. b`, `arg: tya` ==> `f arg : b[arg/x]`
                    if ty_var_f != arg.ty() {
                        panic!(
                            "apply: incompatible types: \
                                function `{:?}` has type `{:?}`, \
                                argument `{:?}` has type `{:?}`",
                            f,
                            ty_var_f,
                            arg,
                            arg.ty()
                        );
                    }
                    Some(self.subst1_(ty_body_f, 0, arg))
                }
                _ => panic!("cannot apply term with a non-pi type"),
            },
        }
    }

    /// Replace DB0 in `t` by `u`, below `k` intermediate binders.
    fn subst1_(&mut self, t: &Expr, k: u32, u: &Expr) -> Expr {
        if t.is_closed() {
            return t.clone(); // shortcut
        }

        match t.view() {
            EKind | EType | EConst(..) => t.clone(),
            EApp(a, b) => {
                let a2 = self.subst1_(a, k, u);
                let b2 = self.subst1_(b, k, u);
                if a == &a2 && b == &b2 {
                    t.clone() // no need to do hashconsing
                } else {
                    self.hashcons_(EApp(a2, b2))
                }
            }
            ELambda(v_ty, body) => {
                let v_ty2 = self.subst1_(v_ty, k, u);
                let body2 = self.subst1_(body, k + 1, u);
                if v_ty == &v_ty2 && body == &body2 {
                    t.clone()
                } else {
                    self.hashcons_(ELambda(v_ty2, body2))
                }
            }
            EPi(v_ty, body) => {
                debug_assert!(v_ty.is_type()); // no need to substitute there
                let body2 = self.subst1_(body, k + 1, u);
                self.hashcons_(EPi(v_ty.clone(), body2))
            }
            EVar(v) => {
                let v2 = v.map_ty(|ty| self.subst1_(ty, k, u));
                self.hashcons_(EVar(v2))
            }
            EBoundVar(v) if v.idx == 0 => {
                // substitute here, accounting for the `k` intermediate binders
                self.shift_(u, k)
            }
            EBoundVar(v) => {
                let v2 = v.map_ty(|ty| self.subst1_(ty, k, u));
                self.hashcons_(EBoundVar(v2))
            }
        }
    }

    /// Shift free DB vars by `k`
    fn shift_(&mut self, t: &Expr, k: u32) -> Expr {
        if k == 0 || t.is_closed() {
            return t.clone(); // shortcut for identity
        }

        match t.view() {
            EKind | EType | EConst(..) => t.clone(),
            EApp(a, b) => {
                let a2 = self.shift_(a, k);
                let b2 = self.shift_(b, k);
                self.hashcons_(EApp(a2, b2))
            }
            ELambda(v_ty, body) => {
                let v_ty2 = self.shift_(v_ty, k);
                let body2 = self.shift_(body, k + 1);
                self.hashcons_(ELambda(v_ty2, body2))
            }
            EPi(v_ty, body) => {
                debug_assert!(v_ty.is_type()); // no need to substitute there
                let body2 = self.shift_(body, k + 1);
                self.hashcons_(EPi(v_ty.clone(), body2))
            }
            EVar(v) => {
                let v = v.map_ty(|ty| self.shift_(ty, k));
                self.hashcons_(EVar(v))
            }
            EBoundVar(v) if v.idx < k => t.clone(), // keep
            EBoundVar(v) => {
                // shift bound var
                let ty = self.shift_(&v.ty, k);
                self.hashcons_(EBoundVar(BoundVarContent {
                    idx: v.idx + k,
                    ty,
                }))
            }
        }
    }

    /// For each pair `(x,u)` in `subst`, replace instances of the free
    /// variable `x` by `u` in `t`.
    pub fn subst(&mut self, t: &Expr, subst: &[(Var, Expr)]) -> Expr {
        struct Replace<'a> {
            cache: fnv::FnvHashMap<Expr, Expr>,
            em: &'a mut ExprManager,
            subst: &'a [(Var, Expr)],
        }

        impl<'a> Replace<'a> {
            // replace in `t`, under `k` intermediate binders.
            fn replace(&mut self, t: &Expr, k: DbIndex) -> Expr {
                match self.cache.get(t) {
                    Some(t2) => t2.clone(),
                    None => {
                        match t.view() {
                            // fast cases first
                            EType | EKind | EConst(..) => t.clone(),
                            EVar(v) => {
                                // lookup `v` in `subst`
                                for (v2, u2) in self.subst.iter() {
                                    if v == v2 {
                                        return self.em.shift_(u2, k);
                                    }
                                }
                                // otherwise just substitute in the type
                                let v2 = v.map_ty(|ty| self.replace(ty, k));
                                let u = self.em.mk_var(v2);
                                self.cache.insert(t.clone(), u.clone());
                                u
                            }
                            ev => {
                                // shallow map + cache
                                let uv =
                                    ev.map(|sub, k| self.replace(sub, k), k);
                                let u = self.em.hashcons_(uv);
                                self.cache.insert(t.clone(), u.clone());
                                u
                            }
                        }
                    }
                }
            }
        }

        let mut replace =
            Replace { cache: fnv::new_table_with_cap(32), em: self, subst };
        replace.replace(t, 0)
    }

    /// Cleanup terms that are only referenced by this table.
    pub fn cleanup(&mut self) {
        self.tbl.retain(|k, _| {
            // if `k` (and `v`) are not used anywhere else, they're the only
            // references and should have a strong count of 2.
            // This is thread safe as the only way this is 2 is if it's already
            // not referenced anywhere, and we don't provide any way to produce
            // a weak ref.
            let n = Arc::strong_count(&k.0);
            debug_assert!(n >= 2);
            n > 2
        })
    }

    ///! ### Creation of new terms.

    /// The type of types. This has type `self.mk_kind()`.
    /// ```
    /// # use trustee::*;
    /// let mut em = ExprManager::new();
    /// let ty = em.mk_ty();
    /// let k = em.mk_kind();
    /// assert_eq!(&k, ty.ty());
    /// ```
    pub fn mk_ty(&self) -> Expr {
        self.builtins_().ty.clone()
    }

    /// The "type" of `type`. This is the only typeless expression.
    ///
    /// Trying to compute this expression's type panics.
    ///
    /// ```should_panic
    /// # use trustee::*;
    /// let mut em = ExprManager::new();
    /// let k = em.mk_kind();
    /// let _ = k.ty();
    /// ```
    pub fn mk_kind(&self) -> Expr {
        self.builtins_().kind.clone()
    }

    /// The type of booleans.
    pub fn mk_bool(&self) -> Expr {
        self.builtins_().bool.clone()
    }

    /// Apply `a` to `b`.
    ///
    /// ```
    /// # use trustee::*;
    /// # let mut em = ExprManager::new();
    /// let b = em.mk_bool();
    /// let b2b = em.mk_arrow(b.clone(), b.clone());
    /// let p = em.mk_var_str("p", b2b);
    /// let a = em.mk_var_str("a", b);
    /// let pa = em.mk_app(p, a);
    /// assert!(match pa.view() { EApp(..) => true, _ => false });
    /// assert!(pa.is_closed());
    /// ```
    pub fn mk_app(&mut self, a: Expr, b: Expr) -> Expr {
        self.hashcons_(EApp(a, b))
    }

    /// Apply `f` to the given arguments.
    pub fn mk_app_iter<I>(&mut self, f: Expr, args: I) -> Expr
    where
        I: IntoIterator<Item = Expr>,
    {
        // TODO: compute type in one go?
        let mut e = f;
        for x in args {
            e = self.mk_app(e, x);
        }
        e
    }

    /// Apply `f` to the given arguments.
    pub fn mk_app_l(&mut self, f: Expr, args: &[Expr]) -> Expr {
        self.mk_app_iter(f, args.iter().cloned())
    }

    /// Make a free variable.
    pub fn mk_var(&mut self, v: Var) -> Expr {
        self.hashcons_(EVar(v))
    }

    /// Make a free variable.
    pub fn mk_var_str(&mut self, name: &str, ty_var: Type) -> Expr {
        self.mk_var(Var::from_str(name, ty_var))
    }

    /// Make a bound variable with given type and index.
    pub fn mk_bound_var(&mut self, idx: DbIndex, ty_var: Type) -> Expr {
        self.hashcons_(EBoundVar(BoundVarContent { idx, ty: ty_var }))
    }

    /// Make a lambda term.
    pub fn mk_lambda(&mut self, ty_var: Type, body: Expr) -> Expr {
        self.hashcons_(ELambda(ty_var, body))
    }

    /// Make a lambda term by abstracting on `v`.
    ///
    /// ```
    /// # use trustee::*;
    /// # let mut em = ExprManager::new();
    /// let b = em.mk_bool();
    /// let b2b = em.mk_arrow(b.clone(), b.clone());
    /// let p = em.mk_var_str("p", b2b);
    /// let x = Var::from_str("x", b.clone());
    /// let ex = em.mk_var(x.clone());
    /// let body = em.mk_app(p, ex);
    /// let f = em.mk_lambda_abs(x, body);
    /// assert!(match f.view() { ELambda(..) => true, _ => false });
    /// assert!(f.is_closed());
    /// let (ty_args, ty_body) = f.ty().unfold_pi();
    /// assert_eq!(ty_args.len(), 1);
    /// assert_eq!(ty_args[0], &em.mk_bool());
    /// assert_eq!(ty_body, &em.mk_bool());
    /// ```
    pub fn mk_lambda_abs(&mut self, v: Var, body: Expr) -> Expr {
        let v_ty = v.ty.clone();
        if !v_ty.is_closed() {
            panic!("mk_abs: var {:?} has non-closed type", &v);
        }
        // replace `v` with `db0` in `body`. This should also take
        // care of shifting the DB as appropriate.
        let db0 = self.mk_bound_var(0, v_ty.clone());
        let body = self.subst(&body, &[(v, db0)]);
        self.mk_lambda(v_ty, body)
    }

    /// Make a pi term.
    pub fn mk_pi(&mut self, ty_var: Expr, body: Expr) -> Expr {
        self.hashcons_(EPi(ty_var, body))
    }

    /// Make an arrow `a -> b` term.
    ///
    /// This builds `Π_:a. b`.
    pub fn mk_arrow(&mut self, ty1: Expr, ty2: Expr) -> Expr {
        // need to shift ty2 to account for the binder
        let ty2 = self.shift_(&ty2, 1);
        self.mk_pi(ty1, ty2)
    }

    /// Declare a new constant with given name and type.
    ///
    /// panics if some constant with the same name exists, or if
    /// the type is not closed.
    pub fn mk_new_const(&mut self, s: Symbol, ty: Type) -> Expr {
        if self.consts.contains_key(&s) {
            panic!("a constant named {:?} already exists", &s);
        }
        if !ty.is_closed() {
            panic!(
                "cannot create constant named {:?} with non-closed type {:?}",
                &s, &ty
            );
        }
        let c = self.hashcons_(EConst(ConstContent { name: s.clone(), ty }));
        self.add_const_(s, c.clone());
        c
    }
}

/// A temporary, self-cleaning, handle to an `ExprManager`.`
///
/// See `ExprManager::get` to obtain that.
pub struct ExprManagerGuard<'a>(std::sync::MutexGuard<'a, ExprManager>);

impl<'a> std::ops::Deref for ExprManagerGuard<'a> {
    type Target = ExprManager;
    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl<'a> std::ops::DerefMut for ExprManagerGuard<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut *self.0
    }
}

/// Expression manager that can be shared between threads.
#[derive(Clone)]
pub struct ExprManagerRef {
    em: Arc<Mutex<ExprManager>>,
}

impl ExprManagerRef {
    /// Create a new term manager.
    pub fn new() -> Self {
        Self::with_capacity(2_048)
    }

    /// Create a new term manager with given initial capacity.
    pub fn with_capacity(n: usize) -> Self {
        let em = Arc::new(Mutex::new(ExprManager::with_capacity(n)));
        ExprManagerRef { em }
    }

    /// Obtain a temporary RAII-cleaned reference to the inner ExprManager.
    pub fn get(&self) -> ExprManagerGuard {
        ExprManagerGuard(self.em.lock().unwrap())
    }

    ///! Delegates

    pub fn cleanup(&self) {
        self.get().cleanup()
    }

    pub fn mk_ty(&self) -> Expr {
        self.get().mk_ty()
    }

    pub fn mk_kind(&self) -> Expr {
        self.get().mk_kind()
    }

    pub fn mk_bool(&self) -> Expr {
        self.get().mk_bool()
    }

    pub fn mk_app(&self, a: Expr, b: Expr) -> Expr {
        self.get().mk_app(a, b)
    }

    pub fn mk_app_iter<I>(&self, f: Expr, args: I) -> Expr
    where
        I: IntoIterator<Item = Expr>,
    {
        self.get().mk_app_iter(f, args)
    }

    pub fn mk_app_l(&self, f: Expr, args: &[Expr]) -> Expr {
        self.get().mk_app_l(f, args)
    }

    pub fn mk_var(&self, v: Var) -> Expr {
        self.get().mk_var(v)
    }

    pub fn mk_var_str(&self, name: &str, ty_var: Type) -> Expr {
        self.mk_var(Var::from_str(name, ty_var))
    }

    pub fn mk_bound_var(&mut self, idx: DbIndex, ty_var: Type) -> Expr {
        self.get().mk_bound_var(idx, ty_var)
    }

    pub fn mk_lambda(&mut self, ty_var: Type, body: Expr) -> Expr {
        self.get().mk_lambda(ty_var, body)
    }

    pub fn mk_lambda_abs(&mut self, v: Var, body: Expr) -> Expr {
        self.get().mk_lambda_abs(v, body)
    }

    pub fn mk_pi(&self, ty_var: Expr, body: Expr) -> Expr {
        self.get().mk_pi(ty_var, body)
    }

    pub fn mk_arrow(&self, ty1: Expr, ty2: Expr) -> Expr {
        self.get().mk_arrow(ty1, ty2)
    }

    /// Declare a new constant with given name and type.
    ///
    /// panics if some constant with the same name exists, or if
    /// the type is not closed.
    pub fn mk_new_const(&self, s: Symbol, ty: Type) -> Expr {
        self.get().mk_new_const(s, ty)
    }
}
