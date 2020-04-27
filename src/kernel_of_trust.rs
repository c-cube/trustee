//! Kernel of Trust: Terms and Theorems

use crate::fnv;
use std::{fmt, ops::Deref, sync::Arc, sync::RwLock};

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
pub type DbIndex = u16;

///! ## Expressions (and types)

/// An expression.
#[derive(Clone)]
pub struct Expr(Arc<ExprImpl>);

/// Types and Terms are the same, but this is helpful for documentation.
pub type Type = Expr;

/// The public view of an expression's root.
#[derive(Clone, Eq, PartialEq, Hash)]
pub enum ExprView {
    Type,
    Kind,
    Const(ConstContent),
    Var(VarContent),
    BoundVar(BoundVarContent),
    App(Expr, Expr),
    Lambda(Type, Expr),
    Pi(Type, Expr),
}

use ExprView::*;

/// The content of an expression.
struct ExprImpl {
    /// The view of the expression.
    view: ExprView,
    /// Number of DB indices missing. 0 means the term is closed.
    db_depth: u16,
    /// Type of the expression. Always present except for `Kind`.
    ty: Option<Expr>,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct ConstContent {
    name: Symbol,
    ty: Expr,
}

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct VarContent {
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

impl VarContent {
    fn map_ty<F>(&self, f: F) -> Self
    where
        F: FnOnce(&Expr) -> Expr,
    {
        VarContent { name: self.name.clone(), ty: f(&self.ty) }
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

// compute the deepest DB index
fn compute_db_depth(e: &ExprView) -> u16 {
    match e {
        Kind | Type => 0,
        Const(c) => c.ty.db_depth(),
        Var(v) => v.ty.db_depth(),
        BoundVar(v) => v.ty.db_depth(),
        App(a, b) => a.db_depth().max(b.db_depth()),
        Lambda(v_ty, e) | Pi(v_ty, e) => v_ty.db_depth().max(e.db_depth()),
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
            ExprView::Kind => true,
            _ => false,
        }
    }

    /// Is this the representation of `Type`?
    #[inline]
    pub fn is_type(&self) -> bool {
        match self.0.view {
            ExprView::Type => true,
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
        while let App(f, a) = e.view() {
            e = f;
            v.push(a);
        }
        v.reverse();
        (e, v)
    }

    /// Deepest bound variable in the expr.
    ///
    /// 0 means it's a closed term.
    #[inline]
    fn db_depth(&self) -> u16 {
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
            Kind => write!(out, "kind"),
            Type => write!(out, "type"),
            Const(c) => write!(out, "{}", c.name.name()),
            Var(v) => write!(out, "{}", v.name.name()),
            BoundVar(v) => write!(out, "x{}", (k - v.idx)),
            App(..) => {
                let (f, args) = self.unfold_app();
                write!(out, "(")?;
                f.pp_(k, out)?;
                for x in args {
                    x.pp_(k, out)?;
                }
                write!(out, ")")
            }
            Lambda(ty_x, body) => {
                write!(out, "(%x{} : ", k)?;
                ty_x.pp_(k, out)?;
                write!(out, ". ")?;
                body.pp_(k + 1, out)?;
                write!(out, ")")
            }
            Pi(_x, body) => {
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

/// Global manager for expressions, used to implement perfect sharing, allocating
/// new terms, etc.
pub struct ExprManager {
    tbl: RwLock<fnv::FnvHashMap<Expr, Expr>>,
    consts: RwLock<fnv::FnvHashMap<Symbol, Expr>>,
    builtins: Option<Builtins>,
}

struct Builtins {
    kind: Expr,
    ty: Expr,
    bool: Expr,
}

impl ExprManager {
    /// Create a new term manager.
    pub fn new() -> Self {
        Self::with_capacity(2_048)
    }

    /// Add to the internal table, return the canonical representant.
    fn hashcons_(&self, ev: ExprView) -> Expr {
        let tbl = self.tbl.read().unwrap(); // lock tbl
        match tbl.get(&ev) {
            Some(v) => v.clone(),
            None => {
                // need to insert the term, so first we need to compute its type.
                drop(tbl);
                let ty = self.compute_ty(&ev);
                let e = Expr::make_(ev, ty);
                // lock table, again, but this time we'll write to it.
                // invariant: computing the type doesn't insert `e` in the table.
                let mut tbl = self.tbl.write().unwrap();
                tbl.insert(e.clone(), e.clone());
                e
            }
        }
    }

    fn hashcons_builtin_(&self, ev: ExprView, ty: Option<Expr>) -> Expr {
        let mut tbl = self.tbl.write().unwrap();
        debug_assert!(!tbl.contains_key(&ev));
        let e = Expr::make_(ev, ty);
        tbl.insert(e.clone(), e.clone());
        e
    }

    fn add_const_(&self, c: Symbol, e: Expr) {
        let mut consts = self.consts.write().unwrap();
        consts.insert(c, e);
    }

    // compute the type for this expression
    fn compute_ty(&self, e: &ExprView) -> Option<Expr> {
        match e {
            Kind => None,
            Type => Some(self.builtins_().ty.clone()),
            Const(c) => Some(c.ty.clone()),
            Var(v) => Some(v.ty.clone()),
            BoundVar(v) => Some(v.ty.clone()),
            Lambda(v_ty, e) => {
                // type of `λx:a. t` is `Πx:a. typeof(b)`.
                Some(self.hashcons_(Pi(v_ty.clone(), e.ty().clone())))
            }
            Pi(v_ty, e) => {
                if !v_ty.is_type() {
                    panic!(
                        "pi: variable must have type `type`, not {:?}",
                        v_ty
                    );
                };
                if !e.ty().is_type() {
                    panic!("pi: body must have type `type`, not {:?}", e.ty());
                };
                Some(self.builtins_().ty.clone())
            }
            App(a, b) => match &a.ty().0.view {
                Pi(ty_var_a, ref body_a) => {
                    if ty_var_a != b.ty() {
                        panic!(
                                "apply: incompatible types: \
                                function `{:?}` has type `{:?}`, argument `{:?}` has type `{:?}`",
                                a,ty_var_a,
                                b, b.ty()
                            );
                    }
                    Some(self.subst1_(body_a, b))
                }
                _ => panic!("cannot apply term with a non-pi type"),
            },
        }
    }

    /// Replace DB0 in `t` by `u`.
    fn subst1_(&self, t: &Expr, u: &Expr) -> Expr {
        if t.is_closed() {
            return t.clone(); // shortcut
        }

        match t.view() {
            Kind | Type | Const(..) => t.clone(),
            App(a, b) => self.mk_app(self.subst1_(a, u), self.subst1_(b, u)),
            Lambda(v_ty, body) => self.hashcons_(Lambda(
                self.subst1_(v_ty, u),
                self.subst1_(body, u),
            )),
            Pi(v_ty, body) => {
                debug_assert!(v_ty.is_type()); // no need to substitute there
                self.hashcons_(Pi(v_ty.clone(), self.subst1_(body, u)))
            }
            Var(v) => self.hashcons_(Var(v.map_ty(|ty| self.subst1_(ty, u)))),
            BoundVar(v) if v.idx == 0 => u.clone(), // substitute here
            BoundVar(v) => {
                self.hashcons_(BoundVar(v.map_ty(|ty| self.subst1_(ty, u))))
            }
        }
    }

    #[inline]
    fn builtins_(&self) -> &Builtins {
        match self.builtins {
            None => panic!("term manager should have builtins"),
            Some(ref b) => &b,
        }
    }

    /// Create a new term manager with given initial capacity.
    pub fn with_capacity(n: usize) -> Self {
        let tbl = fnv::new_fnv_map_cap(n);
        let mut tm = ExprManager {
            tbl: RwLock::new(tbl),
            consts: RwLock::new(fnv::new_fnv_map_cap(n)),
            builtins: None,
        };
        // insert initial builtins
        let kind = tm.hashcons_builtin_(Kind, None);
        let ty = tm.hashcons_builtin_(Type, Some(kind.clone()));
        let s_bool = Symbol::from_str("Bool");
        let bool = tm.hashcons_builtin_(
            Const(ConstContent { name: s_bool.clone(), ty: ty.clone() }),
            Some(ty.clone()),
        );
        tm.add_const_(s_bool, bool.clone());
        let builtins = Builtins { bool, kind, ty };
        tm.builtins = Some(builtins);
        tm
    }

    ///! ### Creation of new terms.

    /// The type of types. This has type `self.mk_kind()`.
    /// ```
    /// # use trustee::*;
    /// let em = ExprManager::new();
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
    /// let em = ExprManager::new();
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
    pub fn mk_app(&self, a: Expr, b: Expr) -> Expr {
        self.hashcons_(App(a, b))
    }

    /// Apply `f` to the given arguments.
    pub fn mk_app_iter<I>(&self, f: Expr, args: I) -> Expr
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
    pub fn mk_app_l(&self, f: Expr, args: &[Expr]) -> Expr {
        self.mk_app_iter(f, args.iter().cloned())
    }

    /// Make a free variable.
    pub fn mk_var(&self, name: Symbol, ty_var: Type) -> Expr {
        self.hashcons_(Var(VarContent { name, ty: ty_var }))
    }

    /// Make a bound variable with given type and index.
    pub fn mk_bound_var(&self, idx: DbIndex, ty_var: Type) -> Expr {
        self.hashcons_(BoundVar(BoundVarContent { idx, ty: ty_var }))
    }

    /// Make a lambda term.
    pub fn mk_lambda(&self, ty_var: Type, body: Expr) -> Expr {
        self.hashcons_(Lambda(ty_var, body))
    }

    /// Make a pi term.
    pub fn mk_pi(&self, ty_var: Expr, body: Expr) -> Expr {
        self.hashcons_(Pi(ty_var, body))
    }

    pub fn new_constant(&self, s: Symbol, ty: Type) -> Expr {
        if self.consts.read().unwrap().contains_key(&s) {
            panic!("a constant named {:?} already exists", &s);
        }
        if !ty.is_closed() {
            panic!(
                "cannot create constant named {:?} with non-closed type {:?}",
                &s, &ty
            );
        }
        let c = self.hashcons_(Const(ConstContent { name: s.clone(), ty }));
        self.add_const_(s, c.clone());
        c
    }
}
