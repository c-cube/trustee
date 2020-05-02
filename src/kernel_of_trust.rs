//! Kernel of Trust: Terms and Theorems

use crate::fnv;
use std::{fmt, ops::Deref, sync::Arc};

///! # Symbols.

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

///! # Expressions, types, variables

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
///
/// Variables are equal iff they have the same name and the same type.
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
    /// Symbol for the variable.
    #[inline]
    pub fn name(&self) -> &Symbol {
        &self.name
    }

    /// Type of the variable.
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

struct FreeVars<'a> {
    seen: fnv::FnvHashSet<&'a Expr>,
    st: Vec<&'a Expr>,
}

impl<'a> Iterator for FreeVars<'a> {
    type Item = &'a Var;
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(e) = self.st.pop() {
            if self.seen.contains(&e) {
                continue;
            }
            self.seen.insert(e);

            match e.view() {
                EVar(v) => return Some(v),
                EType | EKind => (),
                EConst(c) => self.st.push(&c.ty),
                EBoundVar(v) => self.st.push(&v.ty),
                EApp(a, b) => {
                    self.st.push(a);
                    self.st.push(b);
                }
                EPi(_, body) => self.st.push(body),
                ELambda(ty, body) => {
                    self.st.push(ty);
                    self.st.push(body);
                }
            }
        }
        None
    }
}

impl<'a> FreeVars<'a> {
    fn new() -> Self {
        FreeVars { seen: fnv::new_set_with_cap(16), st: vec![] }
    }

    /// Add an expression to explore
    fn push(&mut self, e: &'a Expr) {
        self.st.push(e)
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

    /// View a variable.
    pub fn as_var(&self) -> Option<&Var> {
        if let EVar(ref v) = self.0.view {
            Some(&v)
        } else {
            None
        }
    }

    /// View as constant.
    pub fn as_const(&self) -> Option<&ConstContent> {
        if let EConst(ref c) = self.0.view {
            Some(&c)
        } else {
            None
        }
    }

    /// View as application.
    pub fn as_app(&self) -> Option<(&Expr, &Expr)> {
        if let EApp(ref a, ref b) = self.0.view {
            Some((&a, &b))
        } else {
            None
        }
    }

    /// View as a lambda-expression.
    pub fn as_lambda(&self) -> Option<(&Type, &Expr)> {
        if let ELambda(ref ty, ref bod) = self.0.view {
            Some((&ty, &bod))
        } else {
            None
        }
    }

    /// `(a=b).unfold_eq()` returns `Some((a,b))`.
    pub fn unfold_eq(&self) -> Option<(&Expr, &Expr)> {
        let (hd1, b) = self.as_app()?;
        let (hd2, a) = hd1.as_app()?;
        let (c, _alpha) = hd2.as_app()?;
        if c.as_const()?.name.name() == "=" {
            Some((a, b))
        } else {
            None
        }
    }

    /// `(a==>b).unfold_imply()` returns `Some((a,b))`.
    pub fn unfold_imply(&self) -> Option<(&Expr, &Expr)> {
        let (hd1, b) = self.as_app()?;
        let (hd2, a) = hd1.as_app()?;
        if hd2.as_const()?.name.name() == "==>" {
            Some((a, b))
        } else {
            None
        }
    }

    /// Free variables of a given term.
    pub fn free_vars(&self) -> impl Iterator<Item = &Var> {
        let mut fv = FreeVars::new();
        fv.push(self);
        fv
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
            EPi(x, body) => {
                write!(out, "(Πx{}", k)?;
                if !x.is_type() {
                    write!(out, ":")?;
                    x.pp_(k, out)?;
                }
                write!(out, ". ")?;
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

///! # Theorems.
///
/// Theorems are proved correct by construction.

/// A theorem.
#[derive(Clone)]
pub struct Thm(Arc<ThmImpl>);

#[derive(Clone)]
struct ThmImpl {
    /// Conclusion of the theorem.
    concl: Expr,
    /// Hypothesis of the theorem.
    hyps: Vec<Expr>,
}

/// Free variables of a set of terms
pub fn free_vars_iter<'a, I>(i: I) -> impl Iterator<Item = &'a Var>
where
    I: Iterator<Item = &'a Expr>,
{
    let mut fv = FreeVars::new();
    for t in i {
        fv.push(t);
    }
    fv
}

impl Thm {
    fn make_(concl: Expr, mut hyps: Vec<Expr>) -> Self {
        if hyps.len() >= 2 {
            hyps.sort_unstable();
            hyps.dedup();
            hyps.shrink_to_fit();
        }
        Thm(Arc::new(ThmImpl { concl, hyps }))
    }

    /// Conclusion of the theorem
    #[inline]
    pub fn concl(&self) -> &Expr {
        &self.0.concl
    }

    /// Hypothesis of the theorem
    #[inline]
    pub fn hyps(&self) -> &[Expr] {
        self.0.hyps.as_slice()
    }
}

impl fmt::Debug for Thm {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        if self.hyps().len() == 0 {
            write!(out, "|- {:?}", self.concl())
        } else {
            for h in self.hyps() {
                write!(out, "    {:?}\n", h)?;
            }
            write!(out, " |- {:?}", self.concl())
        }
    }
}

///! # Expression and theorem manager.
///
/// The state used to ensure proper hashconsing of terms and to build terms
/// and theorems.

/// Global manager for expressions, used to implement perfect sharing, allocating
/// new terms, etc.
pub struct ExprManager {
    tbl: fnv::FnvHashMap<Expr, Expr>,
    builtins: Option<ExprBuiltins>,
    consts: fnv::FnvHashMap<Symbol, Expr>,
    eq: Option<Expr>,
    imply: Option<Expr>,
    next_cleanup: usize,
    axioms: Vec<Thm>,
}

impl fmt::Debug for ExprManager {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<expr manager>")
    }
}

// period between 2 cleanups
const CLEANUP_PERIOD: usize = 500;

/// A set of builtin symbols.
struct ExprBuiltins {
    kind: Expr,
    ty: Expr,
    bool: Expr,
}

fn hyps_merge(th1: &Thm, th2: &Thm) -> Vec<Expr> {
    if th1.0.hyps.len() == 0 {
        th2.0.hyps.clone()
    } else if th2.0.hyps.len() == 0 {
        th1.0.hyps.clone()
    } else {
        let mut hyps: Vec<_> = th1.0.hyps.clone();
        hyps.extend_from_slice(&th2.0.hyps[..]);
        hyps
    }
}

impl ExprManager {
    /// Create a new term manager with given initial capacity.
    pub fn with_capacity(n: usize) -> Self {
        let tbl = fnv::new_table_with_cap(n);
        let mut em = ExprManager {
            tbl,
            builtins: None,
            consts: fnv::new_table_with_cap(n),
            eq: None,
            imply: None,
            next_cleanup: CLEANUP_PERIOD,
            axioms: vec![],
        };
        // insert initial builtins
        let kind = em.hashcons_builtin_(EKind, None);
        let ty = em.hashcons_builtin_(EType, Some(kind.clone()));
        let bool = {
            let name = Symbol::from_str("Bool");
            em.hashcons_builtin_(
                EConst(ConstContent { name, ty: ty.clone() }),
                Some(ty.clone()),
            )
        };
        em.add_const_(bool.clone());
        let builtins = ExprBuiltins { bool, kind, ty };
        em.builtins = Some(builtins);
        em
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
                // need to insert the term, so first we need to compute its type.
                drop(tbl);

                // every n cycles, do a `cleanup`
                // TODO: maybe if last cleanups were ineffective, increase n,
                // otherwise decrease n (down to some min value)
                if self.next_cleanup == 0 {
                    self.next_cleanup = CLEANUP_PERIOD;
                    self.cleanup();
                }

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

    fn add_const_(&mut self, e: Expr) {
        let consts = &mut self.consts;
        let name = if let EConst(ref c) = e.0.view {
            c.name.clone()
        } else {
            unreachable!();
        };
        consts.insert(name, e);
    }

    fn hashcons_builtin_(&mut self, ev: ExprView, ty: Option<Expr>) -> Expr {
        let tbl = &mut self.tbl;
        debug_assert!(!tbl.contains_key(&ev));
        let e = Expr::make_(ev, ty);
        tbl.insert(e.clone(), e.clone());
        e
    }

    /// Get the `=` constant
    pub fn mk_eq(&mut self) -> Expr {
        match self.eq {
            Some(ref c) => c.clone(),
            None => {
                let ty = self.mk_ty();
                let bool = self.mk_bool();
                let db0 = self.mk_bound_var(0, ty.clone());
                let arr = self.mk_arrow(db0.clone(), bool.clone());
                let arr = self.mk_arrow(db0.clone(), arr);
                let ty_eq = self.mk_pi(ty.clone(), arr);
                let name = Symbol::from_str("=");
                let c = self.mk_new_const(name, ty_eq);
                self.eq = Some(c.clone());
                c
            }
        }
    }

    /// Make `a = b`.
    ///
    /// Panics if `a` and `b` do not have the same type.
    pub fn mk_eq_app(&mut self, a: Expr, b: Expr) -> Expr {
        if a.ty() != b.ty() {
            panic!("mk_eq: {:?} and {:?} have incompatible types", &a, &b);
        }
        let eq = self.mk_eq();
        self.mk_app_l(eq, &[a.ty().clone(), a, b])
    }

    /// Get the `==>` constant.
    pub fn mk_imply(&mut self) -> Expr {
        match self.imply {
            Some(ref c) => c.clone(),
            None => {
                let bool = self.mk_bool();
                let arr = self.mk_arrow(bool.clone(), bool.clone());
                let arr = self.mk_arrow(bool.clone(), arr);
                let name = Symbol::from_str("==>");
                let i = self.mk_new_const(name, arr);
                self.imply = Some(i.clone());
                i
            }
        }
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
        // TODO: do cleanup in topological order? examine roots first,
        // or some kind of fixpoint, since when we remove a term we also
        // decrease its subterms' refcount

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
    ///
    /// # Examples
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
    fn mk_new_const(&mut self, s: Symbol, ty: Type) -> Expr {
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
        self.add_const_(c.clone());
        c
    }

    /// `assume F` is `F |- F`
    pub fn thm_assume(&mut self, e: &Expr) -> Thm {
        Thm::make_(e.clone(), vec![e.clone()])
    }

    /// `refl t` is `|- t=t`
    pub fn thm_refl(&mut self, e: Expr) -> Thm {
        let t = self.mk_eq_app(e.clone(), e.clone());
        Thm::make_(t, vec![])
    }

    /// `trans (F1 |- a=b) (F2 |- b'=c)` is `F1, F2 |- a=c`.
    ///
    /// Can fail if the conclusions don't match properly.
    pub fn thm_trans(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm, String> {
        let (a, b) =
            th1.concl().unfold_eq().ok_or("trans: th1 must be an equation")?;
        let (b2, c) =
            th2.concl().unfold_eq().ok_or("trans: th2 must be an equation")?;
        if b != b2 {
            Err("trans: th1 and th2's conclusions do not align")?;
        }

        let hyps = hyps_merge(th1, th2);
        let eq_a_c = self.mk_eq_app(a.clone(), c.clone());
        let th = Thm::make_(eq_a_c, hyps);
        Ok(th)
    }

    /// `congr (F1 |- f=g) (F2 |- t=u)` is `F1, F2 |- f t=g u`
    pub fn thm_congr(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm, String> {
        let (f, g) =
            th1.0.concl.unfold_eq().ok_or_else(|| {
                format!("congr: {:?} must be an equality", th1)
            })?;
        let (t, u) =
            th2.0.concl.unfold_eq().ok_or_else(|| {
                format!("congr: {:?} must be an equality", th2)
            })?;
        let ft = self.mk_app(f.clone(), t.clone());
        let gu = self.mk_app(g.clone(), u.clone());
        let eq = self.mk_eq_app(ft, gu);
        let hyps = hyps_merge(th1, th2);
        Ok(Thm::make_(eq, hyps))
    }

    /// `instantiate thm σ` produces `Fσ |- Gσ`  where `thm` is `F |- G`
    pub fn thm_instantiate(&mut self, th: &Thm, subst: &[(Var, Expr)]) -> Thm {
        let mut hyps = th.0.hyps.clone();
        let concl = self.subst(&th.0.concl, subst);
        for t in hyps.iter_mut() {
            *t = self.subst(t, subst);
        }
        Thm::make_(concl, hyps)
    }

    /// `abs x (F |- t=u)` is `F |- (λx.t)=(λx.u)`
    ///
    /// Panics if `x` occurs freely in `F`.
    pub fn thm_abs(&mut self, v: &Var, th: &Thm) -> Result<Thm, String> {
        if free_vars_iter(th.0.hyps.iter()).any(|v2| v == v2) {
            panic!("abs: variable {:?} occurs in hyps of {:?}", v, th);
        }

        let (t, u) =
            th.0.concl
                .unfold_eq()
                .ok_or("abs: thm's conclusion should be an equality")?;
        let lam_t = self.mk_lambda_abs(v.clone(), t.clone());
        let lam_u = self.mk_lambda_abs(v.clone(), u.clone());
        let eq = self.mk_eq_app(lam_t, lam_u);
        Ok(Thm::make_(eq, th.0.hyps.clone()))
    }

    /// `cut (F1 |- b) (F2, b |- c)` is `F1, F2 |- c`
    ///
    /// This fails if `b` does not occur _syntactically_ in the hypothesis
    /// of the second theorem.
    ///
    /// NOTE: this is not strictly necessary, as it's not an axiom in HOL light,
    /// but we include it here anyway.
    pub fn thm_cut(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm, String> {
        let th1_c = &th1.0.concl;
        if !th2.0.hyps.contains(th1_c) {
            Err("cut: th2's hyps do not contain th1's conclusion")?
        }
        let concl = th2.0.concl.clone();
        let mut hyps = th2.0.hyps.clone();
        hyps.retain(|u| u != th1_c);
        hyps.extend_from_slice(&th1.0.hyps[..]);
        Ok(Thm::make_(concl, hyps))
    }

    /// `mp (F1 |- a) (F2 |- a' ==> b)` is `F1, F2 |- b`
    /// where `a` and `a'` are alpha equivalent.
    pub fn thm_mp(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm, String> {
        let th2_c = &th2.0.concl;
        let (a, b) = th2_c.unfold_imply().ok_or_else(|| {
            format!("mp: second theorem {:?} must be an implication", th2)
        })?;
        if &th1.0.concl != a {
            let msg =format!("mp: conclusion of {:?} does not match LHS of implication of {:?}", th1, th2);
            return Err(msg);
        }
        let hyps = hyps_merge(th1, th2);
        Ok(Thm::make_(b.clone(), hyps))
    }

    /// `bool_eq (F1 |- a) (F2 |- a=b)` is `F1, F2 |- b`.
    /// This is the boolean equivalent of transitivity.
    pub fn thm_bool_eq(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm, String> {
        let th2_c = &th2.0.concl;
        let (a, b) = th2_c
            .unfold_eq()
            .filter(|(a, _)| a.ty() == &self.builtins_().bool)
            .ok_or_else(|| {
                //Some((a, b)) if a.ty() == &self.builtins_().bool => (a, b),
                format!(
                "bool-eq: {:?} should have a boleean equallity as conclusion",
                th2
            )
            })?;
        if a != &th1.0.concl {
            return Err(format!(
                "bool-eq: the conclusion of {:?} is not compatible with {:?}",
                th1, th2
            ));
        }

        let hyps = hyps_merge(th1, th2);
        Ok(Thm::make_(b.clone(), hyps))
    }

    /// `bool_eq_intro (F1, a |- b) (F2, b |- a)` is `F1, F2 |- b=a`.
    /// This is a way of building a boolean `a=b` from proofs of
    /// `a==>b` and `b==>a` (or `a|-b` and [b|-a`).
    pub fn thm_bool_eq_intro(&mut self, th1: &Thm, th2: &Thm) -> Thm {
        let mut hyps = vec![];
        hyps.extend(th1.0.hyps.iter().filter(|x| *x != &th2.0.concl).cloned());
        hyps.extend(th2.0.hyps.iter().filter(|x| *x != &th1.0.concl).cloned());
        let eq = self.mk_eq_app(th2.0.concl.clone(), th1.0.concl.clone());
        Thm::make_(eq, hyps)
    }

    /// `beta_conv ((λx.u) a)` is `|- (λx.u) a = u[x:=a]`.
    /// Fails if the term is not a beta-redex.
    pub fn thm_beta_conv(&mut self, e: &Expr) -> Result<Thm, String> {
        let (f, arg) = e.as_app().ok_or_else(|| {
            format!("beta-conv: expect an application, not {:?}", e)
        })?;
        let (ty, bod) = f.as_lambda().ok_or_else(|| {
            format!("beta-conv: expect a lambda, not {:?}", f)
        })?;
        debug_assert_eq!(ty, arg.ty()); // should already be enforced by typing.

        let lhs = e.clone();
        let rhs = self.subst1_(bod, 0, arg);
        let eq = self.mk_eq_app(lhs, rhs);
        Ok(Thm::make_(eq, vec![]))
    }

    /// `new_basic_definition (x=t)` where `x` is a variable and `t` a term
    /// with a closed type,
    /// returns a theorem `|- x=t` where `x` is now a constant, along with
    /// the constant `x`
    pub fn thm_new_basic_definition(&mut self, e: Expr) -> Result<Thm, String> {
        let (x, rhs) = e.unfold_eq().and_then(|(x,rhs)| {
            x.as_var().map(|x| (x,rhs))
        }).ok_or_else(|| format!("new definition: {:?} should be an equation `x = rhs` with rhs closed", e))?;
        if !rhs.is_closed() {
            Err(format!("rhs {:?} should be closed", rhs))?;
        }
        // checks that the type of `x` is closed
        if !x.ty.is_closed() {
            Err(format!("{:?} should have a closed type, not {:?}", x, x.ty))?;
        }

        let c = self.mk_new_const(x.name.clone(), x.ty.clone());
        let eqn = self.mk_eq_app(c, rhs.clone());
        Ok(Thm::make_(eqn, vec![]))
    }

    /// Create a new axiom `assumptions |- concl`.
    /// **use with caution**
    pub fn thm_axiom(&mut self, hyps: Vec<Expr>, concl: Expr) -> Thm {
        let thm = Thm::make_(concl, hyps);
        self.axioms.push(thm.clone());
        thm
    }
}
