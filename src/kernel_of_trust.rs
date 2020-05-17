//! Kernel of Trust: Terms and Theorems

use crate::fnv;
use std::{fmt, ops::Deref, sync::atomic};

#[cfg(features = "noarc")]
pub type Ref<T> = std::rc::Rc<T>;
#[cfg(features = "noarc")]
pub type WeakRef<T> = std::rc::Weak<T>;
#[cfg(features = "noarc")]
pub type Lock<T> = std::cell::RefCell<T>;

#[cfg(not(features = "noarc"))]
pub type Ref<T> = std::sync::Arc<T>;
#[cfg(not(features = "noarc"))]
pub type WeakRef<T> = std::sync::Weak<T>;
#[cfg(not(features = "noarc"))]
pub type Lock<T> = std::sync::Mutex<T>;

// TODO: use a proper enum for errors
/// Result type.
pub type Result<T> = std::result::Result<T, String>;

///! # Symbols.

/// Builtin symbols
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Hash, Eq, PartialEq)]
pub enum BuiltinSymbol {
    Eq,
    Imply,
    Select,
    Bool,
}
use BuiltinSymbol as BS;

/// Any kind of symbol.
#[derive(Debug, Clone, Ord, PartialOrd, Hash, Eq, PartialEq)]
pub enum Symbol {
    Builtin(BuiltinSymbol),
    Named(Ref<str>),
}

impl Symbol {
    /// New symbol from this string.
    pub fn from_str(s: &str) -> Self {
        let a = Ref::from(s);
        Symbol::Named(a)
    }

    pub fn name(&self) -> &str {
        match &self {
            Symbol::Builtin(s) => match s {
                BS::Eq => "=",
                BS::Imply => "==>",
                BS::Select => "select",
                BS::Bool => "Bool",
            },
            Symbol::Named(s) => &*s,
        }
    }
}

/// De Buijn indices.
pub type DbIndex = u32;

///! # Expressions, types, variables

/// An expression.
#[derive(Clone)]
pub struct Expr(Ref<ExprImpl>);

/// A weak reference to an expression.
#[derive(Clone)]
struct WExpr(WeakRef<ExprImpl>);

/// Types and Terms are the same, but this is helpful for documentation.
pub type Type = Expr;

/// The public view of an expression's root.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
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
    pub name: Symbol,
    pub ty: Expr,
}

/// The content of an expression.
struct ExprImpl {
    /// The view of the expression.
    view: ExprView,
    /// Number of DB indices missing. 0 means the term is closed.
    db_depth: DbIndex,
    /// Unique ID of the expr manager responsible for creating this expr.
    em_uid: u32,
    /// Type of the expression. Always present except for `Kind`.
    ty: Option<Expr>,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct ConstContent {
    name: Symbol,
    ty: Expr,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
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
            &(self.0.as_ref() as *const ExprImpl),
            &(other.0.as_ref() as *const _),
        )
    }
}

impl std::hash::Hash for Expr {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        // hash pointer
        std::ptr::hash(self.0.as_ref() as *const ExprImpl, h)
    }
}

// used to be able to lookup in the hashconsing map using an `ExprView`
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
}

impl BoundVarContent {
    /// De Bruijn index.
    pub fn idx(&self) -> DbIndex {
        self.idx
    }

    pub fn ty(&self) -> &Expr {
        &self.ty
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
        EConst(c) => {
            let d = c.ty.db_depth();
            debug_assert_eq!(d, 0); // constants should be closed
            d
        }
        EVar(v) => v.ty.db_depth(),
        EBoundVar(v) => u32::max(v.idx + 1, v.ty.db_depth()),
        EApp(a, b) => a.db_depth().max(b.db_depth()),
        ELambda(v_ty, e) | EPi(v_ty, e) => {
            // `e`'s depth is decremented here
            v_ty.db_depth().max(pred_db_idx(e.db_depth()))
        }
    }
}

impl ExprView {
    /// Shallow map, with a depth parameter.
    ///
    /// `k` is the current number of surrounding binders, it is passed back
    /// to the callback `f`, possibly incremented by one.
    pub fn map<F>(&self, mut f: F, k: DbIndex) -> Result<Self>
    where
        F: FnMut(&Expr, DbIndex) -> Result<Expr>,
    {
        Ok(match self {
            EType | EKind => self.clone(),
            EConst(c) => {
                EConst(ConstContent { ty: f(&c.ty, k)?, name: c.name.clone() })
            }
            EVar(v) => EVar(Var { ty: f(&v.ty, k)?, name: v.name.clone() }),
            EBoundVar(v) => {
                EBoundVar(BoundVarContent { ty: f(&v.ty, k)?, idx: v.idx })
            }
            EApp(a, b) => EApp(f(a, k)?, f(b, k)?),
            EPi(ty_a, b) => EPi(f(ty_a, k)?, f(b, k + 1)?),
            ELambda(ty_a, b) => ELambda(f(ty_a, k)?, f(b, k + 1)?),
        })
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
                EPi(ty, body) | ELambda(ty, body) => {
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

    /// Obtain a weak reference to this expression.
    #[inline]
    fn weak(&self) -> WExpr {
        WExpr(Ref::downgrade(&self.0))
    }

    /// Safe version of `ty`, that works even for `Kind`.
    pub fn ty_opt(&self) -> &Option<Expr> {
        &self.0.ty
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

    /// View as a pi-expression.
    pub fn as_pi(&self) -> Option<(&Type, &Expr)> {
        if let EPi(ref ty, ref bod) = self.0.view {
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

    /// Does this contain any free variables?
    pub fn has_free_vars(&self) -> bool {
        self.free_vars().next().is_some()
    }

    // helper for building expressions
    fn make_(v: ExprView, em_uid: u32, ty: Option<Expr>) -> Self {
        let db_depth = compute_db_depth(&v);
        Expr(Ref::new(ExprImpl { view: v, em_uid, ty, db_depth }))
    }

    // pretty print
    fn pp_(&self, k: DbIndex, out: &mut fmt::Formatter) -> fmt::Result {
        match self.view() {
            EKind => write!(out, "kind"),
            EType => write!(out, "type"),
            EConst(c) => write!(out, "{}", c.name.name()),
            EVar(v) => write!(out, "{}", v.name.name()),
            EBoundVar(v) => {
                // we may want to print non closed terms, so we need isize
                write!(out, "x{}", (k as isize - v.idx as isize - 1))
            }
            EApp(..) => {
                let (f, args) = self.unfold_app();
                write!(out, "(")?;
                f.pp_(k, out)?;
                for x in args {
                    write!(out, " ")?;
                    x.pp_(k, out)?;
                }
                write!(out, ")")
            }
            ELambda(ty_x, body) => {
                if ty_x.is_type() {
                    write!(out, "(Λx{} : ", k)?;
                } else {
                    write!(out, "(λx{} : ", k)?;
                }
                ty_x.pp_(k, out)?;
                write!(out, ". ")?;
                body.pp_(k + 1, out)?;
                write!(out, ")")
            }
            // TODO: disable
            EPi(x, body) if false && !x.is_type() && body.is_closed() => {
                // TODO: precedence to know whether to print "()"
                write!(out, "(")?;
                x.pp_(k, out)?;
                write!(out, ":")?;
                x.ty().pp_(k, out)?;
                write!(out, " -> ")?;
                body.pp_(k + 1, out)?;
                write!(out, ")")
            }
            EPi(x, body) => {
                write!(out, "(Πx{}", k)?;
                if !x.is_type() {
                    write!(out, " : ")?;
                    x.pp_(k, out)?;
                }
                write!(out, ". ")?;
                body.pp_(k + 1, out)?;
                write!(out, ")")
            }
        }?;
        //write!(out, "/{:?}", self.0.as_ref() as *const _)?; // pp pointer
        Ok(())
    }

    /// Basic printer.
    pub fn to_string(&self) -> String {
        format!("{:?}", self)
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
        write!(out, "{}:{:?}", self.name.name(), self.ty)
    }
}

///! # Theorems.
///
/// Theorems are proved correct by construction.

/// A theorem.
#[derive(Clone)]
pub struct Thm(Ref<ThmImpl>);

#[derive(Clone)]
struct ThmImpl {
    /// Conclusion of the theorem.
    concl: Expr,
    /// Hypothesis of the theorem.
    hyps: Vec<Expr>,
    /// Unique ID of the `ExprManager`
    em_uid: u32,
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
    fn make_(concl: Expr, em_uid: u32, mut hyps: Vec<Expr>) -> Self {
        if hyps.len() >= 2 {
            hyps.sort_unstable();
            hyps.dedup();
            hyps.shrink_to_fit();
        }
        Thm(Ref::new(ThmImpl { concl, em_uid, hyps }))
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
    /// Hashconsing table, with weak semantics.
    tbl: fnv::FnvHashMap<ExprView, WExpr>,
    builtins: Option<ExprBuiltins>,
    consts: fnv::FnvHashMap<Symbol, Expr>, // TODO: WExpr + collection? duplicate with `tbl`
    eq: Option<Expr>,
    imply: Option<Expr>,
    select: Option<Expr>,
    next_cleanup: usize,
    axioms: Vec<Thm>,
    uid: u32, // Unique to this EM
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

/// A substitution.
pub type Subst = Vec<(Var, Expr)>;

// used to allocate unique ExprManager IDs
static EM_ID: atomic::AtomicUsize = atomic::AtomicUsize::new(0);

impl ExprManager {
    /// Create a new term manager with given initial capacity.
    pub fn with_capacity(n: usize) -> Self {
        let tbl = fnv::new_table_with_cap(n);
        // allocate new uid
        let uid = EM_ID.fetch_add(1, atomic::Ordering::SeqCst);
        if uid > std::u32::MAX as usize {
            panic!("allocated more than u32::MAX ExprManager, cannot allocate more");
        }
        let mut em = ExprManager {
            tbl,
            builtins: None,
            consts: fnv::new_table_with_cap(n),
            eq: None,
            imply: None,
            select: None,
            next_cleanup: CLEANUP_PERIOD,
            axioms: vec![],
            uid: uid as u32,
        };
        // insert initial builtins
        let kind = em.hashcons_builtin_(EKind, None);
        em.tbl.insert(kind.view().clone(), kind.weak());
        let ty = em.hashcons_builtin_(EType, Some(kind.clone()));
        em.tbl.insert(ty.view().clone(), ty.weak());
        let bool = {
            let name = Symbol::Builtin(BS::Bool);
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
    fn hashcons_(&mut self, ev: ExprView) -> Result<Expr> {
        let tbl = &mut self.tbl; // lock tbl
        match tbl.get(&ev) {
            Some(v) => match WeakRef::upgrade(&v.0) {
                Some(t) => return Ok(Expr(t)), // still alive!
                None => (),
            },
            None => (),
        }
        // need to use `self` to build the type, so drop `tbl` first.
        drop(tbl);

        // every n cycles, do a `cleanup`
        // TODO: maybe if last cleanups were ineffective, increase n,
        // otherwise decrease n (down to some min value)
        if self.next_cleanup == 0 {
            eprintln!("expr.hashcons: cleanup"); // TODO: comment, or use callback in expr manager
            self.cleanup();
        } else {
            self.next_cleanup -= 1;
        }

        // need to insert the term, so first we need to compute its type.
        let ty = self.compute_ty_(&ev)?;
        let key = ev.clone();
        let e = Expr::make_(ev, self.uid, ty);
        //#[rustfmt::skip]
        //eprintln!("insert.expr.hashcons {:?} at {:?}", &e, e.0.as_ref() as *const _);
        //eprintln!("ev mem: {}", self.tbl.contains_key(&ev2));
        //eprintln!("btw table is {:#?}", &self.tbl);

        // lock table, again, but this time we'll write to it.
        // invariant: computing the type doesn't insert `e` in the table.
        let tbl = &mut self.tbl;
        tbl.insert(key, e.weak());
        //eprintln!("e.ev mem: {}", self.tbl.contains_key(&e.0.view));
        Ok(e)
    }

    fn add_const_(&mut self, e: Expr) {
        let consts = &mut self.consts;
        let name = if let EConst(ref c) = e.0.view {
            c.name.clone()
        } else {
            unreachable!("not a constant: {:?}", e);
        };
        self.tbl.insert(e.view().clone(), e.weak());
        consts.insert(name, e);
    }

    fn hashcons_builtin_(&mut self, ev: ExprView, ty: Option<Expr>) -> Expr {
        let tbl = &mut self.tbl;
        debug_assert!(!tbl.contains_key(&ev));
        let e = Expr::make_(ev, self.uid, ty);
        tbl.insert(e.view().clone(), e.weak());
        e
    }

    #[inline]
    fn check_uid_(&self, e: &Expr) {
        assert!(self.uid == e.0.em_uid); // term should belong to this EM
    }

    #[inline]
    fn check_thm_uid_(&self, th: &Thm) {
        assert!(self.uid == th.0.em_uid); // theorem should belong to this EM
    }

    /// Get the `=` constant
    pub fn mk_eq(&mut self) -> Expr {
        match self.eq {
            Some(ref c) => c.clone(),
            None => {
                let ty = self.mk_ty();
                let bool = self.mk_bool();
                let db0 = self.mk_bound_var(0, ty.clone());
                let arr = self.mk_arrow(db0.clone(), bool.clone()).unwrap();
                let arr = self.mk_arrow(db0.clone(), arr).unwrap();
                let ty_eq = self.mk_pi_(ty.clone(), arr).unwrap();
                let name = Symbol::Builtin(BS::Eq);
                let c = self.mk_new_const(name, ty_eq).unwrap();
                self.eq = Some(c.clone());
                c
            }
        }
    }

    /// Make `a = b`.
    ///
    /// Panics if `a` and `b` do not have the same type.
    pub fn mk_eq_app(&mut self, a: Expr, b: Expr) -> Result<Expr> {
        self.check_uid_(&a);
        self.check_uid_(&b);
        if a.ty() != b.ty() {
            return Err(format!(
                "mk_eq: {:?} and {:?} have incompatible types",
                &a, &b
            ));
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
                let arr = self.mk_arrow(bool.clone(), bool.clone()).unwrap();
                let arr = self.mk_arrow(bool.clone(), arr).unwrap();
                let name = Symbol::Builtin(BS::Imply);
                let i = self.mk_new_const(name, arr).unwrap();
                self.imply = Some(i.clone());
                i
            }
        }
    }

    /// Get the `select` constant.
    pub fn mk_select(&mut self) -> Expr {
        match self.select {
            Some(ref c) => c.clone(),
            None => {
                let ty = self.mk_ty();
                // build type `Πa. (a->bool)->a`
                let db0 = self.mk_bound_var(0, ty.clone());
                let bool = self.mk_bool();
                let arr = self.mk_arrow(db0.clone(), bool.clone()).unwrap();
                let arr = self.mk_arrow(arr, db0.clone()).unwrap();
                let ty = self.mk_pi_(ty, arr).unwrap();
                let name = Symbol::Builtin(BS::Select);
                let res = self.mk_new_const(name, ty).unwrap();
                self.select = Some(res.clone());
                res
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
    fn compute_ty_(&mut self, e: &ExprView) -> Result<Option<Expr>> {
        Ok(match e {
            EKind => None,
            EType => Some(self.builtins_().ty.clone()),
            EConst(c) => Some(c.ty.clone()),
            EVar(v) => Some(v.ty.clone()),
            EBoundVar(v) => Some(v.ty.clone()),
            ELambda(v_ty, body) => {
                // type of `λx:a. t` is `Πx:a. typeof(b)`.
                let ty_body = body.ty().clone();
                Some(self.hashcons_(EPi(v_ty.clone(), ty_body))?)
            }
            EPi(v_ty, e) => {
                if !v_ty.is_type() && !v_ty.ty().is_type() {
                    return Err(format!(
                        "pi: variable must be a type or be of type `type`, \
                        not `{:?}` : `{:?}`",
                        v_ty,
                        v_ty.ty()
                    ));
                };
                if !e.ty().is_type() && !e.ty().is_kind() {
                    return Err(format!(
                        "pi: body must have type `type` or `kind`, not {:?}",
                        e.ty()
                    ));
                };
                Some(self.builtins_().ty.clone())
            }
            EApp(f, arg) => match &f.ty().0.view {
                EPi(ty_var_f, ref ty_body_f) => {
                    // rule: `f: Πx:tya. b`, `arg: tya` ==> `f arg : b[arg/x]`
                    if ty_var_f != arg.ty() {
                        return Err(format!(
                            "apply: incompatible types: \
                                function `{:?}` has type `{:?}`, \
                                expecting arg of type {:?}, \
                                argument `{:?}` has type `{:?}`",
                            f,
                            f.ty(),
                            ty_var_f,
                            arg,
                            arg.ty()
                        ));
                    }
                    Some(self.subst1_(ty_body_f, 0, arg)?)
                }
                _ => panic!("cannot apply term with a non-pi type"),
            },
        })
    }

    // TODO: have a (dense) stack of substitutions to do? could be useful
    // for type inference in `f t1…tn`, instantiating `n` Π types at once.

    /// Replace DB0 in `t` by `u`, under `k` intermediate binders.
    fn subst1_(&mut self, t: &Expr, k: u32, u: &Expr) -> Result<Expr> {
        if t.is_closed() {
            return Ok(t.clone()); // shortcut
        }

        Ok(match t.view() {
            EKind | EType | EConst(..) => t.clone(),
            EApp(a, b) => {
                let a2 = self.subst1_(a, k, u)?;
                let b2 = self.subst1_(b, k, u)?;
                if a == &a2 && b == &b2 {
                    t.clone() // no need to do hashconsing
                } else {
                    self.hashcons_(EApp(a2, b2))?
                }
            }
            ELambda(v_ty, body) => {
                let v_ty2 = self.subst1_(v_ty, k, u)?;
                let body2 = self.subst1_(body, k + 1, u)?;
                if v_ty == &v_ty2 && body == &body2 {
                    t.clone()
                } else {
                    self.hashcons_(ELambda(v_ty2, body2))?
                }
            }
            EPi(v_ty, body) => {
                let v_ty2 = self.subst1_(v_ty, k, u)?;
                let body2 = self.subst1_(body, k + 1, u)?;
                self.hashcons_(EPi(v_ty2, body2))?
            }
            EVar(v) => {
                let v2 = Var {
                    ty: self.subst1_(&v.ty, k, u)?,
                    name: v.name().clone(),
                };
                self.hashcons_(EVar(v2))?
            }
            EBoundVar(v) if v.idx == k => {
                // substitute here, but shifting `u` by `k` to
                // account for the `k` intermediate binders
                self.shift_(u, k, 0)?
            }
            EBoundVar(v) if v.idx > k => {
                // need to unshift by 1, since we remove a binder and this is open
                let v2 = BoundVarContent {
                    idx: v.idx - 1,
                    ty: self.subst1_(&v.ty, k, u)?,
                };
                self.hashcons_(EBoundVar(v2))?
            }
            EBoundVar(v) => {
                let v2 = BoundVarContent {
                    idx: v.idx,
                    ty: self.subst1_(&v.ty, k, u)?,
                };
                self.hashcons_(EBoundVar(v2))?
            }
        })
    }

    /// Shift free DB vars by `n` under `k` intermediate binders
    fn shift_(&mut self, t: &Expr, n: DbIndex, k: DbIndex) -> Result<Expr> {
        if n == 0 || t.is_closed() {
            return Ok(t.clone()); // shortcut for identity
        }

        let ev = t.view();
        Ok(match ev {
            EKind | EType | EConst(..) => t.clone(),
            EApp(..) | ELambda(..) | EPi(..) | EVar(..) => {
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
                self.hashcons_(EBoundVar(BoundVarContent {
                    idx: v.idx + n,
                    ty,
                }))?
            }
        })
    }

    /// For each pair `(x,u)` in `subst`, replace instances of the free
    /// variable `x` by `u` in `t`.
    pub fn subst(&mut self, t: &Expr, subst: &[(Var, Expr)]) -> Result<Expr> {
        self.check_uid_(&t);
        struct Replace<'a> {
            // cache, relative to depth
            em: &'a mut ExprManager,
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
                                let u3 = self.em.shift_(u2, k, 0)?;
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
                        self.em.mk_var(v2)
                    }
                    ev => {
                        // shallow map + cache
                        let uv = ev.map(|sub, k| self.replace(sub, k), k)?;
                        self.em.hashcons_(uv)?
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
        let mut replace = Replace { em: self, subst };
        eprintln!("### start replace `{:?}`, subst {:?}", t, subst);
        replace.replace(t, 0)
    }

    /// Cleanup terms that are only referenced by this table.
    ///
    /// This is done regularly when new terms are created, but one can
    /// also call `cleanup` manually.
    pub fn cleanup(&mut self) {
        self.next_cleanup = CLEANUP_PERIOD;

        self.tbl.retain(|_, v| {
            // if `v` is not used anywhere else, it's the only
            // references and should have a strong count of 1.
            // This is thread safe as the only way this is 1 is if it's already
            // not referenced anywhere, and we don't provide any way to produce
            // a weak ref.
            let n = WeakRef::strong_count(&v.0);
            n > 0
        })
    }

    /// The type of types. This has type `self.mk_kind()`.
    pub fn mk_ty(&self) -> Expr {
        self.builtins_().ty.clone()
    }

    /// The "type" of `type`. This is the only typeless expression.
    ///
    /// Trying to compute this expression's type panics.
    pub fn mk_kind(&self) -> Expr {
        self.builtins_().kind.clone()
    }

    /// The type of booleans.
    pub fn mk_bool(&self) -> Expr {
        self.builtins_().bool.clone()
    }

    /// Apply `a` to `b`.
    pub fn mk_app(&mut self, a: Expr, b: Expr) -> Result<Expr> {
        self.check_uid_(&a);
        self.check_uid_(&b);
        self.hashcons_(EApp(a, b))
    }

    /// Apply `f` to the given arguments.
    ///
    /// `I` is an iterator that takes a closure and calls it on
    /// a series of expressions successively.
    pub fn mk_app_iter<I>(&mut self, f: Expr, mut args: I) -> Result<Expr>
    where
        I: FnMut(
            &mut Self,
            &mut dyn FnMut(&mut Self, Expr) -> Result<()>,
        ) -> Result<()>,
    {
        // TODO: compute type in one go?
        let mut e = f;
        args(self, &mut |em: &mut Self, x: Expr| {
            let e2 = e.clone();
            e = em.mk_app(e2, x)?;
            Ok(())
        })?;
        Ok(e)
    }

    /// Apply `f` to the given arguments.
    pub fn mk_app_l(&mut self, f: Expr, args: &[Expr]) -> Result<Expr> {
        self.mk_app_iter(f, |em, f| {
            for x in args {
                f(em, x.clone())?
            }
            Ok(())
        })
    }

    /// Make a free variable.
    pub fn mk_var(&mut self, v: Var) -> Expr {
        self.check_uid_(&v.ty);
        self.hashcons_(EVar(v)).expect("mk_var can't fail")
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

    /// Make a lambda term.
    fn mk_lambda_(&mut self, ty_var: Type, body: Expr) -> Result<Expr> {
        self.check_uid_(&ty_var);
        self.check_uid_(&body);
        self.hashcons_(ELambda(ty_var, body))
    }

    /// Substitute `v` with db0 in `body`.
    fn abs_on_(&mut self, v: Var, body: Expr) -> Result<Expr> {
        self.check_uid_(&v.ty);
        self.check_uid_(&body);
        let v_ty = &v.ty;
        if !v_ty.is_closed() {
            return Err(format!(
                "mk_abs: var {:?} has non-closed type {:?}",
                &v, v_ty
            ));
        }
        let v_ty = v_ty.clone();
        // replace `v` with `db0` in `body`. This should also take
        // care of shifting the DB by 1 as appropriate.
        let db0 = self.mk_bound_var(0, v_ty.clone());
        let body = self.shift_(&body, 1, 0)?;
        self.subst(&body, &[(v, db0)])
    }

    /// Make a lambda term by abstracting on `v`.
    pub fn mk_lambda(&mut self, v: Var, body: Expr) -> Result<Expr> {
        self.check_uid_(&v.ty);
        self.check_uid_(&body);
        let v_ty = v.ty.clone();
        let body = self.abs_on_(v, body)?;
        self.mk_lambda_(v_ty, body)
    }

    /// Bind several variables at once.
    pub fn mk_lambda_l<I>(&mut self, vars: I, body: Expr) -> Result<Expr>
    where
        I: DoubleEndedIterator<Item = Var>,
    {
        let mut e = body;
        // TODO: substitute more efficiently (with a stack, rather than one by one)?
        // right-assoc
        for v in vars.rev() {
            e = self.mk_lambda(v, e)?;
        }
        Ok(e)
    }

    /// Make a pi term.
    fn mk_pi_(&mut self, ty_var: Expr, body: Expr) -> Result<Expr> {
        self.hashcons_(EPi(ty_var, body))
    }

    /// Make a pi term by absracting on `v`.
    pub fn mk_pi(&mut self, v: Var, body: Expr) -> Result<Expr> {
        self.check_uid_(&v.ty);
        self.check_uid_(&body);
        let v_ty = v.ty.clone();
        let body = self.abs_on_(v, body)?;
        self.mk_pi_(v_ty, body)
    }

    /// Bind several variables at once.
    pub fn mk_pi_l<I>(&mut self, vars: I, body: Expr) -> Result<Expr>
    where
        I: DoubleEndedIterator<Item = Var>,
    {
        let mut e = body;
        // TODO: substitute more efficiently (with a stack, rather than one by one)?
        // right-assoc
        for v in vars.rev() {
            e = self.mk_pi(v, e)?;
        }
        Ok(e)
    }

    /// Make an arrow `a -> b` term.
    ///
    /// This builds `Π_:a. b`.
    pub fn mk_arrow(&mut self, ty1: Expr, ty2: Expr) -> Result<Expr> {
        // need to shift ty2 by 1 to account for the Π binder.
        self.check_uid_(&ty1);
        self.check_uid_(&ty2);
        let ty2 = self.shift_(&ty2, 1, 0)?;
        self.mk_pi_(ty1, ty2)
    }

    /// Declare a new constant with given name and type.
    ///
    /// panics if some constant with the same name exists, or if
    /// the type is not closed.
    /// This constant has no axiom associated to it, it is entirely opaque.
    pub fn mk_new_const(&mut self, s: Symbol, ty: Type) -> Result<Expr> {
        self.check_uid_(&ty);
        if self.consts.contains_key(&s) {
            return Err(format!("a constant named {:?} already exists", &s));
        }
        if !ty.is_closed() || ty.free_vars().next().is_some() {
            panic!(
                "cannot create constant named {:?} with non-closed type {:?}",
                &s, &ty
            );
        }
        let c = self.hashcons_(EConst(ConstContent { name: s.clone(), ty }))?;
        self.add_const_(c.clone());
        Ok(c)
    }

    /// `assume F` is `F |- F`
    pub fn thm_assume(&mut self, e: &Expr) -> Thm {
        self.check_uid_(&e);
        Thm::make_(e.clone(), self.uid, vec![e.clone()])
    }

    /// `refl t` is `|- t=t`
    pub fn thm_refl(&mut self, e: Expr) -> Thm {
        self.check_uid_(&e);
        let t = self.mk_eq_app(e.clone(), e.clone()).expect("refl");
        Thm::make_(t, self.uid, vec![])
    }

    /// `trans (F1 |- a=b) (F2 |- b'=c)` is `F1, F2 |- a=c`.
    ///
    /// Can fail if the conclusions don't match properly.
    pub fn thm_trans(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm> {
        self.check_thm_uid_(th1);
        self.check_thm_uid_(th2);
        let (a, b) =
            th1.concl().unfold_eq().ok_or("trans: th1 must be an equation")?;
        let (b2, c) =
            th2.concl().unfold_eq().ok_or("trans: th2 must be an equation")?;
        if b != b2 {
            Err("trans: th1 and th2's conclusions do not align")?;
        }

        let hyps = hyps_merge(th1, th2);
        let eq_a_c = self.mk_eq_app(a.clone(), c.clone())?;
        let th = Thm::make_(eq_a_c, self.uid, hyps);
        Ok(th)
    }

    /// `congr (F1 |- f=g) (F2 |- t=u)` is `F1, F2 |- f t=g u`
    pub fn thm_congr(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm> {
        self.check_thm_uid_(th1);
        self.check_thm_uid_(th2);
        let (f, g) =
            th1.0.concl.unfold_eq().ok_or_else(|| {
                format!("congr: {:?} must be an equality", th1)
            })?;
        let (t, u) =
            th2.0.concl.unfold_eq().ok_or_else(|| {
                format!("congr: {:?} must be an equality", th2)
            })?;
        let ft = self.mk_app(f.clone(), t.clone())?;
        let gu = self.mk_app(g.clone(), u.clone())?;
        let eq = self.mk_eq_app(ft, gu)?;
        let hyps = hyps_merge(th1, th2);
        Ok(Thm::make_(eq, self.uid, hyps))
    }

    /// `instantiate thm σ` produces `Fσ |- Gσ`  where `thm` is `F |- G`
    ///
    /// Returns an error if the substitution is not closed.
    pub fn thm_instantiate(
        &mut self,
        th: &Thm,
        subst: &[(Var, Expr)],
    ) -> Result<Thm> {
        self.check_thm_uid_(th);
        if let Some((v, t)) = subst.iter().find(|(_, t)| !t.is_closed()) {
            return Err(format!(
                    "instantiate: substitution {:?} contains non-closed binding {:?} := {:?}",
                    subst, v, t));
        }

        let mut hyps = th.0.hyps.clone();
        let concl = self.subst(&th.0.concl, subst)?;
        for t in hyps.iter_mut() {
            *t = self.subst(t, subst)?;
        }
        Ok(Thm::make_(concl, self.uid, hyps))
    }

    /// `abs x (F |- t=u)` is `F |- (λx.t)=(λx.u)`
    ///
    /// Panics if `x` occurs freely in `F`.
    pub fn thm_abs(&mut self, v: &Var, th: &Thm) -> Result<Thm> {
        self.check_uid_(&v.ty);
        self.check_thm_uid_(th);
        if free_vars_iter(th.0.hyps.iter()).any(|v2| v == v2) {
            return Err(format!(
                "abs: variable {:?} occurs in hyps of {:?}",
                v, th
            ));
        }

        let (t, u) =
            th.0.concl
                .unfold_eq()
                .ok_or("abs: thm's conclusion should be an equality")?;
        let lam_t = self.mk_lambda(v.clone(), t.clone())?;
        let lam_u = self.mk_lambda(v.clone(), u.clone())?;
        let eq = self.mk_eq_app(lam_t, lam_u)?;
        Ok(Thm::make_(eq, self.uid, th.0.hyps.clone()))
    }

    /// `cut (F1 |- b) (F2, b |- c)` is `F1, F2 |- c`
    ///
    /// This fails if `b` does not occur _syntactically_ in the hypothesis
    /// of the second theorem.
    ///
    /// NOTE: this is not strictly necessary, as it's not an axiom in HOL light,
    /// but we include it here anyway.
    pub fn thm_cut(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm> {
        self.check_thm_uid_(th1);
        self.check_thm_uid_(th2);
        let th1_c = &th1.0.concl;
        if !th2.0.hyps.contains(th1_c) {
            Err("cut: th2's hyps do not contain th1's conclusion")?
        }
        let concl = th2.0.concl.clone();
        let mut hyps = th2.0.hyps.clone();
        hyps.retain(|u| u != th1_c);
        hyps.extend_from_slice(&th1.0.hyps[..]);
        Ok(Thm::make_(concl, self.uid, hyps))
    }

    /// `mp (F1 |- a) (F2 |- a' ==> b)` is `F1, F2 |- b`
    /// where `a` and `a'` are alpha equivalent.
    pub fn thm_mp(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm> {
        self.check_thm_uid_(th1);
        self.check_thm_uid_(th2);
        let th2_c = &th2.0.concl;
        let (a, b) = th2_c.unfold_imply().ok_or_else(|| {
            format!("mp: second theorem {:?} must be an implication", th2)
        })?;
        if &th1.0.concl != a {
            let msg = format!(
                "mp: conclusion of {:?} does not match LHS of implication of {:?}",
                th1, th2
            );
            return Err(msg);
        }
        let hyps = hyps_merge(th1, th2);
        Ok(Thm::make_(b.clone(), self.uid, hyps))
    }

    /// `bool_eq (F1 |- a) (F2 |- a=b)` is `F1, F2 |- b`.
    /// This is the boolean equivalent of transitivity.
    pub fn thm_bool_eq(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm> {
        self.check_thm_uid_(th1);
        self.check_thm_uid_(th2);
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
        Ok(Thm::make_(b.clone(), self.uid, hyps))
    }

    /// `bool_eq_intro (F1, a |- b) (F2, b |- a)` is `F1, F2 |- b=a`.
    /// This is a way of building a boolean `a=b` from proofs of
    /// `a==>b` and `b==>a` (or `a|-b` and [b|-a`).
    pub fn thm_bool_eq_intro(&mut self, th1: &Thm, th2: &Thm) -> Result<Thm> {
        self.check_thm_uid_(th1);
        self.check_thm_uid_(th2);
        let mut hyps = vec![];
        hyps.extend(th1.0.hyps.iter().filter(|x| *x != &th2.0.concl).cloned());
        hyps.extend(th2.0.hyps.iter().filter(|x| *x != &th1.0.concl).cloned());
        let eq = self.mk_eq_app(th2.0.concl.clone(), th1.0.concl.clone())?;
        Ok(Thm::make_(eq, self.uid, hyps))
    }

    /// `beta_conv ((λx.u) a)` is `|- (λx.u) a = u[x:=a]`.
    /// Fails if the term is not a beta-redex.
    pub fn thm_beta_conv(&mut self, e: &Expr) -> Result<Thm> {
        self.check_uid_(e);
        let (f, arg) = e.as_app().ok_or_else(|| {
            format!("beta-conv: expect an application, not {:?}", e)
        })?;
        let (ty, bod) = f.as_lambda().ok_or_else(|| {
            format!("beta-conv: expect a lambda, not {:?}", f)
        })?;
        debug_assert_eq!(ty, arg.ty()); // should already be enforced by typing.

        let lhs = e.clone();
        let rhs = self.subst1_(bod, 0, arg)?;
        let eq = self.mk_eq_app(lhs, rhs)?;
        Ok(Thm::make_(eq, self.uid, vec![]))
    }

    /// `new_basic_definition (x=t)` where `x` is a variable and `t` a term
    /// with a closed type,
    /// returns a theorem `|- x=t` where `x` is now a constant, along with
    /// the constant `x`.
    pub fn thm_new_basic_definition(&mut self, e: Expr) -> Result<(Thm, Expr)> {
        self.check_uid_(&e);
        let (x, rhs) = e
            .unfold_eq()
            .and_then(|(x, rhs)| x.as_var().map(|x| (x, rhs)))
            .ok_or_else(|| {
                format!(
                    "new definition: {:?} should be an equation `x = rhs` with rhs closed",
                    e
                )
            })?;
        if !rhs.is_closed() || rhs.has_free_vars() {
            return Err(format!("rhs {:?} should be closed", rhs));
        }
        // checks that the type of `x` is closed
        if !x.ty.is_closed() || x.ty.has_free_vars() {
            return Err(format!(
                "{:?} should have a closed type, not {:?}",
                x, x.ty
            ));
        }

        let c = self.mk_new_const(x.name.clone(), x.ty.clone())?;
        let eqn = self.mk_eq_app(c.clone(), rhs.clone())?;
        let thm = Thm::make_(eqn, self.uid, vec![]);
        Ok((thm, c))
    }

    /// Create a new axiom `assumptions |- concl`.
    /// **use with caution**
    pub fn thm_axiom(&mut self, hyps: Vec<Expr>, concl: Expr) -> Thm {
        self.check_uid_(&concl);
        hyps.iter().for_each(|e| self.check_uid_(e));

        let thm = Thm::make_(concl, self.uid, hyps);
        self.axioms.push(thm.clone());
        thm
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
            return Err(format!(
                "new_basic_type_def: theorem must not have hyps, {:?}",
                thm_inhabited
            ));
        }
        let (phi, witness) =
            thm_inhabited.concl().as_app().ok_or_else(|| {
                format!(
                    "conclusion of theorem must be `(Phi x)`, not `{:?}`",
                    thm_inhabited.concl()
                )
            })?;
        dbg!((phi, witness));
        // the concrete type
        let ty = witness.ty().clone();
        // check that all free variables are type variables
        let mut fvars: Vec<Var> =
            thm_inhabited.concl().free_vars().cloned().collect();
        fvars.sort_unstable();
        fvars.dedup();

        if let Some(v) = fvars.iter().find(|v| !v.ty.is_type()) {
            return Err(format!(
                "free variable `{:?}` has type `{:?}`, not `type`",
                &v, &v.ty
            ));
        }
        dbg!(&fvars);

        // free vars, as expressions
        let fvars_exprs: Vec<_> =
            fvars.iter().map(|v| self.mk_var(v.clone())).collect();

        // construct new type and mapping functions
        let tau = {
            let ttype = self.mk_ty();
            let ty_tau = self.mk_pi_l(fvars.iter().cloned(), ttype)?;
            self.mk_new_const(name_tau, ty_tau)?
        };
        dbg!(&tau);

        // `tau` applied to `fvars`
        let tau_vars = self.mk_app_l(tau.clone(), &fvars_exprs)?;
        dbg!(&tau_vars);

        let c_abs = {
            let ty = self.mk_arrow(ty.clone(), tau_vars.clone())?;
            let ty = self.mk_pi_l(fvars.iter().cloned(), ty)?;
            self.mk_new_const(abs, ty)?
        };
        let c_repr = {
            let ty = self.mk_arrow(tau_vars.clone(), ty.clone())?;
            let ty = self.mk_pi_l(fvars.iter().cloned(), ty)?;
            self.mk_new_const(repr, ty)?
        };
        dbg!(&c_abs, c_abs.ty(), &c_repr, c_repr.ty());

        let abs_x = self.mk_var_str("x", tau_vars.clone());
        let abs_thm = {
            // `|- abs (repr x) = x`
            let repr = self.mk_app_l(c_repr.clone(), &fvars_exprs)?;
            let t = self.mk_app(repr, abs_x.clone())?;
            let abs = self.mk_app_l(c_abs.clone(), &fvars_exprs)?;
            let abs_t = self.mk_app(abs, t)?;
            let eqn = self.mk_eq_app(abs_t.clone(), abs_x.clone())?;
            dbg!(Thm::make_(eqn, self.uid, vec![]))
        };
        let repr_x = self.mk_var_str("x", ty.clone());
        let repr_thm = {
            // `|- Phi x <=> repr (abs x) = x`
            let abs = self.mk_app_l(c_abs.clone(), &fvars_exprs)?;
            let t1 = self.mk_app(abs, repr_x.clone())?;
            let repr = self.mk_app_l(c_repr.clone(), &fvars_exprs)?;
            let t2 = dbg!(self.mk_app(repr, t1))?;
            let eq_t2_x = dbg!(self.mk_eq_app(t2, repr_x.clone()))?;
            let phi_x = dbg!(self.mk_app(phi.clone(), repr_x.clone()))?;
            dbg!(Thm::make_(self.mk_eq_app(phi_x, eq_t2_x)?, self.uid, vec![]))
        };

        let c = NewTypeDef {
            tau,
            c_repr,
            c_abs,
            fvars,
            repr_x: repr_x.as_var().unwrap().clone(),
            abs_thm,
            abs_x: abs_x.as_var().unwrap().clone(),
            repr_thm,
        };
        Ok(c)
    }
}

/// Helper for defining new type.
#[derive(Debug, Clone)]
pub struct NewTypeDef {
    /// the new type constructor
    pub tau: Expr,
    pub fvars: Vec<Var>,
    /// Function from the general type to `tau`
    pub c_abs: Expr,
    /// Function from `tau` back to the general type
    pub c_repr: Expr,
    /// `abs_thm` is `|- abs (repr x) = x`
    pub abs_thm: Thm,
    pub abs_x: Var,
    /// `repr_thm` is `|- Phi x <=> repr (abs x) = x`
    pub repr_thm: Thm,
    pub repr_x: Var,
}
