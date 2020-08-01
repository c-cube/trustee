//! Kernel of Trust: Terms and Theorems

use crate::{fnv, meta, rstr::RStr};
use std::{fmt, ops::Deref, sync::atomic};

pub type Ref<T> = std::rc::Rc<T>;
pub type WeakRef<T> = std::rc::Weak<T>;
pub type Lock<T> = std::cell::RefCell<T>;

/// For infix/prefix/postfix constants.
pub type Fixity = crate::syntax::Fixity;

/// Errors that can be returned from the Kernel.
#[derive(Debug, Clone)]
pub struct Error {
    pub msg: ErrorMsg,
    pub source: Option<Box<Error>>,
}

/// An error message.
#[derive(Debug, Clone)]
pub enum ErrorMsg {
    EStatic(&'static str),
    EDyn(String),
}

impl fmt::Display for Error {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        match &self.msg {
            ErrorMsg::EStatic(msg) => write!(out, "{}", msg),
            ErrorMsg::EDyn(s) => write!(out, "{}", &s),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match &self.source {
            None => None,
            Some(p) => Some(&*p),
        }
    }
}

impl Error {
    /// Build a new error.
    pub fn new(msg: &'static str) -> Self {
        Error {
            msg: ErrorMsg::EStatic(msg),
            source: None,
        }
    }

    pub fn new_string(msg: String) -> Self {
        Error {
            msg: ErrorMsg::EDyn(msg),
            source: None,
        }
    }

    /// Change the source of this error.
    pub fn set_source(mut self, src: Self) -> Self {
        self.source = Some(Box::new(src));
        self
    }

    pub fn to_string(&self) -> String {
        format!("{}", self)
    }
}

/// Result type.
pub type Result<T> = std::result::Result<T, Error>;

///! # Symbols.

/// Description of builtin symbols
#[derive(Debug)]
pub struct BuiltinSymbol<'a> {
    eq: &'a str,
    bool: &'a str,
}

impl<'a> BuiltinSymbol<'a> {
    /// Default symbols.
    pub fn default() -> Self {
        Self {
            eq: "=",
            bool: "bool",
        }
    }
}

impl<'a> Default for BuiltinSymbol<'a> {
    fn default() -> Self {
        Self::default()
    }
}

/// A logic symbol.
#[derive(Debug, Clone, Ord, PartialOrd, Hash, Eq, PartialEq)]
pub struct Symbol(RStr);

impl Symbol {
    /// New symbol from this string.
    pub fn from_str(s: &str) -> Self {
        let a = RStr::from(s);
        Symbol(a)
    }

    pub fn from_rstr(s: &RStr) -> Self {
        Symbol(s.clone())
    }

    pub fn from_rc_str(s: &std::rc::Rc<str>) -> Self {
        let a: RStr = RStr::from(s.as_ref());
        Symbol(a)
    }

    pub fn name(&self) -> &str {
        &*self.0
    }
}

impl std::borrow::Borrow<str> for Symbol {
    fn borrow(&self) -> &str {
        &*self.0
    }
}

impl<'a> From<&'a str> for Symbol {
    fn from(s: &str) -> Self {
        Symbol::from_str(s)
    }
}

/// De Buijn indices.
pub type DbIndex = u32;

///! # Expressions, types, variables

/// An expression.
///
/// The expression is refcounted and is thus cheaply clonable.
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
    EConst(Box<ConstContent>),
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

#[derive(Clone, Debug)]
pub struct ConstContent {
    pub name: Symbol,
    pub ty: Expr,
    tag: ConstTag,
    fix: std::cell::Cell<Fixity>,
}

#[derive(Debug, PartialEq, Clone, Copy)]
#[repr(u8)]
enum ConstTag {
    None,
    Eq,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct BoundVarContent {
    idx: DbIndex,
    ty: Expr,
}

impl Eq for ConstContent {}
impl PartialEq for ConstContent {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.ty == other.ty
    }
}

impl std::hash::Hash for ConstContent {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state);
        self.ty.hash(state)
    }
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

impl fmt::Display for Expr {
    // use the pretty-printer from `syntax`
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        crate::syntax::print_expr(self, out)
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
        Var {
            name: Symbol::from_str(name),
            ty,
        }
    }

    pub fn from_rstr(name: &RStr, ty: Type) -> Var {
        Var {
            name: Symbol::from_rstr(name),
            ty,
        }
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

impl ConstContent {
    #[inline]
    pub fn fixity(&self) -> Fixity {
        self.fix.get()
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
            EConst(c) => EConst(Box::new(ConstContent {
                ty: f(&c.ty, k)?,
                name: c.name.clone(),
                tag: c.tag,
                fix: c.fix.clone(),
            })),
            EVar(v) => EVar(Var {
                ty: f(&v.ty, k)?,
                name: v.name.clone(),
            }),
            EBoundVar(v) => EBoundVar(BoundVarContent {
                ty: f(&v.ty, k)?,
                idx: v.idx,
            }),
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
        FreeVars {
            seen: fnv::new_set_with_cap(16),
            st: vec![],
        }
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

    /// Is this the representation of `=`?
    pub fn is_eq(&self) -> bool {
        match &self.0.view {
            EConst(c) => c.tag == ConstTag::Eq,
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
        Expr(Ref::new(ExprImpl {
            view: v,
            em_uid,
            ty,
            db_depth,
        }))
    }

    // pretty print
    fn pp_(&self, k: DbIndex, out: &mut fmt::Formatter, full: bool) -> fmt::Result {
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
                if !full && f.is_eq() && args.len() == 3 {
                    // special: `a=b`, skip type arg
                    args[1].pp_(k, out, full)?;
                    write!(out, " = ")?;
                    args[2].pp_(k, out, full)?;
                } else {
                    f.pp_(k, out, full)?;
                    for x in args {
                        write!(out, " ")?;
                        x.pp_(k, out, full)?;
                    }
                }
                write!(out, ")")
            }
            ELambda(ty_x, body) => {
                if full {
                    write!(out, "(\\x{} : ", k)?;
                    ty_x.pp_(k, out, full)?;
                } else {
                    write!(out, "(\\x{}", k)?;
                }
                write!(out, ". ")?;
                body.pp_(k + 1, out, full)?;
                write!(out, ")")
            }
            // TODO: disable
            EPi(x, body) if false && !x.is_type() && body.is_closed() => {
                // TODO: precedence to know whether to print "()"
                write!(out, "(")?;
                x.pp_(k, out, full)?;
                if full {
                    write!(out, ":")?;
                    x.ty().pp_(k, out, full)?;
                }
                write!(out, " -> ")?;
                body.pp_(k + 1, out, full)?;
                write!(out, ")")
            }
            EPi(x, body) => {
                write!(out, "(Πx{}", k)?;
                if full && !x.is_type() {
                    write!(out, " : ")?;
                    x.pp_(k, out, full)?;
                }
                write!(out, ". ")?;
                body.pp_(k + 1, out, full)?;
                write!(out, ")")
            }
        }?;
        //write!(out, "/{:?}", self.0.as_ref() as *const _)?; // pp pointer
        Ok(())
    }

    /// Basic printer.
    pub fn to_string(&self) -> String {
        format!("{}", self)
    }
}

impl fmt::Debug for Expr {
    // printer
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        self.pp_(0, out, true)
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
        Thm(Ref::new(ThmImpl {
            concl,
            em_uid,
            hyps,
        }))
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

    #[inline]
    pub fn hyps_vec(&self) -> &Vec<Expr> {
        &self.0.hyps
    }
}

impl fmt::Display for Thm {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        if self.hyps().len() == 0 {
            write!(out, "`|- {}`", self.concl())
        } else {
            let mut first = true;
            for h in self.hyps() {
                if out.alternate() {
                    write!(out, "    {}\n", h)?;
                } else {
                    if first {
                        first = false;
                        write!(out, "`")?;
                    } else {
                        write!(out, ", ")?;
                    }
                    write!(out, "{}", h)?;
                }
            }
            write!(out, " |- {}`", self.concl())
        }
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

impl PartialEq for Thm {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0.as_ref() as *const _, other.0.as_ref() as *const _)
    }
}

/// A substitution.
pub type Subst = Vec<(Var, Expr)>;

///! # Context for Expressions and Theorem.
///
/// The proof context is responsible for creating new terms and new theorems,
/// in a way that ensures theorems are valid.

/// Global manager for expressions, used to implement perfect sharing, allocating
/// new terms, etc.
pub struct Ctx {
    /// Hashconsing table, with weak semantics.
    tbl: fnv::FnvHashMap<ExprView, WExpr>,
    builtins: Option<ExprBuiltins>,
    consts: fnv::FnvHashMap<Symbol, Expr>,
    /// Temporary used to merge sets of hypotheses
    tmp_hyps: fnv::FnvHashSet<Expr>,
    lemmas: fnv::FnvHashMap<Symbol, Thm>,
    /// The defined chunks of code. These comprise some user defined tactics,
    /// derived rules, etc.
    meta_chunks: fnv::FnvHashMap<RStr, meta::Chunk>,
    eq: Option<Expr>,
    next_cleanup: usize,
    axioms: Vec<Thm>,
    uid: u32, // Unique to this ctx
    allow_new_axioms: bool,
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

impl fmt::Debug for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<expr manager>")
    }
}

// period between 2 cleanups
const CLEANUP_PERIOD: usize = 5000;

/// A set of builtin symbols.
struct ExprBuiltins {
    ty: Expr,
    bool: Expr,
}

fn hyps_merge(th1: &mut Thm, th2: &mut Thm) -> Vec<Expr> {
    use std::mem::swap;
    let mut v = vec![];
    if th1.0.hyps.len() == 0 {
        match Ref::get_mut(&mut th2.0) {
            None => th2.0.hyps.clone(),
            Some(th) => {
                swap(&mut v, &mut th.hyps);
                v
            }
        }
    } else if th2.0.hyps.len() == 0 {
        match Ref::get_mut(&mut th1.0) {
            None => th1.0.hyps.clone(),
            Some(th) => {
                swap(&mut v, &mut th.hyps);
                v
            }
        }
    } else {
        let mut v = match Ref::get_mut(&mut th1.0) {
            None => th1.0.hyps.clone(),
            Some(th) => {
                swap(&mut v, &mut th.hyps);
                v
            }
        };
        v.extend_from_slice(&th2.0.hyps[..]);
        v
    }
}

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
        let mut ctx = Ctx {
            tbl,
            builtins: None,
            consts: fnv::new_table_with_cap(n),
            tmp_hyps: fnv::new_set_with_cap(16),
            lemmas: fnv::new_table_with_cap(n),
            meta_chunks: fnv::new_table_with_cap(16),
            next_cleanup: CLEANUP_PERIOD,
            axioms: vec![],
            uid: uid as u32,
            eq: None,
            allow_new_axioms: true,
        };
        // insert initial builtins
        let kind = ctx.hashcons_builtin_(EKind, None);
        ctx.tbl.insert(kind.view().clone(), kind.weak());
        let ty = ctx.hashcons_builtin_(EType, Some(kind.clone()));
        ctx.tbl.insert(ty.view().clone(), ty.weak());
        let bool = {
            let name = Symbol::from_str(bs.bool);
            ctx.hashcons_builtin_(
                EConst(Box::new(ConstContent {
                    name,
                    ty: ty.clone(),
                    tag: ConstTag::None,
                    fix: std::cell::Cell::new(Fixity::Nullary),
                })),
                Some(ty.clone()),
            )
        };
        ctx.add_const_(bool.clone());
        let builtins = ExprBuiltins { bool, ty };
        ctx.builtins = Some(builtins);
        // build `=`. It needs `builtins` to be set.
        let eq = {
            let name = Symbol::from_str(bs.eq);
            let ty = ctx.mk_ty();
            let bool = ctx.mk_bool();
            let db0 = ctx.mk_bound_var(0, ty.clone());
            let arr = ctx.mk_arrow(db0.clone(), bool.clone()).unwrap();
            let arr = ctx.mk_arrow(db0.clone(), arr).unwrap();
            let ty_eq = ctx.mk_pi_(ty.clone(), arr).unwrap();
            let fix = FIXITY_EQ;
            ctx.mk_const_with_(name, ty_eq, ConstTag::Eq, fix).unwrap()
        };
        ctx.eq = Some(eq);

        ctx
    }

    /// New context with the default builtin symbols.
    pub fn new() -> Self {
        Self::with_capacity(&BuiltinSymbol::default(), 2_048)
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
            // eprintln!("expr.hashcons: cleanup");
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
        let name = if let EConst(c) = &e.0.view {
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

    fn mk_const_with_(&mut self, s: Symbol, ty: Type, tag: ConstTag, f: Fixity) -> Result<Expr> {
        self.check_uid_(&ty);
        if self.consts.contains_key(&s) {
            return Err(Error::new("a constant with this name already exists"));
        }
        if !ty.is_closed() || ty.free_vars().next().is_some() {
            return Err(Error::new("cannot create constant with non-closed type"));
        }
        let c = self.hashcons_(EConst(Box::new(ConstContent {
            name: s.clone(),
            ty,
            tag,
            fix: std::cell::Cell::new(f),
        })))?;
        self.add_const_(c.clone());
        Ok(c)
    }

    #[inline]
    fn check_uid_(&self, e: &Expr) {
        assert!(self.uid == e.0.em_uid); // term should belong to this EM
    }

    #[inline]
    fn check_thm_uid_(&self, th: &Thm) {
        assert!(self.uid == th.0.em_uid); // theorem should belong to this EM
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
                    return Err(Error::new(
                        "pi: variable must be a type or be of type `type`",
                    ));
                };
                if !e.ty().is_type() && !e.ty().is_kind() {
                    return Err(Error::new("pi: body must have type `type` or `kind`"));
                };
                Some(self.builtins_().ty.clone())
            }
            EApp(f, arg) => match &f.ty().0.view {
                EPi(ty_var_f, ref ty_body_f) => {
                    // rule: `f: Πx:tya. b`, `arg: tya` ==> `f arg : b[arg/x]`
                    if ty_var_f != arg.ty() {
                        return Err(Error::new("apply: incompatible types"));
                    }
                    Some(self.subst1_(ty_body_f, 0, arg)?)
                }
                _ => return Err(Error::new("cannot apply term with a non-pi type")),
            },
        })
    }

    // TODO(perf): have a (dense) stack of substitutions to do? could be useful
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
                self.hashcons_(EBoundVar(BoundVarContent { idx: v.idx + n, ty }))?
            }
        })
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
            return Err(Error::new("mk_abs: var has non-closed type"));
        }
        let v_ty = v_ty.clone();
        // replace `v` with `db0` in `body`. This should also take
        // care of shifting the DB by 1 as appropriate.
        let db0 = self.mk_bound_var(0, v_ty.clone());
        let body = self.shift_(&body, 1, 0)?;
        self.subst(&body, &[(v, db0)])
    }

    /// Make a pi term.
    fn mk_pi_(&mut self, ty_var: Expr, body: Expr) -> Result<Expr> {
        self.hashcons_(EPi(ty_var, body))
    }
}

pub(crate) const FIXITY_EQ: Fixity = Fixity::Infix((30, 31));
pub(crate) const FIXITY_LAM: Fixity = Fixity::Binder((10, 11));
pub(crate) const FIXITY_PI: Fixity = Fixity::Binder((24, 25));
pub(crate) const FIXITY_ARROW: Fixity = Fixity::Infix((81, 80));

// public interface
impl Ctx {
    /// Get the `=` constant
    pub fn mk_eq(&mut self) -> Expr {
        match self.eq {
            Some(ref c) => c.clone(),
            None => panic!("equality is not defined in this context"),
        }
    }

    /// Make `a = b`.
    ///
    /// Fails if `a` and `b` do not have the same type.
    pub fn mk_eq_app(&mut self, a: Expr, b: Expr) -> Result<Expr> {
        self.check_uid_(&a);
        self.check_uid_(&b);
        if a.ty() != b.ty() {
            return Err(Error::new("mk_eq: incompatible_types"));
        }
        let eq = self.mk_eq();
        self.mk_app_l(eq, &[a.ty().clone(), a, b])
    }

    /// For each pair `(x,u)` in `subst`, replace instances of the free
    /// variable `x` by `u` in `t`.
    pub fn subst(&mut self, t: &Expr, subst: &[(Var, Expr)]) -> Result<Expr> {
        self.check_uid_(&t);
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
    pub fn mk_ty(&self) -> Expr {
        self.builtins_().ty.clone()
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
        let body = self.abs_on_(v, body)?;
        self.mk_lambda_(v_ty, body)
    }

    /// Bind several variables at once.
    pub fn mk_lambda_l(&mut self, vars: &[Var], body: Expr) -> Result<Expr> {
        let mut e = body;
        // TODO: substitute more efficiently (with a stack, rather than one by one)?
        // right-assoc
        for v in vars.iter().rev() {
            e = self.mk_lambda(v.clone(), e)?;
        }
        Ok(e)
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
    pub fn mk_pi_l(&mut self, vars: &[Var], body: Expr) -> Result<Expr> {
        let mut e = body;
        // TODO: substitute more efficiently (with a stack, rather than one by one)?
        // right-assoc
        for v in vars.iter().rev() {
            e = self.mk_pi(v.clone(), e)?;
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
    /// Fails if some constant with the same name exists, or if
    /// the type is not closed.
    /// This constant has no axiom associated to it, it is entirely opaque.
    pub fn mk_new_const(&mut self, s: impl Into<Symbol>, ty: Type) -> Result<Expr> {
        self.mk_const_with_(s.into(), ty, ConstTag::None, Fixity::Nullary)
    }

    // TODO: return a result, and only allow infix/binder if type is inferrable
    /// Change the fixity of a given constant.
    ///
    /// Does nothing if the constant is not defined.
    pub fn set_fixity(&mut self, s: &str, f: Fixity) {
        if let Some(t) = self.consts.get_mut(s) {
            match t.view() {
                EConst(c) => c.fix.set(f),
                _ => panic!("expected constant"),
            }
        }
    }

    /// Find a constant by name. Returns `None` if no such constant exists.
    ///
    /// Use `as_const` on the expression to get its content.
    pub fn find_const(&self, s: &str) -> Option<(&Expr, Fixity)> {
        self.consts.get(s).map(|e| {
            let f = e.as_const().unwrap().fixity();
            (e, f)
        })
    }

    pub fn iter_consts(&self) -> impl Iterator<Item = (&str, &Expr)> {
        self.consts.iter().map(|(k, e)| (k.name(), e))
    }

    /// Find a meta-language chunk by name. Returns `None` if no such constant exists.
    pub fn find_meta_chunk(&self, s: &str) -> Option<&meta::Chunk> {
        self.meta_chunks.get(s)
    }

    /// Define a meta-language chunk.
    ///
    /// Will erase previous binding if existing.
    pub fn define_meta_chunk(&mut self, s: impl Into<RStr>, c: meta::Chunk) {
        self.meta_chunks.insert(s.into(), c);
    }

    /// Iterate over all meta chunks.
    pub fn iter_meta_chunks(&self) -> impl Iterator<Item = (&str, &meta::Chunk)> {
        self.meta_chunks.iter().map(|(s, c)| (s.get(), c))
    }

    /// Define a named lemma.
    ///
    /// If another lemma with the same name exists, it will be replaced.
    pub fn define_lemma(&mut self, name: impl Into<Symbol>, th: Thm) {
        self.lemmas.insert(name.into(), th);
    }

    /// Find a lemma by name. Returns `None` if no such theorem exists.
    pub fn find_lemma(&self, s: &str) -> Option<&Thm> {
        self.lemmas.get(s)
    }

    /// Iterate over all lemmas.
    pub fn iter_lemmas(&self) -> impl Iterator<Item = (&str, &Thm)> {
        self.lemmas.iter().map(|(s, t)| (s.name(), t))
    }

    /// `assume F` is `F |- F`.
    ///
    /// This fails if `F` is not a boolean.
    pub fn thm_assume(&mut self, e: Expr) -> Result<Thm> {
        self.check_uid_(&e);
        if e.ty() != &self.builtins_().bool {
            return Err(Error::new("cannot assume non-boolean expression"));
        }
        Ok(Thm::make_(e.clone(), self.uid, vec![e.clone()]))
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
    pub fn thm_trans(&mut self, mut th1: Thm, mut th2: Thm) -> Result<Thm> {
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
        let hyps = hyps_merge(&mut th1, &mut th2);
        let th = Thm::make_(eq_a_c, self.uid, hyps);
        Ok(th)
    }

    /// `congr (F1 |- f=g) (F2 |- t=u)` is `F1, F2 |- f t=g u`
    pub fn thm_congr(&mut self, mut th1: Thm, mut th2: Thm) -> Result<Thm> {
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
        let hyps = hyps_merge(&mut th1, &mut th2);
        Ok(Thm::make_(eq, self.uid, hyps))
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
        let eq = self.mk_eq_app(ft, gu)?;
        {
            let thref = Ref::make_mut(&mut th.0);
            thref.concl = eq;
        }
        Ok(th)
    }

    /// `instantiate thm σ` produces `Fσ |- Gσ`  where `thm` is `F |- G`
    ///
    /// Returns an error if the substitution is not closed.
    pub fn thm_instantiate(&mut self, mut th: Thm, subst: &[(Var, Expr)]) -> Result<Thm> {
        self.check_thm_uid_(&th);
        if subst.iter().any(|(_, t)| !t.is_closed()) {
            return Err(Error::new(
                "instantiate: substitution contains non-closed binding",
            ));
        }

        {
            let thref = Ref::make_mut(&mut th.0);
            thref.concl = self.subst(&thref.concl, subst)?;
            for t in thref.hyps.iter_mut() {
                *t = self.subst(t, subst)?;
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
        if free_vars_iter(thm.0.hyps.iter()).any(|v2| v == v2) {
            return Err(Error::new("abs: variable occurs in one of the hypothesis"));
        }

        let (t, u) = thm
            .0
            .concl
            .unfold_eq()
            .ok_or_else(|| Error::new("abs: thm conclusion should be an equality"))?;

        let lam_t = self.mk_lambda(v.clone(), t.clone())?;
        let lam_u = self.mk_lambda(v.clone(), u.clone())?;
        let eq = self.mk_eq_app(lam_t, lam_u)?;
        {
            let thref = Ref::make_mut(&mut thm.0); // clone or acquire
            thref.concl = eq;
        }
        Ok(thm)
    }

    /// `cut (F1 |- b) (F2, b |- c)` is `F1, F2 |- c`
    ///
    /// This fails if `b` does not occur _syntactically_ in the hypothesis
    /// of the second theorem.
    ///
    /// NOTE: this is not strictly necessary, as it's not an axiom in HOL light,
    /// but we include it here anyway.
    pub fn thm_cut(&mut self, mut th1: Thm, mut th2: Thm) -> Result<Thm> {
        self.check_thm_uid_(&th1);
        self.check_thm_uid_(&th2);
        let th1_c = th1.0.concl.clone();
        if !th2.0.hyps.contains(&th1_c) {
            return Err(Error::new(
                "cut: th2's hyps do not contain th1's conclusion",
            ));
        }
        let th2_c = th2.0.concl.clone();

        let hyps: Vec<_> = {
            self.tmp_hyps.clear();

            if let Some(th1m) = Ref::get_mut(&mut th1.0) {
                self.tmp_hyps.extend(th1m.hyps.drain(..))
            } else {
                // must clone
                self.tmp_hyps.extend(th1.0.hyps.iter().cloned())
            }

            if let Some(th2m) = Ref::get_mut(&mut th2.0) {
                self.tmp_hyps
                    .extend(th2m.hyps.drain(..).filter(|u| *u != th1_c))
            } else {
                // must clone
                self.tmp_hyps
                    .extend(th2.0.hyps.iter().filter(|u| **u != th1_c).cloned())
            }

            self.tmp_hyps.drain().collect()
        };
        let th_res = Thm::make_(th2_c, self.uid, hyps);
        Ok(th_res)
    }

    /// `bool_eq (F1 |- a) (F2 |- a=b)` is `F1, F2 |- b`.
    /// This is the boolean equivalent of transitivity.
    pub fn thm_bool_eq(&mut self, mut th1: Thm, mut th2: Thm) -> Result<Thm> {
        self.check_thm_uid_(&th1);
        self.check_thm_uid_(&th2);
        let th2_c = &th2.0.concl;
        let (a, b) = th2_c
            .unfold_eq()
            .filter(|(a, _)| a.ty() == &self.builtins_().bool)
            .ok_or_else(|| {
                //Some((a, b)) if a.ty() == &self.builtins_().bool => (a, b),
                Error::new("bool-eq: th2 should have a boleean equality as conclusion")
            })?;
        if a != &th1.0.concl {
            return Err(Error::new(
                "bool-eq: the conclusion of th1 is not compatible with th2's concl LHS",
            ));
        }
        let b = b.clone();

        let hyps = hyps_merge(&mut th1, &mut th2);
        Ok(Thm::make_(b, self.uid, hyps))
    }

    /// `bool_eq_intro (F1, a |- b) (F2, b |- a)` is `F1, F2 |- b=a`.
    /// This is a way of building a boolean `a=b` from proofs of
    ///  `a|-b` and `b|-a`.
    pub fn thm_bool_eq_intro(&mut self, mut th1: Thm, mut th2: Thm) -> Result<Thm> {
        self.check_thm_uid_(&th1);
        self.check_thm_uid_(&th2);
        let eq = self.mk_eq_app(th2.0.concl.clone(), th1.0.concl.clone())?;
        // TODO: use self.tmp_hyps
        {
            let th1_c = th1.0.concl.clone();
            let thref1 = Ref::make_mut(&mut th1.0);
            thref1.hyps.retain(|x| x != &th2.0.concl);
            match Ref::get_mut(&mut th2.0) {
                None => {
                    thref1
                        .hyps
                        .extend(th2.hyps().iter().filter(|x| *x != &th1_c).cloned());
                }
                Some(thref2) => {
                    let mut v = vec![]; // steal thref2.hyps
                    std::mem::swap(&mut v, &mut thref2.hyps);
                    thref1.hyps.extend(v.into_iter().filter(|x| x != &th1_c));
                }
            }
            thref1.concl = eq;
        }
        Ok(th1)
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
                Error::new("new definition: expr should be an equation `x = rhs` with rhs closed")
            })?;
        if !rhs.is_closed() || rhs.has_free_vars() {
            return Err(Error::new("RHS of equation should be closed"));
        }
        // checks that the type of `x` is closed
        if !x.ty.is_closed() || x.ty.has_free_vars() {
            return Err(Error::new("LHS of equation should have a closed type"));
        }

        let c = self.mk_new_const(x.name.clone(), x.ty.clone())?;
        let eqn = self.mk_eq_app(c.clone(), rhs.clone())?;
        let thm = Thm::make_(eqn, self.uid, vec![]);
        Ok((thm, c))
    }

    /// Create a new axiom `assumptions |- concl`.
    /// **use with caution**
    ///
    /// Fails if `pledge_no_new_axiom` was called earlier on this context.
    pub fn thm_axiom(&mut self, hyps: Vec<Expr>, concl: Expr) -> Result<Thm> {
        if !self.allow_new_axioms {
            return Err(Error::new("this context has pledge to not take new axioms"));
        }
        self.check_uid_(&concl);
        hyps.iter().for_each(|e| self.check_uid_(e));

        let thm = Thm::make_(concl, self.uid, hyps);
        self.axioms.push(thm.clone());
        Ok(thm)
    }

    /// Pledge that no new call to `thm_axiom` will occur.
    ///
    /// This freezes the logical theory to the consequences of the builtin
    /// rules and the already created axioms.
    pub fn pledge_no_new_axiom(&mut self) {
        self.allow_new_axioms = false;
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
        let mut fvars: Vec<Var> = thm_inhabited.concl().free_vars().cloned().collect();
        fvars.sort_unstable();
        fvars.dedup();

        if fvars.iter().any(|v| !v.ty.is_type()) {
            return Err(Error::new(
                "new_basic_type_def: definition contains \
                a free variable that does not have type `type`",
            ));
        }

        // free vars, as expressions
        let fvars_exprs: Vec<_> = fvars.iter().map(|v| self.mk_var(v.clone())).collect();

        // construct new type and mapping functions
        let tau = {
            let ttype = self.mk_ty();
            let ty_tau = self.mk_pi_l(&fvars, ttype)?;
            self.mk_new_const(name_tau, ty_tau)?
        };

        // `tau` applied to `fvars`
        let tau_vars = self.mk_app_l(tau.clone(), &fvars_exprs)?;

        let c_abs = {
            let ty = self.mk_arrow(ty.clone(), tau_vars.clone())?;
            let ty = self.mk_pi_l(&fvars, ty)?;
            self.mk_new_const(abs, ty)?
        };
        let c_repr = {
            let ty = self.mk_arrow(tau_vars.clone(), ty.clone())?;
            let ty = self.mk_pi_l(&fvars, ty)?;
            self.mk_new_const(repr, ty)?
        };

        let abs_x = self.mk_var_str("x", tau_vars.clone());
        let abs_thm = {
            // `|- abs (repr x) = x`
            let repr = self.mk_app_l(c_repr.clone(), &fvars_exprs)?;
            let t = self.mk_app(repr, abs_x.clone())?;
            let abs = self.mk_app_l(c_abs.clone(), &fvars_exprs)?;
            let abs_t = self.mk_app(abs, t)?;
            let eqn = self.mk_eq_app(abs_t.clone(), abs_x.clone())?;
            Thm::make_(eqn, self.uid, vec![])
        };
        let repr_x = self.mk_var_str("x", ty.clone());
        let repr_thm = {
            // `|- Phi x <=> repr (abs x) = x`
            let abs = self.mk_app_l(c_abs.clone(), &fvars_exprs)?;
            let t1 = self.mk_app(abs, repr_x.clone())?;
            let repr = self.mk_app_l(c_repr.clone(), &fvars_exprs)?;
            let t2 = self.mk_app(repr, t1)?;
            let eq_t2_x = self.mk_eq_app(t2, repr_x.clone())?;
            let phi_x = self.mk_app(phi.clone(), repr_x.clone())?;
            Thm::make_(self.mk_eq_app(phi_x, eq_t2_x)?, self.uid, vec![])
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
}
