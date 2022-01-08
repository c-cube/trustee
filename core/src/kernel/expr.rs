//! # Expressions, types, variables

use super::{symbol::Symbol, Proof, Ref, WeakRef};
use crate::{error::Result, fnv, rstr::RStr};
use smallvec::{smallvec, SmallVec};
use std::{fmt, ops::Deref};

/// De Buijn indices.
pub type DbIndex = u32;

/// An expression.
///
/// The expression is refcounted and is thus cheaply clonable.
#[derive(Clone)]
pub struct Expr(pub(super) Ref<ExprImpl>);

/// Small vector of exprs.
pub type Exprs = SmallVec<[Expr; 3]>;

/// A weak reference to an expression.
///
/// This is only used in the hashconsing table, so that it is not
/// the only reference keeping a term alive.
#[derive(Clone)]
pub(super) struct WExpr(pub(super) WeakRef<ExprImpl>);

/// Types and Terms are the same, but this is helpful for documentation.
pub type Type = Expr;

/// Type arguments to a constant
pub type ConstArgs = SmallVec<[Type; 3]>;

/// The public view of an expression's root.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum ExprView {
    EType,
    EKind,
    EConst(Const, ConstArgs),
    EVar(Var),
    EBoundVar(BoundVarContent),
    EApp(Expr, Expr),
    ELambda(Type, Expr),
    EArrow(Expr, Expr),
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

/// A small vector of variables.
pub type Vars = SmallVec<[Var; 3]>;

/// The content of an expression.
pub(super) struct ExprImpl {
    /// Unique ID of the expr manager responsible for creating this expr.
    ctx_uid: u32,
    /// The view of the expression.
    view: ExprView,
    /// Maximum DB index in expr. 0 means the term is closed.
    db_depth: DbIndex,
    /// Type of the expression. Always present except for `Kind`.
    ty: Option<Expr>,
}

/// A constant.
///
/// Constants are symbols with a type declaration ("opaque constant")
/// or a definition ("defined constants"). A defined constant can become
/// opaque if we just forget its definition.
#[derive(Clone, Debug)]
pub struct Const(pub(crate) Ref<ConstImpl>);

#[derive(Debug)]
pub struct ConstImpl {
    pub name: Symbol,
    /// Generation of this constant, incremented to handle shadowing.
    pub(super) gen: u32,
    pub arity: u8,
    pub kind: ConstKind,
    pub(super) tag: ConstTag,
    pub(super) proof: Option<Proof>,
}

/// The kind of constant. We deal with type constants and expr constants
/// in mostly the same way.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ConstKind {
    TyConst,
    ExprConst {
        /// Type of the constant when applied to type arguments.
        /// It is implicitly parametrized by `arity` arguments.
        ty: Expr,
    },
}

/// Tag for special constants.
#[derive(Debug, PartialEq, Clone, Copy)]
#[repr(u8)]
pub(super) enum ConstTag {
    None,
    Bool,
    Eq,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct BoundVarContent {
    pub(super) idx: DbIndex,
    pub(super) ty: Expr,
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
        EConst(c, args) => {
            let arity = c.0.arity;
            if let ConstKind::ExprConst { ty } = c.0.kind {
                let d = ty.db_depth();
                assert!(d <= arity as u32);
            }
            let mut d = 0;
            for a in &args[..] {
                d = d.max(a.db_depth())
            }
            d
        }
        EVar(v) => v.ty.db_depth(),
        EBoundVar(v) => u32::max(v.idx + 1, v.ty.db_depth()),
        EApp(a, b) | EArrow(a, b) => a.db_depth().max(b.db_depth()),
        ELambda(v_ty, e) => {
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
        let r = match self {
            EType | EKind => self.clone(),
            EConst(c, args) => {
                let args = args
                    .iter()
                    .map(|x| f(x, k))
                    .collect::<Result<SmallVec<[Expr; 3]>>>()?;
                EConst(c.clone(), args)
            }
            EVar(v) => EVar(Var {
                ty: f(&v.ty, k)?,
                name: v.name.clone(),
            }),
            EBoundVar(v) => EBoundVar(BoundVarContent {
                ty: f(&v.ty, k)?,
                idx: v.idx,
            }),
            EApp(a, b) => EApp(f(a, k)?, f(b, k)?),
            EArrow(a, b) => EArrow(f(a, k)?, f(b, k)?),
            ELambda(ty_a, b) => ELambda(f(ty_a, k)?, f(b, k + 1)?),
        };
        Ok(r)
    }

    /// Iterate on immediate subterms.
    pub fn iter<F>(&self, mut f: F, k: DbIndex) -> Result<()>
    where
        F: FnMut(&Expr, DbIndex) -> Result<()>,
    {
        match self {
            EType | EKind => {}
            EConst(_c, args) => {
                for a in &args[..] {
                    f(a, k)?;
                }
            }
            EVar(v) => {
                f(&v.ty, k)?;
            }
            EBoundVar(v) => {
                f(&v.ty, k)?;
            }
            EApp(a, b) | EArrow(a, b) => {
                f(a, k)?;
                f(b, k)?;
            }
            ELambda(ty_a, b) => {
                f(ty_a, k)?;
                f(b, k + 1)?;
            }
        };
        Ok(())
    }
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

/// Iterator over free variables of an expr.
struct FreeVars<'a> {
    seen: fnv::FnvHashSet<&'a Expr>,
    st: Vec<&'a Expr>, // stack for traversal
}

mod free_vars_impl {
    use super::*;

    impl<'a> Iterator for FreeVars<'a> {
        type Item = &'a Var;
        fn next(&mut self) -> Option<Self::Item> {
            while let Some(e) = self.st.pop() {
                if self.seen.contains(&e) {
                    continue;
                }
                self.seen.insert(e);

                match e.view() {
                    EVar(v) => {
                        self.st.push(&v.ty);
                        return Some(v);
                    }
                    EType | EKind => (),
                    EConst(_c, args) => {
                        for a in &args[..] {
                            self.st.push(a)
                        }
                    }
                    EBoundVar(v) => self.st.push(&v.ty),
                    EApp(a, b) | EArrow(a, b) => {
                        self.st.push(a);
                        self.st.push(b);
                    }
                }
            }
            None
        }
    }

    impl<'a> FreeVars<'a> {
        pub fn new() -> Self {
            FreeVars {
                seen: fnv::new_set_with_cap(16),
                st: vec![],
            }
        }

        /// Add an expression to explore
        pub fn push(&mut self, e: &'a Expr) {
            self.st.push(e)
        }
    }
}

impl Expr {
    /// View the expression's root.
    #[inline]
    pub fn view(&self) -> &ExprView {
        &self.0.view
    }

    pub(super) fn ctx_uid(&self) -> u32 {
        self.0.ctx_uid
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

    /// Is this a functional type?
    pub fn is_fun_type(&self) -> bool {
        match self.0.view {
            EArrow(..) => true,
            _ => false,
        }
    }

    /// Is this the representation of `=`?
    pub fn is_eq(&self) -> bool {
        match &self.0.view {
            EConst(c, _) => c.0.tag == ConstTag::Eq,
            _ => false,
        }
    }

    /// Is this the representation of `bool`?
    pub fn is_bool(&self) -> bool {
        match &self.0.view {
            EConst(c, _) => c.0.tag == ConstTag::Bool,
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
    pub(super) fn weak(&self) -> WExpr {
        WExpr(Ref::downgrade(&self.0))
    }

    /// Safe version of `ty`, that works even for `Kind`.
    pub fn ty_opt(&self) -> &Option<Expr> {
        &self.0.ty
    }

    /// `e.unfold_app()` returns a tuple `(f, args)` where `args`
    /// iterates over arguments.
    pub fn unfold_app(&self) -> (&Expr, SmallVec<[&Expr; 3]>) {
        let mut e = self;
        let mut v = smallvec![];
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
    pub fn unfold_arrow(&self) -> (SmallVec<[&Type; 3]>, &Expr) {
        let mut e = self;
        let mut v = smallvec![];
        while let EArrow(ty_arg, body) = e.view() {
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
    pub fn as_const(&self) -> Option<(&Const, &ConstArgs)> {
        if let EConst(ref c, ref args) = self.0.view {
            Some((c, args))
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

    /// View as application.
    pub fn as_arrow(&self) -> Option<(&Expr, &Expr)> {
        if let EArrow(ref a, ref b) = self.0.view {
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
        if hd2.is_eq() {
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
    pub(super) fn db_depth(&self) -> DbIndex {
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
    pub(super) fn make_(v: ExprView, em_uid: u32, ty: Option<Expr>) -> Self {
        let db_depth = compute_db_depth(&v);
        Expr(Ref::new(ExprImpl {
            view: v,
            ctx_uid: em_uid,
            ty,
            db_depth,
        }))
    }

    // pretty print
    fn pp_(&self, k: DbIndex, out: &mut fmt::Formatter, full: bool) -> fmt::Result {
        match self.view() {
            EKind => write!(out, "kind"),
            EType => write!(out, "type"),
            EConst(c, args) => {
                if args.is_empty() {
                    write!(out, "{}", c.0.name.name())
                } else {
                    write!(out, "({}", c.0.name.name());
                    for a in &args[..] {
                        write!(out, " ");
                        a.pp_(k, out, full)?;
                    }
                    write!(out, ")")
                }
            }
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
            EArrow(a, b) => {
                write!(out, "(-> ")?;
                a.pp_(k, out, full)?;
                write!(out, " ")?;
                b.pp_(k, out, full)?;
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

mod impls {
    use super::*;

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

    impl Eq for Const {}
    impl PartialEq for Const {
        fn eq(&self, other: &Self) -> bool {
            self.0.name == other.0.name && self.0.gen == other.0.gen && self.0.kind == other.0.kind
        }
    }

    impl std::hash::Hash for Const {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.0.name.hash(state);
            self.0.gen.hash(state);
            self.0.kind.hash(state)
        }
    }

    impl Deref for Const {
        type Target = ConstImpl;
        fn deref(&self) -> &Self::Target {
            &*self.0
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn test_sizeof_expr() {
        let sz = std::mem::size_of::<Expr>();
        assert_eq!(8, sz);
    }

    #[cfg(target_pointer_width = "64")]
    #[test]
    fn test_sizeof_view() {
        let sz = std::mem::size_of::<ExprImpl>();
        assert_eq!(64, sz);
    }
}
