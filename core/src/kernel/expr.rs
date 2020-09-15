//! # Expressions, types, variables

use super::{symbol::Symbol, Ref, WeakRef};
use crate::{error::Result, fnv, rstr::RStr};
use std::{fmt, ops::Deref};

/// De Buijn indices.
pub type DbIndex = u32;

/// An expression.
///
/// The expression is refcounted and is thus cheaply clonable.
#[derive(Clone)]
pub struct Expr(pub(super) Ref<ExprImpl>);

/// A weak reference to an expression.
#[derive(Clone)]
pub(super) struct WExpr(pub(super) WeakRef<ExprImpl>);

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
pub(super) struct ExprImpl {
    /// The view of the expression.
    view: ExprView,
    /// Number of DB indices missing. 0 means the term is closed.
    db_depth: DbIndex,
    /// Unique ID of the expr manager responsible for creating this expr.
    ctx_uid: u32,
    /// Type of the expression. Always present except for `Kind`.
    ty: Option<Expr>,
}

/// For infix/prefix/postfix constants.
pub type Fixity = crate::syntax::Fixity;

#[derive(Clone, Debug)]
pub struct ConstContent {
    pub name: Symbol,
    pub ty: Expr,
    pub(super) tag: ConstTag,
    /// Generation of this constant, incremented to handle shadowing.
    pub(super) gen: u32,
    pub(super) fix: std::cell::Cell<Fixity>, // TODO: remvoe and store in ctx?
}

/// Tag for special constants.
#[derive(Debug, PartialEq, Clone, Copy)]
#[repr(u8)]
pub(super) enum ConstTag {
    None,
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
        let r = match self {
            EType | EKind => self.clone(),
            EConst(c) => EConst(Box::new(ConstContent {
                ty: f(&c.ty, k)?,
                name: c.name.clone(),
                gen: c.gen,
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
        };
        Ok(r)
    }

    /// Iterate on immediate subterms.
    pub fn iter<F>(&self, mut f: F, k: DbIndex) -> Result<()>
    where
        F: FnMut(&Expr, DbIndex) -> Result<()>,
    {
        match self {
            EType | EKind | EConst(..) => (),
            EVar(v) => {
                f(&v.ty, k)?;
            }
            EBoundVar(v) => {
                f(&v.ty, k)?;
            }
            EApp(a, b) => {
                f(a, k)?;
                f(b, k)?;
            }
            EPi(ty_a, b) => {
                f(ty_a, k)?;
                f(b, k + 1)?;
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

struct FreeVars<'a> {
    seen: fnv::FnvHashSet<&'a Expr>,
    st: Vec<&'a Expr>,
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
            EPi(..) => true,
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
    pub(super) fn weak(&self) -> WExpr {
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
}
