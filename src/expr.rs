//! Types and Expressions.

use std::sync::Arc;

/// A type.
#[derive(Clone, Eq, Debug)]
pub struct Ty(Arc<TyView>);

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TyView {
    Arrow(Ty, Ty),
    App(String, Vec<Ty>),
    Var(String),
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}

impl std::ops::Deref for Ty {
    type Target = TyView;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

lazy_static! {
    static ref BOOL: Ty = Ty::var("Bool");
}

impl Ty {
    pub fn view(&self) -> &TyView {
        &self.0
    }

    /// Make a variable with the given name.
    pub fn var<S>(v: S) -> Self
    where
        S: Into<String>,
    {
        Ty(Arc::new(TyView::Var(v.into())))
    }

    pub fn bool() -> Self {
        BOOL.clone()
    }

    /// `ty.arrow_ty(ty2)` makes the type `ty -> ty2`
    pub fn arrow_to(&self, other: &Self) -> Self {
        Ty(Arc::new(TyView::Arrow(self.clone(), other.clone())))
    }

    /// Make a constant constructor type (e.g. `int`).
    pub fn app0(s: String) -> Self {
        Ty(Arc::new(TyView::App(s, vec![])))
    }

    /// Make a constructor application (e.g. `list int`).
    pub fn app(s: String, args: &[Self]) -> Self {
        Ty(Arc::new(TyView::App(s, args.iter().cloned().collect())))
    }
}

/// Builtin symbols.
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Builtin {
    True,
    False,
    Equal,
    Not,
}

/// Name of a variable.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum VarName {
    Builtin(Builtin),
    Sym(String),
}

/// A (typed) variable.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Var {
    pub name: VarName,
    pub ty: Ty,
}

/// An expression.
///
/// It is refcounted, and thus, fast to clone.
#[derive(Clone, Eq, Debug)]
pub struct Expr(Arc<ExprCell>);

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ExprCell {
    view: ExprView,
    ty: Ty,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ExprView {
    Var(Var),
    App(Expr, Expr),
    Lam(Var, Expr),
}

use ExprView::*;

impl std::ops::Deref for Expr {
    type Target = ExprView;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0.view
    }
}

impl Expr {
    /// Get the type of this expression.
    #[inline]
    pub fn ty(&self) -> &Ty {
        &self.0.ty
    }

    /// Get the view of this expression.
    #[inline]
    pub fn view(&self) -> &ExprView {
        &self.0.view
    }

    /// Create a new variable.
    pub fn var_str<S>(v: S, ty: &Ty) -> Self
    where
        S: Into<String>,
    {
        // make a variable on the fly
        let v = Var {
            name: VarName::Sym(v.into()),
            ty: ty.clone(),
        };
        Expr(Arc::new(ExprCell {
            ty: ty.clone(),
            view: Var(v),
        }))
    }

    /// Make the variable `=` for the given type.
    pub fn eq(ty: &Ty) -> Self {
        let ty = ty.arrow_to(&ty.arrow_to(&Ty::bool()));
        let v = Var {
            name: VarName::Builtin(Builtin::Equal),
            ty,
        };
        Self::var(v)
    }

    /// Create a new variable.
    pub fn var(v: Var) -> Self {
        Expr(Arc::new(ExprCell {
            ty: v.ty.clone(),
            view: Var(v),
        }))
    }

    /// `f.app(x)` builds the term `(f x)`.
    ///
    /// This will check the types and panic if it not that case that
    /// `f : a -> b` and `x : a`.
    pub fn app(&self, arg: &Self) -> Self {
        match self.ty().view() {
            &TyView::Arrow(ref a, ref b) if a == arg.ty() => Expr(Arc::new(ExprCell {
                view: App(self.clone(), arg.clone()),
                ty: b.clone(),
            })),
            _ => panic!("type error: cannot apply {:?} to {:?}", &self, &arg),
        }
    }

    /// Apply a function to multiple arguments.
    pub fn app_many<I>(&self, args: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut f = self.clone();
        for arg in args {
            let ty = match f.ty().view() {
                &TyView::Arrow(ref a, ref b) if a == arg.ty() => b.clone(),
                _ => panic!("type error: cannot apply {:?} to {:?}", &f, &arg),
            };
            f = Expr(Arc::new(ExprCell {
                view: App(f, arg.clone()),
                ty: ty,
            }))
        }
        f
    }

    /// Build the term `λv. body`
    pub fn lam(v: Var, body: &Self) -> Self {
        let ty = v.ty.arrow_to(body.ty());
        Expr(Arc::new(ExprCell {
            view: Lam(v, body.clone()),
            ty,
        }))
    }
}
