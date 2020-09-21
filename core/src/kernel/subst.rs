//! # Substitutions
//!
//! A substitution is useful for instantiating a theorem into a more
//! specialized theorem. Is it the workhorse of theorem re-use: first,
//! prove a general theorem with free variables; then, instantiate it
//! every time it is required.

use super::*;

/// A substitution.
#[derive(Clone)]
pub struct Subst(Ref<SubstImpl>);

type Binding = (Var, Expr);

enum SubstImpl {
    S0,
    S1([Binding; 1]),
    S2([Binding; 2]),
    S3([Binding; 3]),
    S4(Box<[Binding]>),
}

/// Builder for a substitution.o
///
/// This can only be linearly used.
pub struct SubstBuilder(Vec<Binding>);

mod impls {
    use {super::*, std::fmt};

    impl fmt::Debug for Subst {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "(subst")?;
            for (v, e) in self.iter() {
                write!(f, " ({:?} := {:?})", v.name(), e)?;
            }
            write!(f, ")")
        }
    }

    impl std::ops::Deref for Subst {
        type Target = [(Var, Expr)];

        fn deref(&self) -> &Self::Target {
            match &*self.0 {
                SubstImpl::S0 => &[],
                SubstImpl::S1(a) => &a[..],
                SubstImpl::S2(a) => &a[..],
                SubstImpl::S3(a) => &a[..],
                SubstImpl::S4(v) => &*v,
            }
        }
    }

    impl std::iter::FromIterator<(Var, Expr)> for Subst {
        fn from_iter<T: IntoIterator<Item = (Var, Expr)>>(iter: T) -> Self {
            let mut s = SubstBuilder::new();
            for e in iter.into_iter() {
                s.add_binding(e.0, e.1)
            }
            s.into_subst()
        }
    }

    impl From<SubstBuilder> for Subst {
        fn from(b: SubstBuilder) -> Self {
            b.into_subst()
        }
    }

    impl SubstBuilder {
        /// New builder.
        pub fn new() -> Self {
            Self(vec![])
        }

        /// Add a binding to the substitution.
        pub fn add_binding(&mut self, v: Var, e: Expr) {
            self.0.push((v, e))
        }

        pub fn into_subst(self) -> Subst {
            let i = match self.0.len() {
                0 => SubstImpl::S0,
                1 => {
                    let mut b = self.0.into_iter();
                    let v0 = b.next().unwrap();
                    SubstImpl::S1([v0])
                }
                2 => {
                    let mut b = self.0.into_iter();
                    let v0 = b.next().unwrap();
                    let v1 = b.next().unwrap();
                    SubstImpl::S2([v0, v1])
                }
                3 => {
                    let mut b = self.0.into_iter();
                    let v0 = b.next().unwrap();
                    let v1 = b.next().unwrap();
                    let v2 = b.next().unwrap();
                    SubstImpl::S3([v0, v1, v2])
                }
                _ => SubstImpl::S4(self.0.into_boxed_slice()),
            };
            Subst(Ref::new(i))
        }
    }
}
