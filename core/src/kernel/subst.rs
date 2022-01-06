//! # Substitutions
//!
//! A substitution is useful for instantiating a theorem into a more
//! specialized theorem. Is it the workhorse of theorem re-use: first,
//! prove a general theorem with free variables; then, instantiate it
//! every time it is required.

use smallvec::{smallvec, SmallVec};
use {super::*, crate::rptr::RPtr};

/// A substitution.
#[derive(Clone)]
pub struct Subst(RPtr<SubstImpl>);

type Binding = (Var, Expr);
type Bindings = SmallVec<[Binding; 4]>;

struct SubstImpl(Bindings);

#[derive(Clone)]
pub struct SubstBuilder(Bindings);

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
        type Target = [Binding];

        #[inline]
        fn deref(&self) -> &Self::Target {
            &*(self.0).0
        }
    }

    impl std::cmp::PartialEq for Subst {
        fn eq(&self, other: &Self) -> bool {
            let s1 = &self[..];
            let s2 = &other[..];
            s1 == s2
        }
    }

    impl std::cmp::Eq for Subst {}

    impl std::hash::Hash for Subst {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            let s = &self[..];
            s.hash(state)
        }
    }

    impl std::iter::FromIterator<(Var, Expr)> for Subst {
        fn from_iter<T: IntoIterator<Item = (Var, Expr)>>(iter: T) -> Self {
            let mut vec = SmallVec::new();
            for e in iter.into_iter() {
                vec.push((e.0, e.1))
            }
            Subst(RPtr::new(SubstImpl(vec)))
        }
    }

    impl SubstBuilder {
        /// New builder.
        pub fn new() -> Self {
            Self(smallvec![])
        }

        /// Add a binding to the substitution.
        pub fn add_binding(&mut self, v: Var, e: Expr) {
            self.0.push((v, e))
        }

        pub fn into_subst(self) -> Subst {
            Subst(RPtr::new(SubstImpl(self.0)))
        }
    }
}
