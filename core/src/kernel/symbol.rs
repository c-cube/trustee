///! # Symbols.
use crate::rstr::RStr;

/// Description of builtin symbols
#[derive(Debug)]
pub struct BuiltinSymbol<'a> {
    pub eq: &'a str,
    pub bool: &'a str,
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

    pub fn to_rstr(&self) -> RStr {
        self.0.clone()
    }

    pub fn from_rc_str(s: &std::rc::Rc<str>) -> Self {
        let a: RStr = RStr::from(s.as_ref());
        Symbol(a)
    }

    pub fn name(&self) -> &str {
        &*self.0
    }
}

mod impls {
    use super::*;

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

    impl From<RStr> for Symbol {
        fn from(s: RStr) -> Self {
            Symbol(s)
        }
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
}
