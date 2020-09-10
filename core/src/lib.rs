//! # Trustee core library.
//!
//! This library contains the kernel of trust for Trustee, i.e. the set
//! of type definitions (most importantly, expressions and theorems),
//! and rules to build them safely.
//!
//! It also contains:
//! - a small, custom meta-language for interactive use of Trustee (in `meta`)
//! - barebone syntax for expressions, patterns, etc. (in `syntax`)
//! - a small collection of algorithms for congruence closure,
//!   rewriting, term orderings, unification, beta-reduction, etc. (in `algo`)

// unsafe needs to be visible
#![deny(unsafe_code)]

pub mod algo;
pub mod error;
mod fnv;
pub mod kernel_of_trust;
pub mod meta;
pub mod position;
pub mod rptr;
pub mod rstr;
pub mod syntax;

pub use fnv::{new_set_with_cap, new_table_with_cap, FnvHashMap, FnvHashSet};

pub use crate::meta::{load_prelude_hol, run_code};
pub use algo::pattern::{self, Pattern, PatternView};
pub use error::{Error, Result};
pub use kernel_of_trust::ExprView::*;
pub use kernel_of_trust::{Ctx, Expr, ExprView, Symbol, Thm, Var};
pub use syntax::{parse_expr, parse_expr_with_args, parse_pattern, parse_pattern_with_args};

pub(crate) mod macros {
    #[macro_export]
    macro_rules! logtrace{
        ($($t:expr),*) => {
            #[cfg(feature="logging")]
            log::trace!($($t),*)
        }
    }

    #[macro_export]
    macro_rules! logdebug{
        ($($t:expr),*) => {
            #[cfg(feature="logging")]
            log::debug!($($t),*)
        }
    }

    #[macro_export]
    macro_rules! logerr{
        ($($t:expr),*) => {
            #[cfg(feature="logging")]
            log::error!($($t),*)
        }
    }
}
