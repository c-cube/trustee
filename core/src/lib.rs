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
pub mod kernel;
pub mod meta;
pub mod position;
pub mod proof;
pub mod rptr;
pub mod rstr;
pub mod syntax;
pub mod tef;

#[deprecated = "use kernel"]
pub use kernel as kernel_of_trust;

pub use fnv::{new_set_with_cap, new_table_with_cap, FnvHashMap, FnvHashSet};

pub use crate::meta::{load_prelude_hol, run_code};
pub use algo::pattern::{self, Pattern, PatternView};
pub use error::{Error, Result};
pub use kernel::ExprView::*;
pub use kernel::{Const, ConstArgs, Ctx, Expr, ExprView, Symbol, Thm, Var, Vars};
pub use syntax::{parse_expr, parse_expr_with_args, parse_pattern, parse_pattern_with_args};

pub(crate) mod macros {
    #[allow(unused_macros)]
    #[macro_export]
    macro_rules! ignore{
        () => { () };
        ($t :expr) => {{
            #[allow(unused_value)]
            let _ = $t;
        } };
        ($t0: expr, $($t:expr),*) => {{
            #[allow(unused_value)]
            let _ = $t0;
            crate::ignore!($($t),*)
        }}
    }

    #[macro_export]
    macro_rules! logtrace{
        ($($t:expr),*) => {{
            {
                #[cfg(feature="logging")]
                log::trace!($($t),*)
            }

            {
                #[cfg(not(feature="logging"))]
                crate::ignore!($($t),*)
            }
        }}
    }

    #[macro_export]
    macro_rules! logdebug{
        ($($t:expr),*) => {{
            {
                #[cfg(feature="logging")]
                log::debug!($($t),*)
            }

            {
                #[cfg(not(feature="logging"))]
                crate::ignore!($($t),*)
            }
        }}
    }

    #[macro_export]
    macro_rules! logerr{
        ($($t:expr),*) => {{
            {
                #[cfg(feature="logging")]
                log::error!($($t),*);
            }

            {
                #[cfg(not(feature="logging"))]
                crate::ignore!($($t),*);
            }
        }}
    }
}
