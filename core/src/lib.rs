#![deny(unsafe_code)]

pub mod algo;
mod fnv;
pub mod kernel_of_trust;
pub mod meta;
pub mod position;
pub mod rptr;
pub mod rstr;
pub mod syntax;

pub use fnv::{new_set_with_cap, new_table_with_cap, FnvHashMap, FnvHashSet};

pub use crate::meta::{load_prelude_hol, run_code};
pub use kernel_of_trust::ExprView::*;
pub use kernel_of_trust::{Ctx, Error, Expr, ExprView, Result, Symbol, Thm, Var};
pub use syntax::{parse_expr, parse_expr_with_args};

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
