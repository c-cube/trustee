pub mod algo;
mod fnv;
pub mod kernel_of_trust;
pub mod meta;
pub mod syntax;

pub use fnv::{new_set_with_cap, new_table_with_cap, FnvHashMap, FnvHashSet};

pub use kernel_of_trust::ExprView::*;
pub use kernel_of_trust::{
    Ctx, Error, Expr, ExprView, Result, Symbol, Thm, Var,
};
pub use syntax::{parse_expr, parse_expr_with_args};