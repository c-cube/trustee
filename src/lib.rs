use std::{
    hash::Hash,
    sync::atomic::{AtomicU64, Ordering},
    sync::Arc,
};

/// Used to allocate new IDs
static ID_N: AtomicU64 = AtomicU64::new(0);

#[derive(PartialEq, Debug, Hash)]
pub struct ID {
    id: u64,
    name: String,
}

impl Eq for ID {}

impl ID {
    /// Create new ID
    pub fn new(s: String) -> ID {
        let id = ID_N.fetch_add(1, Ordering::AcqRel);
        ID { id, name: s }
    }

    pub fn name(&self) -> &str {
        &*self.name
    }
}

/// An expression or a type.
#[derive(Clone, Eq, Ord, PartialOrd, Hash)]
pub struct Expr(Arc<ExprCell>);

impl PartialEq for Expr {
    // pointer equality, or recursive equality
    #[inline]
    fn eq(&self, other: &Expr) -> bool {
        std::ptr::eq(self.0.as_ref(), other.0.as_ref()) || *self.0 == *other.0
    }
}

static EXPR_N: AtomicU64 = AtomicU64::new(0);

#[derive(PartialEq, Eq, Ord, PartialOrd, Hash)]
struct ExprCell {
    id: usize,
    view: ExprView,
    ty: Option<Expr>, // lazily computed
}

#[derive(PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum ExprView {
    Type,
    Kind,
    Const {},
}
