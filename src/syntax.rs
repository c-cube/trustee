//! A basic syntax for parsing and printing terms.
//!
//! This syntax is optional and is not needed at all when using the kernel.
//! We follow https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
//! for the main parser and terminology.

use crate::{database as db, kernel_of_trust as k};
use std::{cell::RefCell, rc::Rc};

/// Reuse symbols from the kernel.
type Symbol = k::Symbol;

/// The AST used for parsing and type inference.
#[derive(Debug, Clone)]
pub struct PExpr(Rc<PExprCell>);

/// Content of an expression.
#[derive(Debug, Clone)]
pub struct PExprCell {
    view: PExprView,
    ty: RefCell<Option<k::Expr>>,
}

/// A (possibly type-annotated) variable
#[derive(Debug, Clone)]
pub struct Var {
    name: Symbol,
    ty: Option<PExpr>,
}

/// How a symbol behaves in the grammar: prefix, infix, postfix, constant.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Fixity {
    /// No arguments
    Nullary,
    /// Unary, prefix (e.g. `¬`)
    Prefix(BindingPower),
    /// Infix (e.g. `+`)
    Infix(BindingPower),
    /// Postfix (e.g. `^c`, set complement)
    Postfix(BindingPower),
    /// Binder symbol (e.g. `?`, exists)
    Binder(BindingPower),
}

/// Binding power. The higher,
pub type BindingPower = u32;

#[derive(Debug, Clone)]
pub enum PExprView {
    Var(Symbol),
    DollarVar(Symbol), // `$foo` is the non-infix version of `foo` with explicit type args
    App(PExpr, Vec<PExpr>),
    Bind { binder: Symbol, v: Var, body: PExpr },
}

/// Parser for expressions.
///
/// It uses the precedence table provided by a `Database`, and an IO stream.
pub struct Parser<'a> {
    db: &'a db::Database,
    /// The source code.
    src: &'a str,
    /// Index in `src`
    i: usize,
    /// Current line in `src`
    line: usize,
    /// Current column in `src`
    col: usize,
}

impl<'a> Parser<'a> {
    /// New parser using the given string `src`.
    pub fn new(db: &'a db::Database, src: &'a str) -> Self {
        Self { db, src, i: 0, line: 1, col: 1 }
    }

    // TODO!
}
