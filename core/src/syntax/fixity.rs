/// ## Fixity for symbols
///
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

/// Binding power. The higher, the stronger it tights.
///
/// It's a pair because it's left and right binding powers so we can represent
/// associativity.
/// See https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html .
pub type BindingPower = (u16, u16);

impl Fixity {
    pub fn bp(&self) -> BindingPower {
        match self {
            Fixity::Nullary => (0, 0),
            Fixity::Prefix(p) => *p,
            Fixity::Infix(p) => *p,
            Fixity::Postfix(p) => *p,
            Fixity::Binder(p) => *p,
        }
    }
}

pub(crate) const FIXITY_EQ: Fixity = Fixity::Infix((30, 31));
pub(crate) const FIXITY_LAM: Fixity = Fixity::Binder((10, 11));
pub(crate) const FIXITY_PI: Fixity = Fixity::Binder((24, 25));
pub(crate) const FIXITY_ARROW: Fixity = Fixity::Infix((81, 80));
