//! # Patterns
//!
//! Patterns are useful for representing expression _shapes_, that can be matched
//! against actual expressions to extract some bindings.
//!
//! For example, the pattern `"(f (g ?a) ?b)"` will match `(f (g (g x)) foo)`
//! and bind `?a` to `(g x)`, and `?b? to `foo`.

use {
    crate::{fnv::FnvHashMap as HM, rptr::RPtr, Error, Expr, Result},
    std::fmt,
};

pub type Ty = Expr;

/// A pattern. It is represented as a flattened term-like structure,
/// a bit like a "flatterm" in ATP terms.
#[derive(Clone)]
pub struct Pattern(RPtr<PatternImpl>);

struct PatternImpl {
    meta_vars: Vec<String>,
    /// Not empty.
    nodes: Vec<PatternView>,
    /// Index in `nodes`.
    root: PatternIdx,
}

/// A single node of the pattern.
///
/// This should match a single node of an expression.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum PatternView {
    /// First occurrence of a meta-variable
    Var(VarIdx),
    /// Non-linear occurrence of a meta-variable
    EqVar(VarIdx),
    /// Expression to match verbatim
    Const(Expr),
    /// Application
    App(PatternIdx, PatternIdx),
    /// Any term.
    Wildcard,
    // TODO: with-ty(Pattern, Ty) for checking type
    // TODO? Lam(Ty, PatternIdx),
}

/// A substitution, obtained by successfully matching a pattern against an expression.
///
/// The substitution maps each meta-variable into a sub-expression.
pub struct PatternSubst {
    p: Pattern,
    /// Invariant: same length as `p.meta_vars`
    subst: Vec<Expr>,
}

/// A pattern meta-variable.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct VarIdx(u8);

/// An index in the pattern's structure.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct PatternIdx(u8);

/// A temporary builder for patterns.
pub struct PatternBuilder {
    nodes: Vec<PatternView>,
    meta_vars: Vec<String>,
}

impl PatternBuilder {
    /// Create a new pattern.
    pub fn new() -> Self {
        Self {
            nodes: vec![],
            meta_vars: vec![],
        }
    }

    /// Allocate a new pattern node with given view.
    pub fn alloc_node(&mut self, v: PatternView) -> Result<PatternIdx> {
        let i = self.nodes.len();
        if i > u8::MAX as usize {
            return Err(Error::new("pattern is too long"));
        }
        self.nodes.push(v);
        Ok(PatternIdx(i as u8))
    }

    fn alloc_new_meta_(&mut self, s: &str) -> Result<PatternIdx> {
        let i = self.meta_vars.len();
        if i > u8::MAX as usize {
            return Err(Error::new("too many meta variables in pattern"));
        }
        let i = VarIdx(i as u8);
        self.meta_vars.push(s.to_string());
        let view = PatternView::Var(i);
        self.alloc_node(view)
    }

    /// Find or reuse meta-variable with name `s`.
    pub fn alloc_meta(&mut self, s: &str) -> Result<PatternIdx> {
        if let Some((i, _)) = self.meta_vars.iter().enumerate().find(|(_, x)| &**x == s) {
            // non linear use of that meta
            let i = VarIdx(i as u8);
            self.alloc_node(PatternView::EqVar(i))
        } else {
            self.alloc_new_meta_(s)
        }
    }

    pub fn alloc_wildcard(&mut self) -> Result<PatternIdx> {
        self.alloc_node(PatternView::Wildcard)
    }

    /// Turn the builder into a proper pattern.
    pub fn into_pattern(self, root: PatternIdx) -> Pattern {
        assert!((root.0 as usize) < self.nodes.len());
        let PatternBuilder { nodes, meta_vars } = self;
        Pattern(RPtr::new(PatternImpl {
            root,
            nodes,
            meta_vars,
        }))
    }
}

impl Pattern {
    /// Number of internal nodes.
    pub fn len(&self) -> usize {
        self.0.nodes.len()
    }

    /// Number of meta-variables.
    pub fn n_vars(&self) -> usize {
        self.0.meta_vars.len()
    }

    /// Iterate on the variables bound by this pattern.
    pub fn iter_vars(&self) -> impl Iterator<Item = (&str, VarIdx)> {
        self.0
            .meta_vars
            .iter()
            .enumerate()
            .map(|(i, s)| (&**s, VarIdx(i as u8)))
    }

    /// Flatten applications.
    pub fn unfold_app(&self, i: PatternIdx) -> (PatternIdx, Vec<PatternIdx>) {
        let mut i = i;
        let mut args = vec![];

        while let PatternView::App(a, b) = &self[i] {
            i = *a;
            args.push(*b)
        }
        args.reverse();
        (i, args)
    }

    /// Find a meta-variable by its name.
    pub fn find_var_by_name(&self, name: &str) -> Option<VarIdx> {
        self.0
            .meta_vars
            .iter()
            .enumerate()
            .find(|(_, s)| &**s == name)
            .map(|t| VarIdx(t.0 as u8))
    }

    fn print_(&self, i: PatternIdx, out: &mut fmt::Formatter) -> fmt::Result {
        match &self[i] {
            PatternView::Var(v) => write!(out, "?{}", &self[*v]),
            PatternView::EqVar(v) => write!(out, ".?{}", &self[*v]),
            PatternView::Const(e) => write!(out, "{}", e),
            PatternView::App(_, _) => {
                let (hd, args) = self.unfold_app(i);
                write!(out, "(")?;
                self.print_(hd, out)?;
                for x in args {
                    write!(out, " ")?;
                    self.print_(x, out)?;
                }
                write!(out, ")")
            }
            PatternView::Wildcard => write!(out, "_"),
        }
    }

    fn match_rec_(&self, tbl: &mut HM<VarIdx, Expr>, i: PatternIdx, e: &Expr) -> bool {
        use crate::ExprView as EV;
        match (&self[i], e.view()) {
            (PatternView::Wildcard, _) => {
                true // always matches
            }
            (PatternView::Var(v), _) => {
                if let Some(e2) = tbl.get(&v) {
                    e == e2
                } else {
                    tbl.insert(*v, e.clone());
                    true
                }
            }
            (PatternView::EqVar(v), _) => {
                if let Some(e2) = tbl.get(&v) {
                    e == e2
                } else {
                    tbl.insert(*v, e.clone());
                    true
                }
            }
            (PatternView::App(f, a), EV::EApp(ef, ea)) => {
                self.match_rec_(tbl, *f, ef) && self.match_rec_(tbl, *a, ea)
            }
            (PatternView::App(..), _) => false,
            (PatternView::Const(c), _) => c == e,
        }
    }

    /// Match pattern against the given expression.
    pub fn match_(&self, e: &Expr) -> Option<PatternSubst> {
        let mut tbl = crate::fnv::new_table_with_cap(8);
        if self.match_rec_(&mut tbl, self.0.root, e) {
            let mut subst = Vec::with_capacity(self.n_vars());
            subst.resize(self.n_vars(), e.clone()); // `e` will be entirely erased
            for (v, e2) in tbl.into_iter() {
                subst[v.0 as usize] = e2
            }
            let subst = PatternSubst {
                p: self.clone(),
                subst,
            };
            Some(subst)
        } else {
            None
        }
    }
}

impl PatternSubst {
    /// Get value for a variable, by name.
    ///
    /// Linear in the number of variables bound in this substitution.
    pub fn get_by_name(&self, s: &str) -> Option<&Expr> {
        let i = self.p.find_var_by_name(s)?;
        Some(&self[i])
    }
}

mod impls {
    use super::*;

    impl std::ops::Index<PatternIdx> for Pattern {
        type Output = PatternView;

        #[inline]
        fn index(&self, i: PatternIdx) -> &Self::Output {
            &self.0.nodes[i.0 as usize]
        }
    }

    impl std::ops::Index<VarIdx> for Pattern {
        type Output = str;

        #[inline]
        fn index(&self, i: VarIdx) -> &Self::Output {
            &self.0.meta_vars[i.0 as usize]
        }
    }

    impl std::ops::Index<VarIdx> for PatternSubst {
        type Output = Expr;

        #[inline]
        fn index(&self, i: VarIdx) -> &Self::Output {
            &self.subst[i.0 as usize]
        }
    }

    impl fmt::Debug for Pattern {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            self.print_(self.0.root, f)
        }
    }

    impl fmt::Debug for PatternSubst {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "(subst")?;
            for (i, e) in self.subst.iter().enumerate() {
                write!(f, " (?{} := {})", &self.p[VarIdx(i as u8)], e)?;
            }
            write!(f, ")")
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{meta, syntax, Ctx};

    #[test]
    fn test_pp() -> Result<()> {
        let mut ctx = Ctx::new();
        meta::load_prelude_hol(&mut ctx)?;
        let s = r#"(/\ ?a (\/ ?a (~ ?b)))"#;
        let p = syntax::parse_pattern(&mut ctx, &s)?;
        let s2 = format!("{:?}", p);
        assert_eq!(r#"($/\ ?a ($\/ .?a ($~ ?b)))"#, s2);
        Ok(())
    }

    #[test]
    fn test_itervars() -> Result<()> {
        let mut ctx = Ctx::new();
        let s = r#"(_ ?a (_ ?a (_ ?b)))"#;
        let p = syntax::parse_pattern(&mut ctx, &s)?;

        let vars: Vec<_> = p.iter_vars().collect();

        assert_eq!(vars, vec![("a", VarIdx(0)), ("b", VarIdx(1))]);

        Ok(())
    }

    #[test]
    fn test_match() -> Result<()> {
        let mut ctx = Ctx::new();
        meta::load_prelude_hol(&mut ctx)?;
        let s = r#"/\ ?a (\/ ?a (~ ?b))"#;
        let p = syntax::parse_pattern(&mut ctx, &s)?;
        let e = syntax::parse_expr(&mut ctx, r#"T /\ (T \/ ~ F)"#)?;

        let subst = p.match_(&e).ok_or(Error::new("cannot match"))?;
        assert_eq!("(subst (?a := T) (?b := F))", format!("{:?}", subst));

        let t1 = syntax::parse_expr(&mut ctx, "T")?;
        let t2 = syntax::parse_expr(&mut ctx, "F")?;

        assert_eq!(Some(&t1), subst.get_by_name("a"));
        assert_eq!(Some(&t2), subst.get_by_name("b"));

        Ok(())
    }

    #[test]
    fn test_imply() -> Result<()> {
        let mut ctx = Ctx::new();
        meta::load_prelude_hol(&mut ctx)?;
        let s = r#"==> ?a ?b"#;
        let p = syntax::parse_pattern(&mut ctx, &s)?;

        let e = syntax::parse_expr(&mut ctx, r#"T ==> F"#)?;
        let subst = p.match_(&e).ok_or_else(|| Error::new("match fail"))?;

        let t1 = syntax::parse_expr(&mut ctx, "T")?;
        let t2 = syntax::parse_expr(&mut ctx, "F")?;

        assert_eq!(Some(&t1), subst.get_by_name("a"));
        assert_eq!(Some(&t2), subst.get_by_name("b"));
        Ok(())
    }
}
