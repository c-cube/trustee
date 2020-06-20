//! # Database of definitions and theorems.
//!
//! This database can be serialized and deserialized. (TODO)

use crate::{fnv::*, kernel_of_trust as k, syntax::Fixity, *};

/// A constant, defined or just opaque.
#[derive(Debug, Clone)]
pub struct Constant {
    /// The constant itself.
    pub expr: Expr,
    /// Theorem for `c = …`, if any.
    pub thm: Option<Thm>,
    /// Fixity of the constant: how does it parse/print.
    pub fixity: Fixity,
}

/// A database of definitions and theorems.
#[derive(Debug)]
pub struct Database {
    /// Constants.
    consts: FnvHashMap<String, Constant>,
    ty_defs: FnvHashMap<String, k::NewTypeDef>,
    /// Axioms declared so far
    axioms: Vec<Thm>,
}

impl Database {
    pub fn new(ctx: &mut dyn CtxI) -> Self {
        let mut db = Self {
            consts: new_table_with_cap(32),
            ty_defs: new_table_with_cap(16),
            axioms: vec![],
        };
        db.insert_const_("bool".to_string(), ctx.mk_bool(), Fixity::Nullary);
        db.insert_const_("type".to_string(), ctx.mk_ty(), Fixity::Nullary);
        db.insert_const_("=".to_string(), ctx.mk_eq(), Fixity::Infix((50, 51)));
        db.insert_const_(
            "==>".to_string(),
            ctx.mk_imply(),
            Fixity::Infix((10, 11)),
        );
        db
    }

    /// Find a definition in the database.
    pub fn def_by_name(&self, s: &str) -> Option<&Constant> {
        self.consts.get(s)
    }

    /// Find a type definition in the database.
    pub fn ty_def_by_name(&self, s: &str) -> Option<&k::NewTypeDef> {
        self.ty_defs.get(s)
    }

    pub fn axioms(&self) -> &[Thm] {
        &self.axioms
    }

    /// Change fixity of a constant.
    pub fn set_fixity(&mut self, s: &str, fix: Fixity) -> Result<()> {
        if let Some(c) = self.consts.get_mut(s) {
            c.fixity = fix;
            Ok(())
        } else {
            Err(k::Error::new_string(format!(
                "cannot set fixity of unknown constant `{}`",
                s
            )))
        }
    }

    /// Forget the definition of constant `s`.
    ///
    /// From now on `s` will be opaque, and the only information we have about
    /// it is theorems that contain it.
    pub fn forget_def(&mut self, s: &str) -> Result<()> {
        if let Some(c) = self.consts.get_mut(s) {
            c.thm = None;
            Ok(())
        } else {
            Err(k::Error::new_string(format!(
                "cannot forget def of unknown constant `{}`",
                s
            )))
        }
    }

    /// Add an axiom.
    pub fn add_axiom(&mut self, th: Thm) {
        self.axioms.push(th)
    }

    fn insert_const_(&mut self, name: String, e: Expr, fixity: Fixity) {
        let c = Constant { expr: e, thm: None, fixity };
        self.consts.insert(name, c);
    }

    /// Add a definition.
    pub fn insert_def(&mut self, name: String, e: Expr, th: Thm) {
        let c = Constant { expr: e, thm: Some(th), fixity: Fixity::Nullary };
        self.consts.insert(name, c);
    }

    /// Add a type definition.
    pub fn insert_ty_def(&mut self, d: k::NewTypeDef) {
        self.insert_def(
            d.c_abs.to_string(),
            d.c_abs.clone(),
            d.abs_thm.clone(),
        );
        self.insert_def(
            d.c_repr.to_string(),
            d.c_repr.clone(),
            d.repr_thm.clone(),
        );
        self.ty_defs.insert(d.tau.to_string(), d);
    }

    /// Lookup any kind of value that has the given name.
    ///
    /// The value may be a definition, a type definition, a named theorem, etc.
    pub fn get_by_name(&self, s: &str) -> Option<AnyValue> {
        if let Some(c) = self.def_by_name(s) {
            Some(AnyValue::Def(c))
        } else if let Some(d) = self.ty_def_by_name(s) {
            Some(AnyValue::TyDef(d))
        } else {
            None
        }
    }

    pub fn size(&self) -> usize {
        let Self { consts, ty_defs, axioms } = self;
        consts.len() + ty_defs.len() + axioms.len()
    }

    /// Iterate on all items in the database.
    pub fn all_items(&self) -> impl Iterator<Item = AnyValue> {
        use AnyValue as A;
        self.consts
            .iter()
            .map(|(_, c)| A::Def(c))
            .chain(self.ty_defs.iter().map(|(_, d)| A::TyDef(d)))
            .chain(self.axioms.iter().map(|th| A::Axiom(th)))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum AnyValue<'a> {
    Def(&'a Constant),
    TyDef(&'a k::NewTypeDef),
    Axiom(&'a Thm),
}
