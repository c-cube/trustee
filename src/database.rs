//! # Database of definitions and theorems.
//!
//! This database can be serialized and deserialized. (TODO)

use crate::fnv::*;
use crate::kernel_of_trust as k;
use crate::*;

/// Used for looking up theorems.
#[derive(Debug, Eq, PartialEq, Hash)]
pub struct ThmKey(pub Expr, pub Vec<Expr>);

impl ThmKey {
    /// New key from this theorem.
    pub fn new(th: &Thm) -> Self {
        ThmKey(th.concl().clone(), th.hyps_vec().clone())
    }
}

/// A database of definitions and theorems.
#[derive(Debug)]
pub struct Database {
    /// Counter for basic names.
    n: usize,
    defs: FnvHashMap<String, (Expr, Thm)>,
    ty_defs: FnvHashMap<String, k::NewTypeDef>,
    /// Axioms declared so far
    axioms: Vec<Thm>,
    /// Theorems, by name
    thm: FnvHashMap<String, Thm>,
    /// Reverse index of theorems.
    thm_rev: FnvHashMap<ThmKey, Thm>,
}

impl Database {
    pub fn new() -> Self {
        Self {
            n: 0,
            defs: new_table_with_cap(32),
            ty_defs: new_table_with_cap(16),
            axioms: vec![],
            thm: new_table_with_cap(16),
            thm_rev: new_table_with_cap(16),
        }
    }

    /// Find a definition in the database.
    pub fn def_by_name(&self, s: &str) -> Option<&(Expr, Thm)> {
        self.defs.get(s)
    }

    /// Find a type definition in the database.
    pub fn ty_def_by_name(&self, s: &str) -> Option<&k::NewTypeDef> {
        self.ty_defs.get(s)
    }

    pub fn axioms(&self) -> &[Thm] {
        &self.axioms
    }

    /// Find a theorem in the database, using its name.
    pub fn thm_by_name(&self, s: &str) -> Option<&Thm> {
        self.thm.get(s)
    }

    /// Find a theorem in the database, using its structural key.
    pub fn thm_by_key(&self, k: &ThmKey) -> Option<&Thm> {
        self.thm_rev.get(k)
    }

    fn insert_thm_(&mut self, name: String, thm: Thm) {
        if self.thm.contains_key(&name) {
            panic!("theorem named {:?} already declared in DB", name)
        }
        self.thm.insert(name, thm.clone());
        self.thm_rev.insert(ThmKey::new(&thm), thm);
    }

    /// Insert a new theorem into the DB.
    pub fn insert_thm(&mut self, name: Option<&str>, thm: Thm) {
        let name = name.map_or_else(
            || {
                self.n += 1;
                format!("$thm{}", self.n)
            },
            |s| s.to_string(),
        );
        self.insert_thm_(name, thm)
    }

    /// Add an axiom.
    pub fn add_axiom(&mut self, th: Thm) {
        self.axioms.push(th)
    }

    /// Add a definition.
    pub fn insert_def(&mut self, name: String, e: Expr, th: Thm) {
        self.insert_thm_(name.clone(), th.clone());
        self.defs.insert(name, (e, th));
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
        if let Some((e, th)) = self.def_by_name(s) {
            Some(AnyValue::Def(e, th))
        } else if let Some(th) = self.thm_by_name(s) {
            Some(AnyValue::Thm(th))
        } else if let Some(d) = self.ty_def_by_name(s) {
            Some(AnyValue::TyDef(d))
        } else {
            None
        }
    }

    pub fn size(&self) -> usize {
        let Self { defs, thm, ty_defs, thm_rev: _, n: _, axioms } = self;
        defs.len() + thm.len() + ty_defs.len() + axioms.len() + defs.len()
    }

    /// Iterate on all items in the database.
    pub fn all_items(&self) -> impl Iterator<Item = AnyValue> {
        use AnyValue as A;
        self.defs
            .iter()
            .map(|(_, (t, th))| A::Def(t, th))
            .chain(self.ty_defs.iter().map(|(_, d)| A::TyDef(d)))
            .chain(self.thm.iter().map(|(_, th)| A::Thm(th)))
            .chain(self.axioms.iter().map(|th| A::Axiom(th)))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum AnyValue<'a> {
    Def(&'a Expr, &'a Thm),
    TyDef(&'a k::NewTypeDef),
    Thm(&'a Thm),
    Axiom(&'a Thm),
}
