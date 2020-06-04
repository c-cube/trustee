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

    /// Insert a new theorem into the DB.
    pub fn insert_thm(&mut self, name: Option<&str>, thm: Thm) {
        let name = name.map_or_else(
            || {
                self.n += 1;
                format!("$thm{}", self.n)
            },
            |s| s.to_string(),
        );
        if self.thm.contains_key(&name) {
            panic!("theorem named {:?} already declared in DB", name)
        }
        self.thm.insert(name, thm.clone());
        self.thm_rev.insert(ThmKey::new(&thm), thm);
    }
}
