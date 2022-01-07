//! # Proof Printing

use {crate::fnv::FnvHashMap as HM, crate::kernel::*, std::io::Write};

pub struct Printer<'a> {
    out: &'a mut dyn Write,
    /// For each expressions to print, number of times it is required.
    rc_expr: HM<Expr, u32>,
    /// For each theorem to print, number of times it is required.
    rc_thm: HM<Thm, u32>,
    /// Id for expressions already printed
    id_expr: HM<Expr, Id>,
    /// Id for theorems already printed
    id_thm: HM<Thm, Id>,
    max_id: u32,
    free_ids: Vec<u32>,
    last_id: Id,
}

/// Tasks during first DFS
#[derive(Debug)]
enum Task1 {
    ExploreExpr(Expr),
    ExploreThm(Thm),
}

/// Tasks during second DFS
#[derive(Debug)]
enum Task2 {
    /// Start processing `e` in the traversal. Means we also explore its deps.
    EnterExpr(Expr),
    /// Print `e`. Deps must have been printed.
    PrintExpr(Expr),
    /// Decrement refcount of `e`, as it's no longer needed by some parent.
    ExitExpr(Expr),
    EnterThm(Thm),
    PrintThm(Thm),
    ExitThm(Thm),
}

type Id = u32;

impl<'a> Printer<'a> {
    /// New printer
    pub fn new(out: &'a mut dyn Write) -> Self {
        Self {
            out,
            rc_expr: HM::default(),
            rc_thm: HM::default(),
            id_expr: HM::default(),
            id_thm: HM::default(),
            max_id: 0,
            free_ids: vec![],
            last_id: 0,
        }
    }

    // find a free number
    fn alloc_ref_(&mut self) -> u32 {
        let id = if let Some(u) = self.free_ids.pop() {
            u
        } else {
            let i = self.max_id;
            self.max_id += 1;
            i
        };
        self.last_id = id;
        id
    }

    fn free_id(&mut self, i: Id) {
        self.free_ids.push(i);
    }

    fn get_term_id(&self, e: &Expr) -> Result<Id> {
        self.id_expr
            .get(e)
            .copied()
            .ok_or_else(|| Error::new_string(format!("cannot find name for expression `{}`", e)))
    }

    fn get_thm_id(&self, th: &Thm) -> Result<Id> {
        self.id_thm
            .get(th)
            .copied()
            .ok_or_else(|| Error::new_string(format!("cannot find name for theorem `{}`", th)))
    }

    /// Compute refcount of each element of the proof (expression or theorem).
    fn gather_refcounts(&mut self, th: &Thm) -> Result<()> {
        let mut to_explore = vec![];
        to_explore.push(Task1::ExploreThm(th.clone()));

        while let Some(t) = to_explore.pop() {
            crate::logtrace!("dfs1.explore {:?}", t);
            match t {
                Task1::ExploreExpr(e) => {
                    if let Some(rc) = self.rc_expr.get_mut(&e) {
                        *rc += 1
                    } else {
                        self.rc_expr.insert(e.clone(), 1);

                        // explore sub-terms
                        e.view()
                            .iter(
                                |e2, _| {
                                    to_explore.push(Task1::ExploreExpr(e2.clone()));
                                    Ok(())
                                },
                                0,
                            )
                            .unwrap();
                    }
                }
                Task1::ExploreThm(th) => {
                    if let Some(rc) = self.rc_thm.get_mut(&th) {
                        *rc += 1;
                    } else {
                        let pr = match th.proof() {
                            None => return Err(Error::new("theorem has no proof")),
                            Some(pr) => pr,
                        };

                        self.rc_thm.insert(th.clone(), 1);

                        // print dependencies
                        let mut ve = vec![];
                        let mut vth = vec![];
                        pr.premises(|e| ve.push(e.clone()), |th| vth.push(th.clone()));

                        for th in vth {
                            to_explore.push(Task1::ExploreThm(th));
                        }
                        for e in ve {
                            to_explore.push(Task1::ExploreExpr(e));
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Traverse the graph of theorems and expressions, printing them on
    /// the fly.
    fn print_loop(&mut self, th: &Thm) -> Result<()> {
        let mut to_explore = vec![];
        to_explore.push(Task2::ExitThm(th.clone()));
        to_explore.push(Task2::EnterThm(th.clone()));

        while let Some(t) = to_explore.pop() {
            crate::logtrace!("dfs2.explore {:?}", t);
            match t {
                Task2::EnterExpr(e) => {
                    assert!(self.rc_expr.contains_key(&e));

                    if let Some(_) = self.id_expr.get_mut(&e) {
                        continue; // already printed, nothing to do
                    }

                    let id = self.alloc_ref_();
                    assert!(self.id_expr.iter().all(|(_, id2)| id != *id2));
                    self.id_expr.insert(e.clone(), id);

                    // release dependencies
                    e.view()
                        .iter(
                            |e2, _| {
                                to_explore.push(Task2::ExitExpr(e2.clone()));
                                Ok(())
                            },
                            0,
                        )
                        .unwrap();

                    // print expr, after dependencies have been printed
                    to_explore.push(Task2::PrintExpr(e.clone()));

                    // print dependencies
                    e.view()
                        .iter(
                            |e2, _| {
                                to_explore.push(Task2::EnterExpr(e2.clone()));
                                Ok(())
                            },
                            0,
                        )
                        .unwrap();
                }
                Task2::PrintExpr(e) => {
                    let id = self.get_term_id(&e)?;

                    match e.view() {
                        EType => {
                            writeln!(self.out, "ty {}", id)?;
                        }
                        EKind => return Err(Error::new("cannot print kind")),
                        EConst(..) if e.is_bool() => {
                            writeln!(self.out, "bool {}", id)?;
                        }
                        EConst(c, args) => {
                            // FIXME: see if `c` has a proof, in which case use a get
                            write!(self.out, "c {} {}", id, c.name.name())?;
                            for a in &args[..] {
                                let aid = self.get_term_id(&a)?;
                                write!(self.out, " {}", aid)?;
                            }
                            writeln!(self.out)?;
                        }
                        EVar(v) => {
                            let tyid = self.get_term_id(&v.ty)?;
                            writeln!(self.out, "v {} {} {}", id, v.name.name(), tyid)?;
                        }
                        EBoundVar(v) => {
                            let tyid = self.get_term_id(v.ty())?;
                            writeln!(self.out, "bv {} {} {}", id, v.idx(), tyid)?;
                        }
                        EApp(f, a) => {
                            let idf = self.get_term_id(&f)?;
                            let ida = self.get_term_id(&a)?;
                            assert_ne!(idf, ida);
                            writeln!(self.out, "@ {} {} {}", id, idf, ida)?;
                        }
                        ELambda(tyv, bod) => {
                            let idty = self.get_term_id(&tyv)?;
                            let idbod = self.get_term_id(&bod)?;
                            writeln!(self.out, "\\ {} {} {}", id, idty, idbod)?;
                        }
                        EArrow(a, ret) => {
                            let ida = self.get_term_id(&a)?;
                            let idret = self.get_term_id(&ret)?;
                            writeln!(self.out, "-> {} {} {}", id, ida, idret)?;
                        }
                    }
                }
                Task2::ExitExpr(e) => {
                    let n = self.rc_expr.get_mut(&e).expect("refcount err");
                    *n -= 1;

                    // not needed anymore
                    if *n == 0 {
                        let id = self.get_term_id(&e)?;
                        self.free_id(id);
                        self.id_expr.remove(&e);
                        self.rc_expr.remove(&e);
                    }
                }
                Task2::EnterThm(th) => {
                    assert!(self.rc_thm.contains_key(&th));

                    if let Some(_) = self.id_thm.get_mut(&th) {
                        continue; // already printed, nothing to do
                    }

                    let id = self.alloc_ref_();
                    assert!(self.id_thm.iter().all(|(_, id2)| id != *id2));
                    self.id_thm.insert(th.clone(), id);

                    let pr = match th.proof() {
                        None => return Err(Error::new("theorem has no proof")),
                        Some(pr) => pr,
                    };

                    // print dependencies
                    let mut ve = vec![];
                    let mut vth = vec![];
                    pr.premises(|e| ve.push(e.clone()), |th| vth.push(th.clone()));

                    for th in vth.clone() {
                        to_explore.push(Task2::ExitThm(th.clone()));
                    }
                    for e in ve.clone() {
                        to_explore.push(Task2::ExitExpr(e.clone()));
                    }

                    // print th, after dependencies have been printed
                    to_explore.push(Task2::PrintThm(th.clone()));

                    for th in vth {
                        to_explore.push(Task2::EnterThm(th));
                    }
                    for e in ve {
                        to_explore.push(Task2::EnterExpr(e));
                    }
                }
                Task2::ExitThm(th) => {
                    let n = self.rc_thm.get_mut(&th).expect("refcount err");
                    *n -= 1;
                    if *n == 0 {
                        let id = self.get_thm_id(&th)?;
                        self.free_id(id);
                        self.id_thm.remove(&th);
                        self.rc_thm.remove(&th);
                    }
                }
                Task2::PrintThm(th) => {
                    let id = self.get_thm_id(&th)?;

                    let pr = match th.proof() {
                        None => return Err(Error::new("theorem has no proof")),
                        Some(pr) => pr,
                    };

                    match &**pr {
                        ProofView::Assume(e) => {
                            let ide = self.get_term_id(e)?;
                            writeln!(self.out, "ASS {} {}", id, ide)?;
                        }
                        ProofView::Refl(e) => {
                            let ide = self.get_term_id(e)?;
                            writeln!(self.out, "RFL {} {}", id, ide)?;
                        }
                        ProofView::Trans(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "TRNS {} {} {}", id, n1, n2)?;
                        }
                        ProofView::Congr(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "CGR {} {} {}", id, n1, n2)?;
                        }
                        ProofView::CongrTy(th1, ty) => {
                            let idty = self.get_term_id(&ty)?;
                            let n1 = self.get_thm_id(&th1)?;
                            writeln!(self.out, "CGRTY {} {} {}", id, n1, idty)?;
                        }
                        ProofView::Instantiate(th1, subst) => {
                            let n1 = self.get_thm_id(&th1)?;
                            write!(self.out, "SBST {} {}", id, n1)?;
                            for (v, e) in &subst[..] {
                                let eid = self.get_term_id(e)?;
                                write!(self.out, " {} {}", v.name.name(), eid)?;
                            }
                            writeln!(self.out)?;
                        }
                        ProofView::Abs(v, th1) => {
                            let ty = self.get_term_id(&v.ty)?;
                            let n1 = self.get_thm_id(&th1)?;
                            writeln!(self.out, "ABS {} {} {} {}", id, v.name.name(), ty, n1)?;
                        }
                        ProofView::Axiom(e) => {
                            let eid = self.get_term_id(e)?;
                            writeln!(self.out, "AX {} {}", id, eid)?;
                        }
                        ProofView::Cut(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "CUT {} {} {}", id, n1, n2)?;
                        }
                        ProofView::BoolEq(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "BEQ {} {} {}", id, n1, n2)?;
                        }
                        ProofView::BoolEqIntro(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "BEQI {} {} {}", id, n1, n2)?;
                        }
                        ProofView::BetaConv(e) => {
                            let eid = self.get_term_id(e)?;
                            writeln!(self.out, "BETA {} {}", id, eid)?;
                        }
                        ProofView::NewDef(e) => {
                            let eid = self.get_term_id(e)?;
                            writeln!(self.out, "DEF {} {}", id, eid)?;
                        }
                        ProofView::NewTyDef(e, th) => {
                            let ide = self.get_term_id(e)?;
                            let idth = self.get_thm_id(th)?;
                            writeln!(self.out, "TYDEF {} {} {}", id, ide, idth)?;
                        }
                        ProofView::GetThm(r) => {
                            writeln!(self.out, "GET {} {}", id, r)?;
                        }
                        ProofView::CallRule1(r, th1) => {
                            let id1 = self.get_thm_id(th1)?;
                            writeln!(self.out, "CALL {} {} {}", id, r, id1)?;
                        }
                        ProofView::CallRule2(r, th1, th2) => {
                            let id1 = self.get_thm_id(th1)?;
                            let id2 = self.get_thm_id(th2)?;
                            writeln!(self.out, "CALL {} {} {} {}", id, r, id1, id2)?;
                        }
                        ProofView::CallRuleN(r, a) => {
                            write!(self.out, "CALL {} {}", id, r)?;
                            for th in &a[..] {
                                let id = self.get_thm_id(th)?;
                                write!(self.out, " {}", id)?;
                            }
                            writeln!(self.out)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Print proof of this theorem and its parents, recursively.
    pub fn print_proof(&mut self, th: &Thm) -> Result<Id> {
        self.gather_refcounts(th)?;
        self.print_loop(th)?;
        let id = self.last_id;
        Ok(id)
    }

    pub fn set_name(&mut self, id: Id, name: &str) -> Result<()> {
        crate::logdebug!("set name {} := {}", id, name);
        writeln!(self.out, "SET {} {}", id, name)?;
        Ok(())
    }
}

/// Print proof into stirng, if present.
pub fn proof_to_string(th: &Thm) -> Option<String> {
    let mut v = vec![];
    let mut p = Printer::new(&mut v);
    if let Err(_e) = p.print_proof(th) {
        return None;
    }
    std::string::String::from_utf8(v).ok()
}
