//! # Proof Printing

use {super::*, crate::fnv::FnvHashMap as HM, std::io::Write};

pub struct Printer<'a> {
    out: &'a mut dyn Write,
    /// For each expressions to print, number of times it is required.
    expr_seen: HM<Expr, Ref>,
    /// For each theorem to print, number of times it is required.
    thm_seen: HM<Thm, Ref>,
    max_id: u32,
    free_ids: Vec<u32>,
    to_explore: Vec<Task>,
    last_id: Id,
}

#[derive(Debug)]
enum Task {
    EnterExpr(Expr),
    ExitExpr(Expr),
    PrintExpr(Expr),
    EnterThm(Thm),
    ExitThm(Thm),
    PrintThm(Thm),
}

type Id = u32;

#[derive(Debug, Clone, Copy)]
struct Ref {
    id: Id,
    count: u32,
}

impl<'a> Printer<'a> {
    /// New printer
    pub fn new(out: &'a mut dyn Write) -> Self {
        Self {
            out,
            expr_seen: HM::default(),
            thm_seen: HM::default(),
            max_id: 0,
            free_ids: vec![],
            to_explore: vec![],
            last_id: 0,
        }
    }

    // find a free number
    fn alloc_ref_(&mut self) -> u32 {
        if let Some(u) = self.free_ids.pop() {
            u
        } else {
            let i = self.max_id;
            self.max_id += 1;
            i
        }
    }

    fn free_id(&mut self, i: Id) {
        self.free_ids.push(i);
        self.last_id = i;
    }

    fn get_term_id(&self, e: &Expr) -> Result<Id> {
        self.expr_seen
            .get(e)
            .map(|r| r.id)
            .ok_or_else(|| Error::new_string(format!("cannot find name for expression `{}`", e)))
    }

    fn get_thm_id(&self, th: &Thm) -> Result<Id> {
        self.thm_seen
            .get(th)
            .map(|r| r.id)
            .ok_or_else(|| Error::new_string(format!("cannot find name for theorem `{}`", th)))
    }

    fn print_loop(&mut self) -> Result<()> {
        while let Some(t) = self.to_explore.pop() {
            crate::logtrace!("explore {:?}", t);
            match t {
                Task::EnterExpr(e) => {
                    if let Some(eref) = self.expr_seen.get_mut(&e) {
                        // already printed, be need to hold on to it
                        eref.count += 1;
                    } else {
                        let id = self.alloc_ref_();
                        let eref = Ref { id, count: 1 };
                        self.expr_seen.insert(e.clone(), eref);

                        e.view()
                            .iter(
                                |e2, _| {
                                    self.to_explore.push(Task::ExitExpr(e2.clone()));
                                    Ok(())
                                },
                                0,
                            )
                            .unwrap();

                        // print expr, after dependencies have been printed
                        self.to_explore.push(Task::PrintExpr(e.clone()));

                        e.view()
                            .iter(
                                |e2, _| {
                                    self.to_explore.push(Task::EnterExpr(e2.clone()));
                                    Ok(())
                                },
                                0,
                            )
                            .unwrap();
                    }
                }
                Task::ExitExpr(e) => {
                    let eref = self
                        .expr_seen
                        .get_mut(&e)
                        .ok_or_else(|| Error::new("refcount error"))?;
                    eref.count -= 1;

                    // not needed anymore
                    if eref.count == 0 {
                        let id = eref.id;
                        self.free_id(id);
                        self.expr_seen.remove(&e);
                    }
                }
                Task::PrintExpr(e) => {
                    let id = self.get_term_id(&e)?;

                    match e.view() {
                        EType => {
                            writeln!(self.out, "{} #type", id)?;
                        }
                        EKind => return Err(Error::new("cannot print kind")),
                        EConst(c) => {
                            let tyid = self.get_term_id(&c.ty)?;
                            writeln!(self.out, "{} c {} {}", id, c.name.name(), tyid)?;
                        }
                        EVar(v) => {
                            let tyid = self.get_term_id(&v.ty)?;
                            writeln!(self.out, "{} v {} {}", id, v.name.name(), tyid)?;
                        }
                        EBoundVar(v) => {
                            let tyid = self.get_term_id(&v.ty)?;
                            writeln!(self.out, "{} bv {} {}", id, v.idx, tyid)?;
                        }
                        EApp(f, a) => {
                            let idf = self.get_term_id(&f)?;
                            let ida = self.get_term_id(&a)?;
                            writeln!(self.out, "{} @ {} {}", id, idf, ida)?;
                        }
                        ELambda(tyv, bod) => {
                            let idty = self.get_term_id(&tyv)?;
                            let idbod = self.get_term_id(&bod)?;
                            writeln!(self.out, "{} \\ {} {}", id, idty, idbod)?;
                        }
                        EPi(tyv, bod) => {
                            let idty = self.get_term_id(&tyv)?;
                            let idbod = self.get_term_id(&bod)?;
                            writeln!(self.out, "{} P {} {}", id, idty, idbod)?;
                        }
                    }
                }
                Task::EnterThm(th) => {
                    if let Some(thref) = self.thm_seen.get_mut(&th) {
                        // already printed, be need to hold on to it
                        thref.count += 1;
                    } else {
                        let pr = match th.proof() {
                            None => return Err(Error::new("theorem has no proof")),
                            Some(pr) => pr,
                        };

                        let id = self.alloc_ref_();
                        let thref = Ref { id, count: 1 };
                        self.thm_seen.insert(th.clone(), thref);

                        // print dependencies
                        let mut ve = vec![];
                        let mut vth = vec![];
                        pr.premises(|e| ve.push(e.clone()), |th| vth.push(th.clone()));

                        for th in vth.clone() {
                            self.to_explore.push(Task::ExitThm(th.clone()));
                        }
                        for e in ve.clone() {
                            self.to_explore.push(Task::ExitExpr(e.clone()));
                        }

                        // print th, after dependencies have been printed
                        self.to_explore.push(Task::PrintThm(th.clone()));

                        for th in vth {
                            self.to_explore.push(Task::EnterThm(th.clone()));
                        }
                        for e in ve {
                            self.to_explore.push(Task::EnterExpr(e.clone()));
                        }
                    }
                }
                Task::ExitThm(th) => {
                    let thref = self
                        .thm_seen
                        .get_mut(&th)
                        .ok_or_else(|| Error::new("theorem refcount error"))?;
                    thref.count -= 1;
                    if thref.count == 0 {
                        let id = thref.id;
                        self.thm_seen.remove(&th);
                        self.free_id(id);
                    }
                }
                Task::PrintThm(th) => {
                    let id = self.get_thm_id(&th)?;

                    let pr = match th.proof() {
                        None => return Err(Error::new("theorem has no proof")),
                        Some(pr) => pr,
                    };

                    match &**pr {
                        ProofView::Assume(e) => {
                            let ide = self.get_term_id(e)?;
                            writeln!(self.out, "{} ASS {}", id, ide)?;
                        }
                        ProofView::Refl(e) => {
                            let ide = self.get_term_id(e)?;
                            writeln!(self.out, "{} RFL {}", id, ide)?;
                        }
                        ProofView::Trans(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "{} TRNS {} {}", id, n1, n2)?;
                        }
                        ProofView::Congr(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "{} CGR {} {})", id, n1, n2)?;
                        }
                        ProofView::CongrTy(th1, ty) => {
                            let idty = self.get_term_id(&ty)?;
                            let n1 = self.get_thm_id(&th1)?;
                            writeln!(self.out, "{} CGRTY {} {})", id, n1, idty)?;
                        }
                        ProofView::Instantiate(th1, subst) => {
                            let n1 = self.get_thm_id(&th1)?;
                            write!(self.out, "{} SBST {}", id, n1)?;
                            for (v, e) in &subst[..] {
                                let eid = self.get_term_id(e)?;
                                write!(self.out, " {} {}", v.name.name(), eid)?;
                            }
                            writeln!(self.out, "")?;
                        }
                        ProofView::Abs(v, th1) => {
                            let ty = self.get_term_id(&v.ty)?;
                            let n1 = self.get_thm_id(&th1)?;
                            writeln!(self.out, "{} ABS {} {} {}", id, v.name.name(), ty, n1)?;
                        }
                        ProofView::Axiom(e) => {
                            let eid = self.get_term_id(e)?;
                            writeln!(self.out, "{} AX {}", id, eid)?;
                        }
                        ProofView::Cut(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "{} CUT {} {}", id, n1, n2)?;
                        }
                        ProofView::BoolEq(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "{} BEQ {} {}", id, n1, n2)?;
                        }
                        ProofView::BoolEqIntro(th1, th2) => {
                            let n1 = self.get_thm_id(&th1)?;
                            let n2 = self.get_thm_id(&th2)?;
                            writeln!(self.out, "{} BEQI {} {}", id, n1, n2)?;
                        }
                        ProofView::BetaConv(e) => {
                            let eid = self.get_term_id(e)?;
                            writeln!(self.out, "{} BETA {}", id, eid)?;
                        }
                        ProofView::NewDef(e) => {
                            let eid = self.get_term_id(e)?;
                            writeln!(self.out, "{} DEF {}", id, eid)?;
                        }
                        ProofView::NewTyDef(e, th) => {
                            let ide = self.get_term_id(e)?;
                            let idth = self.get_thm_id(th)?;
                            writeln!(self.out, "{} TYDEF {} {}", id, ide, idth)?;
                        }
                        ProofView::GetThm(r) => {
                            writeln!(self.out, "{} GET {}", id, r)?;
                        }
                        ProofView::CallRule1(r, th1) => {
                            let id1 = self.get_thm_id(th1)?;
                            writeln!(self.out, "{} CALL {} {}", id, r, id1)?;
                        }
                        ProofView::CallRule2(r, th1, th2) => {
                            let id1 = self.get_thm_id(th1)?;
                            let id2 = self.get_thm_id(th2)?;
                            writeln!(self.out, "{} CALL {} {} {}", id, r, id1, id2)?;
                        }
                        ProofView::CallRuleN(r, a) => {
                            write!(self.out, "{} CALL {}", id, r)?;
                            for th in &a[..] {
                                let id = self.get_thm_id(th)?;
                                write!(self.out, " {}", id)?;
                            }
                            writeln!(self.out, "")?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Print proof of this theorem and its parents, recursively.
    pub fn print_proof(&mut self, th: &Thm) -> Result<Id> {
        self.to_explore.push(Task::ExitThm(th.clone()));
        self.to_explore.push(Task::EnterThm(th.clone()));
        self.print_loop()?;
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
