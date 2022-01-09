//! Congruence closure.

use super::*;
use std::collections::{HashMap, HashSet, VecDeque};

/// congruence closure state.
pub struct CC<'a> {
    ctx: &'a mut Ctx,
    tbl: HashMap<Expr, NodeIdx>,
    nodes: Vec<Node>,
    sigs: HashMap<Signature, NodeIdx>,
    tasks: VecDeque<Task>,
    tmp_tbl: HashSet<NodeIdx>, // temporary
}

#[derive(Eq, PartialEq, Debug, Hash, Clone)]
enum Signature {
    SApp(NodeIdx, NodeIdx),
    SAppTy(NodeIdx, Expr),
}

#[derive(Debug)]
enum Task {
    Merge(NodeIdx, NodeIdx, Expl),
    UpdateSig(NodeIdx),
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct NodeIdx(u32);

impl NodeIdx {
    /// Access the unique index within.
    #[inline]
    pub fn idx(&self) -> usize {
        self.0 as usize
    }
}

struct Node {
    e: Expr,
    /// Pointer to representative (via union find).
    root: Option<NodeIdx>,
    /// Proof forest.
    expl: Option<(NodeIdx, Expl)>,
    /// Next element of the class.
    next: NodeIdx,
    /// All nodes that are parents of `e`.
    parents: Vec<NodeIdx>,
    /// Original signature for `e`, if any.
    sig: Option<Signature>,
}

/// Explanation for the merge of two classes.
#[derive(Clone, Debug)]
enum Expl {
    /// merge two applications because of subterms
    ECong,
    /// merge two type applications because of heads
    ECongTy,
    /// merge two terms because of `thm`
    EMerge { th: Thm },
}
use Expl::*;

impl<'a> CC<'a> {
    /// New congruence closure.
    pub fn new(ctx: &'a mut Ctx) -> Self {
        Self {
            ctx,
            tbl: HashMap::new(),
            nodes: vec![],
            tasks: VecDeque::new(),
            sigs: HashMap::new(),
            tmp_tbl: HashSet::new(),
        }
    }

    /// Add an theorem theorem to the congruence closure.
    ///
    /// Fails if the conclusion is not an equation.
    pub fn add_thm(&mut self, th: Thm) -> Result<()> {
        if let Some((a, b)) = th.concl().unfold_eq() {
            let na = self.add(a);
            let nb = self.add(b);
            if self.find(na) != self.find(nb) {
                // merge the two classes
                self.tasks
                    .push_front(Task::Merge(na, nb, Expl::EMerge { th: th.clone() }));
            }
            Ok(())
        } else {
            return Err(Error::new(
                "cc: cannot add theorem with non equational conclusion",
            ));
        }
    }

    /// Add the expression to the congruence closure.
    pub fn add(&mut self, e: &Expr) -> NodeIdx {
        match self.tbl.get(e) {
            Some(n) => *n,
            None => {
                let n = self.nodes.len();
                if n > u32::MAX as usize {
                    panic!("reached max size for the congruence closure");
                }
                let idx = NodeIdx(n as u32);
                self.tbl.insert(e.clone(), idx);
                self.nodes.push(Node {
                    e: e.clone(),
                    next: idx,
                    root: None,
                    expl: None,
                    parents: vec![],
                    sig: None,
                });
                match e.view() {
                    EApp(f, arg) => {
                        let f_idx = self.add(f);
                        let f_repr = self.find(f_idx);
                        self.nodes[f_repr.idx()].parents.push(idx);
                        let sig = if arg.ty().is_type() {
                            Signature::SAppTy(f_idx, arg.clone())
                        } else {
                            let arg_idx = self.add(arg);
                            let arg_repr = self.find(arg_idx);
                            self.nodes[arg_repr.idx()].parents.push(idx);
                            Signature::SApp(f_idx, arg_idx)
                        };
                        // find congruences, if any
                        self.tasks.push_back(Task::UpdateSig(idx));
                        self.nodes[idx.idx()].sig = Some(sig);
                    }
                    // TODO: handle lambda? need a rule for `abs` with DB index
                    ELambda(..) => (),
                    EVar(..) | EBoundVar(..) | EConst(..) | EArrow(..) | EKind | EType => (),
                }
                idx
            }
        }
    }

    /// Find representative for the given node.
    fn find(&self, idx: NodeIdx) -> NodeIdx {
        let mut i = idx;
        loop {
            let n = &self.nodes[i.idx()];
            match &n.root {
                None => return i,
                Some(n2) => {
                    i = *n2;
                }
            }
        }
    }

    /// Are these nodes equal?
    pub fn are_eq(&self, n1: NodeIdx, n2: NodeIdx) -> bool {
        self.find(n1) == self.find(n2)
    }

    /// Find common ancestor of `n1` and `n2`.
    /// Precondition: `find(n1) == find(n2)`.
    fn find_common_ancestor(&mut self, n1: NodeIdx, n2: NodeIdx) -> Result<NodeIdx> {
        self.tmp_tbl.clear();

        // add whole path to `tmp_tbl`
        let mut i = n1;
        loop {
            self.tmp_tbl.insert(i);
            let n = &self.nodes[i.idx()];
            match n.expl {
                Some((n2, _)) => i = n2,
                None => break,
            }
        }

        i = n2;
        loop {
            // in both paths
            if self.tmp_tbl.contains(&i) {
                return Ok(i);
            }

            let n = &self.nodes[i.idx()];
            match n.expl {
                Some((n2, _)) => i = n2,
                None => return Err(Error::new("no common ancestor")),
            }
        }
    }

    /// Explain why `n1 == parent`.
    fn explain_along(&mut self, n_init: NodeIdx, parent: NodeIdx) -> Result<Thm> {
        let mut idx = n_init;
        let mut th = {
            let e1 = self.nodes[idx.idx()].e.clone();
            self.ctx.thm_refl(e1)
        };

        while idx != parent {
            let n = &self.nodes[idx.idx()];
            match &n.expl {
                None => return Err(Error::new("not an ancestor")),
                Some((idx2, expl_n2)) => {
                    let idx2 = *idx2;
                    let expl_n2 = expl_n2.clone();

                    let n2 = &self.nodes[idx2.idx()];

                    // theorem for `n == n2`
                    let mut th_n_n2 = match expl_n2 {
                        EMerge { th } => th.clone(),
                        ECong => match (n.sig.clone(), n2.sig.clone()) {
                            (Some(Signature::SApp(h1, arg1)), Some(Signature::SApp(h2, arg2))) => {
                                let th_hd = self.prove_eq(h1, h2)?;
                                let th_arg = self.prove_eq(arg1, arg2)?;
                                self.ctx.thm_congr(th_hd, th_arg)?
                            }
                            _ => panic!("cong on non applications"),
                        },
                        ECongTy => match (n.sig.clone(), n2.sig.clone()) {
                            (
                                Some(Signature::SAppTy(h1, arg1)),
                                Some(Signature::SAppTy(h2, arg2)),
                            ) => {
                                assert_eq!(&arg1, &arg2);
                                let th_hd = self.prove_eq(h1, h2)?;
                                self.ctx.thm_congr_ty(th_hd, &arg1)?
                            }
                            _ => panic!("congTy on non applications"),
                        },
                    };

                    // re-borrow
                    let n = &self.nodes[idx.idx()];
                    let n2 = &self.nodes[idx2.idx()];
                    if let Some((a, b)) = th_n_n2.concl().unfold_eq() {
                        if b == &n.e {
                            debug_assert_eq!(a, &n2.e);
                            // th_n_n2 is proof of `n2 == n`, so we need
                            // symmetry to get `n == n2`
                            th_n_n2 = self.ctx.thm_sym(th_n_n2)?;
                        } else {
                            debug_assert_eq!(a, &n.e);
                            debug_assert_eq!(b, &n2.e);
                        }
                    } else {
                        return Err(Error::new("theorem is not equational"));
                    }

                    // th is proof for `n_init == n`, so the composition
                    // gives `n_init == n2`
                    th = self.ctx.thm_trans(th, th_n_n2)?;
                    idx = idx2;
                }
            }
        }
        Ok(th)
    }

    /// Re-root proof forest at `i`.
    fn reroot_at(&mut self, mut i: NodeIdx) {
        let mut prev = None;
        loop {
            let n = &mut self.nodes[i.idx()];
            match &n.expl {
                None => {
                    n.expl = prev;
                    return;
                }
                Some((j, expl_i_j)) => {
                    let j = *j;
                    let expl_i_j = expl_i_j.clone();
                    n.expl = prev;
                    prev = Some((i, expl_i_j));
                    i = j; // continue
                }
            }
        }
    }

    /// Provide a theorem for `n1 == n2`.
    ///
    /// Fails if `n1` and `n2` are not equal, or if some error occurs
    /// during the proof (indicating a bug).
    pub fn prove_eq(&mut self, n1: NodeIdx, n2: NodeIdx) -> Result<Thm> {
        let r1 = self.find(n1);
        let r2 = self.find(n2);

        if r1 == r2 {
            let middle = self.find_common_ancestor(n1, n2)?;
            let th1 = self.explain_along(n1, middle)?;
            let th2 = self.explain_along(n2, middle)?;
            let th2 = self.ctx.thm_sym(th2)?; // prove middle=n2
            let th = self.ctx.thm_trans(th1, th2)?;
            Ok(th)
        } else {
            Err(Error::new("nodes are not equal"))
        }
    }

    /// Fixpoint of the congruence closure algorithm.
    pub fn update(&mut self) {
        while let Some(t) = self.tasks.pop_front() {
            match t {
                Task::UpdateSig(i) => {
                    let n = &self.nodes[i.idx()];
                    if let Some(sig) = &n.sig {
                        let (sig2, expl) = match sig {
                            Signature::SApp(a, b) => {
                                let a2 = self.find(*a);
                                let b2 = self.find(*b);
                                (Signature::SApp(a2, b2), Expl::ECong)
                            }
                            Signature::SAppTy(a, b) => {
                                (Signature::SAppTy(self.find(*a), b.clone()), Expl::ECongTy)
                            }
                        };
                        if let Some(repr) = self.sigs.get(&sig2) {
                            // collision, merge
                            //eprintln!("congrence found for {:?}", sig2);
                            self.tasks.push_front(Task::Merge(i, *repr, expl))
                        } else {
                            // insert into table so we can detect collisions
                            self.sigs.insert(sig2, i);
                        }
                    }
                }
                Task::Merge(i, j, expl_i_j) => {
                    let r1 = self.find(i);
                    let r2 = self.find(j);

                    // these should be roots
                    debug_assert!(self.nodes[r1.idx()].root.is_none());
                    debug_assert!(self.nodes[r2.idx()].root.is_none());

                    if r1 != r2 {
                        // merge [r1] into [r2]
                        {
                            let mut i = r1;
                            loop {
                                self.nodes[i.idx()].root = Some(r2);
                                i = self.nodes[i.idx()].next;

                                if i == r1 {
                                    break;
                                }
                            }
                        }
                        let r1n = self.nodes[r1.idx()].next;
                        self.nodes[r1.idx()].next = self.nodes[r2.idx()].next;
                        self.nodes[r2.idx()].next = r1n;

                        // update signatures of parents of [r1]
                        for x in &self.nodes[r1.idx()].parents {
                            debug_assert!(self.nodes[x.idx()].sig.is_some());
                            self.tasks.push_back(Task::UpdateSig(*x));
                        }

                        // merge parent sets
                        let p1: Vec<_> = self.nodes[r1.idx()].parents.drain(..).collect();
                        self.nodes[r2.idx()].parents.extend(p1);

                        self.reroot_at(i);
                        self.nodes[i.idx()].expl = Some((j, expl_i_j));
                    }
                }
            }
        }
    }
}

/// prove
pub fn prove_cc(ctx: &mut Ctx, hyps: &[Thm], goal: &Expr) -> Result<Option<Thm>> {
    let mut cc = CC::new(ctx);

    let (e1, e2) = match goal.unfold_eq() {
        Some(tup) => tup,
        None => return Err(Error::new("prove_cc requires an equational goal")),
    };

    for th in hyps {
        cc.add_thm(th.clone())?;
    }
    let n1 = cc.add(e1);
    let n2 = cc.add(e2);

    cc.update();

    if cc.are_eq(n1, n2) {
        Ok(Some(cc.prove_eq(n1, n2)?))
    } else {
        Ok(None)
    }
}
