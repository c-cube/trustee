//! Algorithms that are outside the kernel of trust itself.

use crate::{kernel_of_trust as k, *};

/// Result of the definition of a new polymorphic constant.
#[derive(Debug, Clone)]
pub struct NewPolyDef {
    /// Constant being defined
    pub c: Expr,
    /// Theorem defining `c` (as `c = …`)
    pub thm: Thm,
    /// Type variables, in the order they are abstracted on
    pub ty_vars: Vec<Var>,
    /// `c` applied to `ty_vars`
    pub c_applied: Expr,
    /// `thm_c` applied to `ty_vars`
    pub thm_applied: Thm,
}

/// Make a definition from a polymorphic term, by closing it first.
///
/// `ExprManager::thm_new_basic_definition` requires the term to be closed,
/// so we must gather type variables and close over them.
///
/// Returns a tuple `(thm_def, c, vars)` where `thm_def` is the theorem
/// defining the new constant `c`, and `vars` is the set of type variables
/// closed over.
pub fn thm_new_poly_definition(
    em: &mut dyn CtxI,
    c: &str,
    rhs: Expr,
) -> Result<NewPolyDef> {
    let mut vars_ty_rhs: Vec<Var> = rhs.ty().free_vars().cloned().collect();
    //eprintln!("vars_of_ty({:?}) = {:?}", &rhs, &vars_ty_rhs);
    vars_ty_rhs.sort_unstable();
    vars_ty_rhs.dedup();

    if vars_ty_rhs.iter().any(|v| !v.ty.is_type()) {
        return Err(Error::new_string(format!("thm_new_poly_definition: cannot make a polymorphic \
        definition for {}\nusing rhs = {:?}\nrhs contains non-type free variables",
        c, rhs)));
    }

    let ty_closed = em.mk_pi_l(&vars_ty_rhs, rhs.ty().clone())?;
    let eqn = {
        let rhs_closed = em.mk_lambda_l(&vars_ty_rhs, rhs.clone())?;
        let v = em.mk_var_str(c, ty_closed);
        em.mk_eq_app(v, rhs_closed)?
    };
    let (thm, c) = em.thm_new_basic_definition(eqn)?;

    // type variables as expressions
    let e_vars: Vec<_> =
        vars_ty_rhs.iter().cloned().map(|v| em.mk_var(v)).collect();

    let c_applied = em.mk_app_l(c.clone(), &e_vars)?;

    // apply `thm` to the type variables
    let thm_applied = {
        let mut thm = thm.clone();
        for v in e_vars.iter() {
            thm = em.thm_congr_ty(thm, &v)?;
            // now replace `(λa:type. …) v` with its beta reduced version
            let thm_rhs = thm
                .concl()
                .unfold_eq()
                .ok_or_else(|| Error::new("rhs must be an equality"))?
                .1;
            let thm_beta = em.thm_beta_conv(thm_rhs)?;
            thm = em.thm_trans(thm, thm_beta)?;
        }
        thm
    };

    Ok(NewPolyDef { thm, c, ty_vars: vars_ty_rhs, thm_applied, c_applied })
}

/// Data used to rename variables, if needed, prior to implementation.
pub struct RenamingData {
    v2: fnv::FnvHashSet<Var>,
    var_count: usize,
    buf: String,
    renaming: fnv::FnvHashMap<Var, Var>,
}

impl RenamingData {
    pub fn rename_var(&mut self, v: &Var) -> Var {
        use std::fmt::Write;

        match self.renaming.get(&v) {
            Some(v2) => v2.clone(),
            None => {
                // allocate a new variable that isn't in `v2`
                let ty = v.ty.clone();
                let v2 = loop {
                    self.buf.clear();
                    write!(&mut self.buf, "_x_{}", self.var_count)
                        .expect("cannot print temporary variable name");
                    let new_v = Var::from_str(&self.buf[..], ty.clone());
                    if !self.v2.contains(&new_v) {
                        break new_v;
                    }
                };
                self.var_count += 1;
                self.renaming.insert(v.clone(), v2.clone());
                v2
            }
        }
    }
}

/// Do we need to rename `e1`prior to unification?
///
/// The answer is `Some(data)` if there are shared variables, where `data`
/// can be used to perform the renaming, `None` otherwise.
pub fn need_to_rename_before_unif(
    e1: &Expr,
    e2: &Expr,
) -> Option<RenamingData> {
    let v1: fnv::FnvHashSet<Var> = e1.free_vars().cloned().collect();
    if v1.is_empty() {
        return None;
    }

    let v2: fnv::FnvHashSet<Var> = e2.free_vars().cloned().collect();

    let inter = v1.intersection(&v2);
    if inter.take(1).count() > 0 {
        Some(RenamingData {
            v2,
            var_count: 0,
            buf: String::with_capacity(16),
            renaming: fnv::new_table_with_cap(8),
        })
    } else {
        None
    }
}

// TODO: use binary search?
/// A substitution obtained by unification.
#[derive(Debug, Clone)]
pub struct UnifySubst<'a>(Vec<(&'a Var, &'a Expr)>);

impl<'a> UnifySubst<'a> {
    /// New empty substitution.
    pub fn new() -> Self {
        Self(vec![])
    }

    /// Find a variable `v` in this substitution.
    pub fn find(&self, v: &'a Var) -> Option<&'a Expr> {
        match self.0.binary_search_by_key(&v, |pair| pair.0) {
            Ok(i) => Some(&self.0[i].1),
            Err(_) => None,
        }
    }

    /// Combination of `find` and `deref`.
    pub fn find_rec(&self, v: &'a Var) -> Option<&'a Expr> {
        match self.find(v) {
            None => None,
            Some(e) => Some(self.deref(e)),
        }
    }

    /// if `e` is a bound variable, follow the binding, recursively.
    pub fn deref(&self, e: &'a Expr) -> &'a Expr {
        match e.view() {
            EVar(v) => match self.find(v) {
                None => e,
                Some(u) => self.deref(u),
            },
            _ => e,
        }
    }

    pub fn to_k_subst(&self) -> k::Subst {
        self.0
            .iter()
            .map(|(v, e)| ((*v).clone(), (*e).clone()))
            .collect::<Vec<_>>()
    }

    fn add_(&mut self, v: &'a Var, e: &'a Expr) {
        debug_assert!(self.find(v).is_none());
        self.0.push((v, e));
        // the implementation is pattern-defeating quicksort, which is linear
        // on already sorted slices of input. I therefore expect that this
        // should be linear.
        self.0.sort_unstable();
    }
}

impl<'a> Into<kernel_of_trust::Subst> for UnifySubst<'a> {
    fn into(self) -> kernel_of_trust::Subst {
        self.0
            .into_iter()
            .map(|(v, e)| ((*v).clone(), (*e).clone()))
            .collect::<Vec<_>>()
    }
}

#[derive(Copy, Clone, Eq, PartialEq)]
enum UnifOp {
    Match,
    Unify,
}

pub struct UnifySt<'a> {
    op: UnifOp,
    solved: fnv::FnvHashSet<(&'a Expr, &'a Expr)>,
    subst: UnifySubst<'a>,
    to_solve: Vec<(&'a Expr, &'a Expr)>,
}

impl<'a> UnifySt<'a> {
    fn new(op: UnifOp) -> Self {
        UnifySt {
            op,
            solved: fnv::new_set_with_cap(16),
            subst: UnifySubst(Vec::with_capacity(16)),
            to_solve: Vec::with_capacity(16),
        }
    }

    // make sure `e1 = e2` holds
    fn add_pair(&mut self, e1: &'a Expr, e2: &'a Expr) {
        if e1 != e2 && !self.solved.contains(&(e1, e2)) {
            self.to_solve.push((e1, e2))
        }
    }

    /// Does `v` occur in `e`?
    fn occur_check(&self, v: &'a Var, e: &'a Expr) -> bool {
        let e = self.subst.deref(e);
        match e.ty_opt() {
            Some(ty) if self.occur_check(v, ty) => return true,
            _ => (),
        }
        match e.view() {
            EType | EKind | EConst(..) => false,
            EVar(v2) => v == v2,
            EBoundVar(_) => false,
            EApp(f, arg) => self.occur_check(v, f) || self.occur_check(v, arg),
            ELambda(_, body) | EPi(_, body) => self.occur_check(v, body),
        }
    }

    // solve and consume
    fn solve(mut self) -> Option<UnifySubst<'a>> {
        let sat = loop {
            let (e1, e2) = match self.to_solve.pop() {
                None => break true, // done
                Some(tup) => tup,
            };
            let e1 = self.subst.deref(e1);
            let e2 = self.subst.deref(e2);

            // trivial cases: syntactic eq, or already cached
            if e1 == e2 || self.solved.contains(&(e1, e2)) {
                continue;
            }

            // assume we solved this pair
            self.solved.insert((e1, e2));

            // unify types
            match (e1.ty_opt(), e2.ty_opt()) {
                (Some(ty1), Some(ty2)) if ty1 == ty2 => (),
                (Some(ty1), Some(ty2)) => self.add_pair(ty1, ty2),
                (None, Some(_)) => break false,
                (Some(_), None) => break false,
                (None, None) => (),
            }

            match (e1.view(), e2.view()) {
                (EType, _) => break false,
                (EKind, _) => break false,
                (EConst(..), _) => break false, // closed types: equal or incompatible
                (EBoundVar(v1), EBoundVar(v2)) => {
                    if v1.idx() != v2.idx() {
                        break false;
                    }
                    self.add_pair(v1.ty(), v2.ty())
                }
                (EVar(v), _) => {
                    if !e2.is_closed() || self.occur_check(v, e2) {
                        break false;
                    }
                    self.subst.add_(v, e2);
                }
                (_, EVar(v)) if self.op == UnifOp::Unify => {
                    if !e1.is_closed() || self.occur_check(v, e1) {
                        break false;
                    }
                    self.subst.add_(v, e1)
                }
                (EApp(f1, a1), EApp(f2, a2)) => {
                    self.add_pair(f1, f2);
                    self.add_pair(a1, a2);
                }
                (EPi(tyv1, body1), EPi(tyv2, body2)) => {
                    self.add_pair(tyv1, tyv2);
                    self.add_pair(body1, body2);
                }
                (ELambda(tyv1, body1), ELambda(tyv2, body2)) => {
                    self.add_pair(tyv1, tyv2);
                    self.add_pair(body1, body2);
                }
                (EBoundVar(..), _) => break false,
                (EApp(..), _) => break false,
                (ELambda(..), _) => break false,
                (EPi(..), _) => break false,
            }
        };
        if sat {
            Some(self.subst)
        } else {
            None
        }
    }

    pub fn start(
        mut self,
        e1: &'a Expr,
        e2: &'a Expr,
    ) -> Option<UnifySubst<'a>> {
        self.to_solve.clear();
        self.add_pair(e1, e2);
        self.solve()
    }
}

// TODO: a function for variable renaming

// TODO: when we have a parser, write some tests
/// Unify the two expressions.
pub fn unify<'a>(e1: &'a Expr, e2: &'a Expr) -> Option<UnifySubst<'a>> {
    let mut st = UnifySt::new(UnifOp::Unify);
    st.add_pair(e1, e2);
    st.solve()
}

/// Match the LHS (pattern) against the RHS.
pub fn match_<'a>(e1: &'a Expr, e2: &'a Expr) -> Option<UnifySubst<'a>> {
    let mut st = UnifySt::new(UnifOp::Match);
    st.add_pair(e1, e2);
    st.solve()
}

/// Prove symmetry of equality.
///
/// Goes from `A |- t=u` to `A |- u=t`.
pub fn thm_sym(em: &mut dyn CtxI, th: Thm) -> Result<Thm> {
    // start with `F |- t=u`.
    // now by left-congruence with `refl(=)`, `F |- ((=) t) = ((=) u)`.
    // by right-congruence with `refl(t)`, `F |- (((=) t) t) = (((=) u) t)`.
    // in other words, `F |- (t=t)=(u=t)`.
    // Just do bool_eq_elim with `|- t=t` (refl(t)) and we're done.
    let (t, u) = th
        .concl()
        .unfold_eq()
        .ok_or_else(|| Error::new("sym: expect an equation"))?;
    let refl_t = em.thm_refl(t.clone());
    let th_tequ_eq_ueqt = {
        let eq = em.mk_eq();
        let eq_u = em.mk_app(eq, u.ty().clone())?;
        let th_r = em.thm_refl(eq_u);
        let th_c_r = em.thm_congr(th_r, th)?;
        em.thm_congr(th_c_r, refl_t.clone())?
    };
    em.thm_bool_eq(refl_t, th_tequ_eq_ueqt)
}

/// Prove symmetry of equality as an equation.
///
/// Goes from `t=u` to `|- (t=u) = (u=t)`.
pub fn thm_sym_conv(ctx: &mut dyn CtxI, e: Expr) -> Result<Thm> {
    // start with `t=u |- t=u`.
    // apply thm_sym to get `t=u |- u=t`.
    let (t, u) =
        e.unfold_eq().ok_or_else(|| Error::new("sym: expect an equation"))?;
    let th1 = {
        let hyp = ctx.thm_assume(e.clone());
        thm_sym(ctx, hyp)?
    };

    let th2 = {
        let eq = ctx.mk_eq_app(u.clone(), t.clone())?;
        let hyp = ctx.thm_assume(eq);
        thm_sym(ctx, hyp)?
    };

    ctx.thm_bool_eq_intro(th1, th2)
}

/// Congruence closure.
pub mod cc {
    use super::*;
    use std::collections::{HashMap, HashSet, VecDeque};

    /// congruence closure state.
    pub struct CC<'a> {
        ctx: &'a mut dyn CtxI,
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
    pub struct NodeIdx(usize);

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
        pub fn new(ctx: &'a mut dyn CtxI) -> Self {
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
                    eprintln!(
                        "cc: merge {:?} and {:?} from add thm {:?}",
                        na, nb, &th
                    );
                    // merge the two classes
                    self.tasks.push_front(Task::Merge(
                        na,
                        nb,
                        Expl::EMerge { th: th.clone() },
                    ));
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
                    let idx = NodeIdx(self.nodes.len());
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
                            self.nodes[f_repr.0].parents.push(idx);
                            let sig = if arg.ty().is_type() {
                                Signature::SAppTy(f_idx, arg.clone())
                            } else {
                                let arg_idx = self.add(arg);
                                let arg_repr = self.find(arg_idx);
                                self.nodes[arg_repr.0].parents.push(idx);
                                Signature::SApp(f_idx, arg_idx)
                            };
                            // find congruences, if any
                            self.tasks.push_back(Task::UpdateSig(idx));
                            self.nodes[idx.0].sig = Some(sig);
                        }
                        // TODO: handle lambda? need a rule for `abs` with DB index
                        ELambda(..) => (),
                        EVar(..) | EBoundVar(..) | EConst(..) | EPi(..)
                        | EKind | EType => (),
                    }
                    idx
                }
            }
        }

        /// Find representative for the given node.
        fn find(&self, idx: NodeIdx) -> NodeIdx {
            let mut i = idx;
            loop {
                let n = &self.nodes[i.0];
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
        fn find_common_ancestor(
            &mut self,
            n1: NodeIdx,
            n2: NodeIdx,
        ) -> Result<NodeIdx> {
            self.tmp_tbl.clear();

            // add whole path to `tmp_tbl`
            let mut i = n1;
            loop {
                self.tmp_tbl.insert(i);
                let n = &self.nodes[i.0];
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

                let n = &self.nodes[i.0];
                match n.expl {
                    Some((n2, _)) => i = n2,
                    None => return Err(Error::new("no common ancestor")),
                }
            }
        }

        /// Explain why `n1 == parent`.
        fn explain_along(
            &mut self,
            n_init: NodeIdx,
            parent: NodeIdx,
        ) -> Result<Thm> {
            let mut idx = n_init;
            let mut th = {
                let e1 = self.nodes[idx.0].e.clone();
                self.ctx.thm_refl(e1)
            };

            while idx != parent {
                let n = &self.nodes[idx.0];
                match &n.expl {
                    None => return Err(Error::new("not an ancestor")),
                    Some((idx2, expl_n2)) => {
                        let idx2 = *idx2;
                        let expl_n2 = expl_n2.clone();

                        let n2 = &self.nodes[idx2.0];

                        // theorem for `n == n2`
                        let mut th_n_n2 = match expl_n2 {
                            EMerge { th } => th.clone(),
                            ECong => match (n.sig.clone(), n2.sig.clone()) {
                                (
                                    Some(Signature::SApp(h1, arg1)),
                                    Some(Signature::SApp(h2, arg2)),
                                ) => {
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
                        let n = &self.nodes[idx.0];
                        let n2 = &self.nodes[idx2.0];
                        if let Some((a, b)) = th_n_n2.concl().unfold_eq() {
                            if b == &n.e {
                                debug_assert_eq!(a, &n2.e);
                                // th_n_n2 is proof of `n2 == n`, so we need
                                // symmetry to get `n == n2`
                                th_n_n2 = thm_sym(self.ctx, th_n_n2)?;
                            } else {
                                debug_assert_eq!(a, &n.e);
                                debug_assert_eq!(b, &n2.e);
                            }
                        } else {
                            return Err(Error::new(
                                "theorem is not equational",
                            ));
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
                let n = &mut self.nodes[i.0];
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
                let th2 = thm_sym(self.ctx, th2)?; // prove middle=n2
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
                        let n = &self.nodes[i.0];
                        if let Some(sig) = &n.sig {
                            let (sig2, expl) = match sig {
                                Signature::SApp(a, b) => {
                                    let a2 = self.find(*a);
                                    let b2 = self.find(*b);
                                    (Signature::SApp(a2, b2), Expl::ECong)
                                }
                                Signature::SAppTy(a, b) => (
                                    Signature::SAppTy(self.find(*a), b.clone()),
                                    Expl::ECongTy,
                                ),
                            };
                            if let Some(repr) = self.sigs.get(&sig2) {
                                // collision, merge
                                //eprintln!("congrence found for {:?}", sig2);
                                self.tasks
                                    .push_front(Task::Merge(i, *repr, expl))
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
                        debug_assert!(self.nodes[r1.0].root.is_none());
                        debug_assert!(self.nodes[r2.0].root.is_none());

                        if r1 != r2 {
                            // merge [r1] into [r2]
                            {
                                let mut i = r1;
                                loop {
                                    self.nodes[i.0].root = Some(r2);
                                    i = self.nodes[i.0].next;

                                    if i == r1 {
                                        break;
                                    }
                                }
                            }
                            let r1n = self.nodes[r1.0].next;
                            self.nodes[r1.0].next = self.nodes[r2.0].next;
                            self.nodes[r2.0].next = r1n;

                            // update signatures of parents of [r1]
                            for x in &self.nodes[r1.0].parents {
                                debug_assert!(self.nodes[x.0].sig.is_some());
                                self.tasks.push_back(Task::UpdateSig(*x));
                            }

                            // merge parent sets
                            let p1: Vec<_> =
                                self.nodes[r1.0].parents.drain(..).collect();
                            self.nodes[r2.0].parents.extend(p1);

                            self.reroot_at(i);
                            self.nodes[i.0].expl = Some((j, expl_i_j));
                        }
                    }
                }
            }
        }
    }

    /// prove
    pub fn prove_cc(
        ctx: &mut dyn CtxI,
        hyps: &[Thm],
        goal: &Expr,
    ) -> Result<Option<Thm>> {
        let mut cc = CC::new(ctx);

        let (e1, e2) = match goal.unfold_eq() {
            Some(tup) => tup,
            None => {
                return Err(Error::new("prove_cc requires an equational goal"))
            }
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
}

pub use cc::{prove_cc, CC};

/// ## Rewriting
///
/// Rewriting algorithms.
pub mod rw {
    use super::*;

    /// Result of a rewrite step.
    pub enum RewriteResult {
        /// No rewrite step.
        RwSame,
        /// A theorem `A |- a=b` where `a` is the initial term, and `b` the result.
        RwStep(Thm),
    }

    use RewriteResult::*;

    /// A term rewriter that operates at the root of a term.
    pub trait Rewriter {
        /// `rewriter.step(ctx, e)` is called on a term `e` and can trigger a rewrite step.
        ///
        /// If it returns `Some(A |- e=e2)`, then the term rewrites into `e2`
        /// with the given proof.
        fn step(&mut self, ctx: &mut dyn CtxI, e: &Expr) -> Option<Thm>;
    }

    /// Rewrite `e` using the rewriter `rw`.
    ///
    /// The rewriter is called on every non-type subterm, starting from the leaves.
    pub fn rewrite_bottom_up<RW>(
        ctx: &mut dyn CtxI,
        rw: &mut RW,
        e: Expr,
    ) -> Result<RewriteResult>
    where
        RW: Rewriter,
    {
        let r = match e.view() {
            EType | EKind | EVar(..) | EBoundVar(..) | EPi(..) => RwSame,
            _ if e.ty().is_type() => RwSame,
            EConst(..) => {
                match rw.step(ctx, &e) {
                    None => RwSame,
                    Some(th2) => {
                        let e2 = {
                            let (_, b) = th2.concl().unfold_eq().ok_or_else(|| {
                            Error::new("rewrite function must return an equation")
                        })?;
                            b.clone()
                        };
                        match rewrite_bottom_up(ctx, rw, e2)? {
                            RwSame => RwStep(th2),
                            RwStep(th3) => RwStep(ctx.thm_trans(th2, th3)?),
                        }
                    }
                }
            }
            EApp(hd, a) => {
                let r1 = rewrite_bottom_up(ctx, rw, hd.clone())?;
                let r2 = rewrite_bottom_up(ctx, rw, a.clone())?;
                match (r1, r2) {
                    (RwSame, RwSame) => RwSame,
                    (RwStep(th), RwSame) => {
                        if a.ty().is_type() {
                            RwStep(ctx.thm_congr_ty(th, a)?)
                        } else {
                            let th2 = ctx.thm_refl(a.clone());
                            RwStep(ctx.thm_congr(th, th2)?)
                        }
                    }
                    (RwSame, RwStep(th)) => {
                        let th_hd = ctx.thm_refl(hd.clone());
                        RwStep(ctx.thm_congr(th_hd, th)?)
                    }
                    (RwStep(th1), RwStep(th2)) => {
                        RwStep(ctx.thm_congr(th1, th2)?)
                    }
                }
            }
            // TODO: rewrite under lambdas?
            //
            // But then we need either:
            // - introduce variable `x`, turn `λbody` into `x, body[0\x]`,
            //   rewrite
            //   then use `abs(x,
            ELambda(..) => RwSame,
        };
        Ok(r)
    }

    /// A rewrite rule.
    pub struct RewriteRule {
        lhs: Expr,
        th: Thm,
    }

    impl RewriteRule {
        fn new_(th: &Thm, ordered: bool) -> Result<Self> {
            let (lhs, rhs) = th.concl().unfold_eq().ok_or_else(|| {
                Error::new("rewrite rule conclusion must be an equation")
            })?;
            let vl: Vec<_> = lhs.free_vars().collect();
            let vr: Vec<_> = rhs.free_vars().collect();
            if th.hyps().len() > 0 {
                // TODO: if there are hypothesis, we need a `prove` procedure
                // to dischard the guard upon matching
                return Err(Error::new("rewrite rule must have no hypothesis"));
            }
            match vr.iter().find(|v| !vl.contains(v)) {
                None => (),
                Some(v) => {
                    return Err(Error::new_string(format!(
                    "variable {:?} occurs freely in RHS of rule but not LHS",
                    v
                )))
                }
            };
            // TODO: not used for now?
            if !ordered {
                match vl.iter().find(|v| !vr.contains(v)) {
                    None => (),
                    Some(v) => {
                        return Err(Error::new_string(format!(
                            "variable {:?} occurs freely in LHS of unordered rule but not RHS",
                            v
                        )))
                    }
                };
            }
            Ok(Self { lhs: lhs.clone(), th: th.clone() })
        }

        /// Create a rewrite rule from a theorem `|- lhs=rhs`.
        ///
        /// Will fail if the theorem is not an equation, or if some
        /// free variables of `rhs` are not in `lhs`, or if the theorem has
        /// assumptions.
        pub fn new(th: &Thm) -> Result<Self> {
            Self::new_(th, false)
        }

        /// Create an unordered rewrite rule from a theorem `|- t1=t2`.
        ///
        /// This can rewrite both `t1σ` into `t2σ`, or `t2σ` into `t1σ`
        /// for a substitution `σ`, depending on which is the bigger term.
        ///
        /// Will fail if the theorem is not an equation, or if `t1` and `t2`
        /// do not have the same set of free `t1` and `t2`
        /// do not have the same set of free variables.
        /// free variables of `rhs` are not in `lhs`.
        pub fn new_unordered(th: &Thm) -> Result<Self> {
            Self::new_(th, true)
        }
    }

    /// A set of rewrite rules.
    ///
    /// Implementation details are hidden, but this implements `Rewriter`.
    pub struct RewriteRuleSet {
        // TODO: use a better kind of indexing
        rules: Vec<RewriteRule>,
    }

    impl Rewriter for RewriteRuleSet {
        fn step(&mut self, ctx: &mut dyn CtxI, e: &Expr) -> Option<Thm> {
            for r in &self.rules {
                match match_(&r.lhs, e) {
                    None => (),
                    Some(subst) => {
                        // match happened.
                        let th = ctx
                            .thm_instantiate(r.th.clone(), &subst.to_k_subst())
                            .expect("invalid instantiation");
                        return Some(th);
                    }
                }
            }
            None
        }
    }

    impl RewriteRuleSet {
        /// New rule set.
        pub fn new() -> Self {
            Self { rules: vec![] }
        }

        /// Add a single rule.
        pub fn add_rule(&mut self, r: RewriteRule) {
            self.rules.push(r)
        }

        /// Add a set of rules.
        pub fn add_rules<I>(&mut self, i: I)
        where
            I: Iterator<Item = RewriteRule>,
        {
            for r in i {
                self.rules.push(r)
            }
        }
    }

    impl std::iter::FromIterator<RewriteRule> for RewriteRuleSet {
        fn from_iter<T>(iter: T) -> Self
        where
            T: IntoIterator<Item = RewriteRule>,
        {
            let mut s = Self::new();
            s.add_rules(iter.into_iter());
            s
        }
    }
}

pub use rw::{RewriteRule, RewriteRuleSet, Rewriter};

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_sym() {
        let mut ctx = Ctx::new();
        let bool = ctx.mk_bool();
        let x = ctx.mk_var_str("x", bool.clone());
        let y = ctx.mk_var_str("y", bool.clone());
        let x_eq_y = ctx.mk_eq_app(x.clone(), y.clone()).unwrap();
        let y_eq_x = ctx.mk_eq_app(y.clone(), x.clone()).unwrap();
        let th = ctx.thm_assume(x_eq_y).unwrap();
        let th2 = thm_sym(&mut ctx, th).unwrap();
        assert_eq!(th2.concl(), &y_eq_x);
    }

    #[test]
    fn test_sym_conv() {
        let mut ctx = Ctx::new();
        let bool = ctx.mk_bool();
        let x = ctx.mk_var_str("x", bool.clone());
        let y = ctx.mk_var_str("y", bool.clone());
        let x_eq_y = ctx.mk_eq_app(x.clone(), y.clone()).unwrap();
        let y_eq_x = ctx.mk_eq_app(y.clone(), x.clone()).unwrap();
        let eq_b = ctx.mk_eq_app(x_eq_y.clone(), y_eq_x.clone()).unwrap();
        let th = thm_sym_conv(&mut ctx, x_eq_y.clone()).unwrap();
        assert_eq!(th.concl(), &eq_b);
    }
}
