//! KBO: Knuth Bendix Ordering
//!
//! KBO is a reduction ordering widely used in automated theorem provers.
//! It is parametrized with a weight function and a precedence,
//! but here we provide default non-specified ones.

use {
    crate::{
        fnv,
        kernel_of_trust::{self as k, Expr, ExprView as EV, Var},
    },
    std::cmp::Ordering,
};

pub trait KBOParams {
    /// Precedence between symbols.
    fn prec(&self, a: &k::Symbol, b: &k::Symbol) -> Ordering;

    /// Weight of a symbol.
    fn weight(&self, _f: &k::Symbol) -> u16 {
        1
    }
}

/// Default KBO parameters.
#[derive(Debug, Copy, Clone)]
pub struct DefaultParams;

/// Compare the two expressions according to KBO.
pub fn compare(kbo: &mut dyn KBOParams, a: Expr, b: Expr) -> Option<Ordering> {
    use kbo_cmp::*;
    let mut st = State::new();
    let mut wb = Weight(0);
    tc_kbo(kbo, &mut st, &mut wb, &a, &b)
}

mod kbo_cmp {
    use super::*;

    use fnv::FnvHashMap as HM;

    pub struct State {
        /// Number of variables occurring only positively (in first term)
        pos_counter: u16,
        /// Number of variables occurring only negatively (in second term)
        neg_counter: u16,
        /// State for one variable, where we could occurrences in the LHS and RHS terms.
        var_balance: HM<k::Var, i32>,
    }

    #[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd, Hash, Debug)]
    pub struct Weight(pub isize);

    impl State {
        pub fn new() -> Self {
            Self {
                pos_counter: 0,
                neg_counter: 0,
                var_balance: HM::default(),
            }
        }

        pub fn add_pos_var(&mut self, v: &k::Var) {
            let n = self.var_balance.get(&v).copied().unwrap_or(0);
            if n == 0 {
                self.pos_counter += 1;
            } else if n == -1 {
                self.neg_counter -= 1
            };
            self.var_balance.insert(v.clone(), n + 1);
        }

        pub fn add_neg_var(&mut self, v: &k::Var) {
            let n = self.var_balance.get(&v).copied().unwrap_or(0);
            if n == 0 {
                self.neg_counter += 1;
            } else if n == 1 {
                self.pos_counter -= 1
            };
            self.var_balance.insert(v.clone(), n - 1);
        }
    }

    /// Update term balance, weight balance, and check whether `t`
    /// contains the variable `s`.
    pub fn balance_weight(
        kbo: &mut dyn KBOParams,
        st: &mut State,
        wb: &mut Weight,
        t: &Expr,
        s: Option<&Var>,
        pos: bool,
    ) -> bool {
        match t.view() {
            EV::EBoundVar(..) => {
                if pos {
                    wb.0 += 1;
                } else {
                    wb.0 -= 1;
                }
                false
            }
            EV::EConst(c) => {
                let wc = kbo.weight(&c.name);
                assert!(wc > 0);
                if pos {
                    wb.0 += wc as isize;
                } else {
                    wb.0 -= wc as isize;
                }
                false
            }
            EV::EVar(v) => {
                if pos {
                    st.add_pos_var(v);
                } else {
                    st.add_neg_var(v);
                }
                if pos {
                    wb.0 += 1; // TODO: weight for variables?
                } else {
                    wb.0 -= 1;
                }
                if let Some(s) = s {
                    s == v
                } else {
                    false
                }
            }
            EV::EApp(f, a) => {
                let r1 = balance_weight(kbo, st, wb, f, s, pos);
                let r2 = balance_weight(kbo, st, wb, a, s, pos);
                r1 || r2
            }
            EV::ELambda(_ty, bod) => {
                if pos {
                    wb.0 += 1;
                } else {
                    wb.0 -= 1;
                }
                balance_weight(kbo, st, wb, bod, s, pos)
            }
            EV::EPi(..) | EV::EType | EV::EKind => false, // ignore types
        }
    }

    pub fn balance_weight_rec(
        kbo: &mut dyn KBOParams,
        st: &mut State,
        wb: &mut Weight,
        ts: &[&Expr],
        s: Option<&Var>,
        pos: bool,
    ) -> bool {
        let mut r = false;
        for t in ts {
            let rt = balance_weight(kbo, st, wb, t, s, pos);
            r = r || rt;
        }
        r
    }

    pub fn tc_kbo(
        kbo: &mut dyn KBOParams,
        st: &mut State,
        wb: &mut Weight,
        t1: &Expr,
        t2: &Expr,
    ) -> Option<Ordering> {
        if t1 == t2 {
            return Some(Ordering::Equal);
        }

        match (t1.view(), t2.view()) {
            (EV::EVar(x1), EV::EVar(x2)) => {
                st.add_pos_var(x1);
                st.add_neg_var(x2);
                None
            }
            (EV::EVar(x), _) => {
                st.add_pos_var(x);
                wb.0 += 1;
                let contains = balance_weight(kbo, st, wb, t2, Some(x), false);
                if contains {
                    Some(Ordering::Less)
                } else {
                    None
                }
            }
            (_, EV::EVar(y)) => {
                st.add_neg_var(y);
                wb.0 -= 1;
                let contains = balance_weight(kbo, st, wb, t1, Some(y), true);
                if contains {
                    Some(Ordering::Greater)
                } else {
                    None
                }
            }
            _ => {
                let (f1, ts1) = t1.unfold_app();
                let (f2, ts2) = t2.unfold_app();

                // precedences for heads
                let cmp_p = {
                    match (f1.view(), f2.view()) {
                        (EV::EConst(c1), EV::EConst(c2)) => Some(kbo.prec(&c1.name, &c2.name)),
                        _ => None,
                    }
                };

                balance_weight(kbo, st, wb, f1, None, true);
                balance_weight(kbo, st, wb, f2, None, false);

                let res_lex = if let Some(Ordering::Equal) = cmp_p {
                    tc_kbo_lex(kbo, st, wb, &ts1, &ts2)
                } else {
                    balance_weight_rec(kbo, st, wb, &ts1, None, true);
                    balance_weight_rec(kbo, st, wb, &ts2, None, false);
                    None
                };

                // in any case, check that no negative (resp. positive) var
                // occurs more than in the other side.
                let l_or_none = if st.neg_counter == 0 {
                    Some(Ordering::Less)
                } else {
                    None
                };

                let g_or_none = if st.neg_counter == 0 {
                    Some(Ordering::Greater)
                } else {
                    None
                };

                // now consider: weight, then precedence.
                if wb.0 > 0 {
                    g_or_none
                } else if wb.0 < 0 {
                    l_or_none
                } else if let Some(Ordering::Greater) = cmp_p {
                    g_or_none
                } else if let Some(Ordering::Less) = cmp_p {
                    l_or_none
                } else if let Some(Ordering::Equal) = cmp_p {
                    match res_lex {
                        Some(Ordering::Equal) => Some(Ordering::Equal),
                        Some(Ordering::Less) => l_or_none,
                        Some(Ordering::Greater) => g_or_none,
                        None => None,
                    }
                } else {
                    None
                }
            }
        }
    }

    /// Lexicographic order
    pub fn tc_kbo_lex(
        kbo: &mut dyn KBOParams,
        st: &mut State,
        wb: &mut Weight,
        mut t1: &[&Expr],
        mut t2: &[&Expr],
    ) -> Option<Ordering> {
        loop {
            if t1.len() == 0 && t2.len() == 0 {
                return Some(Ordering::Equal);
            } else if t1.len() == 0 {
                balance_weight_rec(kbo, st, wb, t2, None, false);
                return Some(Ordering::Less);
            } else if t2.len() == 0 {
                balance_weight_rec(kbo, st, wb, t1, None, true);
                return Some(Ordering::Greater);
            } else {
                match tc_kbo(kbo, st, wb, &t1[0], &t2[0]) {
                    Some(Ordering::Equal) => {
                        // continue further
                        t1 = &t1[1..];
                        t2 = &t2[1..];
                    }
                    res => {
                        // balance weights and return
                        balance_weight_rec(kbo, st, wb, t1, None, true);
                        balance_weight_rec(kbo, st, wb, t2, None, false);
                        return res;
                    }
                }
            }
        }
    }
}

mod impls {
    use super::*;

    impl KBOParams for DefaultParams {
        fn prec(&self, a: &k::Symbol, b: &k::Symbol) -> Ordering {
            // use the alphabetical order
            a.name().cmp(b.name())
        }
    }
}
