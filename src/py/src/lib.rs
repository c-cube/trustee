// see https://github.com/dgrunwald/rust-cpython

use cpython::{
    exc, // CompareOp, PyObject,
    py_class,
    py_module_initializer,
    PyErr,
    PyResult,
    Python,
};
use std::{sync::Arc, sync::Mutex};
use trustee::kernel_of_trust as k;

// add bindings to the generated python module
// N.B: names: "rust2py" must be the name of the `.so` or `.pyd` file
py_module_initializer!(trustee, inittrustee_py, PyInit_trustee, |py, m| {
    m.add(py, "__doc__", "Python bindings for trustee.")?;
    m.add_class::<ExprManager>(py)?;
    m.add_class::<Expr>(py)?;
    Ok(())
});

fn mk_err(py: Python, s: String) -> PyErr {
    PyErr::new::<exc::ValueError, _>(py, s)
}

py_class!(class Expr |py| {
    data expr: k::Expr;
    data em: Arc<Mutex<k::ExprManager>>;

    def __repr__(&self) -> PyResult<String> {
        let e = self.expr(py);
        Ok(e.to_string())
    }

    def __str__(&self) -> PyResult<String> {
        let e = self.expr(py);
        Ok(e.to_string())
    }

    // application!
    def __call__(&self, arg : Expr) -> PyResult<Expr> {
        let em = self.em(py);
        let mut g_em = em.lock().unwrap();
        let e = g_em.mk_app(self.expr(py).clone(), arg.expr(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        drop(g_em);
        Expr::create_instance(py, e, em.clone())
    }

    def ty(&self) -> PyResult<Expr> {
        let e = self.expr(py);
        match e.ty_opt() {
            None => Err(PyErr::new::<exc::ValueError,_>(py, "no type")),
            Some(ty) => Expr::create_instance(py, ty.clone(), self.em(py).clone())
        }
    }

    def arrow(&self, u: Expr) -> PyResult<Expr> {
        let a = self.expr(py);
        let b = u.expr(py);
        let em = self.em(py);
        let atob = em.lock().unwrap().mk_arrow(a.clone(), b.clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, atob, em.clone())
    }

    // TODO: var(ty)
    // TODO: mk_eq(other)

    /* FIXME
    def __richcmp__(&self, other : Expr, op : CompareOp) -> PyResult<bool> {
        match op {
            CompareOp::Eq => Ok(self.expr(py) == other.expr(py)),
            _ => Err(PyErr::new::<exc::NotImplementedError,_>(py, "not implemented"))
        }
    }
    */

});

py_class!(class Thm |py| {
    data thm: k::Thm;
    data em: Arc<Mutex<k::ExprManager>>;

    def __repr__(&self) -> PyResult<String> {
        let th = self.thm(py);
        Ok(th.to_string())
    }

    def __str__(&self) -> PyResult<String> {
        let th = self.thm(py);
        Ok(th.to_string())
    }

    def concl(&self) -> PyResult<Expr> {
        let e = self.thm(py).concl();
        Expr::create_instance(py, e.clone(), self.em(py).clone())
    }

    def hyps(&self) -> PyResult<Vec<Expr>> {
        let e = self.thm(py).hyps().iter().map(|e| {
            Expr::create_instance(py, e.clone(), self.em(py).clone())
        }).collect::<PyResult<Vec<_>>>()?;
        Ok(e)
    }
});

py_class!(class NewTypeDef |py| {
    data td: k::NewTypeDef;
    data em: Arc<Mutex<k::ExprManager>>;

    def __repr__(&self) -> PyResult<String> {
        Ok(format!("{:?}", self.td(py)))
    }

    /// The new type constructor
    def tau(&self) -> PyResult<Expr> {
        let td = self.td(py);
        let em = self.em(py);
        Expr::create_instance(py, td.tau.clone(), em.clone())
    }

    /// Function from the general type to `tau`
    def c_abs(&self) -> PyResult<Expr> {
        let td = self.td(py);
        let em = self.em(py);
        Expr::create_instance(py, td.c_abs.clone(), em.clone())
    }

    /// Function from `tau` back to the general type
    def c_repr(&self) -> PyResult<Expr> {
        let td = self.td(py);
        let em = self.em(py);
        Expr::create_instance(py, td.c_repr.clone(), em.clone())
    }

    /// `abs_thm` is `|- abs (repr x) = x`
    def abs_thm(&self) -> PyResult<Thm> {
        let td = self.td(py);
        let em = self.em(py);
        Thm::create_instance(py, td.abs_thm.clone(), em.clone())
    }

    /// `repr_thm` is `|- Phi x <=> repr (abs x) = x`
    def repr_thm(&self) -> PyResult<Thm> {
        let td = self.td(py);
        let em = self.em(py);
        Thm::create_instance(py, td.abs_thm.clone(), em.clone())
    }
});

py_class!(class ExprManager |py| {
    data em: Arc<Mutex<k::ExprManager>>;

    def __new__(_cls) -> PyResult<ExprManager> {
        ExprManager::create_instance(py, Arc::new(Mutex::new(k::ExprManager::new())))
    }

    def type_(&self) -> PyResult<Expr> {
        let em = self.em(py).lock().unwrap();
        let ty = em.mk_ty();
        Expr::create_instance(py, ty, self.em(py).clone())
    }

    def var(&self, name: &str, ty: Expr) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let v = em.mk_var_str(name, ty.expr(py).clone());
        Expr::create_instance(py, v, self.em(py).clone())
    }

    def lam(&self, v: Expr, body: Expr) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let v = v.expr(py).as_var()
            .ok_or_else(|| mk_err(py, "in lam, expected variable".to_string()))?;
        let e = em.mk_lambda(v.clone(),
            body.expr(py).clone()).map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, e, self.em(py).clone())
    }

    def pi(&self, v: Expr, body: Expr) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let v = v.expr(py).as_var()
            .ok_or_else(|| mk_err(py, "in pi, expected variable".to_string()))?;
        let v = em.mk_pi(v.clone(),
            body.expr(py).clone()).map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, v, self.em(py).clone())
    }

    def bool(&self) -> PyResult<Expr> {
        let em = self.em(py).lock().unwrap();
        let e = em.mk_bool();
        Expr::create_instance(py, e, self.em(py).clone())
    }

    def imply(&self) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let e = em.mk_imply();
        Expr::create_instance(py, e, self.em(py).clone())
    }

    def select(&self) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let e = em.mk_select();
        Expr::create_instance(py, e, self.em(py).clone())
    }

    def eq(&self) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let e = em.mk_eq();
        Expr::create_instance(py, e, self.em(py).clone())
    }

    /// `eq_app(a,b)` is `a = b`.
    ///
    /// Fails if `a` and `b` do not have the same type.
    def eq_app(&self, e1: Expr, e2: Expr) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let e = em.mk_eq_app(e1.expr(py).clone(), e2.expr(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, e, self.em(py).clone())
    }

    /// `assume F` is `F |- F`
    def assume(&self, e: Expr) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_assume(e.expr(py).clone());
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `refl t` is `|- t=t`
    def refl(&self, e: Expr) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_refl(e.expr(py).clone());
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `beta_conv ((λx.u) a)` is `|- (λx.u) a = u[x:=a]`.
    /// Fails if the term is not a beta-redex.
    def beta_conv(&self, e: Expr) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_beta_conv(e.expr(py))
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `mp (F1 |- a) (F2 |- a' ==> b)` is `F1, F2 |- b`
    /// where `a` and `a'` are alpha equivalent.
    def mp(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_mp(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `trans (F1 |- a=b) (F2 |- b'=c)` is `F1, F2 |- a=c`.
    ///
    /// Can fail if the conclusions don't match properly.
    def trans(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_trans(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `congr (F1 |- f=g) ty` is `F1 |- f ty=g ty`
    def congr(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_congr(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `cut (F1 |- b) (F2, b |- c)` is `F1, F2 |- c`
    ///
    /// This fails if `b` does not occur _syntactically_ in the hypothesis
    /// of the second theorem.
    ///
    /// NOTE: this is not strictly necessary, as it's not an axiom in HOL light,
    /// but we include it here anyway.
    def cut(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_cut(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `bool_eq (F1 |- a) (F2 |- a=b)` is `F1, F2 |- b`.
    /// This is the boolean equivalent of transitivity.
    def bool_eq(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_bool_eq(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `bool_eq_intro (F1, a |- b) (F2, b |- a)` is `F1, F2 |- b=a`.
    /// This is a way of building a boolean `a=b` from proofs of
    /// `a==>b` and `b==>a` (or `a|-b` and [b|-a`).
    def bool_eq_intro(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_bool_eq_intro(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `congr_ty (F1 |- f=g) ty` is `F1 |- f ty=g ty`
    def congr_ty(&self, th1: Thm, ty: Expr) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_congr_ty(th1.thm(py).clone(), ty.expr(py))
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `abs x (F |- t=u)` is `F |- (λx.t)=(λx.u)`
    ///
    /// Panics if `x` occurs freely in `F`.
    def abs(&self, v: Expr, th1: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let v = v.expr(py).as_var()
            .ok_or_else(|| mk_err(py, "in abs, expected variable".to_string()))?;
        let th = em.thm_abs(v, th1.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// `basic_def(x=t)` where `x` is a variable and `t` a term
    /// with a closed type,
    /// returns a theorem `|- x=t` where `x` is now a constant, along with
    /// the constant `x`.
    def basic_def(&self, e: Expr) -> PyResult<(Thm, Expr)> {
        let mut em = self.em(py).lock().unwrap();
        let (th, e) = em.thm_new_basic_definition(e.expr(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        let th = Thm::create_instance(py, th, self.em(py).clone())?;
        let e = Expr::create_instance(py, e, self.em(py).clone())?;
        Ok((th,e))
    }

    /// Create a new axiom `assumptions |- concl`.
    /// **use with caution**
    def axiom(&self, hyps: Vec<Expr>, concl: Expr) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let hyps = hyps.into_iter().map(|e| e.expr(py).clone()).collect();
        let th = em.thm_axiom(hyps, concl.expr(py).clone());
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// Introduce a new type operator.
    ///
    /// Here, too, we follow HOL light:
    /// `new_basic_type_definition(tau, abs, repr, inhabited)`
    /// where `inhabited` is the theorem `|- Phi x` with `x : ty`,
    /// defines a new type operator named `tau` and two functions,
    /// `abs : ty -> tau` and `repr: tau -> ty`.
    ///
    /// It returns a struct `NewTypeDef` containing `tau, absthm, reprthm`, where:
    /// - `tau` is the new (possibly parametrized) type operator
    /// - `absthm` is `|- abs (repr x) = x`
    /// - `reprthm` is `|- Phi x <=> repr (abs x) = x`
    def basic_ty_def(&self, name_tau: &str, name_abs: &str, name_repr: &str,
        thm: Thm) -> PyResult<NewTypeDef> {
        let mut em = self.em(py).lock().unwrap();
        let td = em.thm_new_basic_type_definition(
            k::Symbol::from_str(name_tau),
            k::Symbol::from_str(name_abs),
            k::Symbol::from_str(name_repr),
            thm.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        NewTypeDef::create_instance(py, td, self.em(py).clone())
    }

    /// `instantiate thm σ` produces `Fσ |- Gσ`  where `thm` is `F |- G`
    ///
    /// Returns an error if the substitution is not closed.
    def instantiate(&self, thm: Thm, subst: Vec<(Expr, Expr)>) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let subst = subst.into_iter().map(|(v,e)| {
            let v = v.expr(py).as_var()
                .ok_or_else(|| mk_err(py, "instantiate: need variables".to_string()))?;
            Ok((v.clone(), e.expr(py).clone()))
        }).collect::<PyResult<Vec<_>>>()?;
        let th = em.thm_instantiate(thm.thm(py).clone(), &subst)
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    /// Parse the list of open theory files.
    def parse_ot(&self, files: Vec<String>)
        -> PyResult<(Vec<Expr>, Vec<Thm>, Vec<Thm>)> {
        let mut em = self.em(py).lock().unwrap();
        let mut ot_vm = trustee::open_theory::VM::new(&mut em);
        for s in files {
            ot_vm.parse_file(&s)
                .map_err(|e| mk_err(py, e.to_string()))?;
        }
        let article = ot_vm.into_article();
        let (v1,v2,v3) = article.get(&mut em);
        let v1 = v1.into_iter().map(|e| {
            Expr::create_instance(py, e, self.em(py).clone())
        }).collect::<PyResult<Vec<_>>>()?;
        let v2 = v2.into_iter().map(|e| {
            Thm::create_instance(py, e, self.em(py).clone())
        }).collect::<PyResult<Vec<_>>>()?;
        let v3 = v3.into_iter().map(|e| {
            Thm::create_instance(py, e, self.em(py).clone())
        }).collect::<PyResult<Vec<_>>>()?;
        Ok((v1,v2,v3))
    }
});
