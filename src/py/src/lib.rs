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

    def lambda(&self, name: &str, ty: Expr, body: Expr) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let v = em.mk_lambda(k::Var::from_str(name, ty.expr(py).clone()),
            body.expr(py).clone()).map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, v, self.em(py).clone())
    }

    def pi(&self, name: &str, ty: Expr, body: Expr) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let v = em.mk_pi(k::Var::from_str(name, ty.expr(py).clone()),
            body.expr(py).clone()).map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, v, self.em(py).clone())
    }

    def bool(&self) -> PyResult<Expr> {
        let em = self.em(py).lock().unwrap();
        let e = em.mk_ty();
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

    def eq_app(&self, e1: Expr, e2: Expr) -> PyResult<Expr> {
        let mut em = self.em(py).lock().unwrap();
        let e = em.mk_eq_app(e1.expr(py).clone(), e2.expr(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, e, self.em(py).clone())
    }

    def assume(&self, e: Expr) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_assume(e.expr(py).clone());
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def refl(&self, e: Expr) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_refl(e.expr(py).clone());
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def beta_conv(&self, e: Expr) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_beta_conv(e.expr(py))
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def mp(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_mp(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def trans(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_trans(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def congr(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_congr(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def cut(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_cut(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def bool_eq(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_bool_eq(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def bool_eq_intro(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_bool_eq_intro(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def congr_ty(&self, th1: Thm, ty: Expr) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let th = em.thm_congr_ty(th1.thm(py).clone(), ty.expr(py))
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    def abs(&self, v: Expr, th1: Thm) -> PyResult<Thm> {
        let mut em = self.em(py).lock().unwrap();
        let v = v.expr(py).as_var()
            .ok_or_else(|| mk_err(py, "in abs, expected variable".to_string()))?;
        let th = em.thm_abs(v, th1.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.em(py).clone())
    }

    // TODO new basic def
    // TODO new type op
    // TODO instantiate
});
