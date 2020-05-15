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
py_module_initializer!(
    trustee_py,
    inittrustee_py,
    PyInit_trustee_py,
    |py, m| {
        m.add(py, "__doc__", "Python bindings for trustee.")?;
        m.add_class::<ExprManager>(py)?;
        m.add_class::<Expr>(py)?;
        Ok(())
    }
);

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
            .map_err(|e| mk_err(py, e))?;
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
            .map_err(|e| mk_err(py, e))?;
        Expr::create_instance(py, atob, em.clone())
    }

    // TODO: pi(other)
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

// TODO: class that wraps theorem + ExprManager

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
            body.expr(py).clone()).map_err(|e| mk_err(py, e))?;
        Expr::create_instance(py, v, self.em(py).clone())
    }

    // TODO: bool
    // TODO: eq
    // TODO: imply
    // TODO: select
    // TODO: all the theorem entry points
});
