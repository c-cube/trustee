// see https://github.com/dgrunwald/rust-cpython

#[macro_use]
extern crate cpython;

use cpython::{
    exc, // CompareOp, PyObject,
    py_class,
    py_module_initializer,
    CompareOp,
    PyErr,
    PyObject,
    PyResult,
    Python,
    PythonObject,
    ToPyObject,
};
use std::{sync::Arc, sync::Mutex};
use trustee::{database as db, kernel_of_trust as k, utils};

// add bindings to the generated python module
// N.B: names: "rust2py" must be the name of the `.so` or `.pyd` file
py_module_initializer!(trustee, inittrustee_py, PyInit_trustee, |py, m| {
    m.add(py, "__doc__", "Python bindings for trustee.")?;
    m.add_class::<Ctx>(py)?;
    m.add_class::<Expr>(py)?;
    m.add_class::<Thm>(py)?;
    m.add_class::<NewTypeDef>(py)?;
    Ok(())
});

fn mk_err(py: Python, s: String) -> PyErr {
    PyErr::new::<exc::ValueError, _>(py, s)
}

py_class!(pub class Expr |py| {
    data expr: k::Expr;
    data ctx: Arc<Mutex<k::Ctx>>;

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
        let em = self.ctx(py);
        let mut g_em = em.lock().unwrap();
        let e = {
            g_em.mk_app(self.expr(py).clone(), arg.expr(py).clone())
                .map_err(|e| mk_err(py, e.to_string()))?
        };
        drop(g_em);
        Expr::create_instance(py, e, em.clone())
    }

    /* FIXME
    // application!
    def __call__(&self, * arg : &[Expr] ) -> PyResult<Expr> {
        let em = self.ctx(py);
        let mut g_em = em.lock().unwrap();
        let e = {
            let args =
                arg.iter().map(|e| e.expr(py).clone()).collect::<Vec<_>>();
            g_em.mk_app_l(self.expr(py).clone(), &args)
                .map_err(|e| mk_err(py, e.to_string()))?
        };
        drop(g_em);
        Expr::create_instance(py, e, em.clone())
    }
    */

    def ty(&self) -> PyResult<Expr> {
        let e = self.expr(py);
        match e.ty_opt() {
            None => Err(PyErr::new::<exc::ValueError,_>(py, "no type")),
            Some(ty) => Expr::create_instance(py, ty.clone(), self.ctx(py).clone())
        }
    }

    def arrow(&self, u: Expr) -> PyResult<Expr> {
        let a = self.expr(py);
        let b = u.expr(py);
        let em = self.ctx(py);
        let atob = em.lock().unwrap().mk_arrow(a.clone(), b.clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, atob, em.clone())
    }

    // TODO: var(ty)
    // TODO: mk_eq(other)

    def __richcmp__(&self, other : Expr, op : CompareOp) -> PyResult<bool> {
        let e1 = self.expr(py);
        let e2 = other.expr(py);
        match op {
            CompareOp::Eq => Ok(e1 == e2),
            CompareOp::Ne => Ok(e1 != e2),
            _ => Err(PyErr::new::<exc::NotImplementedError,_>(py, "not implemented".to_string()))
        }
    }

});

py_class!(pub class Thm |py| {
    data thm: k::Thm;
    data ctx: Arc<Mutex<k::Ctx>>;

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
        Expr::create_instance(py, e.clone(), self.ctx(py).clone())
    }

    def hyps(&self) -> PyResult<Vec<Expr>> {
        let e = self.thm(py).hyps().iter().map(|e| {
            Expr::create_instance(py, e.clone(), self.ctx(py).clone())
        }).collect::<PyResult<Vec<_>>>()?;
        Ok(e)
    }
});

py_class!(pub class Constant |py| {
    data c: db::Constant;
    data ctx: Arc<Mutex<k::Ctx>>;

    def __repr__(&self) -> PyResult<String> {
        Ok(format!("{:?}", self.c(py)))
    }

    def expr(&self) -> PyResult<Expr> {
        let c = self.c(py);
        let em = self.ctx(py);
        Expr::create_instance(py, c.expr.clone(), em.clone())
    }

    def thm(&self) -> PyResult<Option<Thm>> {
        let c = self.c(py);
        match &c.thm {
            None => Ok(None),
            Some(th) => {
                let em = self.ctx(py);
                Thm::create_instance(py, th.clone(), em.clone())
                    .map(|x| Some(x))
            }
        }
    }
});

py_class!(pub class NewTypeDef |py| {
    data td: k::NewTypeDef;
    data ctx: Arc<Mutex<k::Ctx>>;

    def __repr__(&self) -> PyResult<String> {
        Ok(format!("{:?}", self.td(py)))
    }

    /// The new type constructor
    def tau(&self) -> PyResult<Expr> {
        let td = self.td(py);
        let em = self.ctx(py);
        Expr::create_instance(py, td.tau.clone(), em.clone())
    }

    /// Function from the general type to `tau`
    def c_abs(&self) -> PyResult<Expr> {
        let td = self.td(py);
        let em = self.ctx(py);
        Expr::create_instance(py, td.c_abs.clone(), em.clone())
    }

    /// Function from `tau` back to the general type
    def c_repr(&self) -> PyResult<Expr> {
        let td = self.td(py);
        let em = self.ctx(py);
        Expr::create_instance(py, td.c_repr.clone(), em.clone())
    }

    /// `abs_thm` is `|- abs (repr x) = x`
    def abs_thm(&self) -> PyResult<Thm> {
        let td = self.td(py);
        let em = self.ctx(py);
        Thm::create_instance(py, td.abs_thm.clone(), em.clone())
    }

    /// `repr_thm` is `|- Phi x <=> repr (abs x) = x`
    def repr_thm(&self) -> PyResult<Thm> {
        let td = self.td(py);
        let em = self.ctx(py);
        Thm::create_instance(py, td.repr_thm.clone(), em.clone())
    }
});

py_class!(pub class NewPolyDef |py| {
    data def: utils::NewPolyDef;
    data ctx: Arc<Mutex<k::Ctx>>;

    def __repr__(&self) -> PyResult<String> {
        Ok(format!("{:?}", self.def(py)))
    }

    /// The new constant.
    def c(&self) -> PyResult<Expr> {
        let d = self.def(py);
        let em = self.ctx(py);
        Expr::create_instance(py, d.c_applied.clone(), em.clone())
    }

    /// The theorem defining the new constant.
    def thm(&self) -> PyResult<Thm> {
        let d = self.def(py);
        let em = self.ctx(py);
        Thm::create_instance(py, d.thm_applied.clone(), em.clone())
    }
});

fn any_val_to_py_obj<'a>(
    py: Python,
    v: db::AnyValue<'a>,
    ctx: &Arc<Mutex<k::Ctx>>,
) -> PyResult<PyObject> {
    use db::AnyValue as A;
    match v {
        A::Def(c) => {
            let c = Constant::create_instance(py, c.clone(), ctx.clone())?;
            Ok(c.into_object())
        }
        A::Thm(th) => {
            let th = Thm::create_instance(py, th.clone(), ctx.clone())?;
            Ok(th.into_object())
        }
        A::Axiom(th) => {
            let th = Thm::create_instance(py, th.clone(), ctx.clone())?;
            Ok(th.into_object())
        }
        A::TyDef(d) => {
            let d = NewTypeDef::create_instance(py, d.clone(), ctx.clone())?;
            Ok(d.into_object())
        }
    }
}

py_class!(pub class Ctx |py| {
    data ctx: Arc<Mutex<k::Ctx>>;
    data db: Arc<Mutex<trustee::Database>>;

    def __new__(_cls) -> PyResult<Ctx> {
        let ctx = Arc::new(Mutex::new(k::Ctx::new()));
        let db = Arc::new(Mutex::new(trustee::Database::new()));
        Ctx::create_instance(py, ctx, db)
    }

    /// Lookup in the DB
    def __getitem__(&self, s: &str) -> PyResult<cpython::PyObject> {
        self.find(py, s)
    }

    /// Number of elements
    def __len__(&self) -> PyResult<usize> {
        Ok(self.db(py).lock().unwrap().size())
    }

    /// Lookup in the DB.
    def find(&self, s: &str) -> PyResult<cpython::PyObject> {
        let db = self.db(py).lock().unwrap();
        match db.get_by_name(s) {
            Some(a) => {
                Ok(any_val_to_py_obj(py, a, &self.ctx(py))?)
            }
            None => {
                Err(mk_err(py, "no object with that name in the DB".to_string()))
            }
        }
    }

    /// Return a list of all items in the DB.
    def db_items(&self) -> PyResult<Vec<PyObject>> {
        let db = self.db(py).lock().unwrap();
        let v = db.all_items().map(|v| {
            any_val_to_py_obj(py, v, self.ctx(py))
        }).collect::<PyResult<Vec<_>>>()?;
        Ok(v)
    }

    def __contains__(&self, s: &str) -> PyResult<bool> {
        let db = self.db(py).lock().unwrap();
        Ok(db.get_by_name(s).is_some())
    }

    def type_(&self) -> PyResult<Expr> {
        let em = self.ctx(py).lock().unwrap();
        let ty = em.mk_ty();
        Expr::create_instance(py, ty, self.ctx(py).clone())
    }

    def var(&self, name: &str, ty: Expr) -> PyResult<Expr> {
        let mut em = self.ctx(py).lock().unwrap();
        let v = em.mk_var_str(name, ty.expr(py).clone());
        Expr::create_instance(py, v, self.ctx(py).clone())
    }

    def lam(&self, v: Expr, body: Expr) -> PyResult<Expr> {
        let mut em = self.ctx(py).lock().unwrap();
        let v = v.expr(py).as_var()
            .ok_or_else(|| mk_err(py, "in lam, expected variable".to_string()))?;
        let e = em.mk_lambda(v.clone(),
            body.expr(py).clone()).map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, e, self.ctx(py).clone())
    }

    def pi(&self, v: Expr, body: Expr) -> PyResult<Expr> {
        let mut em = self.ctx(py).lock().unwrap();
        let v = v.expr(py).as_var()
            .ok_or_else(|| mk_err(py, "in pi, expected variable".to_string()))?;
        let v = em.mk_pi(v.clone(),
            body.expr(py).clone()).map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, v, self.ctx(py).clone())
    }

    def bool(&self) -> PyResult<Expr> {
        let em = self.ctx(py).lock().unwrap();
        let e = em.mk_bool();
        Expr::create_instance(py, e, self.ctx(py).clone())
    }

    def imply(&self) -> PyResult<Expr> {
        let mut em = self.ctx(py).lock().unwrap();
        let e = em.mk_imply();
        Expr::create_instance(py, e, self.ctx(py).clone())
    }

    def select(&self) -> PyResult<Expr> {
        let mut em = self.ctx(py).lock().unwrap();
        let e = em.mk_select();
        Expr::create_instance(py, e, self.ctx(py).clone())
    }

    def eq(&self) -> PyResult<Expr> {
        let mut em = self.ctx(py).lock().unwrap();
        let e = em.mk_eq();
        Expr::create_instance(py, e, self.ctx(py).clone())
    }

    /// `eq_app(a,b)` is `a = b`.
    ///
    /// Fails if `a` and `b` do not have the same type.
    def eq_app(&self, e1: Expr, e2: Expr) -> PyResult<Expr> {
        let mut em = self.ctx(py).lock().unwrap();
        let e = em.mk_eq_app(e1.expr(py).clone(), e2.expr(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, e, self.ctx(py).clone())
    }

    /// `assume F` is `F |- F`
    def assume(&self, e: Expr) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_assume(e.expr(py).clone());
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `refl t` is `|- t=t`
    def refl(&self, e: Expr) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_refl(e.expr(py).clone());
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `beta_conv ((λx.u) a)` is `|- (λx.u) a = u[x:=a]`.
    /// Fails if the term is not a beta-redex.
    def beta_conv(&self, e: Expr) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_beta_conv(e.expr(py))
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `mp (F1 |- a) (F2 |- a' ==> b)` is `F1, F2 |- b`
    /// where `a` and `a'` are alpha equivalent.
    def mp(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_mp(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `trans (F1 |- a=b) (F2 |- b'=c)` is `F1, F2 |- a=c`.
    ///
    /// Can fail if the conclusions don't match properly.
    def trans(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_trans(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// Symmetry: `sym (F |- a=b)` is `F |- b=a`
    def sym(&self, th: Thm) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = utils::thm_sym(&mut *em, th.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `congr (F1 |- f=g) ty` is `F1 |- f ty=g ty`
    def congr(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_congr(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `cut (F1 |- b) (F2, b |- c)` is `F1, F2 |- c`
    ///
    /// This fails if `b` does not occur _syntactically_ in the hypothesis
    /// of the second theorem.
    ///
    /// NOTE: this is not strictly necessary, as it's not an axiom in HOL light,
    /// but we include it here anyway.
    def cut(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_cut(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `bool_eq (F1 |- a) (F2 |- a=b)` is `F1, F2 |- b`.
    /// This is the boolean equivalent of transitivity.
    def bool_eq(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_bool_eq(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `bool_eq_intro (F1, a |- b) (F2, b |- a)` is `F1, F2 |- b=a`.
    /// This is a way of building a boolean `a=b` from proofs of
    /// `a==>b` and `b==>a` (or `a|-b` and [b|-a`).
    def bool_eq_intro(&self, th1: Thm, th2: Thm) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_bool_eq_intro(th1.thm(py).clone(), th2.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `congr_ty (F1 |- f=g) ty` is `F1 |- f ty=g ty`
    def congr_ty(&self, th1: Thm, ty: Expr) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let th = em.thm_congr_ty(th1.thm(py).clone(), ty.expr(py))
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `abs x (F |- t=u)` is `F |- (λx.t)=(λx.u)`
    ///
    /// Panics if `x` occurs freely in `F`.
    def abs(&self, v: Expr, th1: Thm) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let v = v.expr(py).as_var()
            .ok_or_else(|| mk_err(py, "in abs, expected variable".to_string()))?;
        let th = em.thm_abs(v, th1.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// `basic_def(x=t)` where `x` is a variable and `t` a term
    /// with a closed type,
    /// returns a theorem `|- x=t` where `x` is now a constant, along with
    /// the constant `x`.
    def basic_def(&self, e: Expr) -> PyResult<(Thm, Expr)> {
        let mut em = self.ctx(py).lock().unwrap();
        let (th, e) = em.thm_new_basic_definition(e.expr(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        let th = Thm::create_instance(py, th, self.ctx(py).clone())?;
        let e = Expr::create_instance(py, e, self.ctx(py).clone())?;
        Ok((th,e))
    }

    /// Polymorphic definition.
    def poly_def(&self, name: &str, e: Expr) -> PyResult<NewPolyDef> {
        let mut ctx = self.ctx(py).lock().unwrap();
        let e = e.expr(py);
        let def = utils::thm_new_poly_definition(&mut *ctx, name, e.clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        NewPolyDef::create_instance(py, def, self.ctx(py).clone())
    }

    // TODO: polymorphic type def

    /// Create a new axiom `assumptions |- concl`.
    /// **use with caution**
    def axiom(&self, hyps: Vec<Expr>, concl: Expr) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let hyps = hyps.into_iter().map(|e| e.expr(py).clone()).collect();
        let th = em.thm_axiom(hyps, concl.expr(py).clone());
        Thm::create_instance(py, th, self.ctx(py).clone())
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
        let mut ctx = self.ctx(py).lock().unwrap();
        let td = ctx.thm_new_basic_type_definition(
            k::Symbol::from_str(name_tau),
            k::Symbol::from_str(name_abs),
            k::Symbol::from_str(name_repr),
            thm.thm(py).clone())
            .map_err(|e| mk_err(py, e.to_string()))?;
        NewTypeDef::create_instance(py, td, self.ctx(py).clone())
    }

    /// `instantiate thm σ` produces `Fσ |- Gσ`  where `thm` is `F |- G`
    ///
    /// Returns an error if the substitution is not closed.
    def instantiate(&self, thm: Thm, subst: Vec<(Expr, Expr)>) -> PyResult<Thm> {
        let mut em = self.ctx(py).lock().unwrap();
        let subst = subst.into_iter().map(|(v,e)| {
            let v = v.expr(py).as_var()
                .ok_or_else(|| mk_err(py, "instantiate: need variables".to_string()))?;
            Ok((v.clone(), e.expr(py).clone()))
        }).collect::<PyResult<Vec<_>>>()?;
        let th = em.thm_instantiate(thm.thm(py).clone(), &subst)
            .map_err(|e| mk_err(py, e.to_string()))?;
        Thm::create_instance(py, th, self.ctx(py).clone())
    }

    /// Parse an expression.
    def parse_expr(&self, s: &str) -> PyResult<Expr> {
        use trustee::syntax as sy;
        let mut ctx = self.ctx(py).lock().unwrap();
        let mut db = self.db(py).lock().unwrap();
        let get_fixity = |s:&str| {
            if s == "\\" { Some(sy::Fixity::Binder((5,6))) }
            else {
                match db.def_by_name(&s) {
                    None => None,
                    Some(c) => Some(c.fixity)
                }
            }
        };
        let pe = sy::parse(&get_fixity, s)
            .map_err(|e| mk_err(py, e.to_string()))?;
        let mut tyinf = sy::TypeInferenceCtx::new(&mut *ctx, &mut *db);
        let e = tyinf.infer(&pe)
            .map_err(|e| mk_err(py, e.to_string()))?;
        Expr::create_instance(py, e, self.ctx(py).clone())
    }

    /// Parse the list of open theory files.
    def parse_ot(&self, files: Vec<String>)
        -> PyResult<(trustee::FnvHashMap<String,Expr>, Vec<Thm>, Vec<Thm>)> {
        let mut ctx = self.ctx(py).lock().unwrap();
        let mut db = self.db(py).lock().unwrap();
        let mut ot_vm = trustee::open_theory::VM::new(&mut *ctx, &mut *db);
        for s in files {
            ot_vm.parse_file(&s)
                .map_err(|e| mk_err(py, e.to_string()))?;
        }
        let trustee::open_theory::Article{defs, theorems, assumptions} = ot_vm.into_article();
        let tbl1 = defs.into_iter().map(|(s,e)| {
            let e= Expr::create_instance(py, e, self.ctx(py).clone())?;
            Ok((s,e))
        }).collect::<PyResult<trustee::FnvHashMap<_,_>>>()?;
        let v2 = assumptions.into_iter().map(|e| {
            Thm::create_instance(py, e, self.ctx(py).clone())
        }).collect::<PyResult<Vec<_>>>()?;
        let v3 = theorems.into_iter().map(|e| {
            Thm::create_instance(py, e, self.ctx(py).clone())
        }).collect::<PyResult<Vec<_>>>()?;
        Ok((tbl1,v2,v3))
    }
});
