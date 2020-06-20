//! Parser and interpreter for [OpenTheory](http://www.gilith.com/opentheory/article.html)

use {
    crate::kernel_of_trust as k, crate::*, std::fmt, std::io::BufRead,
    std::rc::Rc,
};

#[derive(Clone, Eq, PartialEq, Hash)]
struct Name {
    ptr: Rc<(Vec<String>, String)>,
}

#[derive(Clone)]
struct Obj(ObjImpl);

/// An object for the VM
#[derive(Debug, Clone)]
enum ObjImpl {
    Int(usize),
    Name(Name),
    List(Vec<Obj>),
    TypeOp(Name, Rc<dyn OTypeOp>),
    Type(Expr),
    Const(Name, Rc<dyn OConst>),
    Var(Var),
    Term(Expr),
    Thm(Thm),
}

use ObjImpl as O;

/// A type operator, i.e. a type builder.
trait OTypeOp: fmt::Debug {
    fn apply(&self, ctx: &mut dyn k::CtxI, args: Vec<Expr>) -> Result<Expr>;
}

impl fmt::Debug for Obj {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/*
impl fmt::Debug for OTypeOp {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "<type op>")
    }
}
*/

/// A constant, parametrized by its type.
trait OConst: fmt::Debug {
    fn expr(&self, ctx: &mut dyn k::CtxI) -> Expr;
    fn apply(&self, ctx: &mut dyn k::CtxI, e: Expr) -> Result<Expr>;
}

impl std::ops::Deref for Obj {
    type Target = ObjImpl;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Obj {
    fn new(o: ObjImpl) -> Self {
        Self(o)
    }

    fn get(self) -> O {
        self.0
    }

    fn as_list(self) -> Result<Vec<Obj>> {
        match self.get() {
            O::List(l) => Ok(l),
            _ => Err(Error::new("expected list")),
        }
    }

    fn as_var(self) -> Result<Var> {
        match self.get() {
            O::Var(v) => Ok(v),
            _ => Err(Error::new("expected var")),
        }
    }

    fn as_term(self) -> Result<Expr> {
        match self.get() {
            O::Term(t) => Ok(t),
            _ => Err(Error::new("expected expr")),
        }
    }

    fn as_name(self) -> Result<Name> {
        match self.get() {
            O::Name(n) => Ok(n),
            _ => Err(Error::new("expected name")),
        }
    }

    fn as_type(self) -> Result<Expr> {
        match self.get() {
            O::Type(t) => Ok(t),
            _ => Err(Error::new("expected type")),
        }
    }

    fn as_thm(self) -> Result<Thm> {
        match self.get() {
            O::Thm(th) => Ok(th),
            _ => Err(Error::new("expected theorem")),
        }
    }
}

impl fmt::Debug for Name {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "{}", self.to_string())
    }
}

impl Name {
    /// Friendly display of a name
    pub fn to_string(&self) -> String {
        let &(ref pre, ref base) = &*self.ptr;
        if pre.len() == 0 {
            return base.clone(); // unqualified
        }
        let mut s = String::new();
        for x in pre.iter() {
            s += x.as_str();
            s += ".";
        }
        s += base.as_str();
        s
    }

    pub fn to_symbol(&self) -> Symbol {
        Symbol::from_str(&self.to_string()) // TODO: improve perf?
    }

    pub fn base(&self) -> &str {
        &self.ptr.1
    }

    /// Number of components in the prefix.
    pub fn len_pre(&self) -> usize {
        self.ptr.0.len()
    }

    /// Parse a string into a name.
    pub fn parse(s: &str) -> Option<Self> {
        let s = s.trim();
        if s.as_bytes()[0] != b'"' || s.as_bytes()[s.len() - 1] != b'"' {
            return None;
        }

        let s = &s[1..s.len() - 1];
        let mut toks: Vec<&str> = s.split(".").collect();
        let base = toks.pop().unwrap().to_string();
        let pre = toks.into_iter().map(|s| s.to_string()).collect();
        Some(Name { ptr: Rc::new((pre, base)) })
    }
}

/// Used for looking up theorems.
#[derive(Debug, Eq, PartialEq, Hash)]
struct ThmKey(Expr, Vec<Expr>);

impl ThmKey {
    /// New key from this theorem.
    pub fn new(th: &Thm) -> Self {
        ThmKey(th.concl().clone(), th.hyps_vec().clone())
    }
}

/// An article obtained by interpreting a theory file (or several).
///
/// We're not exactly compliant here, as we want to be able to parse several
/// OT files without introducing intermediate axioms.
#[derive(Debug, Clone)]
pub struct Article {
    pub defs: fnv::FnvHashMap<String, Expr>,
    pub assumptions: Vec<Thm>,
    pub theorems: Vec<Thm>,
}

impl fmt::Display for Article {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "Article {{\n")?;
        for n in self.defs.iter().map(|x| x.0) {
            write!(out, "  def {:?}\n", n)?;
        }
        for th in &self.assumptions {
            write!(out, "  axiom {}\n", th)?;
        }
        for th in &self.theorems {
            write!(out, "  prove {}\n", th)?;
        }
        write!(out, "}}")
    }
}

/// Callbacks that an OpenTheory VM is parametrized with.
pub trait Callbacks {
    /// Print debug messages.
    fn debug<F>(&mut self, _f: F)
    where
        F: Fn() -> String,
    {
    }
}

/// Trivial implementation for callbacks.
impl Callbacks for () {}

/// Virtual machine.
///
/// This is used to parse and interpret an OpenTheory file.
#[derive(Debug)]
pub struct VM<'a, CB: Callbacks> {
    ctx: &'a mut dyn k::CtxI,
    cb: CB,
    ty_vars: fnv::FnvHashMap<String, Var>,
    vars: fnv::FnvHashMap<String, (Var, Var)>, // "x" -> (x, α)
    defs: fnv::FnvHashMap<Name, Rc<dyn OConst>>,
    ty_defs: fnv::FnvHashMap<Name, Rc<dyn OTypeOp>>,
    stack: Vec<Obj>,
    dict: fnv::FnvHashMap<usize, Obj>,
    assumptions: Vec<Thm>,
    theorems: fnv::FnvHashMap<ThmKey, Thm>,
}

#[derive(Debug)]
struct CustomConst {
    n: Name,
    c: Expr,
    c_vars: Expr,    // c applied to ty_vars
    c_ty_vars: Expr, // typeof(c_vars)
    ty_vars: Vec<Var>,
}

impl OConst for CustomConst {
    fn expr(&self, _: &mut dyn k::CtxI) -> Expr {
        self.c.clone()
    }
    fn apply(&self, em: &mut dyn k::CtxI, ty: Expr) -> Result<Expr> {
        use std::borrow::Cow;

        if self.c_ty_vars == ty {
            // shortcut: already the right type, no unif needed
            let t = self.c_vars.clone();
            return Ok(t);
        }

        let mut c_ty_vars: Expr = self.c_ty_vars.clone();
        let mut ty_vars = Cow::Borrowed(&self.ty_vars);
        // rename if needed
        if let Some(mut data) =
            algo::need_to_rename_before_unif(&c_ty_vars, &ty)
        {
            //eprintln!(
            //    "need to rename in const {:?}:{:?}, to unify with type {:?}",
            //    self.c, self.c_ty_vars, ty
            //);
            ty_vars = Cow::Owned(
                self.ty_vars
                    .iter()
                    .map(|v| data.rename_var(v))
                    .collect::<Vec<Var>>(),
            );
            // type of `c args`
            c_ty_vars = {
                let mut app = self.c.clone();
                for x in ty_vars.iter().cloned() {
                    let v = em.mk_var(x);
                    app = em.mk_app(app, v)?;
                }
                app.ty().clone()
            }
        }
        // match type, so we're sure that `ty_vars` all disappear
        let subst = algo::match_(&c_ty_vars, &ty).ok_or_else(|| {
            Error::new_string(format!(
                "unification failed\n  between {:?} and {:?}\n  \
                    when applying constant {:?}",
                c_ty_vars, ty, self.n,
            ))
        })?;
        //eprintln!(
        //    "unified:\n  between {:?} and {:?}\n  yields {:?}",
        //    c_ty_vars, ty, subst
        //);
        // now apply `c` to the proper type arguments
        let t = {
            let mut app = self.c.clone();
            for v in &ty_vars[..] {
                let ty = match subst.find_rec(v) {
                    Some(e) => e.clone(),
                    None => em.mk_var(v.clone()),
                };
                app = em.mk_app(app, ty)?
            }
            app
        };
        //eprintln!("result constant is {:?}", &t);
        Ok(t)
    }
}

impl<'a, CB: Callbacks> VM<'a, CB> {
    /// Create a new VM using the given expression manager.
    pub fn new_with(ctx: &'a mut dyn k::CtxI, cb: CB) -> Self {
        VM {
            ctx,
            cb,
            ty_vars: fnv::new_table_with_cap(32),
            vars: fnv::new_table_with_cap(32),
            defs: fnv::new_table_with_cap(32),
            ty_defs: fnv::new_table_with_cap(8),
            stack: vec![],
            dict: fnv::new_table_with_cap(32),
            assumptions: vec![],
            theorems: fnv::new_table_with_cap(32),
        }
    }

    /// Turn into an article.
    pub fn into_article(self) -> Article {
        let VM { defs, assumptions, theorems, ctx, .. } = self;
        let defs = defs
            .into_iter()
            .map(|(n, oc)| (n.to_string(), oc.expr(ctx).clone()))
            .collect();
        let theorems: Vec<_> = theorems.into_iter().map(|x| x.1).collect();
        Article { defs, assumptions, theorems }
    }

    #[inline]
    fn push(&mut self, o: Obj) {
        self.cb.debug(|| format!("vm.push {:?}", &o));
        self.stack.push(o)
    }

    fn push_obj(&mut self, o: ObjImpl) {
        self.push(Obj(o))
    }

    fn pop1<F, A>(&mut self, what: &str, f: F) -> Result<A>
    where
        F: Fn(&mut Self, Obj) -> Result<A>,
    {
        if self.stack.len() < 1 {
            return Err(Error::new_string(format!(
                "OT.pop1.{}: empty stack",
                what
            )));
        }
        let x = self.stack.pop().unwrap();
        f(self, x)
    }

    fn pop2<F, A>(&mut self, what: &str, f: F) -> Result<A>
    where
        F: Fn(&mut Self, Obj, Obj) -> Result<A>,
    {
        if self.stack.len() < 2 {
            return Err(Error::new_string(format!(
                "OT.pop2.{}: empty stack",
                what
            )));
        }
        let x = self.stack.pop().unwrap();
        let y = self.stack.pop().unwrap();
        f(self, x, y)
    }

    fn pop3<F, A>(&mut self, what: &str, f: F) -> Result<A>
    where
        F: Fn(&mut Self, Obj, Obj, Obj) -> Result<A>,
    {
        if self.stack.len() < 3 {
            return Err(Error::new_string(format!(
                "OT.pop3.{}: empty stack",
                what
            )));
        }
        let x = self.stack.pop().unwrap();
        let y = self.stack.pop().unwrap();
        let z = self.stack.pop().unwrap();
        f(self, x, y, z)
    }

    fn abs_term(&mut self) -> Result<()> {
        self.pop2("abs_term", |vm, x, y| {
            let body = x.as_term()?;
            let v = y.as_var()?;
            let e = vm.ctx.mk_lambda(v.clone(), body.clone())?;
            vm.push_obj(O::Term(e));
            Ok(())
        })
        .map_err(|e| {
            e.set_source(Error::new("OT: failure in abs_term(<term,var>)"))
        })
    }

    fn abs_thm(&mut self) -> Result<()> {
        self.pop2("abs_thm", |vm, x, y| {
            let th = x.as_thm()?;
            let v = y.as_var()?;
            let th = vm.ctx.thm_abs(&v, th)?;
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| {
            e.set_source(Error::new("OT: failure in abs_thm(<thm,var>)"))
        })
    }

    fn app_term(&mut self) -> Result<()> {
        self.pop2("app_term", |vm, x, y| {
            let x = x.as_term()?;
            let f = y.as_term()?;
            let e = vm.ctx.mk_app(f.clone(), x.clone())?;
            vm.push_obj(O::Term(e));
            Ok(())
        })
        .map_err(|e| {
            e.set_source(Error::new("OT: failure in app_term(<term,term>)"))
        })
    }

    fn app_thm(&mut self) -> Result<()> {
        self.pop2("app_thm", |vm, x, y| {
            let th1 = x.as_thm()?;
            let th2 = y.as_thm()?;
            let th = vm.ctx.thm_congr(th2, th1)?;
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| {
            e.set_source(Error::new("OT: failure in app_thm(<thm,thm>)"))
        })
    }

    fn assume(&mut self) -> Result<()> {
        self.pop1("assume", |vm, x| {
            let t = x.as_term()?;
            let th = vm.ctx.thm_assume(t);
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| e.set_source(Error::new("OT: failure in assume(<term>)")))
    }

    fn axiom(&mut self) -> Result<()> {
        self.pop2("axiom", |vm, x, y| {
            let concl = x.as_term()?;
            let hyps: Vec<Expr> = y
                .as_list()?
                .into_iter()
                .map(|x| {
                    let t = x.as_term().map_err(|e| {
                        e.set_source(Error::new("axiom: hyps contain non-term"))
                    })?;
                    Ok(t.clone())
                })
                .collect::<Result<_>>()?;
            let th_key = ThmKey(concl.clone(), hyps);
            // see if there already is a theorem matching this "axiom"
            let ax = match vm.theorems.get(&th_key) {
                Some(th) => th.clone(),
                None => {
                    let ThmKey(concl, hyps) = th_key; // consume key
                    let ax = vm.ctx.thm_axiom(hyps, concl)?;
                    vm.cb.debug(|| format!("## add axiom {:?}", ax));
                    vm.assumptions.push(ax.clone());
                    ax
                }
            };
            vm.push_obj(O::Thm(ax));
            Ok(())
        })
        .map_err(|e| {
            e.set_source(Error::new("OT: failure in axiom(<term,list>)"))
        })
    }

    fn version(&mut self) -> Result<()> {
        self.pop1("version", |_vm, o| match *o {
            O::Int(6) => Ok(()),
            _ => Err(Error::new_string(format!(
                "OpenTheory: unsupported version {:?}",
                o,
            ))),
        })
    }

    fn nil(&mut self) -> Result<()> {
        self.push_obj(O::List(vec![]));
        Ok(())
    }

    fn type_op(&mut self) -> Result<()> {
        // builder for bool
        #[derive(Debug, Clone)]
        struct TyOpConst(Expr);
        impl OTypeOp for TyOpConst {
            fn apply(
                &self,
                _em: &mut dyn k::CtxI,
                args: Vec<Expr>,
            ) -> Result<Expr> {
                if args.len() != 0 {
                    Err(Error::new_string(format!(
                        "{:?} takes no arguments",
                        self.0
                    )))
                } else {
                    Ok(self.0.clone())
                }
            }
        };

        // builder for arrow
        #[derive(Debug, Clone)]
        struct TyOpArrow;
        impl OTypeOp for TyOpArrow {
            fn apply(
                &self,
                em: &mut dyn k::CtxI,
                mut args: Vec<Expr>,
            ) -> Result<Expr> {
                if args.len() != 2 {
                    return Err(Error::new("-> takes 2 arguments"));
                };
                let ty2 = args.pop().unwrap();
                let ty1 = args.pop().unwrap();
                debug_assert!(args.is_empty());
                em.mk_arrow(ty1, ty2)
            }
        }

        self.pop1("type op", |vm, o| {
            let n = o.as_name()?;
            let oc = if n.len_pre() == 0 && n.base() == "bool" {
                Rc::new(TyOpConst(vm.ctx.mk_bool()))
            } else if n.len_pre() == 0 && n.base() == "ind" {
                Rc::new(TyOpConst(vm.ctx.mk_ind()))
            } else if n.len_pre() == 0 && n.base() == "->" {
                Rc::new(TyOpArrow)
            } else {
                // lookup in definitions
                if let Some(d) = vm.ty_defs.get(&n) {
                    d.clone()
                } else {
                    return Err(Error::new_string(format!(
                        "type_op: undefined type operator {:?}",
                        n,
                    )));
                }
            };
            Ok(vm.push_obj(O::TypeOp(n.clone(), oc.clone())))
        })
    }

    fn def(&mut self) -> Result<()> {
        self.pop2("def", |vm, k, x| match &*k {
            O::Int(i) => {
                vm.dict.insert(*i, x.clone());
                vm.push(x); // push x back
                Ok(())
            }
            _ => Err(Error::new("def: expected int")),
        })
    }

    fn hd_tl(&mut self) -> Result<()> {
        self.pop1("hdTl", |vm, l| {
            let l = l.as_list()?;
            if l.len() == 0 {
                return Err(Error::new("hdTl: empty list"));
            }
            vm.push(l[0].clone());
            let rest = l.iter().skip(1).cloned().collect();
            vm.push_obj(O::List(rest));
            Ok(())
        })
    }

    fn cons(&mut self) -> Result<()> {
        let a = self.pop2("cons", |_vm, mut a, b| match a.0 {
            O::List(ref mut v) => {
                v.insert(0, b);
                Ok(a)
            }
            _ => Err(Error::new("expected a list as second arg")),
        })?;
        self.push(a);
        Ok(())
    }

    fn ref_(&mut self) -> Result<()> {
        self.pop1("ref", |vm, o| match &*o {
            O::Int(n) => {
                if let Some(x) = vm.dict.get(n) {
                    let x = x.clone();
                    vm.push(x); // lookup and push
                    Ok(())
                } else {
                    Err(Error::new_string(format!(
                        "ref: int {} not defined in dictionary",
                        n
                    )))
                }
            }
            _ => Err(Error::new("ref: expected int")),
        })
    }

    fn var_type(&mut self) -> Result<()> {
        self.pop1("var_type", |vm, o| match &*o {
            O::Name(n) => {
                if n.len_pre() != 0 {
                    return Err(Error::new("var_type: need unqualified name"));
                }
                // make a type variable
                let ty = vm.ctx.mk_ty();
                let v = vm.ctx.mk_var_str(&n.ptr.1, ty);
                vm.push_obj(O::Type(v));
                Ok(())
            }
            _ => Err(Error::new("var_type: expected name")),
        })
    }

    fn op_type(&mut self) -> Result<()> {
        self.pop2("op type", |vm, o1, o2| match (&*o1, &*o2) {
            (O::List(l), O::TypeOp(_, f)) => {
                let args: Result<Vec<Expr>> = l
                    .iter()
                    .map(|x| match &**x {
                        O::Type(a) => Ok(a.clone()),
                        _ => Err(Error::new("in op type: expected type")),
                    })
                    .collect();
                let args = args?;
                let r = (&**f as &dyn OTypeOp).apply(vm.ctx, args)?;
                vm.push_obj(O::Type(r));
                Ok(())
            }
            _ => Err(Error::new("op_type: expected <list,typeop>")),
        })
    }

    fn const_(&mut self) -> Result<()> {
        #[derive(Debug)]
        struct ConstEq;
        impl OConst for ConstEq {
            fn expr(&self, em: &mut dyn k::CtxI) -> Expr {
                em.mk_eq()
            }
            fn apply(&self, em: &mut dyn k::CtxI, ty: Expr) -> Result<Expr> {
                let args = ty.unfold_pi().0;
                if args.len() != 2 {
                    Err(Error::new_string(format!(
                        "`=` cannot take type {:?}",
                        ty
                    )))?
                }
                let e = em.mk_eq();
                em.mk_app(e, args[0].clone())
            }
        }
        #[derive(Debug)]
        struct ConstSelect;
        impl OConst for ConstSelect {
            fn expr(&self, em: &mut dyn k::CtxI) -> Expr {
                em.mk_select()
            }
            fn apply(&self, em: &mut dyn k::CtxI, ty: Expr) -> Result<Expr> {
                let a = ty
                    .as_pi()
                    .ok_or_else(|| {
                        Error::new_string(format!(
                            "`select` cannot take type {:?}",
                            ty
                        ))
                    })?
                    .1;
                let e = em.mk_select();
                em.mk_app(e, a.clone())
            }
        }

        self.pop1("const", |vm, o| match &*o {
            O::Name(n) => {
                let oc = match n.base() {
                    "=" if n.len_pre() == 0 => {
                        Rc::new(ConstEq) as Rc<dyn OConst>
                    }
                    "select" if n.len_pre() == 0 => {
                        Rc::new(ConstSelect) as Rc<dyn OConst>
                    }
                    _ => {
                        // lookup in definitions
                        if let Some(d) = vm.defs.get(n) {
                            d.clone()
                        } else {
                            return Err(Error::new_string(format!(
                                "const: undefined constant {:?}",
                                n,
                            )));
                        }
                    }
                };
                vm.push_obj(O::Const(n.clone(), oc));
                Ok(())
            }
            _ => Err(Error::new("const: expected <name>")),
        })
    }

    fn const_term(&mut self) -> Result<()> {
        self.pop2("const term", |vm, x, y| match (&*x, &*y) {
            (O::Type(ty), O::Const(_, c)) => {
                // apply constant to type
                let e = (&**c as &dyn OConst).apply(vm.ctx, ty.clone())?;
                vm.push_obj(O::Term(e));
                Ok(())
            }
            _ => Err(Error::new("const_term: expected <type,const>")),
        })
    }

    fn var(&mut self) -> Result<()> {
        self.pop2("var", |vm, x, y| match (&*x, &*y) {
            (O::Type(ty), O::Name(n)) => {
                // TODO: avoid allocating intermediate `String`
                let v = Var::new(Symbol::from_str(&n.to_string()), ty.clone());
                vm.push_obj(O::Var(v));
                Ok(())
            }
            _ => Err(Error::new("var: expected <type,name>")),
        })
    }

    fn var_term(&mut self) -> Result<()> {
        self.pop1("var_term", |vm, o| match &*o {
            O::Var(v) => {
                let e = vm.ctx.mk_var(v.clone());
                vm.push_obj(O::Term(e));
                Ok(())
            }
            _ => Err(Error::new("var_term: expected <var>")),
        })
    }

    fn define_const(&mut self) -> Result<()> {
        self.pop2("define const", |vm, x, y| match (&*x, &*y) {
            (O::Term(rhs), O::Name(n)) => {
                // make a definition `n := t`
                let def = algo::thm_new_poly_definition(
                    vm.ctx,
                    &n.to_string(),
                    rhs.clone(),
                )?;
                vm.cb.debug(|| {
                    format!(
                        "define const {:?}\n  with thm {:#?}\n  and vars {:?}",
                        n, &def.thm, &def.ty_vars,
                    )
                });
                let c_ty_vars = def.c_applied.ty().clone();
                // now build the constant building closure
                let c = Rc::new(CustomConst {
                    c: def.c.clone(),
                    c_vars: def.c_applied.clone(),
                    ty_vars: def.ty_vars,
                    c_ty_vars,
                    n: n.clone(),
                });

                // define and push
                vm.defs.insert(n.clone(), c.clone());
                vm.theorems.insert(ThmKey::new(&def.thm), def.thm.clone());
                vm.push_obj(O::Const(n.clone(), c));
                vm.push_obj(O::Thm(def.thm_applied));
                Ok(())
            }
            _ => Err(Error::new("define const: expected <term,name>")),
        })
    }

    fn define_const_list(&mut self) -> Result<()> {
        self.pop2("define const list", |vm, x, y| {
            let mut thm = x.as_thm()?.clone();
            let renaming = y
                .as_list()?
                .into_iter()
                .map(|x| match x.0 {
                    O::List(mut vec) if vec.len() == 2 => {
                        let v = vec.pop().unwrap().as_var()?;
                        let n = vec.pop().unwrap().as_name()?;
                        debug_assert_eq!(vec.len(), 0);
                        Ok((n, v))
                    }
                    _ => Err(Error::new(
                        "in define_const_list: expected pair (name,var)",
                    )),
                })
                .collect::<Result<Vec<_>>>()?;
            // find subst
            let subst = thm.hyps().iter().map(|e| {
                let (v, rhs) = e.unfold_eq()
                    .ok_or_else(|| Error::new("theorem ypothesis must be equations"))?;
                let v = v.as_var()
                    .ok_or_else(|| Error::new("in theorem hypothesis, equations must have a variable as LHS"))?;
                Ok((v.clone(), rhs.clone()))
            }).collect::<Result<Vec<(Var,Expr)>>>()?;

            vm.cb.debug(|| {
                format!(
                    "define const list thm={:#?}, renaming={:#?}, subst={:#?}",
                    &thm, &renaming, &subst
                )
            });

            #[derive(Debug)]
            struct LocalConst {
                v: Var,
                n: Name,
                c_applied: Expr,
                thm_applied: Thm,
                cst: Rc<CustomConst>,
            };

            // define each constant
            let c_l = renaming.into_iter().map(|(n, v)| {
                let rhs = subst.iter().find(|(ref v2,_)| &v==v2).ok_or_else(||
                    Error::new_string(format!("define_const_list: no binding for variable {:?}", &v)))?.1.clone();
                let def = algo::thm_new_poly_definition(vm.ctx, &n.to_string(), rhs)?;
                // now build the constant building closure
                let c_ty_vars = def.c_applied.ty().clone();
                let c = Rc::new(CustomConst {
                    c: def.c.clone(),
                    c_vars: def.c_applied.clone(),
                    ty_vars: def.ty_vars,
                    c_ty_vars,
                    n: n.clone(),
                });

                // define and push
                vm.defs.insert(n.clone(), c.clone());
                vm.theorems.insert(ThmKey::new(&def.thm), def.thm.clone());
                Ok(LocalConst{
                    c_applied: def.c_applied, v:v.clone(), n: n.clone(),
                    thm_applied: def.thm_applied, cst: c
                })
            }).collect::<Result<Vec<LocalConst>>>()?;

            // instantiate `thm` with `v_i := c_i`
            thm = {
                let subst: Vec<_> = c_l.iter()
                    .map(|ldef| (ldef.v.clone(),ldef.c_applied.clone())).collect();
                vm.ctx.thm_instantiate(thm, &subst)?
            };

            // resolve instantiated theorem with each constant definition thm
            // to remove the hypotheses
            for ldef in &c_l {
                thm = vm.ctx.thm_cut(ldef.thm_applied.clone(), thm)?;
            }

            // push list of constants
            {
                let l = c_l.into_iter()
                    .map(|ldef| Obj::new(O::Const(ldef.n, ldef.cst))).collect();
                vm.push_obj(O::List(l))
            }

            vm.push_obj(O::Thm(thm));
            Ok(())
        })
    }

    fn define_type_op_(&mut self) -> Result<()> {
        let thm = self.stack.pop().unwrap().as_thm()?.clone();
        let names: Vec<String> = self
            .stack
            .pop()
            .unwrap()
            .as_list()?
            .into_iter()
            .map(|e| e.as_name().map(|n| n.to_string()))
            .collect::<Result<Vec<_>>>()?;
        let rep = self.stack.pop().unwrap().as_name()?.clone();
        let abs = self.stack.pop().unwrap().as_name()?.clone();
        let ty_name = self.stack.pop().unwrap().as_name()?.clone();
        if self.ty_defs.contains_key(&ty_name) {
            return Err(Error::new_string(format!(
                "type operator {:?} already defined",
                &ty_name,
            )));
        }

        let def = self.ctx.thm_new_basic_type_definition(
            ty_name.to_symbol(),
            abs.to_symbol(),
            rep.to_symbol(),
            thm,
        )?;

        // compute reordering of variables wrt `names` so we know in what order
        // to apply parameters expressions

        if def.fvars.len() != names.len() {
            return Err(Error::new_string(format!(
                "expected {} free variables, got {}",
                names.len(),
                def.fvars.len(),
            )));
        }

        let reorder = names
            .iter()
            .map(|ref n| {
                def.fvars
                    .iter()
                    .enumerate()
                    .find_map(|(i, v)| {
                        if v.name().name() == n.as_str() {
                            Some(i)
                        } else {
                            None
                        }
                    })
                    .ok_or_else(|| {
                        Error::new_string(format!(
                            "cannot find variable with name {}",
                            n
                        ))
                    })
            })
            .collect::<Result<Vec<usize>>>()?;

        // implementation of the type constructor

        #[derive(Debug, Clone)]
        struct TyOpCustom(Vec<usize>, k::NewTypeDef);

        impl OTypeOp for TyOpCustom {
            fn apply(
                &self,
                em: &mut dyn k::CtxI,
                args: Vec<Expr>,
            ) -> Result<Expr> {
                if args.len() != self.0.len() {
                    return Err(Error::new("bad arity"));
                }
                // re-shuffle args
                let args2: Vec<Expr> =
                    self.0.iter().map(|i| args[*i].clone()).collect();

                em.mk_app_l(self.1.tau.clone(), &args2[..])
            }
        }

        // now push the results. See
        // http://www.gilith.com/opentheory/article.html#defineTypeOpCommand.

        // define and push type op
        let ty_op = Rc::new(TyOpCustom(reorder, def.clone()));
        self.ty_defs.insert(ty_name.clone(), ty_op.clone());
        self.push_obj(O::TypeOp(ty_name, ty_op));

        let fvars_exprs: Vec<_> =
            def.fvars.iter().map(|v| self.ctx.mk_var(v.clone())).collect();

        // define and push abs
        {
            let c_vars = self.ctx.mk_app_l(def.c_abs.clone(), &fvars_exprs)?;
            let c_ty_vars = c_vars.ty().clone();
            let oc = CustomConst {
                n: abs.clone(),
                c: def.c_abs.clone(),
                c_vars,
                ty_vars: def.fvars.clone(),
                c_ty_vars,
            };
            let def = Rc::new(oc);
            self.defs.insert(abs.clone(), def.clone());
            self.push_obj(O::Const(abs, def))
        }

        // define and push repr
        {
            let c_vars = self.ctx.mk_app_l(def.c_repr.clone(), &fvars_exprs)?;
            let c_ty_vars = c_vars.ty().clone();
            let oc = CustomConst {
                n: rep.clone(),
                c: def.c_repr.clone(),
                c_vars,
                ty_vars: def.fvars.clone(),
                c_ty_vars,
            };
            let def = Rc::new(oc);
            self.defs.insert(rep.clone(), def.clone());
            self.push_obj(O::Const(rep, def))
        }

        // push abs thm
        {
            let abs_thm = def.abs_thm.clone();
            let th = self.ctx.thm_abs(&def.abs_x, abs_thm)?;
            self.push_obj(O::Thm(th));
        }

        // push repr thm
        {
            let repr_thm = def.repr_thm.clone();
            let repr_thm2 = algo::thm_sym(self.ctx, repr_thm)?;
            let th = self.ctx.thm_abs(&def.repr_x, repr_thm2)?;
            self.push_obj(O::Thm(th));
        }

        Ok(())
    }

    fn define_type_op(&mut self) -> Result<()> {
        if self.stack.len() < 5 {
            return Err(Error::new(
                "define_type_op: not enough elements in stack",
            ));
        }
        self.define_type_op_()
            .map_err(|e| e.set_source(Error::new("define_type_op")))
    }

    fn pop(&mut self) -> Result<()> {
        if self.stack.pop().is_some() {
            Ok(())
        } else {
            return Err(Error::new("pop: empty stack"));
        }
    }

    fn remove(&mut self) -> Result<()> {
        self.pop1("remove", |vm, o| match &*o {
            O::Int(n) => {
                let o = vm
                    .dict
                    .remove(n)
                    .ok_or_else(|| Error::new("remove: key not present"))?;
                vm.push(o);
                Ok(())
            }
            _ => Err(Error::new("remove: expected int")),
        })
    }

    fn thm(&mut self) -> Result<()> {
        self.pop3("thm", |vm, x, y, z| {
            let _phi = x.as_term()?;
            let l = y.as_list()?;
            let thm = z.as_thm()?;

            l.into_iter().try_for_each(|x| {
                if let O::Term(_) = x.get() {
                    Ok(())
                } else {
                    return Err(Error::new("thm: expected term in list"));
                }
            })?;
            // TODO?: alpha rename with [terms] and [phi]? does it make any sense?
            vm.cb.debug(|| format!("## add theorem {:?} phi={:?}", thm, _phi));
            let k = ThmKey::new(&thm);
            vm.theorems.insert(k, thm.clone());
            Ok(())
        })
        .map_err(|e| e.set_source(Error::new("OT: failure in thm")))
    }

    fn subst(&mut self) -> Result<()> {
        self.pop2("subst", |vm, x, y| {
            let thm = x.as_thm()?;
            let mut l = y.as_list()?;
            // build type substitution first
            let mut subst = vec![];
            if l.len() != 2 {
                return Err(Error::new("expected pair of subst"));
            }
            let subst_t = l.pop().unwrap();
            let subst_ty = l.pop().unwrap();
            debug_assert_eq!(l.len(), 0);
            subst_ty.as_list()?.into_iter().try_for_each(|x| {
                let mut l = x.as_list()?;
                if l.len() != 2 {
                    return Err(Error::new("expected <name>,<ty> in subst"));
                }
                let ty = l.pop().unwrap().as_type()?;
                let v = l.pop().unwrap().as_name()?;
                let pair = (Var::from_str(&v.to_string(), vm.ctx.mk_ty()), ty);
                subst.push(pair);
                Ok(())
            })?;
            vm.cb.debug(|| {
                format!(
                    "instantiating\n  {:#?}\n  with type subst {:#?}",
                    &thm, subst
                )
            });
            let th1 = vm.ctx.thm_instantiate(thm, &subst[..])?;
            vm.cb.debug(|| format!("instantiated\n  into {:#?}", &th1));
            // then instantiate terms
            subst.clear();
            subst_t.as_list()?.into_iter().try_for_each(|x| {
                let mut l = x.as_list()?;
                if l.len() != 2 {
                    return Err(Error::new("expected <var>,<expr>"));
                }
                let ty = l.pop().unwrap().as_term()?;
                let v = l.pop().unwrap().as_var()?;
                let pair = (v, ty);
                subst.push(pair);
                Ok(())
            })?;
            let th2 = vm.ctx.thm_instantiate(th1, &subst[..])?;
            vm.cb.debug(|| {
                format!(
                    "instantiated\n  into {:#?}\n  with subst {:#?}",
                    &th2, subst,
                )
            });
            vm.push_obj(O::Thm(th2));
            Ok(())
        })
        .map_err(|e| e.set_source(Error::new("OT: failure in subst")))
    }

    fn refl(&mut self) -> Result<()> {
        self.pop1("refl", |vm, x| {
            let t = x.as_term()?.clone();
            let th = vm.ctx.thm_refl(t);
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| e.set_source(Error::new("OT: failure in refl")))
    }

    fn trans(&mut self) -> Result<()> {
        self.pop2("trans", |vm, x, y| {
            let th1 = x.as_thm()?;
            let th2 = y.as_thm()?;
            let th = vm.ctx.thm_trans(th2, th1)?;
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| {
            e.set_source(Error::new("OT: failure in trans(<thm,thm>)"))
        })
    }

    fn sym(&mut self) -> Result<()> {
        self.pop1("sym", |vm, x| {
            let th1 = x.as_thm()?.clone();
            let th = algo::thm_sym(vm.ctx, th1)?;
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| e.set_source(Error::new("OT: failure in refl")))
    }

    fn eq_mp(&mut self) -> Result<()> {
        self.pop2("eq_mp", |vm, x, y| {
            let th1 = x.as_thm()?;
            let th2 = y.as_thm()?;
            let th = vm
                .ctx
                .thm_bool_eq(th1, th2)
                .map_err(|e| e.set_source(Error::new("in eq_mp")))?;
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| {
            e.set_source(Error::new("OT: failure in eq_mp(<thm,thm>)"))
        })
    }

    fn beta_conv(&mut self) -> Result<()> {
        self.pop1("beta_conv", |vm, x| {
            let t = x.as_term()?.clone();
            let th = vm.ctx.thm_beta_conv(&t)?;
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| e.set_source(Error::new("OT: failure in beta_conv")))
    }

    fn deduct_antisym(&mut self) -> Result<()> {
        self.pop2("deduct_antisym", |vm, x, y| {
            let th1 = x.as_thm()?;
            let th2 = y.as_thm()?;
            let th = vm.ctx.thm_bool_eq_intro(th1, th2)?;
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| {
            e.set_source(Error::new("OT: failure in deduct_antisym(<thm,thm>)"))
        })
    }

    fn prove_hyp(&mut self) -> Result<()> {
        self.pop2("prove_hyp", |vm, x, y| {
            let th1 = x.as_thm()?;
            let th2 = y.as_thm()?;
            let th = vm
                .ctx
                .thm_cut(th2, th1)
                .map_err(|e| e.set_source(Error::new("in cut")))?;
            vm.push_obj(O::Thm(th));
            Ok(())
        })
        .map_err(|e| {
            e.set_source(Error::new(
                "OT: failure in prove_hyp(<thm,thm>):\n {}",
            ))
        })
    }

    /// Parse the given reader.
    pub fn parse_str(&mut self, buf: &mut dyn BufRead) -> Result<()> {
        // skip empty lines and comments

        for line in buf.lines() {
            let line =
                line.map_err(|e| Error::new_string(format!("error {:?}", e)))?;
            let line = line.trim();
            self.cb.debug(|| format!("// parse line {}", line));
            if line.starts_with("#") {
                continue;
            } else if line.starts_with("\"") {
                let name = Name::parse(line).ok_or_else(|| {
                    Error::new_string(format!(
                        "cannot parse name from line {:?}",
                        line
                    ))
                })?;
                self.push_obj(ObjImpl::Name(name))
            } else if let Ok(i) = line.parse::<usize>() {
                self.push_obj(ObjImpl::Int(i))
            } else {
                match line {
                    "absTerm" => self.abs_term()?,
                    "absThm" => self.abs_thm()?,
                    "appTerm" => self.app_term()?,
                    "appThm" => self.app_thm()?,
                    "assume" => self.assume()?,
                    "axiom" => self.axiom()?,
                    "version" => self.version()?,
                    "nil" => self.nil()?,
                    "typeOp" => self.type_op()?,
                    "def" => self.def()?,
                    "hdTl" => self.hd_tl()?,
                    "cons" => self.cons()?,
                    "ref" => self.ref_()?,
                    "varType" => self.var_type()?,
                    "opType" => self.op_type()?,
                    "const" => self.const_()?,
                    "constTerm" => self.const_term()?,
                    "var" => self.var()?,
                    "varTerm" => self.var_term()?,
                    "defineConst" => self.define_const()?,
                    "defineConstList" => self.define_const_list()?,
                    "pop" => self.pop()?,
                    "remove" => self.remove()?,
                    "thm" => self.thm()?,
                    "subst" => self.subst()?,
                    "refl" => self.refl()?,
                    "trans" => self.trans()?,
                    "sym" => self.sym()?,
                    "eqMp" => self.eq_mp()?,
                    "betaConv" => self.beta_conv()?,
                    "deductAntisym" => self.deduct_antisym()?,
                    "proveHyp" => self.prove_hyp()?,
                    "defineTypeOp" => self.define_type_op()?,
                    _ => Err(Error::new_string(format!(
                        "unknown command {:?}",
                        line
                    )))?,
                }
            }
        }

        Ok(())
    }

    /// Parse the given file.
    pub fn parse_file(&mut self, file: &str) -> Result<()> {
        let file = std::fs::File::open(file)
            .map_err(|e| Error::new_string(format!("error {:?}", e)))?;
        let mut buf = std::io::BufReader::new(file);
        self.parse_str(&mut buf)
    }
}

impl<'a> VM<'a, ()> {
    /// Trivial constructor.
    pub fn new(ctx: &'a mut dyn k::CtxI) -> Self {
        VM::new_with(ctx, ())
    }
}
