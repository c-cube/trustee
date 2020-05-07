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
struct Obj(Rc<ObjImpl>);

/// A type operator, i.e. a type builder.
trait OTypeOp: fmt::Debug {
    fn apply(
        &self,
        em: &mut k::ExprManager,
        args: Vec<Expr>,
    ) -> Result<Expr, String>;
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
    fn apply(&self, em: &mut k::ExprManager, e: Expr) -> Result<Expr, String>;
}

impl std::ops::Deref for Obj {
    type Target = ObjImpl;
    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

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

    pub fn base(&self) -> &str {
        &self.ptr.1
    }

    /// Number of components in the prefix.
    pub fn len_pre(&self) -> usize {
        self.ptr.0.len()
    }

    /// Parse a string nto a name.
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

/// An article obtained by interpreting a theory file.
#[derive(Debug)]
pub struct Article {
    defs: fnv::FnvHashMap<Name, Rc<dyn OConst>>,
    assumptions: Vec<Thm>,
    theorems: Vec<Thm>,
}

/// Virtual machine.
///
/// This is used to parse and interpret an OpenTheory file.
#[derive(Debug)]
pub struct VM<'a> {
    em: &'a mut ExprManager,
    ty_vars: fnv::FnvHashMap<String, Var>,
    vars: fnv::FnvHashMap<String, (Var, Var)>, // "x" -> (x, α)
    defs: fnv::FnvHashMap<Name, Rc<dyn OConst>>,
    stack: Vec<Obj>,
    dict: fnv::FnvHashMap<usize, Obj>,
    assumptions: Vec<Thm>,
    theorems: Vec<Thm>,
}

impl<'a> VM<'a> {
    /// Create a new VM using the given expression manager.
    pub fn new(em: &'a mut ExprManager) -> Self {
        VM {
            em,
            ty_vars: fnv::new_table_with_cap(32),
            vars: fnv::new_table_with_cap(32),
            defs: fnv::new_table_with_cap(32),
            stack: vec![],
            dict: fnv::new_table_with_cap(32),
            assumptions: vec![],
            theorems: vec![],
        }
    }

    /// Turn into an article.
    pub fn into_article(self) -> Article {
        let VM { defs, assumptions, theorems, .. } = self;
        Article { defs, assumptions, theorems }
    }

    pub fn article_snapshot(&self) -> Article {
        Article {
            defs: self.defs.clone(),
            assumptions: self.assumptions.clone(),
            theorems: self.theorems.clone(),
        }
    }

    #[inline]
    fn push(&mut self, o: Obj) {
        eprintln!("vm.push {:?}", &o);
        self.stack.push(o)
    }

    fn push_obj(&mut self, o: ObjImpl) {
        self.push(Obj(Rc::new(o)))
    }

    fn pop1<F, A>(&mut self, what: &str, f: F) -> Result<A, String>
    where
        F: Fn(&mut Self, Obj) -> Result<A, String>,
    {
        if self.stack.len() < 1 {
            Err(format!("OT.pop1.{}: empty stack in {:?}", what, self))?
        }
        let x = self.stack.pop().unwrap();
        f(self, x).map_err(|e| format!("{}\nin {:?}", e, self))
    }

    fn pop2<F, A>(&mut self, what: &str, f: F) -> Result<A, String>
    where
        F: Fn(&mut Self, Obj, Obj) -> Result<A, String>,
    {
        if self.stack.len() < 2 {
            Err(format!("OT.pop2.{}: empty stack in {:#?}", what, self))?
        }
        let x = self.stack.pop().unwrap();
        let y = self.stack.pop().unwrap();
        f(self, x, y).map_err(|e| format!("{}\nin {:#?}", e, self))
    }

    fn pop3<F, A>(&mut self, what: &str, f: F) -> Result<A, String>
    where
        F: Fn(&mut Self, Obj, Obj, Obj) -> Result<A, String>,
    {
        if self.stack.len() < 3 {
            Err(format!("OT.pop3.{}: empty stack in {:#?}", what, self))?
        }
        let x = self.stack.pop().unwrap();
        let y = self.stack.pop().unwrap();
        let z = self.stack.pop().unwrap();
        f(self, x, y, z).map_err(|e| format!("{}\nin {:#?}", e, self))
    }

    fn abs_term(&mut self) -> Result<(), String> {
        self.pop2("abs_term", |vm, x, y| match (&*x, &*y) {
            (O::Term(body), O::Var(v)) => {
                let e = vm.em.mk_lambda(v.clone(), body.clone());
                vm.push_obj(O::Term(e));
                Ok(())
            }
            _ => Err(format!(
                "abs_term: expected <term,var>, got {:?},{:?}",
                x, y
            )),
        })
    }

    fn abs_thm(&mut self) -> Result<(), String> {
        todo!("abs_thm")
    }
    fn app_term(&mut self) -> Result<(), String> {
        self.pop2("app_term", |vm, x, y| match (&*x, &*y) {
            (O::Term(x), O::Term(f)) => {
                let e = vm.em.mk_app(f.clone(), x.clone());
                vm.push_obj(O::Term(e));
                Ok(())
            }
            _ => Err(format!(
                "app_term: expected <term,term>, got {:?},{:?}",
                x, y
            )),
        })
    }
    fn app_thm(&mut self) -> Result<(), String> {
        todo!("app_thm")
    }
    fn assume(&mut self) -> Result<(), String> {
        todo!("assume")
    }
    fn axiom(&mut self) -> Result<(), String> {
        self.pop2("axiom", |vm, x, y| match (&*x, &*y) {
            (O::Term(concl), O::List(hyps_)) => {
                let mut hyps = Vec::with_capacity(hyps_.len());
                for x in hyps_ {
                    if let O::Term(t) = &*x.0 {
                        hyps.push(t.clone())
                    } else {
                        return Err(format!(
                            "axiom: hyps contain non-term {:?}",
                            x
                        ));
                    }
                }
                let ax = vm.em.thm_axiom(hyps, concl.clone());
                eprintln!("## add axiom {:?}", ax);
                vm.assumptions.push(ax.clone());
                vm.push_obj(O::Thm(ax));
                Ok(())
            }
            _ => Err(format!(
                "axiom: expected <term,list>, got {:?}, {:?}",
                x, y
            ))?,
        })
    }
    fn version(&mut self) -> Result<(), String> {
        self.pop1("version", |_vm, o| match *o {
            O::Int(6) => Ok(()),
            _ => Err(format!(
                "OpenTheory: unsupported version -> Result<(), String> {:?}",
                o
            )),
        })
    }
    fn nil(&mut self) -> Result<(), String> {
        self.push_obj(O::List(vec![]));
        Ok(())
    }
    fn type_op(&mut self) -> Result<(), String> {
        // builder for bool
        #[derive(Debug, Clone)]
        struct TyOpBool;
        impl OTypeOp for TyOpBool {
            fn apply(
                &self,
                em: &mut ExprManager,
                args: Vec<Expr>,
            ) -> Result<Expr, String> {
                if args.len() != 0 {
                    Err(format!("bool takes no arguments"))
                } else {
                    Ok(em.mk_bool())
                }
            }
        };

        // builder for arrow
        #[derive(Debug, Clone)]
        struct TyOpArrow;
        impl OTypeOp for TyOpArrow {
            fn apply(
                &self,
                em: &mut ExprManager,
                mut args: Vec<Expr>,
            ) -> Result<Expr, String> {
                if args.len() != 2 {
                    return Err(format!("-> takes 2 arguments"));
                };
                let ty2 = args.pop().unwrap();
                let ty1 = args.pop().unwrap();
                debug_assert!(args.is_empty());
                Ok(em.mk_arrow(ty1, ty2))
            }
        }

        self.pop1("type op", |vm, o| match &*o {
            O::Name(n) if n.len_pre() == 0 && n.base() == "bool" => {
                Ok(vm.push_obj(O::TypeOp(n.clone(), Rc::new(TyOpBool))))
            }
            O::Name(n) if n.len_pre() == 0 && n.base() == "->" => {
                Ok(vm.push_obj(O::TypeOp(n.clone(), Rc::new(TyOpArrow))))
            }
            _ => Err(format!("unknown operator {:?}", o)),
        })
    }
    fn def(&mut self) -> Result<(), String> {
        self.pop2("def", |vm, k, x| match &*k {
            O::Int(i) => {
                vm.dict.insert(*i, x.clone());
                vm.push(x); // push x back
                Ok(())
            }
            _ => Err(format!("def: expected int, got {:?}", k)),
        })
    }
    fn cons(&mut self) -> Result<(), String> {
        let a =
            self.pop2("cons", |_vm, mut a, b| match Rc::make_mut(&mut a.0) {
                O::List(ref mut v) => {
                    v.insert(0, b);
                    Ok(a)
                }
                _ => Err(format!(
                    "expected a as second arg list, got {:?}, {:?}",
                    a, b
                )),
            })?;
        self.push(a);
        Ok(())
    }
    fn ref_(&mut self) -> Result<(), String> {
        self.pop1("ref", |vm, o| match &*o {
            O::Int(n) => {
                if let Some(x) = vm.dict.get(n) {
                    let x = x.clone();
                    vm.push(x); // lookup and push
                    Ok(())
                } else {
                    Err(format!("ref: int {} not defined in dictionary", n))
                }
            }
            _ => Err(format!("ref: expected int, got {:?}", o)),
        })
    }
    fn var_type(&mut self) -> Result<(), String> {
        self.pop1("var_type", |vm, o| match &*o {
            O::Name(n) => {
                if n.len_pre() != 0 {
                    Err("var_type: need unqualified name")?
                }
                // make a type variable
                let ty = vm.em.mk_ty();
                let v = vm.em.mk_var_str(&n.ptr.1, ty);
                vm.push_obj(O::Type(v));
                Ok(())
            }
            _ => Err(format!("var_type: expected name, got {:?}", o)),
        })
    }
    fn op_type(&mut self) -> Result<(), String> {
        self.pop2("op type", |vm, o1, o2| match (&*o1, &*o2) {
            (O::List(l), O::TypeOp(_, f)) => {
                let args: Result<Vec<Expr>, String> = l
                    .iter()
                    .map(|x| match &**x {
                        O::Type(a) => Ok(a.clone()),
                        _ => Err(format!(
                            "in op type: expected type, got {:?}",
                            x
                        )),
                    })
                    .collect();
                let args = args?;
                let r = (&**f as &dyn OTypeOp).apply(&mut vm.em, args)?;
                vm.push_obj(O::Type(r));
                Ok(())
            }
            _ => Err(format!(
                "op_type: expected <list,typeop>, got {:?}, {:?}",
                o1, o2
            )),
        })
    }
    fn const_(&mut self) -> Result<(), String> {
        #[derive(Debug)]
        struct ConstEq;
        impl OConst for ConstEq {
            fn apply(
                &self,
                em: &mut ExprManager,
                ty: Expr,
            ) -> Result<Expr, String> {
                let args = ty.unfold_pi().0;
                if args.len() != 2 {
                    Err(format!("`=` cannot take type {:?}", ty))?
                }
                let e = em.mk_eq();
                Ok(em.mk_app(e, args[0].clone()))
            }
        }
        #[derive(Debug)]
        struct ConstSelect;
        impl OConst for ConstSelect {
            fn apply(
                &self,
                em: &mut ExprManager,
                ty: Expr,
            ) -> Result<Expr, String> {
                let a = ty
                    .as_pi()
                    .ok_or_else(|| {
                        format!("`select` cannot take type {:?}", ty)
                    })?
                    .1;
                let e = em.mk_select();
                Ok(em.mk_app(e, a.clone()))
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
                            return Err(format!(
                                "const: undefined constant {:?}",
                                n
                            ));
                        }
                    }
                };
                vm.push_obj(O::Const(n.clone(), oc));
                Ok(())
            }
            _ => Err(format!("const: expected <name>, got {:?}", o)),
        })
    }
    fn const_term(&mut self) -> Result<(), String> {
        self.pop2("const term", |vm, x, y| match (&*x, &*y) {
            (O::Type(ty), O::Const(_, c)) => {
                // apply constant to type
                let e = (&**c as &dyn OConst).apply(vm.em, ty.clone())?;
                vm.push_obj(O::Term(e));
                Ok(())
            }
            _ => Err(format!(
                "const_term: expected <type,const>, got {:?}, {:?}",
                x, y
            )),
        })
    }
    fn var(&mut self) -> Result<(), String> {
        self.pop2("var", |vm, x, y| match (&*x, &*y) {
            (O::Type(ty), O::Name(n)) => {
                // TODO: avoid allocating intermediate `String`
                let v = Var::new(Symbol::from_str(&n.to_string()), ty.clone());
                vm.push_obj(O::Var(v));
                Ok(())
            }
            _ => {
                Err(format!("var: expected <type,name>, got {:?}, {:?}", x, y))
            }
        })
    }
    fn var_term(&mut self) -> Result<(), String> {
        self.pop1("var_term", |vm, o| match &*o {
            O::Var(v) => {
                let e = vm.em.mk_var(v.clone());
                vm.push_obj(O::Term(e));
                Ok(())
            }
            _ => Err(format!("var_term: expected <var>, got {:?}", o)),
        })
    }
    fn define_const(&mut self) -> Result<(), String> {
        #[derive(Debug)]
        struct CustomConst {
            n: Name,
            c: Expr,
            c_ty_vars: Expr, // c applied to type variables
            ty_vars: Vec<Var>,
        }

        impl OConst for CustomConst {
            fn apply(
                &self,
                em: &mut ExprManager,
                ty: Expr,
            ) -> Result<Expr, String> {
                let subst =
                    utils::unify(&self.c_ty_vars, &ty).ok_or_else(|| {
                        format!(
                            "unification failed\n  between {:?} and {:?}\n  \
                            when applying constant {:?}",
                            self.c_ty_vars, ty, self.n
                        )
                    })?;
                eprintln!(
                    "unified:\n  between {:?} and {:?}\n  yields {:?}",
                    self.c_ty_vars, ty, subst
                );
                let vars: Vec<Expr> = self
                    .ty_vars
                    .iter()
                    .map(|v| match subst.find_rec(&v) {
                        Some(e) => e.clone(),
                        None => em.mk_var(v.clone()),
                    })
                    .collect();
                let t = em.mk_app_l(self.c.clone(), &vars);
                eprintln!("result constant is {:?}", &t);
                Ok(t)
            }
        }

        self.pop2("define const", |vm, x, y| match (&*x, &*y) {
            (O::Term(rhs), O::Name(n)) => {
                // make a definition `n := t`
                let (thm, c, ty_vars) = utils::thm_new_poly_definition(
                    &mut vm.em,
                    &n.to_string(),
                    rhs.clone(),
                )?;
                eprintln!(
                    "define const {:?} with thm {:?} and vars {:?}",
                    n, thm, ty_vars
                );
                // type of `c` applied to `vars`
                let e_vars: Vec<_> =
                    ty_vars.iter().cloned().map(|v| vm.em.mk_var(v)).collect();
                let app = vm.em.mk_app_l(c.clone(), &e_vars);
                let c_ty_vars = app.ty().clone();
                // now build the constant building closure
                let c = Rc::new(CustomConst {
                    c: c.clone(),
                    ty_vars,
                    c_ty_vars,
                    n: n.clone(),
                });
                // define and push
                vm.defs.insert(n.clone(), c.clone());
                vm.push_obj(O::Const(n.clone(), c));
                vm.push_obj(O::Thm(thm));
                Ok(())
            }
            _ => Err(format!(
                "define const: expected <term,name>, got {:?}, {:?}",
                x, y
            )),
        })
    }
    fn pop(&mut self) -> Result<(), String> {
        if self.stack.pop().is_some() {
            Ok(())
        } else {
            Err("pop: empty stack".to_string())
        }
    }
    fn remove(&mut self) -> Result<(), String> {
        self.pop1("remove", |vm, o| match &*o {
            O::Int(n) => {
                let o = vm.dict.remove(n).ok_or_else(|| {
                    format!("remove: key {:?} not present", n)
                })?;
                vm.push(o);
                Ok(())
            }
            _ => Err(format!("remove: expected int, not {:?}", o)),
        })
    }
    fn thm(&mut self) -> Result<(), String> {
        self.pop3("thm", |vm, x, y, z| match (&*x, &*y, &*z) {
            (O::Term(_phi), O::List(l), O::Thm(thm)) => {
                // TODO: do we need this?
                let mut terms = Vec::with_capacity(l.len());
                for x in l {
                    match &*x.0 {
                        O::Term(t) => terms.push(t),
                        _ => {
                            return Err(format!(
                                "thm: expected term in list, not {:?}",
                                x
                            ))
                        }
                    }
                }
                // TODO?: alpha rename with [terms] and [phi]
                eprintln!("## add theorem {:?} phi={:?}", thm, _phi);
                vm.theorems.push(thm.clone());
                Ok(())
            }
            _ => Err(format!(
                "thm: expected <term, list, thm>, got {:?}, {:?}, {:?}",
                x, y, z
            )),
        })
    }
    fn subst(&mut self) -> Result<(), String> {
        todo!("subst")
    }
    fn refl(&mut self) -> Result<(), String> {
        todo!("refl")
    }
    fn trans(&mut self) -> Result<(), String> {
        todo!("trans")
    }
    fn sym(&mut self) -> Result<(), String> {
        todo!("sym")
    }
    fn eq_mp(&mut self) -> Result<(), String> {
        todo!("eq_mp")
    }
    fn beta_conv(&mut self) -> Result<(), String> {
        todo!("beta_conv")
    }
    fn deduct_antisym(&mut self) -> Result<(), String> {
        todo!("deduct_antisym")
    }
    fn prove_hyp(&mut self) -> Result<(), String> {
        todo!("prove_hyp")
    }

    /// Parse the given reader.
    pub fn parse_str(&mut self, buf: &mut dyn BufRead) -> Result<(), String> {
        // skip empty lines and comments

        for line in buf.lines() {
            let line = line.map_err(|e| format!("error {:?}", e))?;
            let line = line.trim();
            eprintln!("// parse line {}", line);
            if line.starts_with("#") {
                continue;
            } else if line.starts_with("\"") {
                let name = Name::parse(line).ok_or_else(|| {
                    format!("cannot parse name from line {:?}", line)
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
                    "cons" => self.cons()?,
                    "ref" => self.ref_()?,
                    "varType" => self.var_type()?,
                    "opType" => self.op_type()?,
                    "const" => self.const_()?,
                    "constTerm" => self.const_term()?,
                    "var" => self.var()?,
                    "varTerm" => self.var_term()?,
                    "defineConst" => self.define_const()?,
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
                    _ => Err(format!("unknown command {:?}", line))?,
                }
            }
        }

        Ok(())
    }
}
