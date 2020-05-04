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
#[derive(Clone)]
struct OTypeOp(
    Rc<dyn Fn(&mut k::ExprManager, Vec<Expr>) -> Result<Expr, String>>,
);

impl fmt::Debug for Obj {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

impl fmt::Debug for OTypeOp {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "<type op>")
    }
}

/// A constant, parametrized by its type.
#[derive(Clone)]
pub struct OConst(
    Rc<dyn Fn(&mut k::ExprManager, Expr) -> Result<Expr, String>>,
);

impl fmt::Debug for OConst {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "<const>>")
    }
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
    TypeOp(Name, OTypeOp),
    Type(Expr),
    Const(Name, OConst),
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
    defs: fnv::FnvHashMap<Name, OConst>,
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
    defs: fnv::FnvHashMap<Name, OConst>,
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
                let e = vm.em.mk_lambda_abs(v.clone(), body.clone());
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
        todo!("axiom")
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
        self.pop1("type op", |vm, o| match &*o {
            O::Name(n) if n.len_pre() == 0 && n.base() == "bool" => {
                let tyop = |em: &mut ExprManager, args: Vec<Expr>| {
                    if args.len() != 0 {
                        Err(format!("bool takes no arguments"))
                    } else {
                        Ok(em.mk_bool())
                    }
                };
                Ok(vm.push_obj(O::TypeOp(n.clone(), OTypeOp(Rc::new(tyop)))))
            }
            O::Name(n) if n.len_pre() == 0 && n.base() == "->" => {
                let tyop = |em: &mut ExprManager, mut args: Vec<Expr>| {
                    if args.len() != 2 {
                        return Err(format!("-> takes 2 arguments"));
                    };
                    let ty2 = args.pop().unwrap();
                    let ty1 = args.pop().unwrap();
                    debug_assert!(args.is_empty());
                    Ok(em.mk_arrow(ty1, ty2))
                };
                Ok(vm.push_obj(O::TypeOp(n.clone(), OTypeOp(Rc::new(tyop)))))
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
                let r = (*f.0)(&mut vm.em, args)?;
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
        self.pop1("const", |vm, o| match &*o {
            O::Name(n) => {
                let oc = match n.base() {
                    "=" if n.len_pre() == 0 => {
                        let oc = |em: &mut ExprManager, ty: Expr| {
                            let args = ty.unfold_pi().0;
                            if args.len() != 2 {
                                Err(format!("= cannot take type {:?}", ty))?
                            }
                            let e = em.mk_eq();
                            Ok(em.mk_app(e, args[0].clone()))
                        };
                        OConst(Rc::new(oc))
                    }
                    "select" if n.len_pre() == 0 => {
                        todo!("select")
                        /* TODO: generate the select constant
                        let oc = |em: &mut ExprManager, ty: Expr| {
                            let e = em.mk_s();
                            Ok(em.mk_app(e, ty))
                        };
                        OConst(Rc::new(oc))
                        */
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
                let e = (*c.0)(vm.em, ty.clone())?;
                vm.push_obj(O::Term(e));
                Ok(())
            }
            _ => Err(format!(
                "const_term: expected <type,conts>, got {:?}, {:?}",
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
        self.pop2("define const", |vm, x, y| match (&*x, &*y) {
            (O::Term(t), O::Name(n)) => {
                // make a definition `n := t`
                todo!() // TODO: use utils.thm_new_poly_definition
            }
            _ => Err(format!(
                "define const: expected <term,name>, got {:?}, {:?}",
                x, y
            )),
        })
    }
    fn pop(&mut self) -> Result<(), String> {
        todo!("pop")
    }
    fn remove(&mut self) -> Result<(), String> {
        todo!("remove")
    }
    fn thm(&mut self) -> Result<(), String> {
        todo!("thm")
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
            eprintln!("# parse line {}", line);
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
