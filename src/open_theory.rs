//! Parser and interpreter for [OpenTheory](http://www.gilith.com/opentheory/article.html)

use {
    crate::kernel_of_trust as k, crate::*, std::fmt, std::io::BufRead,
    std::rc::Rc,
};

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
struct Name(Rc<(Vec<String>, String)>);

#[derive(Clone, Debug)]
struct Obj(Rc<ObjImpl>);

#[derive(Clone)]
struct TypeOp(Rc<dyn Fn(&mut k::ExprManager, &[Expr]) -> Expr>);

impl fmt::Debug for TypeOp {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "<type op>")
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
    Int(isize),
    Name(Name),
    List(Vec<Obj>),
    TypeOp(Name, TypeOp),
    Type(Expr),
    Const(Name, Expr),
    Var(Var),
    Term(Expr),
    Thm(Thm),
}

use ObjImpl as O;

impl Name {
    pub fn to_string(&self) -> String {
        let mut s = String::new();
        let &(ref pre, ref base) = &*self.0;
        for x in pre.iter() {
            s += x.as_str();
            s += ".";
        }
        s += base.as_str();
        s
    }

    /// Parse a line into a name
    pub fn parse(s: &str) -> Option<Self> {
        let s = s.trim();
        if s.as_bytes()[0] != b'"' || s.as_bytes()[s.len() - 1] != b'"' {
            return None;
        }

        let s = &s[1..s.len() - 2];
        let toks: Vec<&str> = s.split(".").collect();
        let pre =
            toks[0..toks.len() - 1].iter().map(|s| s.to_string()).collect();
        let base = toks[toks.len() - 1].to_string();
        Some(Name(Rc::new((pre, base))))
    }
}

/// An article obtained by interpreting a theory file.
#[derive(Debug)]
pub struct Article {
    defs: fnv::FnvHashMap<Name, Expr>,
    assumptions: Vec<Thm>,
    theorems: Vec<Thm>,
}

/// Virtual machine.
///
/// This is used to parse and interpret an OpenTheory file.
#[derive(Debug, Clone)]
pub struct VM {
    ty_vars: fnv::FnvHashMap<String, Var>,
    vars: fnv::FnvHashMap<String, (Var, Var)>, // "x" -> (x, α)
    defs: fnv::FnvHashMap<Name, Expr>,
    stack: Vec<Obj>,
    dict: fnv::FnvHashMap<usize, Obj>,
    assumptions: Vec<Thm>,
    theorems: Vec<Thm>,
}

impl VM {
    /// Create a new VM.
    pub fn new() -> Self {
        VM {
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
        f(self, x)
    }

    fn pop2<F, A>(&mut self, what: &str, f: F) -> Result<A, String>
    where
        F: Fn(&mut Self, Obj, Obj) -> Result<A, String>,
    {
        if self.stack.len() < 2 {
            Err(format!("OT.pop2.{}: empty stack in {:?}", what, self))?
        }
        let x = self.stack.pop().unwrap();
        let y = self.stack.pop().unwrap();
        f(self, x, y)
    }

    fn pop3<F, A>(&mut self, what: &str, f: F) -> Result<A, String>
    where
        F: Fn(&mut Self, Obj, Obj, Obj) -> Result<A, String>,
    {
        if self.stack.len() < 3 {
            Err(format!("OT.pop3.{}: empty stack in {:?}", what, self))?
        }
        let x = self.stack.pop().unwrap();
        let y = self.stack.pop().unwrap();
        let z = self.stack.pop().unwrap();
        f(self, x, y, z)
    }

    fn abs_term(&mut self) -> Result<(), String> {
        todo!("abs_term")
    }

    fn abs_thm(&mut self) -> Result<(), String> {
        todo!("abs_thm")
    }
    fn app_term(&mut self) -> Result<(), String> {
        todo!("app_term")
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
        todo!("type op")
    }
    fn def(&mut self) -> Result<(), String> {
        todo!("def")
    }
    fn cons(&mut self) -> Result<(), String> {
        let a =
            self.pop2("cons", |_vm, mut a, b| match Rc::make_mut(&mut a.0) {
                O::List(ref mut v) => {
                    v.push(b);
                    Ok(a)
                }
                _ => Err(format!("expected a list {:?}", b)),
            })?;
        self.push(a);
        Ok(())
    }
    fn ref_(&mut self) -> Result<(), String> {
        todo!("ref")
    }
    fn var_type(&mut self) -> Result<(), String> {
        todo!("var_type")
    }
    fn op_type(&mut self) -> Result<(), String> {
        todo!("op_type")
    }
    fn const_(&mut self) -> Result<(), String> {
        todo!("const")
    }
    fn const_term(&mut self) -> Result<(), String> {
        todo!("const_term")
    }
    fn var(&mut self) -> Result<(), String> {
        todo!("var")
    }
    fn var_term(&mut self) -> Result<(), String> {
        todo!("var_term")
    }
    fn define_const(&mut self) -> Result<(), String> {
        todo!("define_const")
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
            if line.starts_with("#") {
                continue;
            } else if line.starts_with("\"") {
                let name = Name::parse(line).ok_or_else(|| {
                    format!("cannot parse name from line {:?}", line)
                })?;
                self.push_obj(ObjImpl::Name(name))
            } else if let Ok(i) = line.parse::<isize>() {
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
