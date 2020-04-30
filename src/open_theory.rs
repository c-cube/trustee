//! Parser and interpreter for [OpenTheory](http://www.gilith.com/opentheory/article.html)

use {
    crate::kernel_of_trust as k, crate::*, std::fmt, std::io::BufRead,
    std::rc::Rc,
};

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
struct Name(Rc<(Vec<String>, String)>);

#[derive(Clone, Debug)]
struct Obj(Rc<ObjImpl>);

struct TypeOp(Box<dyn Fn(&mut k::ExprManager, &[Expr]) -> Expr>);

impl fmt::Debug for TypeOp {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "<type op>")
    }
}

/// An object for the VM
#[derive(Debug)]
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
        dbg!("vm.push", &o);
        self.stack.push(o)
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

    /// Parse the given reader.
    pub fn parse_str(&mut self, buf: &mut dyn BufRead) -> Result<(), String> {
        // skip empty lines and comments

        for line in buf.lines() {
            let line = line.map_err(|e| format!("error {:?}", e))?;
            let line = line.trim();
            if line.starts_with("#") {
                continue;
            }

            dbg!("process line", line);
            // process line
            todo!() // TODO
        }

        Ok(())
    }
}
