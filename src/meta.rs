//! Meta-language.
//!
//! The meta-language is a postscript-like stack language that manipulates
//! expressions, goals, theorems, and other values. It is designed to be
//! used both interactively and as an efficient way of storing proofs.

use {
    crate::{
        fnv::FnvHashMap,
        kernel_of_trust::{self as k, CtxI},
        syntax, Error, Result,
    },
    std::{cell::RefCell, fmt, rc::Rc},
};

/// The state of the meta-language interpreter.
pub struct State<'a> {
    pub ctx: &'a mut dyn CtxI,
    pub stack: Vec<Value>,
    /// Current instruction.
    cur_i: Option<Instr>,
    /// Nested scopes to handle definitions in local dictionaries.
    ///
    /// The toplevel dictionary (at index 0) is the system dictionary.
    scopes: RefCell<Vec<Dict<CodeArray>>>,
    /// Control stack, for function call.
    ctrl_stack: Vec<(CodeArray, usize)>,
}

#[derive(Clone, Debug)]
pub struct CodeArray(Rc<Vec<Instr>>);

#[derive(Clone, Debug)]
pub struct Dict<T>(FnvHashMap<Rc<str>, T>);

/// A value of the language.
#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Sym(Rc<str>),
    //Var(Var),
    Expr(k::Expr),
    Thm(k::Thm),
    CodeArray(CodeArray),
    Array(Rc<Vec<Value>>),
    Dict(Dict<Value>),
    // TODO: Goal? Goals? Tactic?
}

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        use Value::*;

        match (self, other) {
            (Int(i), Int(j)) => i == j,
            (Bool(i), Bool(j)) => i == j,
            (Sym(i), Sym(j)) => i == j,
            (Expr(i), Expr(j)) => i == j,
            _ => false,
        }
    }
}

/// An instruction of the language.
#[derive(Debug, Clone)]
enum Instr {
    /// A core instruction.
    Core(InstrCore),
    /// A rust builtin.
    Builtin(&'static dyn InstrBuiltin),
    /// Immediate value (push itself on stack)
    Im(Value),
    /// Call a word defined using this code array.
    Call(CodeArray),
}

// NOTE: modify `INSTR_CORE` below when modifying this.
/// Core operations: control flow and arithmetic.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum InstrCore {
    Def,
    For,
    If,
    IfElse,
    Loop,
    Exit,
    Dup,
    Exch,
    Drop,
    Rot,
    Begin,
    End,
    Eq,
    Lt,
    Gt,
    Leq,
    Geq,
    Add,
    Mul,
    Sub,
    Div,
    Mod,
    PrintPop,
    PrintStack,
    Clear,
    // TODO: array get, put, push, create
}

/// A custom instruction implemented in rust.
///
/// This is the most direct way of writing efficient "tactics" directly
/// in rust.
pub trait InstrBuiltin: fmt::Debug {
    /// Name of the instruction. The instruction is invoked by its name.
    ///
    /// The name should be consistent with lexical conventions (no whitespaces,
    /// brackets, backquotes, etc.)
    fn name(&self) -> &'static str;

    /// Execute the instruction on the given state.
    fn run(&self, st: &mut State) -> Result<()>;

    /// A one-line help text for this instruction.
    fn help(&self) -> String {
        self.name().to_string()
    }
}

pub(crate) mod parser {
    /// A parser for RPN-like syntax, inspired from postscript.
    pub struct Parser<'b> {
        col: usize,
        line: usize,
        i: usize,
        bytes: &'b [u8],
        cur_: Option<Tok<'b>>,
    }

    // TODO: [ ] for value arrays.
    /// A token for the RPN syntax..
    #[derive(Clone, Copy, Debug, PartialEq)]
    pub enum Tok<'b> {
        Eof,
        Id(&'b str),         // identifier
        QuotedId(&'b str),   // '/' identifier
        QuotedExpr(&'b str), // `some expr`
        Int(i64),
        LBracket,
        RBracket,
        Invalid(char),
    }

    #[inline]
    fn is_id_char(c: u8) -> bool {
        match c {
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => true,
            _ => false,
        }
    }

    impl<'b> Parser<'b> {
        #[inline]
        pub fn eof(&self) -> bool {
            self.i >= self.bytes.len()
        }

        pub fn loc(&self) -> (usize, usize) {
            (self.line, self.col)
        }

        fn skip_white_(&mut self) {
            while self.i < self.bytes.len() {
                let c = self.bytes[self.i];
                if c == b' ' || c == b'\t' {
                    self.i += 1;
                    self.col += 1;
                } else if c == b'\n' {
                    self.i += 1;
                    self.line += 1;
                    self.col = 1
                } else {
                    return;
                }
            }
        }

        /// Next token.
        pub fn next(&mut self) -> Tok {
            self.skip_white_();
            if self.eof() {
                self.cur_ = Some(Tok::Eof);
                return Tok::Eof;
            }
            let tok = match self.bytes[self.i] {
                b'{' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::LBracket
                }
                b'}' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::RBracket
                }
                b'`' => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && self.bytes[j] != b'`' {
                        j += 1;
                    }
                    let src_expr =
                        std::str::from_utf8(&self.bytes[self.i + 1..j])
                            .expect("invalid utf8 slice");
                    self.col += j - self.i + 1;
                    self.i = j + 1;
                    Tok::QuotedExpr(src_expr)
                }
                b'/' => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && {
                        let c = self.bytes[j];
                        is_id_char(c) || c.is_ascii_digit()
                    } {
                        j += 1;
                    }
                    let tok = std::str::from_utf8(&self.bytes[self.i + 1..j])
                        .expect("invalid utf8 slice");
                    self.col += j - self.i + 1;
                    self.i = j + 1;
                    Tok::QuotedId(tok)
                }
                c if is_id_char(c) => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && {
                        let c = self.bytes[j];
                        is_id_char(c) || c.is_ascii_digit()
                    } {
                        j += 1;
                    }
                    let tok = std::str::from_utf8(&self.bytes[self.i..j])
                        .expect("invalid utf8 slice");
                    self.col += j - self.i;
                    self.i = j + 1;
                    Tok::Id(tok)
                }
                c if c.is_ascii_digit() || c == b'-' => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && self.bytes[j].is_ascii_digit()
                    {
                        j += 1;
                    }
                    let tok = std::str::from_utf8(&self.bytes[self.i..j])
                        .expect("invalid utf8 slice");
                    let n = str::parse(tok).expect("cannot parse int");
                    self.col += j - self.i;
                    self.i = j + 1;
                    Tok::Int(n)
                }
                c => Tok::Invalid(std::char::from_u32(c as u32).unwrap()),
            };
            self.cur_ = Some(tok);
            tok
        }

        /// Current token.
        pub fn cur(&mut self) -> Tok {
            if let Some(c) = self.cur_ {
                c
            } else {
                self.next()
            }
        }

        /// New parser.
        pub fn new(s: &'b str) -> Self {
            Self { col: 1, line: 1, i: 0, bytes: s.as_bytes(), cur_: None }
        }
    }
}

mod ml {
    use super::*;

    impl CodeArray {
        fn new(v: Vec<Instr>) -> Self {
            CodeArray(Rc::new(v))
        }
    }

    impl<T> Dict<T> {
        fn new() -> Self {
            Dict(FnvHashMap::default())
        }
    }

    /// All the core instructions.
    const INSTR_CORE: &'static [InstrCore] = {
        use InstrCore::*;
        &[
            Def, For, If, IfElse, Loop, Exit, Dup, Exch, Drop, Rot, Begin, End,
            Eq, Lt, Gt, Leq, Geq, Add, Mul, Sub, Div, Mod, PrintPop,
            PrintStack, Clear,
        ]
    };

    impl InstrBuiltin for InstrCore {
        fn name(&self) -> &'static str {
            use InstrCore::*;

            match self {
                Def => "def",
                For => "for",
                If => "if",
                IfElse => "if",
                Loop => "loop",
                Exit => "exit",
                Dup => "dup",
                Exch => "exch",
                Drop => "drop",
                Rot => "rot",
                Begin => "begin",
                End => "end",
                Eq => "eq",
                Lt => "lt",
                Gt => "gt",
                Leq => "leq",
                Geq => "geq",
                Add => "add",
                Mul => "mul",
                Sub => "sub",
                Div => "div",
                Mod => "mod",
                PrintPop => "ppop",
                PrintStack => "pstack",
                Clear => "clear",
            }
        }

        fn run(&self, st: &mut State) -> Result<()> {
            use InstrCore::*;

            macro_rules! pop1 {
                () => {
                    match st.stack.pop() {
                        Some(v) => v,
                        _ => return Err(Error::new("stack underflow")),
                    }
                };
            };
            macro_rules! pop1_of {
                ($what: literal, $p: pat, $v: ident) => {
                    match pop1!() {
                        $p => $v,
                        _ => {
                            return Err(Error::new(concat!(
                                "type error: expected ",
                                $what
                            )))
                        }
                    };
                };
            };
            macro_rules! pop1_int {
                () => {
                    pop1_of!("int", Value::Int(i), i)
                };
            };
            macro_rules! pop1_bool {
                () => {
                    pop1_of!("bool", Value::Bool(i), i)
                };
            };
            macro_rules! pop1_codearray {
                () => {
                    pop1_of!("code array", Value::CodeArray(i), i)
                };
            };
            macro_rules! pop1_expr {
                () => {
                    pop1_of!("expr", Value::Expr(i), i)
                };
            };
            macro_rules! pop1_sym {
                () => {
                    pop1_of!("sym", Value::Sym(i), i)
                };
            };

            match self {
                Def => {
                    let c = pop1_codearray!();
                    let sym = pop1_sym!();
                    let mut scopes = st.scopes.borrow_mut();
                    scopes.last_mut().unwrap().0.insert(sym.clone(), c);
                }
                For => {
                    let c = pop1_codearray!();
                    let stop = pop1_int!();
                    let step = pop1_int!();
                    let start = pop1_int!();

                    let mut i = start;
                    while if step > 0 { i <= stop } else { i >= stop } {
                        st.stack.push(Value::Int(i));
                        st.exec_instr_(Instr::Call(c.clone()))?;
                        i += step;
                    }
                }
                If => {
                    let c = pop1_codearray!();
                    let b = pop1_bool!();
                    if b {
                        st.exec_codearray_(c);
                        st.exec_loop_()?;
                    }
                }
                IfElse => {
                    let else_ = pop1_codearray!();
                    let then_ = pop1_codearray!();
                    let b = pop1_bool!();
                    if b {
                        st.exec_codearray_(then_);
                    } else {
                        st.exec_codearray_(else_);
                    }
                    st.exec_loop_()?;
                }
                Loop => todo!("loop"), // TODO
                Exit => todo!("exit"), // TODO
                Dup => match st.stack.last() {
                    Some(v) => {
                        let v = v.clone();
                        st.stack.push(v)
                    }
                    None => return Err(Error::new("stack underflow")),
                },
                Rot => {}
                Exch => {
                    let y = pop1!();
                    let x = pop1!();
                    st.stack.push(y);
                    st.stack.push(x);
                }
                Drop => {
                    let _ = pop1!();
                }
                Begin => {
                    let dict = Dict::new();
                    let mut scopes = st.scopes.borrow_mut();
                    scopes.push(dict)
                }
                End => {
                    let mut scopes = st.scopes.borrow_mut();
                    if scopes.len() < 2 {
                        return Err(Error::new(
                            "`end` does not match a `begin`",
                        ));
                    }
                    scopes.pop();
                }
                Eq => {
                    let y = pop1!();
                    let x = pop1!();
                    st.stack.push(Value::Bool(x == y))
                }
                Lt => {
                    let y = pop1_int!();
                    let x = pop1_int!();
                    st.stack.push(Value::Bool(x < y))
                }
                Gt => {
                    let y = pop1_int!();
                    let x = pop1_int!();
                    st.stack.push(Value::Bool(x > y))
                }
                Leq => {
                    let y = pop1_int!();
                    let x = pop1_int!();
                    st.stack.push(Value::Bool(x <= y))
                }
                Geq => {
                    let y = pop1_int!();
                    let x = pop1_int!();
                    st.stack.push(Value::Bool(x >= y))
                }
                Add => {
                    let y = pop1_int!();
                    let x = pop1_int!();
                    st.stack.push(Value::Int(x + y))
                }
                Mul => {
                    let y = pop1_int!();
                    let x = pop1_int!();
                    st.stack.push(Value::Int(x * y))
                }
                Sub => {
                    let y = pop1_int!();
                    let x = pop1_int!();
                    st.stack.push(Value::Int(x - y))
                }
                Div => {
                    let y = pop1_int!();
                    let x = pop1_int!();
                    if y == 0 {
                        return Err(Error::new("division by zero"));
                    }
                    st.stack.push(Value::Int(x / y))
                }
                Mod => {
                    let y = pop1_int!();
                    let x = pop1_int!();
                    if y == 0 {
                        return Err(Error::new("division by zero"));
                    }
                    st.stack.push(Value::Int(x % y))
                }
                PrintPop => {
                    let x = pop1!();
                    println!("  {:?}", x);
                }
                PrintStack => {
                    println!("stack:");
                    for x in st.stack.iter().rev() {
                        println!("  > {:?}", x);
                    }
                }
                Clear => st.stack.clear(),
            }
            Ok(())
        }
    }

    macro_rules! perror {
        ($loc: ident, $fmt: literal) => {
            Error::new_string(format!(
                        concat!( "parse error at {:?}: ", $fmt), $loc))
        };
        ($loc: ident, $fmt: literal, $($arg:expr ),*) => {
            Error::new_string(format!(
                        concat!( "parse error at {:?}: ", $fmt), $loc,
                        $($arg),*))
        };
    }

    impl<'a> State<'a> {
        /// Create a new state.
        pub fn new(ctx: &'a mut dyn CtxI) -> Self {
            // system-level dictionary
            let mut scope0 = Dict::new();
            {
                for ic in INSTR_CORE {
                    let name: Rc<str> = ic.name().into();
                    let ca = CodeArray::new(vec![Instr::Core(*ic)]);
                    scope0.0.insert(name, ca);
                }
                for b in BUILTINS {
                    let name: Rc<str> = b.name().into();
                    let ca = CodeArray::new(vec![Instr::Builtin(*b)]);
                    scope0.0.insert(name, ca);
                }
            }
            Self {
                ctx,
                cur_i: None,
                stack: vec![],
                scopes: RefCell::new(vec![scope0]),
                ctrl_stack: vec![],
            }
        }

        /// Parse an instruction, which is either a word invokation
        /// or the construction of a value to push onto the stack.
        fn parse_instr_(&mut self, p: &mut parser::Parser) -> Result<Instr> {
            use parser::*;

            let loc = p.loc();
            match p.cur() {
                Tok::Eof => return Err(Error::new("unexpected EOF")),
                Tok::RBracket => return Err(Error::new("unexpected '}'")),
                Tok::Invalid(c) => {
                    return Err(perror!(loc, "invalid token {:?}", c))
                }
                Tok::Int(i) => {
                    p.next();
                    Ok(Instr::Im(Value::Int(i)))
                }
                Tok::QuotedId(s) => {
                    let v = Value::Sym(s.into());
                    p.next();
                    Ok(Instr::Im(v))
                }
                Tok::QuotedExpr(s) => {
                    let e = syntax::parse_expr(self.ctx, s)?;
                    p.next();
                    Ok(Instr::Im(Value::Expr(e)))
                }
                Tok::LBracket => {
                    // parse an array of instructions.
                    p.next();
                    let mut ca = vec![];
                    let v = loop {
                        match p.cur() {
                            Tok::RBracket => {
                                p.next();
                                let ca = CodeArray::new(ca);
                                break Value::CodeArray(ca);
                            }
                            _ => {
                                let instr = self.parse_instr_(p)?;
                                ca.push(instr);
                            }
                        }
                    };
                    Ok(Instr::Im(v))
                }
                Tok::Id("true") => {
                    p.next();
                    Ok(Instr::Im(Value::Bool(true)))
                }
                Tok::Id("false") => {
                    p.next();
                    Ok(Instr::Im(Value::Bool(false)))
                }
                Tok::Id(s) => {
                    // Find definition of symbol `s` in `self.scopes`,
                    // starting from the most recent scope.
                    let scopes = self.scopes.borrow();
                    let i = match scopes.iter().rev().find_map(|d| d.0.get(&*s))
                    {
                        None => {
                            return Err(perror!(loc, "unknown word: {}", s))
                        }
                        Some(ca) if ca.0.len() == 1 => ca.0[0].clone(),
                        Some(ca) => Instr::Call(ca.clone()),
                    };
                    p.next();
                    Ok(i)
                }
            }
        }

        /// Execute instruction `i`.
        fn exec_instr_(&mut self, i: Instr) -> Result<()> {
            match i {
                Instr::Im(v) => self.stack.push(v),
                Instr::Builtin(b) => {
                    b.run(self)?;
                }
                Instr::Call(ca) => {
                    // start execution of this block of code
                    self.cur_i = Some(ca.0[0].clone());
                    if ca.0.len() > 1 {
                        self.ctrl_stack.push((ca, 1));
                    }
                }
                Instr::Core(c) => c.run(self)?,
            }
            Ok(())
        }

        fn exec_codearray_(&mut self, ca: CodeArray) {
            // start execution of this block of code
            self.cur_i = Some(ca.0[0].clone());
            if ca.0.len() > 1 {
                self.ctrl_stack.push((ca, 1));
            }
        }

        fn exec_loop_(&mut self) -> Result<()> {
            'top: loop {
                // consume `self.cur` here and now.
                let mut cur0 = None;
                std::mem::swap(&mut self.cur_i, &mut cur0);
                match cur0 {
                    Some(i) => {
                        self.exec_instr_(i)?;
                    }
                    None => {
                        match self.ctrl_stack.last_mut() {
                            None => break 'top,
                            Some((ca, idx)) => {
                                debug_assert!(*idx < ca.0.len());
                                let i = ca.0[*idx].clone();
                                self.cur_i = Some(i);
                                *idx += 1; // point to next instruction in `ca`
                                if *idx + 1 >= ca.0.len() {
                                    // last instruction: tailcall
                                    self.ctrl_stack.pop();
                                }
                            }
                        }
                    }
                }
            }
            Ok(())
        }

        /// Parse and execute the given code.
        pub fn run(&mut self, s: &str) -> Result<()> {
            use parser::*;
            let mut p = Parser::new(s);

            loop {
                if p.cur() == Tok::Eof {
                    break;
                }

                assert!(self.cur_i.is_none());
                let i = self.parse_instr_(&mut p);
                match i {
                    Err(e) => {
                        let (l, c) = p.loc();
                        let e = e.set_source(k::Error::new_string(format!(
                            "at {}:{}",
                            l, c
                        )));
                        return Err(e);
                    }
                    Ok(i) => {
                        self.cur_i = Some(i);
                        self.exec_loop_()?;
                    }
                }
            }
            Ok(())
        }
    }

    /// Builtin functions.
    const BUILTINS: &'static [&'static dyn InstrBuiltin] = &[
        // TODO: theorem combinators, "load", "prelude_hol" (which pushes a string)

    ];

    /* TODO

    /// Parse a theorem, from combinators.
    fn parse_thm_(&mut self) -> Result<k::Thm> {
        use Tok::*;

        match self.peek_() {
            SYM(s) => {
                if let Some(th) = self.ctx.find_lemma(s) {
                    let th = th.clone();
                    self.next_();
                    Ok(th)
                } else {
                    Err(perror!(self, "unknown theorem '{}'", s))
                }
            }
            LPAREN => {
                self.next_();
                let s = self.parse_sym_()?;
                let bool = self.ctx.mk_bool();
                let r = match s {
                    "axiom" => {
                        let e = self.parse_expr_bp_(0, Some(bool))?;
                        let th = self.ctx.thm_axiom(vec![], e)?;
                        th
                    }
                    "assume" => {
                        let e = self.parse_expr_bp_(0, Some(bool))?;
                        let th = self.ctx.thm_assume(e)?;
                        th
                    }
                    "refl" => {
                        let e = self.parse_expr_bp_(0, None)?;
                        let th = self.ctx.thm_refl(e);
                        th
                    }
                    "sym" => {
                        let th1 = self.parse_thm_()?;
                        let th = crate::algo::thm_sym(self.ctx, th1)?;
                        th
                    }
                    "mp" => {
                        let th1 = self.parse_thm_()?;
                        let th2 = self.parse_thm_()?;
                        let th = self.ctx.thm_mp(th1, th2)?;
                        th
                    }
                    "trans" => {
                        let th1 = self.parse_thm_()?;
                        let th2 = self.parse_thm_()?;
                        let th = self.ctx.thm_trans(th1, th2)?;
                        th
                    }
                    "congr" => {
                        let th1 = self.parse_thm_()?;
                        let th2 = self.parse_thm_()?;
                        let th = self.ctx.thm_congr(th1, th2)?;
                        th
                    }
                    "congr_ty" => {
                        let th1 = self.parse_thm_()?;
                        let ty_ty = self.ctx.mk_ty();
                        let ty = self.parse_expr_bp_(0, Some(ty_ty))?;
                        let th = self.ctx.thm_congr_ty(th1, &ty)?;
                        th
                    }
                    "cut" => {
                        let th1 = self.parse_thm_()?;
                        let th2 = self.parse_thm_()?;
                        let th = self.ctx.thm_cut(th1, th2)?;
                        th
                    }
                    "bool_eq" => {
                        let th1 = self.parse_thm_()?;
                        let th2 = self.parse_thm_()?;
                        let th = self.ctx.thm_bool_eq(th1, th2)?;
                        th
                    }
                    "bool_eq_intro" => {
                        let th1 = self.parse_thm_()?;
                        let th2 = self.parse_thm_()?;
                        let th = self.ctx.thm_bool_eq_intro(th1, th2)?;
                        th
                    }
                    "beta_conv" => {
                        let e = self.parse_expr_bp_(0, Some(bool))?;
                        let th = self.ctx.thm_beta_conv(&e)?;
                        th
                    }
                    // TODO: instantiate
                    // TODO: abs
                    _ => {
                        return Err(perror!(
                            self,
                            "unknown theorem combinator {:?}",
                            s
                        ))
                    }
                };
                self.eat_(RPAREN)?;
                Ok(r)
            }
            t => {
                Err(perror!(self, "expected theorem, unexpected token {:?}", t))
            }
        }
    }

    /// Parse a toplevel statement, `.` terminated.
    fn parse_statement_(&mut self) -> Result<ParseOutput> {
        use Tok::*;

        let r = match self.peek_() {
            SYM("def") => {
                self.next_();
                let id = self.parse_sym_()?;
                self.eat_(SYM("="))?;
                let rhs = self.parse_expr_bp_(0, None)?;
                let v = self.ctx.mk_var_str(id, rhs.ty().clone());
                let v_eq_rhs = self.ctx.mk_eq_app(v, rhs)?;
                let d = self.ctx.thm_new_basic_definition(v_eq_rhs)?;
                self.ctx.define_lemma(&format!("def_{}", id), d.0.clone());
                ParseOutput::Def((d.1, d.0))
            }
            SYM("decl") => {
                self.next_();
                let id = self.parse_sym_()?;
                self.eat_(COLON)?;
                let ty_ty = self.ctx.mk_ty();
                let ty = self.parse_expr_bp_(0, Some(ty_ty))?;
                let c = self.ctx.mk_new_const(k::Symbol::from_str(id), ty)?;
                ParseOutput::Expr(c)
            }
            SYM("pledge_no_new_axiom") => {
                self.next_();
                self.ctx.pledge_no_new_axiom();
                ParseOutput::SideEffect("pledged no more axioms")
            }
            SYM("defthm") => {
                self.next_();
                let name = self.parse_sym_()?;
                self.eat_(SYM("="))?;
                let th = self.parse_thm_()?;
                self.ctx.define_lemma(name, th.clone());
                ParseOutput::Thm(th)
            }
            SYM("defty") => todo!("define type"), // TODO
            SYM("thm") => {
                self.next_();
                let th = self.parse_thm_()?;
                ParseOutput::Thm(th)
            }
            SYM("include") => {
                self.next_();
                if let QUOTED_STR(s) = self.next_() {
                    let v = self.include_(s)?;
                    ParseOutput::Include(v)
                } else {
                    return Err(perror!(self, "expected a quoted string"));
                }
            }
            SYM("load_hol") => {
                self.next_();
                let v = self.load_str_(PRELUDE_HOL)?;
                ParseOutput::Include(v)
            }
            // TODO: show <sym>: print description of that (const or thm)
            // TODO: prove <thm>: print the theorem (from tactics)
            _ => ParseOutput::Expr(self.parse_expr_bp_(0, None)?),
        };
        self.eat_(DOT)?;
        Ok(r)
    }

    /// Read string, return how many statements were included.
    fn load_str_(&mut self, s: &str) -> Result<Vec<ParseOutput>> {
        // read file to include
        let mut sub = Parser::new(self.ctx, s);
        sub.parse_statements()
    }

    /// Include file, return how many statements were included.
    fn include_(&mut self, s: &str) -> Result<Vec<ParseOutput>> {
        // read file to include
        let content = std::fs::read_to_string(s).map_err(|e| {
            perror!(self, "error when including file {:?}: {}", s, e)
        })?;
        self.load_str_(&content)
    }
     */
}

/// Standard prelude for HOL logic
pub const PRELUDE_HOL: &'static str = include_str!("prelude.trustee");

#[cfg(test)]
mod test {
    /*
    use super::*;

    #[test]
    fn test_parser_statement() -> Result<()> {
        let mut ctx = k::Ctx::new();
        let d = parse_statement(
            &mut ctx,
            r#"def true = (let f = (\x: bool. x=x) in f=f)."#,
        )?;
        println!("def true: {:?}", d);
        println!("find true? {:?}", ctx.find_const("true"));
        let e = parse_expr(&mut ctx, r#"true"#)?;
        println!("parse true: {:?}", e);

        let d2 = parse_statement(
            &mut ctx,
            r#"def false = (\x: bool. true) = (\x: bool. x) ."#,
        )?;
        println!("def false: {:?}", d2);
        println!("find false? {:?}", ctx.find_const("false"));
        let e = parse_expr(&mut ctx, r#"false"#)?;
        println!("parse false: {:?}", e);

        Ok(())
    }
    */
}
