//! Meta-language.
//!
//! The meta-language is a postscript-like stack language that manipulates
//! expressions, goals, theorems, and other values. It is designed to be
//! used both interactively and as an efficient way of storing proofs.

use {
    crate::{
        algo,
        fnv::{self, FnvHashMap},
        kernel_of_trust::{self as k, CtxI},
        syntax, Error, Result,
    },
    std::{cell::RefCell, fmt, rc::Rc},
};

macro_rules! logdebug {
    ($($t:expr),*) => {
        #[cfg(feature="logging")]
        log::debug!($($t),*)
    }
}

/// The state of the meta-language interpreter.
pub struct State<'a> {
    pub ctx: &'a mut dyn CtxI,
    pub stack: Vec<Value>,
    /// Current instruction.
    cur_i: Option<Instr>,
    /// Nested scopes to handle definitions in local dictionaries.
    ///
    /// The toplevel dictionary (at index 0) is the system dictionary.
    scopes: Vec<Dict>,
    /// Control stack, for function call.
    ctrl_stack: Vec<(CodeArray, usize)>,
}

/// An array of instructions.
///
/// Syntax: `{a b c d}`
#[derive(Clone)]
pub struct CodeArray(Rc<Vec<Instr>>);

impl fmt::Debug for CodeArray {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        out.debug_set().entries(self.0.iter()).finish()
    }
}

#[derive(Clone)]
pub struct ValueArray(Rc<RefCell<Vec<Value>>>);

impl fmt::Debug for ValueArray {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        out.debug_list().entries(self.0.borrow().iter()).finish()
    }
}

/// A dictionary from symbols to values.
///
/// Syntax: TODO
/// Syntax: `begin … end` to create a dictionary and use it in a temporary scope.
#[derive(Clone, Debug)]
pub struct Dict(FnvHashMap<Rc<str>, Value>);

// TODO: syntax for `Value::Source` (""" string?)
// TODO: builtins for creating and manipulating arrays

/// A value of the language.
#[derive(Debug, Clone)]
pub enum Value {
    Int(i64),
    Bool(bool),
    Sym(Rc<str>),
    /// Source code. Obtained only by parsing a file.
    Source(Rc<str>),
    //Var(Var),
    Expr(k::Expr),
    Thm(k::Thm),
    CodeArray(CodeArray),
    Array(ValueArray),
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
    /// Call a word by its name. Useful for late binding and recursion.
    Get(Rc<str>),
}

// NOTE: modify `INSTR_CORE` below when modifying this.
/// Core operations: control flow and arithmetic.
#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq)]
enum InstrCore {
    Def,
    If,
    IfElse,
    Dup,
    Swap,
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
    Inspect,
    Clear,
    /// Load a source string
    Source,
    /// Read a file into a source string
    LoadFile,
}

/// A custom instruction implemented in rust.
///
/// This is the most direct way of writing efficient "tactics" directly
/// in rust.
pub trait InstrBuiltin {
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

impl fmt::Debug for dyn InstrBuiltin {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "{}", self.name())
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
        LBrace,
        RBrace,
        Invalid(char),
    }

    #[inline]
    fn is_id_char(c: u8) -> bool {
        match c {
            b'a'..=b'z'
            | b'A'..=b'Z'
            | b'_'
            | b':'
            | b'='
            | b'+'
            | b'-'
            | b'@'
            | b'!'
            | b'$'
            | b'%'
            | b'^'
            | b'&'
            | b'*'
            | b'|'
            | b'/'
            | b'\\'
            | b';' => true,
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
                if c == b'#' {
                    // eat rest of line
                    while self.i < self.bytes.len()
                        && self.bytes[self.i] != b'\n'
                    {
                        self.i += 1
                    }
                } else if c == b' ' || c == b'\t' {
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
        pub fn next(&mut self) -> Tok<'b> {
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
                b'[' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::LBrace
                }
                b'}' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::RBracket
                }
                b']' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::RBrace
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
                    self.i = j;
                    Tok::Int(n)
                }
                b'"' => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && {
                        let c = self.bytes[j];
                        c != b'"'
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
                    assert!(c != b'-'); // number, dealt with above
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
                    self.i = j;
                    Tok::Id(tok)
                }
                c => Tok::Invalid(std::char::from_u32(c as u32).unwrap()),
            };
            self.cur_ = Some(tok);
            tok
        }

        /// Current token.
        pub fn cur(&mut self) -> Tok<'b> {
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

/// Meta-language.
mod ml {
    use super::*;

    impl CodeArray {
        fn new(v: Vec<Instr>) -> Self {
            CodeArray(Rc::new(v))
        }
    }

    impl Dict {
        fn new() -> Self {
            Dict(fnv::new_table_with_cap(8))
        }
    }

    /// All the core instructions.
    const INSTR_CORE: &'static [InstrCore] = {
        use InstrCore::*;
        &[
            Def, If, IfElse, Dup, Swap, Drop, Rot, Eq, Lt, Gt, Leq, Geq, Add,
            Mul, Sub, Div, Mod, PrintStack, Clear, PrintPop, Inspect, Source,
            LoadFile, Begin, End,
        ]
    };

    impl InstrBuiltin for InstrCore {
        fn name(&self) -> &'static str {
            use InstrCore as I;

            match self {
                I::Def => "def",
                I::If => "if",
                I::IfElse => "ifelse",
                I::Dup => "dup",
                I::Swap => "swap",
                I::Drop => "drop",
                I::Rot => "rot",
                I::Begin => "begin",
                I::End => "end",
                I::Eq => "eq",
                I::Lt => "lt",
                I::Gt => "gt",
                I::Leq => "leq",
                I::Geq => "geq",
                I::Add => "add",
                I::Mul => "mul",
                I::Sub => "sub",
                I::Div => "div",
                I::Mod => "mod",
                I::PrintPop => "==",
                I::PrintStack => "pstack",
                I::Inspect => "inspect",
                I::Clear => "clear",
                I::Source => "source",
                I::LoadFile => "load_file",
            }
        }

        fn run(&self, st: &mut State) -> Result<()> {
            use InstrCore as I;

            match self {
                I::Def => {
                    let c = st.pop1()?;
                    let sym = st.pop1_sym()?;
                    st.scopes[0].0.insert(sym.clone(), c);
                }
                I::If => {
                    let c = st.pop1_codearray()?;
                    let b = st.pop1_bool()?;
                    if b {
                        st.exec_codearray_(&c);
                        st.exec_loop_()?;
                    }
                }
                I::IfElse => {
                    let else_ = st.pop1_codearray()?;
                    let then_ = st.pop1_codearray()?;
                    let b = st.pop1_bool()?;
                    if b {
                        st.exec_codearray_(&then_);
                    } else {
                        st.exec_codearray_(&else_);
                    }
                    st.exec_loop_()?;
                }
                I::Dup => match st.stack.last() {
                    Some(v) => {
                        let v = v.clone();
                        st.stack.push(v)
                    }
                    None => return Err(Error::new("stack underflow")),
                },
                I::Rot => return Err(Error::new("todo: rot")), // TODO
                I::Swap => {
                    let y = st.pop1()?;
                    let x = st.pop1()?;
                    st.stack.push(y);
                    st.stack.push(x);
                }
                I::Drop => {
                    let _ = st.pop1()?;
                }
                I::Begin => {
                    let dict = Dict::new();
                    st.scopes.push(dict)
                }
                I::End => {
                    if st.scopes.len() < 2 {
                        return Err(Error::new(
                            "`end` does not match a `begin`",
                        ));
                    }
                    st.scopes.pop();
                }
                I::Eq => {
                    let y = st.pop1()?;
                    let x = st.pop1()?;
                    st.stack.push(Value::Bool(x == y))
                }
                I::Lt => {
                    let y = st.pop1_int()?;
                    let x = st.pop1_int()?;
                    st.stack.push(Value::Bool(x < y))
                }
                I::Gt => {
                    let y = st.pop1_int()?;
                    let x = st.pop1_int()?;
                    st.stack.push(Value::Bool(x > y))
                }
                I::Leq => {
                    let y = st.pop1_int()?;
                    let x = st.pop1_int()?;
                    st.stack.push(Value::Bool(x <= y))
                }
                I::Geq => {
                    let y = st.pop1_int()?;
                    let x = st.pop1_int()?;
                    st.stack.push(Value::Bool(x >= y))
                }
                I::Add => {
                    let y = st.pop1_int()?;
                    let x = st.pop1_int()?;
                    st.stack.push(Value::Int(x + y))
                }
                I::Mul => {
                    let y = st.pop1_int()?;
                    let x = st.pop1_int()?;
                    st.stack.push(Value::Int(x * y))
                }
                I::Sub => {
                    let y = st.pop1_int()?;
                    let x = st.pop1_int()?;
                    st.stack.push(Value::Int(x - y))
                }
                I::Div => {
                    let y = st.pop1_int()?;
                    let x = st.pop1_int()?;
                    if y == 0 {
                        return Err(Error::new("division by zero"));
                    }
                    st.stack.push(Value::Int(x / y))
                }
                I::Mod => {
                    let y = st.pop1_int()?;
                    let x = st.pop1_int()?;
                    if y == 0 {
                        return Err(Error::new("division by zero"));
                    }
                    st.stack.push(Value::Int(x % y))
                }
                I::PrintPop => {
                    let x = st.pop1()?;
                    println!("  {:?}", x);
                }
                I::PrintStack => {
                    println!("stack:");
                    for x in st.stack.iter().rev() {
                        println!("  > {:?}", x);
                    }
                }
                I::Inspect => {
                    let s = st.pop1_sym()?;

                    // Find definition of symbol `s` in `self.scopes`,
                    // starting from the most recent scope.
                    let v = {
                        if let Some(v) =
                            st.scopes.iter().rev().find_map(|d| d.0.get(&*s))
                        {
                            v.clone()
                        } else if let Some(c) = st.ctx.find_const(&*s) {
                            Value::Expr(c.0.clone())
                        } else if let Some(th) = st.ctx.find_lemma(&*s) {
                            Value::Thm(th.clone())
                        } else {
                            return Err(Error::new_string(format!(
                                "symbol {:?} not found",
                                s
                            )));
                        }
                    };

                    println!(">>  {:?}", v);
                }
                I::Clear => st.stack.clear(),
                I::Source => {
                    let x = st.pop1_source()?;
                    st.run(&x)?;
                }
                I::LoadFile => {
                    let s = st.pop1_sym()?;
                    let content =
                        std::fs::read_to_string(&*s).map_err(|e| {
                            Error::new_string(format!(
                                "cannot load file {:?}: {}",
                                s, e
                            ))
                        })?;
                    st.push_val(Value::Source(content.into()))
                }
            }
            Ok(())
        }
    }

    impl fmt::Debug for InstrCore {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "{}", self.name())
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

    macro_rules! pop1_of {
        ($f:ident, $what: literal, $p: pat, $v: ident, $ret: ty) => {
            pub fn $f(&mut self) -> Result<$ret> {
                match self.pop1()? {
                    $p => Ok($v),
                    _ => {
                        return Err(Error::new(concat!(
                            "type error: expected ",
                            $what
                        )))
                    }
                }
            }
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
                    scope0.0.insert(name, Value::CodeArray(ca));
                }
                for b in logic_builtins::BUILTINS {
                    let name: Rc<str> = b.name().into();
                    let ca = CodeArray::new(vec![Instr::Builtin(*b)]);
                    scope0.0.insert(name, Value::CodeArray(ca));
                }
            }
            Self {
                ctx,
                cur_i: None,
                stack: vec![],
                scopes: vec![scope0],
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
                Tok::RBrace => return Err(Error::new("unexpected ']'")),
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
                Tok::LBrace => {
                    // parse an array of values.
                    p.next();
                    let mut arr = vec![];
                    let v = loop {
                        match p.cur() {
                            Tok::RBrace => {
                                p.next();
                                let va = ValueArray(Rc::new(RefCell::new(arr)));
                                break Value::Array(va);
                            }
                            _ => match self.parse_instr_(p)? {
                                Instr::Im(v) => {
                                    arr.push(v); // only accept values
                                }
                                i => {
                                    self.exec_instr_(i)?;
                                    let v = self.pop1().map_err(|e| {
                                        e.set_source(Error::new(
                                            "evaluate element of an array",
                                        ))
                                    })?;
                                    arr.push(v)
                                }
                            },
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
                    // Find definition of symbol `s` in `self.scopes[0]`,
                    // otherwise emit a dynamic get (for user scopes)
                    let i = match self.scopes[0].0.get(&*s) {
                        Some(Value::CodeArray(ca)) if ca.0.len() == 1 => {
                            ca.0[0].clone()
                        }
                        Some(Value::CodeArray(ca)) => Instr::Call(ca.clone()),
                        Some(v) => Instr::Im(v.clone()),
                        None => Instr::Get(s.into()),
                    };
                    p.next();
                    Ok(i)
                }
            }
        }

        /// Execute instruction `i`.
        ///
        /// This should always be done within or before a `exec_loop_`.
        fn exec_instr_(&mut self, i: Instr) -> Result<()> {
            match i {
                Instr::Im(v) => self.stack.push(v),
                Instr::Builtin(b) => {
                    b.run(self)?; // ask the builtin to eval itself
                }
                Instr::Call(ca) => self.exec_codearray_(&ca),
                Instr::Get(s) => {
                    // Find definition of symbol `s` in `self.scopes`,
                    // starting from the most recent scope.
                    if let Some(v) =
                        self.scopes.iter().rev().find_map(|d| d.0.get(&*s))
                    {
                        if let Value::CodeArray(ca) = v {
                            self.cur_i = Some(ca.0[0].clone());
                            if ca.0.len() > 1 {
                                self.ctrl_stack.push((ca.clone(), 1));
                            }
                        } else {
                            self.stack.push(v.clone())
                        }
                    } else if let Some(c) = self.ctx.find_const(&*s) {
                        self.stack.push(Value::Expr(c.0.clone()))
                    } else if let Some(th) = self.ctx.find_lemma(&*s) {
                        self.stack.push(Value::Thm(th.clone()))
                    } else {
                        return Err(Error::new_string(format!(
                            "symbol {:?} not found",
                            s
                        )));
                    }
                }
                Instr::Core(c) => c.run(self)?,
            }
            Ok(())
        }

        fn exec_codearray_(&mut self, ca: &CodeArray) {
            // start execution of this block of code
            self.cur_i = Some(ca.0[0].clone());
            if ca.0.len() > 1 {
                self.ctrl_stack.push((ca.clone(), 1));
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
                                if *idx >= ca.0.len() {
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

        pub fn pop1(&mut self) -> Result<Value> {
            match self.stack.pop() {
                Some(v) => Ok(v),
                _ => return Err(Error::new("stack underflow")),
            }
        }

        pop1_of!(pop1_int, "int", Value::Int(i), i, i64);
        pop1_of!(pop1_bool, "bool", Value::Bool(i), i, bool);
        pop1_of!(
            pop1_codearray,
            "code array",
            Value::CodeArray(i),
            i,
            CodeArray
        );
        pop1_of!(pop1_array, "array", Value::Array(v), v, ValueArray);
        pop1_of!(pop1_expr, "expr", Value::Expr(i), i, k::Expr);
        pop1_of!(pop1_thm, "thm", Value::Thm(i), i, k::Thm);
        pop1_of!(pop1_sym, "sym", Value::Sym(i), i, Rc<str>);
        pop1_of!(pop1_source, "source", Value::Source(i), i, Rc<str>);

        /// Push a value onto the value stack.
        #[inline]
        pub fn push_val(&mut self, v: Value) {
            self.stack.push(v);
        }

        /// Parse and execute the given code.
        pub fn run(&mut self, s: &str) -> Result<()> {
            use parser::*;
            let mut p = Parser::new(s);

            logdebug!("meta.run {}", s);

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
}

/// Primitives of the meta-language related to theorem proving.
mod logic_builtins {
    use super::*;

    // TODO: defty

    #[derive(Debug, Clone)]
    enum Rule {
        Defconst,
        Defthm,
        Decl,
        SetInfix,
        SetBinder,
        Findconst,
        Findthm,
        ExprTy,
        Axiom,
        Assume,
        Refl,
        Sym,
        Trans,
        Congr,
        CongrTy,
        Cut,
        BoolEq,
        BoolEqIntro,
        BetaConv,
        Instantiate,
        Abs,
        AbsExpr,
        Concl,
        HolPrelude,
        PledgeNoMoreAxioms,
        Rewrite,
    }

    use Rule as R;

    /// Builtin functions for manipulating expressions and theorems.
    pub(super) const BUILTINS: &'static [&'static dyn InstrBuiltin] = &[
        &R::Defconst,
        &R::Defthm,
        &R::Decl,
        &R::SetInfix,
        &R::SetBinder,
        &R::ExprTy,
        &R::Findconst,
        &R::Findthm,
        &R::Axiom,
        &R::Assume,
        &R::Refl,
        &R::Sym,
        &R::Trans,
        &R::Congr,
        &R::CongrTy,
        &R::Cut,
        &R::BoolEq,
        &R::BoolEqIntro,
        &R::BetaConv,
        &R::Instantiate,
        &R::Abs,
        &R::AbsExpr,
        &R::Concl,
        &R::HolPrelude,
        &R::PledgeNoMoreAxioms,
        &R::Rewrite,
    ];

    impl InstrBuiltin for Rule {
        fn name(&self) -> &'static str {
            match self {
                R::Defconst => "defconst",
                R::Defthm => "defthm",
                R::Decl => "decl",
                R::SetInfix => "set_infix",
                R::SetBinder => "set_binder",
                R::ExprTy => "expr_ty",
                R::Findconst => "findconst",
                R::Findthm => "findthm",
                R::Axiom => "axiom",
                R::Assume => "assume",
                R::Refl => "refl",
                R::Sym => "sym",
                R::Trans => "trans",
                R::Congr => "congr",
                R::CongrTy => "congr_ty",
                R::Cut => "cut",
                R::BoolEq => "bool_eq",
                R::BoolEqIntro => "bool_eq_intro",
                R::BetaConv => "beta_conv",
                R::Instantiate => "subst",
                R::Abs => "abs",
                R::AbsExpr => "abs_expr",
                R::Concl => "concl",
                R::HolPrelude => "hol_prelude",
                R::PledgeNoMoreAxioms => "pledge_no_more_axioms",
                R::Rewrite => "rw",
            }
        }

        // th1 th2 -- mp(th1,th2)
        fn run(&self, st: &mut State) -> Result<()> {
            match self {
                R::Defconst => {
                    let rhs = st.pop1_expr()?;
                    let nthm = &st.pop1_sym()?;
                    let nc = st.pop1_sym()?;
                    let def =
                        crate::algo::thm_new_poly_definition(st.ctx, &nc, rhs)?;
                    st.ctx.define_lemma(nthm, def.thm);
                }
                R::Defthm => {
                    let th = st.pop1_thm()?;
                    let name = st.pop1_sym()?;
                    st.ctx.define_lemma(&name, th);
                }
                R::Decl => {
                    let ty = st.pop1_expr()?;
                    let name = st.pop1_sym()?;
                    let _e = st
                        .ctx
                        .mk_new_const(k::Symbol::from_rc_str(&name), ty)?;
                }
                R::ExprTy => {
                    let e = st.pop1_expr()?;
                    if e.is_kind() {
                        return Err(Error::new("cannot get type of `kind`"));
                    }
                    st.stack.push(Value::Expr(e.ty().clone()))
                }
                R::SetInfix => {
                    let j = st.pop1_int()?;
                    let i = st.pop1_int()?;
                    let c = st.pop1_sym()?;
                    let f = syntax::Fixity::Infix((i as u16, j as u16));
                    st.ctx.set_fixity(&*c, f);
                }
                R::SetBinder => {
                    let i = st.pop1_int()?;
                    let c = st.pop1_sym()?;
                    let f = syntax::Fixity::Binder((0, i as u16));
                    st.ctx.set_fixity(&*c, f);
                }
                R::Findconst => {
                    let name = st.pop1_sym()?;
                    let e = st
                        .ctx
                        .find_const(&name)
                        .ok_or_else(|| Error::new("unknown constant"))?
                        .0
                        .clone();
                    st.push_val(Value::Expr(e))
                }
                R::Findthm => {
                    let name = st.pop1_sym()?;
                    let th = st
                        .ctx
                        .find_lemma(&name)
                        .ok_or_else(|| Error::new("unknown theorem"))?
                        .clone();
                    st.push_val(Value::Thm(th))
                }
                R::Axiom => {
                    let e = st.pop1_expr()?;
                    let th = st.ctx.thm_axiom(vec![], e)?;
                    st.push_val(Value::Thm(th))
                }
                R::Assume => {
                    let e = st.pop1_expr()?;
                    let th = st.ctx.thm_assume(e)?;
                    st.push_val(Value::Thm(th))
                }
                R::Refl => {
                    let e = st.pop1_expr()?;
                    let th = st.ctx.thm_refl(e);
                    st.push_val(Value::Thm(th))
                }
                R::Sym => {
                    let th1 = st.pop1_thm()?;
                    let th = crate::algo::thm_sym(st.ctx, th1)?;
                    st.push_val(Value::Thm(th))
                }
                R::Trans => {
                    let th2 = st.pop1_thm()?;
                    let th1 = st.pop1_thm()?;
                    let th = st.ctx.thm_trans(th1, th2)?;
                    st.push_val(Value::Thm(th))
                }
                R::Congr => {
                    let th2 = st.pop1_thm()?;
                    let th1 = st.pop1_thm()?;
                    let th = st.ctx.thm_congr(th1, th2)?;
                    st.push_val(Value::Thm(th))
                }
                R::CongrTy => {
                    let ty = st.pop1_expr()?;
                    let th1 = st.pop1_thm()?;
                    let th = st.ctx.thm_congr_ty(th1, &ty)?;
                    st.push_val(Value::Thm(th))
                }
                R::Cut => {
                    let th2 = st.pop1_thm()?;
                    let th1 = st.pop1_thm()?;
                    let th = st.ctx.thm_cut(th1, th2)?;
                    st.push_val(Value::Thm(th))
                }
                R::BoolEq => {
                    let th2 = st.pop1_thm()?;
                    let th1 = st.pop1_thm()?;
                    let th = st.ctx.thm_bool_eq(th1, th2)?;
                    st.push_val(Value::Thm(th))
                }
                R::BoolEqIntro => {
                    let th2 = st.pop1_thm()?;
                    let th1 = st.pop1_thm()?;
                    let th = st.ctx.thm_bool_eq_intro(th1, th2)?;
                    st.push_val(Value::Thm(th))
                }
                R::BetaConv => {
                    let e = st.pop1_expr()?;
                    let th = st.ctx.thm_beta_conv(&e)?;
                    st.push_val(Value::Thm(th))
                }
                R::Instantiate => {
                    let a = st.pop1_array()?;
                    let th = st.pop1_thm()?;

                    // build substitution
                    let a = a.0.borrow();
                    if a.len() % 2 != 0 {
                        return Err(Error::new("invalid subst (odd length)"));
                    }
                    let mut subst = vec![];
                    for ch in a.as_slice().chunks(2) {
                        match &ch {
                            &[Value::Sym(x), Value::Expr(e)] => {
                                let v = k::Var::from_str(&*x, e.ty().clone());
                                subst.push((v, e.clone()))
                            }
                            _ => {
                                return Err(Error::new("invalid subst binding"))
                            }
                        }
                    }

                    let th = st.ctx.thm_instantiate(th, &subst)?;
                    st.push_val(Value::Thm(th))
                }
                R::Abs => {
                    let ty = st.pop1_expr()?;
                    let v = st.pop1_sym()?;
                    let th = st.pop1_thm()?;
                    let v = k::Var::from_str(&*v, ty);
                    let th = st.ctx.thm_abs(&v, th)?;
                    st.push_val(Value::Thm(th))
                }
                R::AbsExpr => {
                    let e = st.pop1_expr()?;
                    let v = e.as_var().ok_or_else(|| {
                        Error::new("abs_expr: expression must be a variable")
                    })?;
                    let th = st.pop1_thm()?;
                    let th = st.ctx.thm_abs(v, th)?;
                    st.push_val(Value::Thm(th))
                }
                R::Concl => {
                    let th = st.pop1_thm()?;
                    st.push_val(Value::Expr(th.concl().clone()))
                }
                R::HolPrelude => {
                    st.push_val(Value::Source(super::SRC_PRELUDE_HOL.into()))
                }
                R::PledgeNoMoreAxioms => {
                    st.ctx.pledge_no_new_axiom();
                }
                R::Rewrite => {
                    let rw = st.pop1()?;
                    let th = st.pop1_thm()?;

                    let fail = || {
                        Err(Error::new(
                            r#"rw: expect a theorem, "beta", or an array thereof as second parameter"#,
                        ))
                    };
                    let mut beta = false;
                    let mut rw_rules = algo::RewriteRuleSet::new();
                    match rw {
                        Value::Sym(s) if &*s == "beta" => {
                            beta = true;
                        }
                        Value::Array(a) => {
                            let a = a.0.borrow();
                            for x in a.iter() {
                                match x {
                                    Value::Sym(s) if &**s == "beta" => {
                                        beta = true;
                                    }
                                    Value::Thm(th) => {
                                        let rule = algo::RewriteRule::new(&th)?;
                                        rw_rules.add_rule(rule)
                                    }
                                    _ => return fail(),
                                }
                            }
                        }
                        _ => return fail(),
                    }

                    let rw: Box<dyn algo::Rewriter> =
                        if beta && !rw_rules.is_empty() {
                            let mut rw = algo::RewriteCombine::new();
                            rw.add(&algo::RewriterBetaConv);
                            rw.add(&rw_rules);
                            Box::new(rw)
                        } else if beta {
                            Box::new(algo::RewriterBetaConv)
                        } else if !rw_rules.is_empty() {
                            Box::new(rw_rules)
                        } else {
                            return fail();
                        };
                    let th = algo::thm_rw_concl(st.ctx, th, &*rw)?;
                    st.push_val(Value::Thm(th))
                }
            };
            Ok(())
        }
    }
}

/// Standard prelude for HOL logic
pub const SRC_PRELUDE_HOL: &'static str = include_str!("prelude.trustee");

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parser() {
        use parser::Tok as T;
        let a = vec![(
            r#" "a" "b"{mul 2}"d" { 3 } def 2  "#,
            vec![
                T::QuotedId("a"),
                T::QuotedId("b"),
                T::LBracket,
                T::Id("mul"),
                T::Int(2),
                T::RBracket,
                T::QuotedId("d"),
                T::LBracket,
                T::Int(3),
                T::RBracket,
                T::Id("def"),
                T::Int(2),
                T::Eof,
            ],
        )];

        for (s, v) in a {
            let mut p = parser::Parser::new(s);
            let mut toks = vec![];
            loop {
                let t = p.cur().clone();
                toks.push(t);
                if t == T::Eof {
                    break;
                }
                p.next();
            }
            assert_eq!(toks, v)
        }
    }

    #[test]
    fn test_basic_ops() -> Result<()> {
        let mut ctx = k::Ctx::new();
        let mut st = State::new(&mut ctx);

        st.run("1 2 add")?;
        let v = st.pop1_int()?;
        assert_eq!(v, 3);

        Ok(())
    }

    #[test]
    fn test_parse_prelude_and_forall() -> Result<()> {
        let mut ctx = k::Ctx::new();
        let mut st = State::new(&mut ctx);

        st.run(
            r#"
        "T" "def_true" `let f = (\x: bool. x=x) in f=f` defconst
        "forall" "def_forall" `\(a:type) (f:a -> bool). f = (\x:a. T)` defconst
        "forall" 30 set_binder
        "#,
        )?;
        st.run("`forall x:bool. x=T`")?;
        let e = st.pop1_expr()?;
        let b = st.ctx.mk_bool();
        assert_eq!(e.ty().clone(), b);

        Ok(())
    }
}
