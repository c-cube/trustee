//! Meta-language.
//!
//! The meta-language is a tiny lisp-like stack language that manipulates
//! expressions, goals, theorems, and other values. It is designed to be
//! used both interactively and as an efficient way of storing proofs.

use {
    crate::{
        algo,
        kernel_of_trust::{self as k, Ctx},
        rstr::RStr,
        syntax, Error, Result,
    },
    std::{fmt, i16, io, u8},
};

macro_rules! logdebug {
    ($($t:expr),*) => {
        #[cfg(feature="logging")]
        log::debug!($($t),*)
    }
}

macro_rules! logerr{
    ($($t:expr),*) => {
        #[cfg(feature="logging")]
        log::error!($($t),*)
    }
}

/// # Values
///
/// A value of the language.
#[derive(Debug, Clone)]
pub enum Value {
    Nil,
    Int(i64),
    Bool(bool),
    Sym(k::Symbol),
    /// A raw string literal. Obtained by parsing a source file or using
    /// an embedded rust string literal.
    Str(RStr),
    Expr(k::Expr),
    Thm(k::Thm),
    /// An executable chunk.
    Chunk(Chunk),
    /// A builtin instruction implemented in rust.
    Builtin(&'static InstrBuiltin),
    //Array(ValueArray),
}

/// A chunk of code.
///
/// Each derived rule, expression, etc. is compiled to a self-contained chunk.
/// Chunks can be evaluated several times.
#[derive(Clone)]
pub struct Chunk(k::Ref<ChunkImpl>);

struct ChunkImpl {
    /// Instructions to execute.
    instrs: Box<[Instr]>,
    /// Local values, typically chunks, theorems, or terms,
    /// used during the evaluation.
    locals: Box<[Value]>,
    /// Number of local slots required.
    n_slots: u32,
    /// Name of this chunk, if any.
    name: Option<String>,
}

/// Compiler for a given chunk.
struct Compiler {
    instrs: Vec<Instr>,
    locals: Vec<Value>,
    /// Maximum size `slots` ever took.
    n_slots: u32,
    name: Option<String>,
    slots: Vec<CompilerSlot>,
}
struct CompilerSlot {
    /// If this slot is for a named variable.
    var_name: Option<RStr>,
    activated: bool,
}

/// Index in the array of slots.
type SlotIdx = u8;

/// Index in the array of locals.
#[derive(Debug, Copy, Clone, PartialEq)]
struct LocalIdx(u8);

/// ## Instructions
///
/// An instruction of the language.
///
/// Each instruction's last argument is the index of the slot to put the result
/// into. Abbreviations:
/// - `sl` is the slots
/// - `args` is the VM's argument stack.
/// - `$3` is argument number 3 (numbered from 0)`
#[derive(Debug, Copy, Clone)]
enum Instr {
    /// copy `sl[$0]` into `sl[$1]`
    Move(SlotIdx, SlotIdx),
    /// Local a local value into a slot. `sl[$1] = locals[$0]`
    LoadLocal(LocalIdx, SlotIdx),
    /// Put the given (small) integer `$0` into `sl[$1]`
    LoadInteger(i16, SlotIdx),
    /// Set `sl[$1]` to bool `$0`
    LoadBool(bool, SlotIdx),
    /// Set `sl[$1 .. $1 + $0]` to nil
    LoadNilN(u8, SlotIdx),
    /// `sl[$2] = (sl[$0] == sl[$1])`
    Eq(SlotIdx, SlotIdx, SlotIdx),
    Lt(SlotIdx, SlotIdx, SlotIdx),
    Leq(SlotIdx, SlotIdx, SlotIdx),
    Add(SlotIdx, SlotIdx, SlotIdx),
    Mul(SlotIdx, SlotIdx, SlotIdx),
    Sub(SlotIdx, SlotIdx, SlotIdx),
    Div(SlotIdx, SlotIdx, SlotIdx),
    Mod(SlotIdx, SlotIdx, SlotIdx),
    /// evaluates string in `sl[$0]`
    EvalStr(SlotIdx),
    /// read file whose name is `sl[$0]` into a string `sl[$1]`
    LoadFile(SlotIdx, SlotIdx),
    /// Call chunk `sl[$0]` with arguments `sl[$0 + 1 .. $0 + 1 + $1]`,
    /// and put the result into `sl[$2]`.
    ///
    /// `$1` is the number of arguments the function takes.
    Call(SlotIdx, u8, SlotIdx),
    /// Tail-call into chunk `sl[$0]` with arguments `sl[$0 + 1 .. $0 + 1 + $1]`
    Become(LocalIdx, u8),
    /// Pop n values from the slots.
    Pop(u16),
    // TODO: remove argument? should already have set slot
    /// Return from current chunk with value `sl[$0]`.
    Ret(SlotIdx),
    // TODO: control flow:
    // - `Jump(SlotIdx, offset:u16)`
    // - `JumpIfTrue(SlotIdx, offset:i16)`
    // - `JumpIfFalse(SlotIdx, offset:i16)`
}

/// A custom instruction implemented in rust.
///
/// This is the most direct way of writing efficient inference rules or
/// tactics directly in rust.
pub struct InstrBuiltin {
    /// Name of the instruction. The instruction is invoked by its name.
    ///
    /// The name should be consistent with lexical conventions (no whitespaces,
    /// brackets, backquotes, etc.)
    name: &'static str,

    /// Execute the instruction on the given state with arguments.
    run: fn(ctx: &mut Ctx, args: &[Value]) -> Result<Value>,

    /// A one-line help text for this instruction.
    help: &'static str,
}

/// The meta-language virtual machine.
pub struct VM<'a> {
    /// The logical context underlying the VM.
    ///
    /// The context provides means to build expressions, theorems (following
    /// the logic deduction rules), and stores maps from names to
    /// constants, theorems, and chunks.
    pub ctx: &'a mut Ctx,
    /// The stack where values live.
    stack: Vec<Value>,
    /// Control stack, for function calls.
    ctrl_stack: Vec<StackFrame>,
    /// Stack used to pass arguments to a chunk before execution.
    /// This is typically reset before each function call.
    call_stack: Vec<Value>,
    /// In case of error, the error message lives here.
    result: Result<()>,
}

/// A stack frame.
///
/// Each call to a chunk (function) has its own stack frame that points to
/// a slice of `vm.stack` of its given number of locals.
struct StackFrame {
    /// Offset in `vm.stack` where this frame starts.
    /// The size of the stack is determined by `chunk.n_slots`.
    start: u32,
    /// Instruction pointer within `chunk`.
    ic: u32,
    /// Chunk being executed.
    chunk: Chunk,
    /// Offset to put the returned value into.
    res_offset: u32,
}

/// Meta-language.
mod ml {
    use super::*;

    // TODO: extract to a method, and display that with a margin.
    // Also get optional `ic` to write ==> next to it.
    impl fmt::Debug for Chunk {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "chunk [\n")?;
            write!(out, "  name: {:?}\n", &self.0.name)?;
            write!(out, "  n-slots: {}\n", self.0.n_slots)?;
            write!(out, "  ================\n")?;
            for (i, v) in self.0.locals.iter().enumerate() {
                write!(out, "  local[{:5}]: {}\n", i, &v)?;
            }
            write!(out, "  ================\n")?;
            for (i, c) in self.0.instrs.iter().enumerate() {
                write!(out, "  instr[{:5}]: {:?}\n", i, &c)?;
            }
            write!(out, "]\n")?;
            Ok(())
        }
    }

    impl Default for Value {
        fn default() -> Self {
            Value::Nil
        }
    }

    impl fmt::Debug for InstrBuiltin {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "<builtin {}>", self.name)
        }
    }

    impl Chunk {
        /// Access the content.
        #[inline]
        fn get(&self) -> &ChunkImpl {
            &*self.0
        }
    }

    /// Print a value.
    impl fmt::Display for Value {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Value::Nil => write!(out, "nil"),
                Value::Int(i) => write!(out, "{}", i),
                Value::Bool(b) => write!(out, "{}", b),
                Value::Sym(s) => write!(out, "{}", s.name()),
                Value::Str(s) => write!(out, "{:?}", s),
                Value::Expr(e) => write!(out, "{}", e),
                Value::Thm(th) => write!(out, "{}", th),
                Value::Chunk(c) => {
                    if let Some(n) = &c.0.name {
                        write!(out, "<chunk {:?}>", n)
                    } else {
                        write!(out, "<chunk>")
                    }
                }
                Value::Builtin(b) => write!(out, "<builtin {}>", b.name),
                //Value::Array(a) => out.debug_list().entries(a.0.borrow().iter()).finish(),
            }
        }
    }

    impl PartialEq for Value {
        fn eq(&self, other: &Value) -> bool {
            use Value::*;

            match (self, other) {
                (Nil, Nil) => true,
                (Int(i), Int(j)) => i == j,
                (Bool(i), Bool(j)) => i == j,
                (Sym(i), Sym(j)) => i == j,
                (Expr(i), Expr(j)) => i == j,
                _ => false, // other cases are not comparable
            }
        }
    }

    macro_rules! get_slot_as {
        ($f: ident, $what: literal, $p: pat, $v: ident, $ret_ty: ty) => {
            macro_rules! $f {
                ($self: expr, $idx: expr) => {
                    match &$self.stack[$idx as usize] {
                        $p => $v,
                        _ => {
                            $self.result = Err(Error::new(concat!("type error: expected ", $what)));
                            break;
                        }
                    }
                };
            }
        };
    }

    get_slot_as!(get_slot_int, "int", Value::Int(i), i, i64);
    get_slot_as!(get_slot_nil, "nil", (_i @ Value::Nil), _i, ());
    get_slot_as!(get_slot_bool, "bool", Value::Bool(i), i, bool);
    get_slot_as!(get_slot_str, "string", Value::Str(i), i, &str);
    //get_as_of!(get_slot_codearray, "code array", Value::CodeArray(i), i, CodeArray);
    get_slot_as!(get_slot_expr, "expr", Value::Expr(i), i, k::Expr);
    get_slot_as!(get_slot_thm, "thm", Value::Thm(i), i, k::Thm);
    //get_as_of!(get_slot_sym, "sym", Value::Sym(i), i, k::Ref<str>);

    macro_rules! abs_offset {
        ($sf: expr, $i: expr) => {
            ($sf.start as usize) + ($i as usize)
        };
    }

    impl<'a> VM<'a> {
        /// Create a new VM using the given context.
        pub fn new(ctx: &'a mut Ctx) -> Self {
            /* TODO: use a static dictionary instead.
            // system-level dictionary
            let mut scope0 = Dict::new();
            {
                for ic in INSTR_CORE {
                    let name: k::Ref<str> = ic.name().into();
                    let ca = CodeArray::new(vec![Instr::Core(*ic)]);
                    scope0.0.insert(name, Value::CodeArray(ca));
                }
                for b in logic_builtins::BUILTINS {
                    let name: k::Ref<str> = b.name().into();
                    let ca = CodeArray::new(vec![Instr::Builtin(*b)]);
                    scope0.0.insert(name, Value::CodeArray(ca));
                }
            }
            */
            Self {
                ctx,
                stack: Vec::with_capacity(256),
                ctrl_stack: vec![],
                call_stack: vec![],
                result: Ok(()),
            }
        }

        /*


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
                        return Err(Error::new("`end` does not match a `begin`"));
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
                    println!("  {}", x);
                }
                I::PrintStack => {
                    println!("stack:");
                    for x in st.stack.iter().rev() {
                        println!("  > {}", x);
                    }
                }
                I::Inspect => {
                    let x = st.pop1()?;
                    println!(">>  {:?}", x);
                }
                I::Clear => st.stack.clear(),
                I::Source => {
                    let x = st.pop1_source()?;
                    st.run(&x)?;
                }
                I::LoadFile => {
                    let s = st.pop1_sym()?;
                    let content = std::fs::read_to_string(&*s).map_err(|e| {
                        Error::new_string(format!("cannot load file {:?}: {}", s, e))
                    })?;
                    st.push_val(Value::Source(content.into()))
                }
            }
            Ok(())

        }
        */

        /// Main execution loop.
        fn exec_loop_(&mut self) -> Result<()> {
            use Instr as I;
            while let Some(sf) = self.ctrl_stack.last_mut() {
                assert!((sf.ic as usize) < sf.chunk.0.instrs.len());
                let instr = sf.chunk.0.instrs[sf.ic as usize];
                sf.ic += 1;
                logdebug!(
                    "exec loop: ic={} stacklen={} instr={:?}",
                    sf.ic,
                    self.stack.len(),
                    instr
                );
                match instr {
                    I::Move(s0, s1) => {
                        let s0 = abs_offset!(sf, s0);
                        let s1 = abs_offset!(sf, s1);
                        self.stack[s1] = self.stack[s0].clone();
                    }
                    I::LoadLocal(l0, s1) => {
                        let s1 = abs_offset!(sf, s1);
                        self.stack[s1] = sf.chunk.0.locals[l0.0 as usize].clone();
                    }
                    I::LoadInteger(i, s1) => {
                        let s1 = abs_offset!(sf, s1);
                        self.stack[s1] = Value::Int(i as i64);
                    }
                    I::LoadBool(b, s1) => {
                        let s1 = abs_offset!(sf, s1);
                        self.stack[s1] = Value::Bool(b);
                    }
                    I::LoadNilN(n, s1) => {
                        let s1 = abs_offset!(sf, s1);
                        for i in s1..s1 + (n as usize) {
                            self.stack[i] = Value::Nil
                        }
                    }
                    I::Eq(s0, s1, s2) => {
                        let s0 = abs_offset!(sf, s0);
                        let s1 = abs_offset!(sf, s1);
                        let v = Value::Bool(self.stack[s0] == self.stack[s1]);
                        let s2 = abs_offset!(sf, s2);
                        self.stack[s2] = v
                    }
                    I::Lt(_, _, _) => todo!(),  // TODO
                    I::Leq(_, _, _) => todo!(), // TODO
                    I::Add(s0, s1, s2) => {
                        let s0 = get_slot_int!(self, abs_offset!(sf, s0));
                        let s1 = get_slot_int!(self, abs_offset!(sf, s1));
                        self.stack[abs_offset!(sf, s2)] = Value::Int(s0 + s1);
                    }
                    I::Mul(s0, s1, s2) => {
                        let s0 = get_slot_int!(self, abs_offset!(sf, s0));
                        let s1 = get_slot_int!(self, abs_offset!(sf, s1));
                        self.stack[abs_offset!(sf, s2)] = Value::Int(s0 * s1);
                    }
                    I::Sub(s0, s1, s2) => {
                        let s0 = get_slot_int!(self, abs_offset!(sf, s0));
                        let s1 = get_slot_int!(self, abs_offset!(sf, s1));
                        self.stack[abs_offset!(sf, s2)] = Value::Int(s0 - s1);
                    }
                    I::Div(s0, s1, s2) => {
                        let s0 = get_slot_int!(self, abs_offset!(sf, s0));
                        let s1 = get_slot_int!(self, abs_offset!(sf, s1));
                        if *s1 == 0 {
                            self.result = Err(Error::new("division by zero"));
                            break;
                        }
                        self.stack[abs_offset!(sf, s2)] = Value::Int(s0 / s1);
                    }
                    I::Mod(s0, s1, s2) => {
                        let s0 = get_slot_int!(self, abs_offset!(sf, s0));
                        let s1 = get_slot_int!(self, abs_offset!(sf, s1));
                        self.stack[abs_offset!(sf, s2)] = Value::Int(s0 % s1);
                    }
                    I::EvalStr(_) => todo!("eval str"), // TODO
                    I::LoadFile(s0, s1) => {
                        let s0 = get_slot_str!(self, abs_offset!(sf, s0));
                        let s1 = abs_offset!(sf, s1);
                        let content = match std::fs::read_to_string(&**s0 as &str) {
                            Ok(x) => x.into(),
                            Err(e) => {
                                // TODO: some kind of exception handling
                                self.result = Err(Error::new_string(format!(
                                    "cannot load file `{}: {}",
                                    s0, e
                                )));
                                break;
                            }
                        };
                        self.stack[s1] = Value::Str(content)
                    }
                    I::Pop(n) => {
                        let sz_stack = self.stack.len();
                        if n as usize > sz_stack {
                            self.result = Err(Error::new("stack underflow"));
                            break;
                        }
                        self.stack.truncate(sz_stack - n as usize);
                    }
                    I::Call(sl_f, n_args, sl_ret) => {
                        let sl_f = abs_offset!(sf, sl_f);
                        let offset_ret = abs_offset!(sf, sl_ret);

                        let Self { stack, ctx, .. } = self;
                        match &stack[sl_f] {
                            Value::Builtin(b) => {
                                logdebug!("call builtin {:?}", &b.name);
                                let args = &stack[sl_f + 1..sl_f + 1 + n_args as usize];
                                let f = &b.run;
                                match f(ctx, args) {
                                    Ok(ret_value) => {
                                        self.stack[offset_ret] = ret_value;
                                    }
                                    Err(e) => {
                                        self.result = Err(e);
                                        break;
                                    }
                                }
                            }
                            Value::Chunk(c) => {
                                // push frame for `c`
                                let c = c.clone();
                                logdebug!("call chunk {:?}", &c.0.name);
                                self.exec_chunk_(c, n_args, offset_ret as u32)?;
                            }
                            _ => {
                                self.result = Err(Error::new("cannot call value"));
                                break;
                            }
                        }
                    }
                    I::Become(_, _) => todo!(), // TODO
                    I::Ret(sl_v) => {
                        let sl_v = abs_offset!(sf, sl_v);

                        // pop frame, get return address
                        let res_offset = if let Some(sf) = self.ctrl_stack.pop() {
                            sf.res_offset
                        } else {
                            self.result = Err(Error::new("stack underflow"));
                            break;
                        };

                        if res_offset as usize >= self.stack.len() {
                            self.result = Err(Error::new("invalid res offset"));
                            break;
                        }
                        self.stack[res_offset as usize] = self.stack[sl_v].clone();
                    }
                }
            }

            self.result.clone()
        }

        /// Print the current state of the VM in case of error.
        fn print_trace_(&self, out: &mut dyn io::Write) -> io::Result<()> {
            let mut sf_i = 0;
            let mut stack_i = 0;
            write!(out, "== begin stack trace ==\n")?;
            while sf_i < self.ctrl_stack.len() {
                let sf = &self.ctrl_stack[sf_i];
                write!(
                    out,
                    "  frame[i={}, start={}, ic={}]\n",
                    sf_i, sf.start, sf.ic
                )?;
                // TODO: only print `ic-5..ic+5` window
                write!(out, "  frame.chunk {:#?}\n", sf.chunk)?;
                let next_stack_i = sf.start as usize;
                for i in stack_i..next_stack_i {
                    write!(out, "  st[{:5}] = {}\n", i, &self.stack[i])?;
                }
                stack_i = next_stack_i;
                sf_i += 1;
            }
            for i in stack_i..self.stack.len() {
                write!(out, "  st[{:5}] = {}\n", i, &self.stack[i])?;
            }
            write!(out, "== end stack trace ==\n")?;
            Ok(())
        }

        /*
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
        */

        /// Call chunk `c` with `n_args` arguments, put result into slot `offset`.
        fn exec_chunk_(&mut self, c: Chunk, n_args: u8, res_offset: u32) -> Result<()> {
            if self.stack.len() < n_args as usize {
                return Err(k::Error::new("invoking chunk with too few arguments"));
            }

            // start at top of current stack, minus the given number of arguments,
            // since the arguments are shared between callee and caller's frames.
            let start = (self.stack.len() - n_args as usize) as u32;
            self.ctrl_stack.push(StackFrame {
                ic: 0,
                chunk: c.clone(),
                start,
                res_offset,
            });
            self.stack
                .extend(std::iter::repeat(Value::Nil).take(c.0.n_slots as usize));
            Ok(())
        }

        /// Call toplevel chunk `c`
        fn exec_top_chunk_(&mut self, c: Chunk) -> Result<()> {
            self.exec_chunk_(c, 0, 0)?;
            self.exec_loop_() // enter main loop
        }

        /* TODO
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

        /// Push a value onto the value stack.
        #[inline]
        pub fn push_val(&mut self, v: Value) {
            self.stack.push(v);
        }
        */

        /// Reset execution state.
        fn reset(&mut self) {
            self.stack.clear();
            self.ctrl_stack.clear();
            self.result = Ok(());
        }

        /// Parse and execute the given code.
        pub fn run(&mut self, s: &str) -> Result<()> {
            use parser::*;

            self.reset();
            let mut p = Parser::new(self.ctx, s);

            logdebug!("stack len: {}", self.stack.len());
            logdebug!("meta.run {}", s);

            let c = p.parse_top()?;
            logdebug!("chunk: {:?}", &c);

            let res = dbg!(self.exec_top_chunk_(c));
            if res.is_err() {
                let mut s = vec![];
                self.print_trace_(&mut s).unwrap();
                logerr!(
                    "error during execution\n{}",
                    std::str::from_utf8(&s).unwrap_or("<err>")
                );
            }
            res
        }
    }
}

mod lexer {
    /// A parser for RPN-like syntax, inspired from postscript.
    pub struct Lexer<'b> {
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
        Id(&'b str),           // identifier
        QuotedString(&'b str), // "some string"
        QuotedExpr(&'b str),   // `some expr`
        Int(i64),
        LParen,        // '('
        RParen,        // ')'
        LBracket,      // '['
        RBracket,      // ']'
        LBrace,        // '{'
        RBrace,        // '}'
        Invalid(char), // to report an error
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

    impl<'b> Lexer<'b> {
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
                    while self.i < self.bytes.len() && self.bytes[self.i] != b'\n' {
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
                b'(' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::LParen
                }
                b'{' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::LBrace
                }
                b'[' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::LBracket
                }
                b')' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::RParen
                }
                b'}' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::RBrace
                }
                b']' => {
                    self.i += 1;
                    self.col += 1;
                    Tok::RBracket
                }
                b'`' => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && self.bytes[j] != b'`' {
                        j += 1;
                    }
                    let src_expr = std::str::from_utf8(&self.bytes[self.i + 1..j])
                        .expect("invalid utf8 slice");
                    self.col += j - self.i + 1;
                    self.i = j + 1;
                    Tok::QuotedExpr(src_expr)
                }
                c if c.is_ascii_digit() || c == b'-' => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && self.bytes[j].is_ascii_digit() {
                        j += 1;
                    }
                    let tok =
                        std::str::from_utf8(&self.bytes[self.i..j]).expect("invalid utf8 slice");
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
                    Tok::QuotedString(tok)
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
                    let tok =
                        std::str::from_utf8(&self.bytes[self.i..j]).expect("invalid utf8 slice");
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
            Self {
                col: 1,
                line: 1,
                i: 0,
                bytes: s.as_bytes(),
                cur_: None,
            }
        }
    }
}

mod parser {
    use super::*;
    use lexer::Tok;

    macro_rules! perror {
        ($loc: expr, $fmt: literal) => {
            Error::new_string(format!(
                    concat!( "parse error at {:?}: ", $fmt), $loc))
        };
        ($loc: expr, $fmt: literal, $($arg:expr ),*) => {
            Error::new_string(format!(
                    concat!( "parse error at {:?}: ", $fmt), $loc,
                    $($arg),*))
        };
    }

    impl Compiler {
        /// Convert the compiler's state into a proper chunk.
        pub fn into_chunk(self) -> Chunk {
            let c = ChunkImpl {
                instrs: self.instrs.into_boxed_slice(),
                locals: self.locals.into_boxed_slice(),
                n_slots: self.n_slots,
                name: self.name,
            };
            Chunk(k::Ref::new(c))
        }

        #[inline]
        pub fn get_slot_(&mut self, i: SlotIdx) -> &mut CompilerSlot {
            &mut self.slots[i as usize]
        }

        /// Push the value into `self.locals`, return its index.
        pub fn push_local_(&mut self, v: Value) -> Result<LocalIdx> {
            logdebug!("compiler(name={:?}): push local {}", self.name, v);
            let i = self.locals.len();
            if i > u8::MAX as usize {
                return Err(Error::new("maximum number of locals exceeded"));
            }
            self.locals.push(v);
            Ok(LocalIdx(i as u8))
        }

        /// Emit instruction.
        pub fn emit_instr_(&mut self, i: Instr) {
            logdebug!(
                "compiler(name={:?}, n_locals={}): emit instr {:?}",
                self.name,
                self.locals.len(),
                i
            );
            if let I::Pop(n1) = i {
                if let Some(last_i) = self.instrs.last_mut() {
                    if let I::Pop(n2) = last_i {
                        // optim: merge successive `pop`
                        *last_i = I::Pop(n1 + *n2);
                        return;
                    }
                }
            }
            self.instrs.push(i)
        }

        pub fn allocate_top_slot_with_<F>(&mut self, mut f: F) -> Result<SlotIdx>
        where
            F: FnMut(SlotIdx, &mut CompilerSlot),
        {
            let i = self.slots.len();
            if i > u8::MAX as usize {
                return Err(Error::new("maximum number of slots exceeded"));
            }
            self.n_slots = self.n_slots.max(i as u32 + 1);

            let sl = CompilerSlot {
                var_name: None,
                activated: false,
            };
            self.slots.push(sl);
            f(i as u8, &mut self.slots[i]);

            Ok(i as u8)
        }

        /// Allocate a slot on the stack, to hold a temporary result.
        ///
        /// The slot is considered activated already.
        #[inline]
        pub fn allocate_top_slot_(&mut self) -> Result<SlotIdx> {
            self.allocate_top_slot_with_(|_, sl| sl.activated = true)
        }

        /// Find slot for the given variable `v`.
        pub fn find_slot_of_var_(&self, v: &str) -> Option<SlotIdx> {
            for (i, s) in self.slots.iter().enumerate().rev() {
                if let Some(v2) = &s.var_name {
                    if v2.get() == v {
                        return Some(i as u8);
                    }
                }
            }
            None
        }
    }

    /// A parser.
    pub struct Parser<'a> {
        pub(crate) lexer: lexer::Lexer<'a>,
        ctx: &'a mut k::Ctx,
    }

    /* TODO: use that to lookup builtin funs
    /// All the core instructions.
    const INSTR_CORE: &'static [InstrCore] = {
        use InstrCore::*;
        &[
            Def, If, IfElse, Dup, Swap, Drop, Rot, Eq, Lt, Gt, Leq, Geq, Add, Mul, Sub, Div, Mod,
            PrintStack, Clear, PrintPop, Inspect, Source, LoadFile, Begin, End,
        ]
    };

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
    */

    use Instr as I;

    /// A builtin binary operator
    fn binary_op_(s: &str) -> Option<&'static dyn Fn(SlotIdx, SlotIdx, SlotIdx) -> Instr> {
        macro_rules! ret {
            ($i: expr) => {
                Some(&|s1, s2, s3| $i(s1, s2, s3))
            };
        };
        if s == "+" {
            ret!(I::Add)
        } else if s == "-" {
            ret!(I::Sub)
        } else if s == "*" {
            ret!(I::Mul)
        } else if s == "/" {
            ret!(I::Div)
        } else if s == "%" {
            ret!(I::Mod)
        } else {
            None
        }
    }

    /// Resolve the ID as a chunk or builtin, and put it into `sl`.
    fn resolve_id_(
        ctx: &mut Ctx,
        c: &mut Compiler,
        s: &str,
        loc: (usize, usize),
        sl: SlotIdx,
    ) -> Result<()> {
        if let Some(f_var_slot) = c.find_slot_of_var_(s) {
            assert_ne!(f_var_slot, sl);
            c.emit_instr_(I::Move(f_var_slot, sl));
        } else if let Some(b) = basic_primitives::BUILTINS.iter().find(|b| b.name == s) {
            let lidx = c.push_local_(Value::Builtin(b))?;
            c.emit_instr_(I::LoadLocal(lidx, sl));
        } else if let Some(b) = logic_builtins::BUILTINS.iter().find(|b| b.name == s) {
            let lidx = c.push_local_(Value::Builtin(b))?;
            c.emit_instr_(I::LoadLocal(lidx, sl));
        } else if let Some(ch) = ctx.find_meta_chunk(s) {
            let lidx = c.push_local_(Value::Chunk(ch.clone()))?;
            c.emit_instr_(I::LoadLocal(lidx, sl));
        } else {
            return Err(perror!(loc, "unknown identifier '{}'", s));
        }
        Ok(())
    }

    /// Extract current token as an identifier.
    fn cur_tok_as_id_<'a>(lexer: &'a mut lexer::Lexer, errmsg: &'static str) -> Result<&'a str> {
        match lexer.cur() {
            Tok::Id(s) => Ok(s),
            _ => Err(perror!(lexer.loc(), "{}", errmsg)),
        }
    }

    impl<'a> Parser<'a> {
        /// Create a new parser for source string `s`.
        pub fn new(ctx: &'a mut k::Ctx, s: &'a str) -> Self {
            Self {
                ctx,
                lexer: lexer::Lexer::new(s),
            }
        }

        /// Parse the string given at creation time into a chunk.
        pub fn parse_top(&mut self) -> Result<Chunk> {
            let mut c = Compiler {
                instrs: vec![],
                locals: vec![],
                n_slots: 0,
                name: None,
                slots: vec![],
            };

            c.emit_instr_(I::LoadNilN(0, 1)); // get one slot with `nil` in it
            loop {
                let t = self.lexer.cur();

                if t == Tok::Eof {
                    break;
                }

                self.parse_top_statement_(&mut c)?;
            }
            let n = c.locals.len();
            // pop all but last binding
            if n > 1 {
                c.emit_instr_(I::Pop((n - 1) as u16));
            }
            c.emit_instr_(I::Ret(0)); // return the first argument.

            Ok(c.into_chunk())
        }

        /// Current token
        #[inline]
        fn cur_tok_(&mut self) -> Tok {
            self.lexer.cur()
        }

        /// Next token
        #[inline]
        fn next_tok_(&mut self) -> Tok {
            self.lexer.next()
        }

        /// Parse a toplevel statement in a file or CLI input.
        fn parse_top_statement_(&mut self, c: &mut Compiler) -> Result<()> {
            let t = self.lexer.cur();
            let loc = self.lexer.loc();
            match t {
                Tok::Eof => return Err(perror!(loc, "unexpected EOF")),
                Tok::Id(_) | Tok::QuotedString(..) | Tok::QuotedExpr(..) | Tok::Int(..) => {
                    return Err(perror!(loc, "unexpected token {:?}", t))
                }
                Tok::LParen | Tok::LBracket => {
                    let closing = if t == Tok::LParen {
                        Tok::RParen
                    } else {
                        Tok::RBracket
                    };

                    self.lexer.next();
                    match self.lexer.cur() {
                        Tok::Id("def") => {
                            self.lexer.next();
                            //let id = self.parse_id_()?;
                            //logdebug!("parsing def for {:?}", id);
                            todo!() // TODO
                        }
                        _ => {
                            let sl = c.allocate_top_slot_()?;
                            self.parse_expr_app_(c, closing, sl)?;
                            self.eat_(closing, "unclosed expression")?;
                        }
                    }
                }
                Tok::RParen => {
                    return Err(perror!(loc, "non-closed ')'"));
                }
                Tok::RBracket => {
                    return Err(perror!(loc, "non-closed ']'"));
                }
                Tok::LBrace => {
                    return Err(perror!(loc, "unexpected '{{'"));
                }
                Tok::RBrace => {
                    return Err(perror!(loc, "non-closed '}}'"));
                }
                Tok::Invalid(c) => {
                    return Err(perror!(loc, "invalid charachter '{}'", c));
                }
            };
            Ok(())
        }

        /// Parse an application-type expression, closed with `closing`.
        ///
        /// Put the result into slot `sl_res`.
        fn parse_expr_app_(
            &mut self,
            c: &mut Compiler,
            closing: Tok,
            sl_res: SlotIdx,
        ) -> Result<()> {
            let loc = self.lexer.loc();
            let Self { ctx, lexer, .. } = self;
            let id = cur_tok_as_id_(lexer, "expect an identifier after opening")?;
            logdebug!("parse expr app id={:?}", id);

            if let Some(binop_instr) = binary_op_(id) {
                // binary operator
                self.next_tok_();

                let a_slot = c.allocate_top_slot_()?;
                let b_slot = c.allocate_top_slot_()?;
                self.parse_expr_(c, a_slot)?;
                self.parse_expr_(c, b_slot)?;
                c.emit_instr_(binop_instr(a_slot, b_slot, sl_res));
                c.emit_instr_(I::Pop(2));
                self.eat_(closing, "expected closing in application")?;
                return Ok(());
            }

            if id == "do" {
                // composite expression, defining a local scope.
                let l_slots = c.slots.len();

                // store result of last expression
                let tmp_slot = c.allocate_top_slot_()?;

                loop {
                    if self.cur_tok_() == closing {
                        break;
                    }

                    self.parse_expr_or_let_(c, tmp_slot)?;
                }
                self.eat_(closing, "expected closing after `do`")?;

                // now copy result into `sl_res`
                c.emit_instr_(I::Move(tmp_slot, sl_res));
                // restore stack to its former size.
                // This also deallocates local variables.
                if c.slots.len() > l_slots {
                    let to_pop = c.slots.len() - l_slots;
                    assert!(to_pop < u16::MAX as usize);
                    c.emit_instr_(I::Pop(to_pop as u16));
                }
            } else {
                // make a function call.
                let f_slot = c.allocate_top_slot_()?;
                resolve_id_(ctx, c, id, loc, f_slot)?;
                lexer.next();

                // parse arguments
                let mut n_args = 0;
                loop {
                    if self.cur_tok_() == closing {
                        break;
                    }

                    n_args += 1;
                    if n_args > u8::MAX {
                        return Err(perror!(
                            self.lexer.loc(),
                            "maximum number of arguments exceeded"
                        ));
                    }

                    let sl_arg = c.allocate_top_slot_()?;
                    self.parse_expr_(c, sl_arg)?;
                }

                // emit call
                c.emit_instr_(I::Call(f_slot, n_args as u8, sl_res));
                // pop `f` and the arguments.
                c.emit_instr_(I::Pop((n_args + 1) as u16));
            }
            Ok(())
        }

        /// Parse an expression or a `let`-binding, return `true` if
        /// `sl_res` is assigned.
        fn parse_expr_or_let_(&mut self, c: &mut Compiler, sl_res: SlotIdx) -> Result<bool> {
            match self.cur_tok_() {
                Tok::LParen => {
                    self.next_tok_();
                    self.parse_expr_or_let_app_(c, sl_res, Tok::RParen)
                }
                Tok::LBracket => {
                    self.next_tok_();
                    self.parse_expr_or_let_app_(c, sl_res, Tok::RBracket)
                }
                Tok::LBrace => {
                    self.next_tok_();
                    self.parse_infix_(c, sl_res)?;
                    Ok(true)
                }
                _ => {
                    self.parse_expr_(c, sl_res)?;
                    Ok(true)
                }
            }
        }

        /// Parse an item in a `do` group.
        ///
        /// Returns `true` if `sl_res` was set.
        fn parse_expr_or_let_app_(
            &mut self,
            c: &mut Compiler,
            sl_res: SlotIdx,
            closing: Tok,
        ) -> Result<bool> {
            let Self { lexer, .. } = self;
            let id = cur_tok_as_id_(lexer, "expected 'let' or an identifier after opening")?;
            if id == "let" {
                // local definition.
                lexer.next();

                let id: RStr = cur_tok_as_id_(lexer, "expected an identifer after 'let'")?.into();
                self.next_tok_();

                let sl_x = c.allocate_top_slot_with_(|_, sl| {
                    sl.activated = false;
                    sl.var_name = Some(id.clone());
                })?;

                self.parse_expr_(c, sl_x)?;
                c.get_slot_(sl_x).activated = true;
                self.eat_(closing, "unclosed 'let' expression")?;
                return Ok(false);
            }
            self.parse_expr_app_(c, closing, sl_res)?;
            Ok(true)
        }

        /* TODO: local def?
        } else if id == "def" {
            // local definition.
            self.next_tok_();

            let id = self.cur_tok_as_id_("expect identifier after `def`")?;
            let sl_x = c.allocate_top_slot_with_(|_, sl| {
                sl.activated = true;
                sl.var_name = Some(id.clone());
            });
        */

        fn parse_infix_(&mut self, c: &mut Compiler, sl_res: SlotIdx) -> Result<()> {
            logdebug!("parse infix expr");

            let sl_0 = c.allocate_top_slot_()?;
            let sl_a = c.allocate_top_slot_()?;
            self.parse_expr_(c, sl_a)?;

            let loc = self.lexer.loc();
            let Self { ctx, lexer, .. } = self;
            if let Tok::Id(op) = lexer.cur() {
                if let Some(binop_instr) = binary_op_(op) {
                    lexer.next();
                    // only use two slots, and emit binary op
                    self.parse_expr_(c, sl_0)?;
                    self.eat_(Tok::RBrace, "expected '}' to close infix '{'-expr")?;
                    c.emit_instr_(binop_instr(sl_a, sl_0, sl_res));
                } else {
                    resolve_id_(ctx, c, &op, loc, sl_0)?;
                    lexer.next();
                    let sl_b = c.allocate_top_slot_()?;
                    self.parse_expr_(c, sl_b)?;
                    self.eat_(Tok::RBrace, "expected '}' to close infix '{'-expr")?;
                    c.emit_instr_(I::Call(sl_0, 2, sl_res));
                    c.emit_instr_(I::Pop(3));
                }
                Ok(())
            } else {
                return Err(perror!(self.lexer.loc(), "expected an infix operator"));
            }
        }

        /// Parse an expression into slot `sl_res`
        fn parse_expr_(&mut self, c: &mut Compiler, sl_res: SlotIdx) -> Result<()> {
            logdebug!("parse expr (cur {:?})", self.lexer.cur());
            let Self { ctx, lexer, .. } = self;
            let loc = lexer.loc();
            match lexer.cur() {
                Tok::LParen => {
                    lexer.next();
                    self.parse_expr_app_(c, Tok::RParen, sl_res)?;
                }
                Tok::LBracket => {
                    lexer.next();
                    self.parse_expr_app_(c, Tok::RBracket, sl_res)?;
                }
                Tok::LBrace => {
                    // infix: `{a x b}` is `[0]; a; b; [0]=x; call`
                    lexer.next();
                    self.parse_infix_(c, sl_res)?;
                }
                Tok::Int(i) => {
                    lexer.next();
                    if i >= i16::MIN as i64 && i <= i16::MAX as i64 {
                        // TODO: see if it's already in locals, and reuse
                        c.emit_instr_(I::LoadInteger(i as i16, sl_res))
                    } else {
                        // TODO: see if it's already in locals, and reuse
                        let lidx = c.push_local_(Value::Int(i))?;
                        c.emit_instr_(I::LoadLocal(lidx, sl_res));
                    }
                }
                Tok::Id("true") => {
                    lexer.next();
                    c.emit_instr_(I::LoadBool(true, sl_res))
                }
                Tok::Id("false") => {
                    lexer.next();
                    c.emit_instr_(I::LoadBool(true, sl_res))
                }
                Tok::Id(id) => {
                    resolve_id_(ctx, c, id, loc, sl_res)?;
                    lexer.next();
                }
                Tok::QuotedString(s) => {
                    // TODO: find a local that contains `s`, if any,
                    // and reuse it
                    let lidx = c.push_local_(Value::Str(s.into()))?;
                    self.next_tok_();
                    c.emit_instr_(I::LoadLocal(lidx, sl_res))
                }
                Tok::QuotedExpr(e) => {
                    if e.as_bytes().contains(&b'?') {
                        // TODO: interpolation
                        return Err(perror!(loc, "unimplemented: interpolating exprs"));
                    }
                    let e = syntax::parse_expr(self.ctx, e)
                        .map_err(|e| perror!(loc, "while parsing expression: {}", e))?;
                    // TODO: reuse local if `e` is there already
                    let lidx = c.push_local_(Value::Expr(e))?;
                    self.next_tok_();
                    c.emit_instr_(I::LoadLocal(lidx, sl_res))
                }
                Tok::RParen | Tok::RBracket | Tok::RBrace => {
                    return Err(perror!(loc, "invalid closing delimiter"))
                }
                Tok::Invalid(c) => return Err(perror!(loc, "invalid char {}", c)),

                Tok::Eof => return Err(perror!(loc, "unexpected EOF when parsing expr")),
            }
            Ok(())
        }

        /// Expect the token `t`, and consume it; or return an error.
        fn eat_(&mut self, t: lexer::Tok, errmsg: &str) -> Result<()> {
            if self.lexer.cur() == t {
                self.lexer.next();
                Ok(())
            } else {
                Err(perror!(self.lexer.loc(), "{}", errmsg))
            }
        }
    }
}

mod basic_primitives {
    use super::*;

    // TODO: defty

    /// Builtin functions.
    pub(super) const BUILTINS: &'static [InstrBuiltin] = &[
        InstrBuiltin {
            name: "print",
            help: "print a value.",
            run: |_, args: &[Value]| {
                for x in args {
                    println!("> {}", x)
                }
                Ok(Value::Nil)
            },
        },
        /* TODO
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
        */
    ];
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
    pub(super) const BUILTINS: &'static [&'static InstrBuiltin] = &[
        /* TODO
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
        */
    ];

    /* TODO
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
    */
}

/// Standard prelude for HOL logic
pub const SRC_PRELUDE_HOL: &'static str = include_str!("prelude.trustee");

/// Run the given code in a fresh VM.
///
/// This has some overhead, if you want to execute a lot of code efficienty
/// (e.g. in a CLI) consider creating a `VM` and re-using it.
pub fn run_code(ctx: &mut Ctx, s: &str) -> Result<()> {
    let mut st = VM::new(ctx);
    st.run(s)
}

/// Load the HOL prelude into this context.
///
/// This uses a temporary VM. See `run_code` for more details.
pub fn load_prelude_hol(ctx: &mut Ctx) -> Result<()> {
    if ctx.find_const("hol_prelude_loaded").is_none() {
        run_code(ctx, SRC_PRELUDE_HOL)?;
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_sizeof_instr() {
        // make sure instructions remain small
        assert_eq!(std::mem::size_of::<Instr>(), 4);
    }

    #[test]
    fn test_sizeof_value() {
        // make sure values are at most 2 words
        let sz = std::mem::size_of::<k::Symbol>();
        println!("sizeof(symbol) is {}", sz);
        let sz = std::mem::size_of::<k::Expr>();
        println!("sizeof(expr) is {}", sz);
        let sz = std::mem::size_of::<k::Thm>();
        println!("sizeof(thm) is {}", sz);
        let sz = std::mem::size_of::<RStr>();
        println!("sizeof(rstr) is {}", sz);
        let sz = std::mem::size_of::<Value>();
        println!("sizeof(value) is {}", sz);
        assert!(sz <= 16);
    }

    macro_rules! lex_test {
        ($a:expr) => {
            for (s, v) in $a {
                let mut p = lexer::Lexer::new(s);
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
        };
    }

    #[test]
    fn test_lexer() {
        use lexer::Tok as T;
        let a = vec![(
            r#" ("a" "b"[mul 2}"d" { 3 } def) 2  "#,
            vec![
                T::LParen,
                T::QuotedString("a"),
                T::QuotedString("b"),
                T::LBracket,
                T::Id("mul"),
                T::Int(2),
                T::RBrace,
                T::QuotedString("d"),
                T::LBrace,
                T::Int(3),
                T::RBrace,
                T::Id("def"),
                T::RParen,
                T::Int(2),
                T::Eof,
            ],
        )];
        lex_test!(a)
    }

    #[test]
    fn test_lexer2() {
        use lexer::Tok as T;
        let a = vec![(
            r#"(print {1 + 1})"#,
            vec![
                T::LParen,
                T::Id("print"),
                T::LBrace,
                T::Int(1),
                T::Id("+"),
                T::Int(1),
                T::RBrace,
                T::RParen,
                T::Eof,
            ],
        )];
        lex_test!(a)
    }

    /* TODO
    #[test]
    fn test_basic_ops() -> Result<()> {
        let mut ctx = k::Ctx::new();
        let mut st = VM::new(&mut ctx);

        st.run("(+ 1 2)")?;
        let v = st.pop1_int()?;
        assert_eq!(v, 3);

        Ok(())
    }

    // TODO
    #[test]
    fn test_parse_prelude_and_forall() -> Result<()> {
        let mut ctx = k::Ctx::new();
        let mut st = VM::new(&mut ctx);

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

    #[test]
    fn test_load_hol_prelude() -> Result<()> {
        let mut ctx = k::Ctx::new();
        load_prelude_hol(&mut ctx)?;
        load_prelude_hol(&mut ctx)?; // can we load it twice?
        Ok(())
    }
    */
}
