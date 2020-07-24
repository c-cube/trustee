//! Meta-language.
//!
//! The meta-language is a tiny lisp-like stack language that manipulates
//! expressions, goals, theorems, and other values. It is designed to be
//! used both interactively and as an efficient way of storing proofs.

use {
    crate::{
        algo,
        kernel_of_trust::{self as k, Ctx},
        rptr::RPtr,
        rstr::RStr,
        syntax, Error, Result,
    },
    std::{fmt, i16, io, u8},
};

macro_rules! logtrace{
    ($($t:expr),*) => {
        #[cfg(feature="logging")]
        log::trace!($($t),*)
    }
}
macro_rules! logdebug{
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

// TODO: closure

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
    // TODO: add `cons?`, `car`, `cdr`… or destructuring
    /// Cons: a pair of values. This is the basis for lists.
    Cons(RPtr<(Value, Value)>),
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
    name: Option<RStr>,
}

/// Compiler for a given chunk.
struct Compiler<'a> {
    instrs: Vec<Instr>,
    locals: Vec<Value>,
    /// Maximum size `slots` ever took.
    n_slots: u32,
    name: Option<RStr>,
    slots: Vec<CompilerSlot>,
    /// Parent compiler, used to resolve values from outer scopes.
    parent: Option<&'a Compiler<'a>>,
}

#[derive(Debug)]
struct CompilerSlot {
    /// If this slot is for a named variable.
    var_name: Option<RStr>,
    state: CompilerSlotState,
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum CompilerSlotState {
    Unused,
    NotActivatedYet,
    Activated,
}

/// Result of parsing an expression into the current chunk.
///
/// All expressions return a value, which lives in a slot (`self.slot`).
/// The slot might have been allocated for this purpose, in which case
/// `self.temporary` will be true, meaning the slot can be disposed of
/// when the expression is not needed anymore.
#[derive(Clone, Debug)]
struct ExprRes {
    /// Where the result lives.
    slot: SlotIdx,
    /// Was the slot allocated for this expression?
    temporary: bool,
    /// Does this actually return? If true, it means evaluation exited.
    exited: bool,
}

/// Index in the array of slots.
#[derive(Copy, Clone, PartialEq)]
struct SlotIdx(u8);

/// Index in the array of locals.
#[derive(Copy, Clone, PartialEq)]
struct LocalIdx(u8);

#[must_use]
#[derive(Debug)]
struct JumpPosition(usize);

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
    /// Load the current chunk into `sl[$0]`
    LoadSelfChunk(SlotIdx),
    /// Set `sl[$1]` to bool `$0`
    LoadBool(bool, SlotIdx),
    /// Set `sl[$1]` to nil
    LoadNil(SlotIdx),
    /// Set `sl[$2]` to `cons(sl[$0], sl[$1])`
    Cons(SlotIdx, SlotIdx, SlotIdx),
    /// `sl[$2] = (sl[$0] == sl[$1])`
    Eq(SlotIdx, SlotIdx, SlotIdx),
    /// `sl[$2] = (sl[$0] != sl[$1])`
    Neq(SlotIdx, SlotIdx, SlotIdx),
    Lt(SlotIdx, SlotIdx, SlotIdx),
    Leq(SlotIdx, SlotIdx, SlotIdx),
    Add(SlotIdx, SlotIdx, SlotIdx),
    Mul(SlotIdx, SlotIdx, SlotIdx),
    Sub(SlotIdx, SlotIdx, SlotIdx),
    Div(SlotIdx, SlotIdx, SlotIdx),
    Mod(SlotIdx, SlotIdx, SlotIdx),
    /// puts `is-cons sl[$0]` into `sl[$1]`
    IsPair(SlotIdx, SlotIdx),
    /// puts `car sl[$0]` into `sl[$1]`
    Car(SlotIdx, SlotIdx),
    /// puts `cdr sl[$0]` into `sl[$1]`
    Cdr(SlotIdx, SlotIdx),
    /// Set `sl[$1]` to `not sl[$0]`
    Not(SlotIdx, SlotIdx),
    /// Jump to `ic + $1` if `sl[$0]` is false
    JumpIfFalse(SlotIdx, i16),
    /// Jump to `ic + $1` if `sl[$0]` is true
    JumpIfTrue(SlotIdx, i16),
    /// Jump to `ic + $1` unconditionally
    Jump(i16),
    /// Push `sl[$0]` into the call array, before a call.
    PushCallArgCpy(SlotIdx),
    /// Push `sl[$0]` into the call array and empty it, before a call.
    PushCallArgMove(SlotIdx),
    // TODO: reinstate `Call1`
    /// Call chunk `sl[$0]` with arguments in `vm.call_args`
    /// and put the result into `sl[$2]`.
    ///
    /// `$1` is the number of arguments the function takes.
    Call(SlotIdx, SlotIdx),
    /// Tail-call into chunk `sl[$0]` with arguments in `call_args`.
    /// Does not return.
    Become(SlotIdx),
    // TODO: remove argument? should already have set slot
    /// Return from current chunk with value `sl[$0]`.
    Ret(SlotIdx),
    // TODO: control flow:
    // - `Jump(SlotIdx, offset:u16)`
    // - `JumpIfTrue(SlotIdx, offset:i16)`
    // - `JumpIfFalse(SlotIdx, offset:i16)`
    /// Error.
    Trap,
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

// TODO: check `exited` in all subexpressions?

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
    /// Array of arguments used to pass arguments to a chunk before execution.
    /// This is typically reset before each function call.
    call_args: Vec<Value>,
    /// In case of error, the error message lives here.
    result: Result<Value>,
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

    impl Value {
        /// Build a cons.
        pub fn cons(x: Value, y: Value) -> Value {
            Value::Cons(RPtr::new((x, y)))
        }

        /// Build a proper list using `cons`.
        pub fn list(xs: &[Value]) -> Value {
            let mut r = Value::Nil;
            for x in xs.iter().rev() {
                r = Value::cons(x.clone(), r)
            }
            r
        }

        /// Build a proper list using `cons`.
        pub fn list_iter<I, V>(xs: I) -> Value
        where
            V: Into<Value>,
            I: DoubleEndedIterator<Item = V>,
        {
            let mut r = Value::Nil;
            for x in xs.rev() {
                r = Value::cons(x.into(), r)
            }
            r
        }
    }

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

    impl fmt::Debug for SlotIdx {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "sl[{}]", self.0)
        }
    }
    impl fmt::Debug for LocalIdx {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "loc[{}]", self.0)
        }
    }

    impl Chunk {
        /// Trivial chunk that returns `nil`
        pub fn retnil() -> Self {
            Chunk(k::Ref::new(ChunkImpl {
                name: None,
                instrs: vec![Instr::Ret(SlotIdx(0))].into(),
                locals: Box::new([]),
                n_slots: 1,
            }))
        }
    }

    /// Print a value.
    impl fmt::Display for Value {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Value::Nil => write!(out, "nil"),
                Value::Int(i) => write!(out, "{}", i),
                Value::Bool(b) => write!(out, "{}", b),
                Value::Sym(s) => write!(out, ":{}", s.name()),
                Value::Cons(v) => write!(out, "{{{} . {}}}", v.0, v.1),
                Value::Str(s) => write!(out, "{:?}", s),
                Value::Expr(e) => write!(out, "`{}`", e),
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
                (Str(i), Str(j)) => i == j,
                (Cons(i), Cons(j)) => i == j,
                (Expr(i), Expr(j)) => i == j,
                (Chunk(c1), Chunk(c2)) => std::ptr::eq(&*c1.0 as *const _, &*c2.0),
                (Builtin(b1), Builtin(b2)) => std::ptr::eq(&*b1 as *const _, &*b2),
                _ => false, // other cases are not comparable
            }
        }
    }

    impl From<i64> for Value {
        fn from(x: i64) -> Self {
            Value::Int(x)
        }
    }

    impl From<i32> for Value {
        fn from(x: i32) -> Self {
            Value::Int(x as i64)
        }
    }

    impl From<bool> for Value {
        fn from(b: bool) -> Self {
            Value::Bool(b)
        }
    }

    impl From<()> for Value {
        fn from(_: ()) -> Self {
            Value::Nil
        }
    }

    impl From<k::Expr> for Value {
        fn from(e: k::Expr) -> Self {
            Value::Expr(e)
        }
    }

    impl From<k::Thm> for Value {
        fn from(th: k::Thm) -> Self {
            Value::Thm(th)
        }
    }

    impl<T> From<Vec<T>> for Value
    where
        T: Into<Value>,
    {
        fn from(v: Vec<T>) -> Self {
            Value::list_iter(v.into_iter())
        }
    }

    macro_rules! get_slot_as {
        ($f: ident, $what: literal, $p: pat, $v: expr, $ret_ty: ty) => {
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
    //get_slot_as!(get_slot_nil, "nil", (_i @ Value::Nil), _i, ());
    get_slot_as!(get_slot_bool, "bool", Value::Bool(i), *i, bool);
    //get_slot_as!(get_slot_str, "string", Value::Str(i), i, &str);
    //get_as_of!(get_slot_codearray, "code array", Value::CodeArray(i), i, CodeArray);
    //get_slot_as!(get_slot_expr, "expr", Value::Expr(i), i, k::Expr);
    //get_slot_as!(get_slot_thm, "thm", Value::Thm(i), i, k::Thm);
    //get_as_of!(get_slot_sym, "sym", Value::Sym(i), i, k::Ref<str>);

    macro_rules! abs_offset {
        ($sf: expr, $i: expr) => {
            ($sf.start as usize) + ($i.0 as usize)
        };
    }

    impl<'a> VM<'a> {
        /// Create a new VM using the given context.
        pub fn new(ctx: &'a mut Ctx) -> Self {
            Self {
                ctx,
                stack: Vec::with_capacity(256),
                ctrl_stack: vec![],
                call_args: vec![],
                result: Ok(Value::Nil),
            }
        }

        /// Main execution loop.
        fn exec_loop_(&mut self) -> Result<Value> {
            use Instr as I;
            while let Some(sf) = self.ctrl_stack.last_mut() {
                assert!((sf.ic as usize) < sf.chunk.0.instrs.len());
                let instr = sf.chunk.0.instrs[sf.ic as usize];
                logdebug!(
                    "exec loop: ic={} stacklen={} instr={:?}",
                    sf.ic,
                    self.stack.len(),
                    instr
                );

                sf.ic += 1; // ready for next iteration
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
                    I::LoadSelfChunk(s0) => {
                        let s0 = abs_offset!(sf, s0);
                        self.stack[s0] = Value::Chunk(sf.chunk.clone());
                    }
                    I::LoadInteger(i, s1) => {
                        let s1 = abs_offset!(sf, s1);
                        self.stack[s1] = Value::Int(i as i64);
                    }
                    I::LoadBool(b, s1) => {
                        let s1 = abs_offset!(sf, s1);
                        self.stack[s1] = Value::Bool(b);
                    }
                    I::LoadNil(s1) => {
                        let s1 = abs_offset!(sf, s1);
                        self.stack[s1] = Value::Nil;
                    }
                    I::Cons(s0, s1, s2) => {
                        let s0 = abs_offset!(sf, s0);
                        let s1 = abs_offset!(sf, s1);
                        let v = Value::Cons(RPtr::new((
                            self.stack[s0].clone(),
                            self.stack[s1].clone(),
                        )));
                        let s2 = abs_offset!(sf, s2);
                        self.stack[s2] = v
                    }
                    I::Eq(s0, s1, s2) => {
                        let s0 = abs_offset!(sf, s0);
                        let s1 = abs_offset!(sf, s1);
                        let v = Value::Bool(self.stack[s0] == self.stack[s1]);
                        let s2 = abs_offset!(sf, s2);
                        self.stack[s2] = v
                    }
                    I::Neq(s0, s1, s2) => {
                        let s0 = abs_offset!(sf, s0);
                        let s1 = abs_offset!(sf, s1);
                        let v = Value::Bool(self.stack[s0] != self.stack[s1]);
                        let s2 = abs_offset!(sf, s2);
                        self.stack[s2] = v
                    }
                    I::Lt(s0, s1, s2) => {
                        let s0 = get_slot_int!(self, abs_offset!(sf, s0));
                        let s1 = get_slot_int!(self, abs_offset!(sf, s1));
                        let v = Value::Bool(s0 < s1);
                        let s2 = abs_offset!(sf, s2);
                        self.stack[s2] = v;
                    }
                    I::Leq(s0, s1, s2) => {
                        let s0 = get_slot_int!(self, abs_offset!(sf, s0));
                        let s1 = get_slot_int!(self, abs_offset!(sf, s1));
                        let v = Value::Bool(s0 <= s1);
                        let s2 = abs_offset!(sf, s2);
                        self.stack[s2] = v;
                    }
                    I::Not(s0, s1) => {
                        let s0 = get_slot_bool!(self, abs_offset!(sf, s0));
                        self.stack[abs_offset!(sf, s1)] = Value::Bool(!s0);
                    }
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
                    I::IsPair(s0, s1) => {
                        let b = match &self.stack[abs_offset!(sf, s0)] {
                            Value::Cons(..) => true,
                            _ => false,
                        };
                        self.stack[abs_offset!(sf, s1)] = Value::Bool(b);
                    }
                    I::Car(s0, s1) => {
                        let v = match &self.stack[abs_offset!(sf, s0)] {
                            Value::Cons(p) => p.0.clone(),
                            _ => {
                                self.result = Err(Error::new("car called on a non-pair"));
                                break;
                            }
                        };
                        self.stack[abs_offset!(sf, s1)] = v;
                    }
                    I::Cdr(s0, s1) => {
                        let v = match &self.stack[abs_offset!(sf, s0)] {
                            Value::Cons(p) => p.1.clone(),
                            _ => {
                                self.result = Err(Error::new("cdr called on a non-pair"));
                                break;
                            }
                        };
                        self.stack[abs_offset!(sf, s1)] = v;
                    }
                    I::Jump(offset) => {
                        logdebug!("jump from ic={} with offset {}", sf.ic, offset);
                        sf.ic = (sf.ic as isize + offset as isize) as u32
                    }
                    I::JumpIfTrue(s0, offset) => {
                        let s0 = get_slot_bool!(self, abs_offset!(sf, s0));
                        if s0 {
                            logdebug!("jump from ic={} with offset {}", sf.ic, offset);
                            sf.ic = (sf.ic as isize + offset as isize) as u32
                        }
                    }
                    I::JumpIfFalse(s0, offset) => {
                        let s0 = get_slot_bool!(self, abs_offset!(sf, s0));
                        if !s0 {
                            logdebug!("jump from ic={} with offset {}", sf.ic, offset);
                            sf.ic = (sf.ic as isize + offset as isize) as u32
                        }
                    }
                    I::PushCallArgCpy(sl_arg) => {
                        let sl_f = abs_offset!(sf, sl_arg);
                        let v = self.stack[sl_f].clone();
                        self.call_args.push(v);
                    }
                    I::PushCallArgMove(sl_arg) => {
                        let sl_f = abs_offset!(sf, sl_arg);
                        let mut v = Value::Nil;
                        std::mem::swap(&mut v, &mut self.stack[sl_f]);
                        self.call_args.push(v);
                    }
                    I::Call(sl_f, sl_ret) => {
                        let sl_f = abs_offset!(sf, sl_f);
                        let offset_ret = abs_offset!(sf, sl_ret);

                        let Self {
                            stack,
                            ctx,
                            call_args,
                            ..
                        } = self;
                        match &stack[sl_f] {
                            Value::Builtin(b) => {
                                logdebug!(
                                    "call builtin {:?} with {} args",
                                    &b.name,
                                    call_args.len()
                                );
                                let f = &b.run;
                                let res = f(ctx, &call_args);
                                call_args.clear();
                                match res {
                                    Ok(ret_value) => {
                                        logdebug!("returned {}", ret_value);
                                        self.stack[offset_ret] = ret_value;
                                    }
                                    Err(mut e) => {
                                        // TODO: proper stack trace instead
                                        e = e.set_source(Error::new_string(format!(
                                            "while calling {}",
                                            b.name
                                        )));
                                        self.result = Err(e);
                                        break;
                                    }
                                }
                            }
                            Value::Chunk(c) => {
                                // push frame for `c`
                                let c = c.clone();
                                self.exec_chunk_(c, offset_ret as u32)?;
                            }
                            _ => {
                                self.result = Err(Error::new("cannot call value"));
                                break;
                            }
                        }
                    }
                    I::Become(sl_f) => {
                        if self.ctrl_stack.is_empty() {
                            self.result = Err(Error::new("tailcall from empty stack"));
                            break;
                        }

                        let Self {
                            ctrl_stack,
                            ctx,
                            stack,
                            call_args,
                            ..
                        } = self;

                        // pop last stack frame. the tailcallee will
                        // do without one, or allocate its own.
                        let sf = ctrl_stack.pop().unwrap();

                        // fetch function
                        let offset_f = abs_offset!(sf, sl_f);
                        let offset_ret = sf.res_offset;
                        let f = stack[offset_f].clone();

                        stack.truncate(sf.start as usize);
                        match f {
                            Value::Chunk(c) => {
                                self.exec_chunk_(c, offset_ret as u32)?;
                            }
                            Value::Builtin(b) => {
                                logdebug!("call builtin {:?}", &b.name);
                                let f = &b.run;
                                match f(ctx, &call_args) {
                                    Ok(ret_value) => {
                                        self.stack[offset_ret as usize] = ret_value;
                                    }
                                    Err(e) => {
                                        self.result = Err(e);
                                        break;
                                    }
                                }
                            }
                            _ => {
                                self.result = Err(Error::new("cannot call value"));
                                break;
                            }
                        }
                    }
                    I::Ret(sl_v) => {
                        let sl_v = abs_offset!(sf, sl_v);

                        // pop frame, get return address and frame offset
                        let res_offset;
                        let start;
                        if let Some(sf) = self.ctrl_stack.pop() {
                            res_offset = sf.res_offset;
                            start = sf.start;
                        } else {
                            self.result = Err(Error::new("stack underflow"));
                            break;
                        };

                        if res_offset as usize >= self.stack.len() {
                            self.result = Err(Error::new("invalid res offset"));
                            break;
                        }

                        let ret_val = self.stack[sl_v].clone();

                        if self.ctrl_stack.is_empty() {
                            self.result = Ok(ret_val); // no more frames, will return
                        } else {
                            self.stack[res_offset as usize] = ret_val;
                        }
                        // pop slots of the function call
                        self.stack.truncate(start as usize);
                    }
                    I::Trap => {
                        self.result = Err(Error::new("executed `trap`"));
                        break;
                    }
                }
            }

            self.call_args.clear();
            let mut r = Ok(Value::Nil);
            std::mem::swap(&mut r, &mut self.result);
            r
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

        /// Call chunk `c` with arguments in `self.call_args`,
        /// put result into slot `offset`.
        fn exec_chunk_(&mut self, c: Chunk, res_offset: u32) -> Result<()> {
            logdebug!("call chunk (name={:?})", &c.0.name);
            let start = self.stack.len() as u32;

            // push `self.call_args` on top of stack
            let Self {
                stack, call_args, ..
            } = self;
            stack.extend(call_args.drain(..));

            // also allocate as many slots as needed by `c`.
            self.stack
                .extend(std::iter::repeat(Value::Nil).take(c.0.n_slots as usize));
            self.ctrl_stack.push(StackFrame {
                ic: 0,
                chunk: c,
                start,
                res_offset,
            });
            Ok(())
        }

        /// Call toplevel chunk `c`
        fn exec_top_chunk_(&mut self, c: Chunk) -> Result<Value> {
            assert_eq!(self.call_args.len(), 0);
            self.exec_chunk_(c, 0)?;
            self.exec_loop_()
        }

        /// Reset execution state.
        fn reset(&mut self) {
            self.stack.clear();
            self.ctrl_stack.clear();
            self.call_args.clear();
            self.result = Ok(Value::Nil);
        }

        /// Parse and execute the given code.
        pub fn run(&mut self, s: &str) -> Result<Value> {
            use parser::*;

            self.reset();
            logdebug!("meta.run {}", s);
            let mut lexer = lexer::Lexer::new(s);
            let mut last_r = Value::Nil;

            loop {
                let p = Parser::new(self.ctx, &mut lexer);

                match p.parse_top_statement() {
                    Err(e) => {
                        logerr!("error while parsing: {}", e);
                        return Err(e);
                    }
                    Ok(Some(c)) => {
                        logdebug!("chunk: {:?}", &c);
                        match self.exec_top_chunk_(c) {
                            Ok(x) => last_r = x,
                            Err(e) => {
                                let mut s = vec![];
                                self.print_trace_(&mut s).unwrap();
                                logerr!(
                                    "error during execution\n{}",
                                    std::str::from_utf8(&s).unwrap_or("<err>")
                                );

                                return Err(e);
                            }
                        }
                    }
                    Ok(None) => return Ok(last_r),
                };
            }
        }
    }
}

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

mod lexer {
    use super::*;

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
        ColonId(&'b str),      // `:foo`
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
            | b'='
            | b'+'
            | b'-'
            | b'.'
            | b'@'
            | b'!'
            | b'$'
            | b'%'
            | b'^'
            | b'&'
            | b'*'
            | b'|'
            | b'/'
            | b'>'
            | b'<'
            | b'\\'
            | b'?'
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
                if c == b';' {
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

        /// Expect the token `t`, and consume it; or return an error.
        pub fn eat_(&mut self, t: Tok, errmsg: &str) -> Result<()> {
            if self.cur() == t {
                self.next();
                Ok(())
            } else {
                Err(perror!(self.loc(), "{}", errmsg))
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
                c if c.is_ascii_digit() => {
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
                b':' => {
                    let mut j = self.i + 1;
                    while j < self.bytes.len() && {
                        let c = self.bytes[j];
                        is_id_char(c) || (j > self.i + 1 && c.is_ascii_digit())
                    } {
                        j += 1;
                    }
                    let tok = std::str::from_utf8(&self.bytes[self.i + 1..j])
                        .expect("invalid utf8 slice");
                    self.col += j - self.i;
                    self.i = j;
                    Tok::ColonId(tok)
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
                    match str::parse(tok) {
                        Ok(n) => Tok::Int(n), // if all numerics
                        Err(_) => Tok::Id(tok),
                    }
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

// TODO: accept `?` tokens, with a list of externally passed args.
//  This enables: `run_with_args("(mp ? some_def)", &[my_thm])`

// TODO: enable recursion in `defn` (have `PushSelf` as instr, use it
//  when parsing `f` in a chunk named `f`)?
//  *OR* more general case, `PushFromStack(-n)` so we can tailcall from
//      nested functions?

// TODO: closures (with call_args then `MkClosure(sl_callable, sl_res)`
//          which makes a Value::Closure with all the call_args)

pub(crate) mod parser {
    use super::*;
    use lexer::Tok;

    impl ExprRes {
        /// Make a new expression result.
        fn new(sl: SlotIdx, temporary: bool) -> Self {
            Self {
                slot: sl,
                temporary,
                exited: false,
            }
        }
    }

    impl<'a> Compiler<'a> {
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
            &mut self.slots[i.0 as usize]
        }

        /// Ensure the value is in `self.locals`, return its index.
        pub fn allocate_local_(&mut self, v: Value) -> Result<LocalIdx> {
            logdebug!("compiler(name={:?}): push local {}", self.name, v);

            // see if `v` is a local already.
            if let Some((i, _)) = self.locals.iter().enumerate().find(|(_, v2)| *v2 == &v) {
                return Ok(LocalIdx(i as u8));
            }

            // else push a new local
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
            self.instrs.push(i)
        }

        /// Reserve space for a jump instruction that will be emitted later.
        pub fn reserve_jump_(&mut self) -> JumpPosition {
            let off = self.instrs.len();
            logdebug!(
                "compiler(name={:?}, n_locals={}): reserve jump at offset {}",
                self.name,
                self.locals.len(),
                off
            );

            self.instrs.push(I::Trap); // reserve space
            JumpPosition(off)
        }

        /// Set the jump instruction for a previously reserved jump slot.
        pub fn emit_jump(
            &mut self,
            pos: JumpPosition,
            mk_i: impl FnOnce(i16) -> Instr,
        ) -> Result<()> {
            let i = if let I::Trap = self.instrs[pos.0] {
                let j_offset = self.instrs.len() as isize - pos.0 as isize - 1;
                if j_offset < i16::MIN as isize || j_offset > i16::MAX as isize {
                    return Err(Error::new("jump is too long"));
                }
                mk_i(j_offset as i16)
            } else {
                panic!("jump already edited at pos {}", pos.0);
            };

            logdebug!(
                "compiler(name={:?}, n_locals={}): emit jump {:?} at offset {}",
                self.name,
                self.locals.len(),
                i,
                pos.0
            );
            self.instrs[pos.0] = i;
            Ok(())
        }

        /// Allocate a slot on top of the stack.
        fn allocate_top_slot_(&mut self, st: CompilerSlotState) -> Result<SlotIdx> {
            assert_ne!(st, CompilerSlotState::Unused);
            let i = self.slots.len();
            if i > u8::MAX as usize {
                return Err(Error::new("maximum number of slots exceeded"));
            }
            self.n_slots = self.n_slots.max(i as u32 + 1);

            let sl = CompilerSlot {
                var_name: None,
                state: st,
            };
            self.slots.push(sl);
            Ok(SlotIdx(i as u8))
        }

        /// Allocate or reuse a slot.
        fn allocate_any_slot_(&mut self, st: CompilerSlotState) -> Result<SlotIdx> {
            if let Some((i, sl)) = self
                .slots
                .iter_mut()
                .enumerate()
                .find(|(_, sl)| sl.state == CompilerSlotState::Unused)
            {
                // we can reuse slot `i`
                sl.state = st;
                assert!(i < u8::MAX as usize);
                Ok(SlotIdx(i as u8))
            } else {
                self.allocate_top_slot_(st)
            }
        }

        /// Allocate a variable (bound, local, etc.) somewhere in the stack.
        pub fn allocate_var_(&mut self, name: RStr) -> Result<ExprRes> {
            let slot = self.allocate_any_slot_(CompilerSlotState::NotActivatedYet)?;
            self.get_slot_(slot).var_name = Some(name);
            Ok(ExprRes::new(slot, false))
        }

        /// Allocate a slot on the stack, anywhere, to hold a temporary result.
        pub fn allocate_temporary_(&mut self) -> Result<ExprRes> {
            let slot = self.allocate_any_slot_(CompilerSlotState::Activated)?;
            Ok(ExprRes::new(slot, true))
        }

        pub fn allocate_temporary_on_top_(&mut self) -> Result<ExprRes> {
            let slot = self.allocate_top_slot_(CompilerSlotState::Activated)?;
            Ok(ExprRes::new(slot, true))
        }

        /// Free expression result.
        pub fn free(&mut self, e: &ExprRes) {
            if e.temporary {
                self.deallocate_slot_(e.slot)
            }
        }

        /// Deallocate that slot, it becomes available for further use.
        pub fn deallocate_slot_(&mut self, sl: SlotIdx) {
            if sl.0 as usize + 1 == self.slots.len() {
                // just pop the slot
                self.slots.pop().unwrap();
            } else {
                let sl = self.get_slot_(sl);
                sl.var_name = None;
                sl.state = CompilerSlotState::Unused;
            }
        }

        // TODO: also look in parents scopes, and return an upvalue
        /// Find slot for the given variable `v`.
        pub fn find_slot_of_var(&self, v: &str) -> Option<SlotIdx> {
            for (i, s) in self.slots.iter().enumerate().rev() {
                if s.state != CompilerSlotState::Activated {
                    continue; // slot is not actually ready
                }
                if let Some(v2) = &s.var_name {
                    if v2.get() == v {
                        return Some(SlotIdx(i as u8));
                    }
                }
            }
            None
        }
    }

    /// A parser.
    pub struct Parser<'a, 'b, 'c> {
        pub(crate) lexer: &'c mut lexer::Lexer<'b>,
        ctx: &'a mut k::Ctx,
    }

    use Instr as I;

    /// A builtin binary operator
    fn binary_op_(s: &str) -> Option<&'static dyn Fn(SlotIdx, SlotIdx, SlotIdx) -> Instr> {
        macro_rules! ret {
            ($i: expr) => {
                Some(&|s1, s2, s3| $i(s1, s2, s3))
            };
        };
        macro_rules! ret_swap {
            ($i: expr) => {
                Some(&|s1, s2, s3| $i(s2, s1, s3))
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
        } else if s == "." {
            ret!(I::Cons)
        } else if s == "==" {
            ret!(I::Eq)
        } else if s == "!=" {
            ret!(I::Neq)
        } else if s == "<" {
            ret!(I::Lt)
        } else if s == "<=" {
            ret!(I::Leq)
        } else if s == ">" {
            ret_swap!(I::Lt)
        } else if s == ">=" {
            ret_swap!(I::Leq)
        } else {
            None
        }
    }

    /// A builtin binary operator
    fn unary_op_(s: &str) -> Option<&'static dyn Fn(SlotIdx, SlotIdx) -> Instr> {
        macro_rules! ret {
            ($i: expr) => {
                Some(&|s1, s2| $i(s1, s2))
            };
        };
        if s == "not" {
            ret!(I::Not)
        } else if s == "pair?" {
            ret!(I::IsPair)
        } else if s == "car" {
            ret!(I::Car)
        } else if s == "cdr" {
            ret!(I::Cdr)
        } else {
            None
        }
    }

    /// Resolve the ID as a chunk or builtin, and put it into `sl`.
    fn resolve_id_into_slot_(
        ctx: &mut Ctx,
        c: &mut Compiler,
        s: &str,
        loc: (usize, usize),
        sl: SlotIdx,
    ) -> Result<()> {
        if let Some(f_var_slot) = c.find_slot_of_var(s) {
            assert_ne!(f_var_slot, sl);
            c.emit_instr_(I::Move(f_var_slot, sl));
        } else if c.name.as_ref().filter(|n| n.get() == s).is_some() {
            // call current function
            c.emit_instr_(I::LoadSelfChunk(sl))
        } else if let Some(b) = basic_primitives::BUILTINS.iter().find(|b| b.name == s) {
            let lidx = c.allocate_local_(Value::Builtin(b))?;
            c.emit_instr_(I::LoadLocal(lidx, sl));
        } else if let Some(b) = logic_builtins::BUILTINS.iter().find(|b| b.name == s) {
            let lidx = c.allocate_local_(Value::Builtin(b))?;
            c.emit_instr_(I::LoadLocal(lidx, sl));
        } else if let Some(ch) = ctx.find_meta_chunk(s) {
            let lidx = c.allocate_local_(Value::Chunk(ch.clone()))?;
            c.emit_instr_(I::LoadLocal(lidx, sl));
        } else if let Some(e) = ctx.find_const(s) {
            let lidx = c.allocate_local_(Value::Expr(e.0.clone()))?;
            c.emit_instr_(I::LoadLocal(lidx, sl));
        } else if let Some(th) = ctx.find_lemma(s) {
            let lidx = c.allocate_local_(Value::Thm(th.clone()))?;
            c.emit_instr_(I::LoadLocal(lidx, sl));
        // } else if c.defines_const(s) {
        // TODO: emit `add_local(s); add_local(builtin("find_const")); call
        //
        // or:
        // TODO: parse and eval the top statements one by one.
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

    /// get or create result slot, from an optional slot passed as argument.
    macro_rules! get_res {
        ($c: expr, $sl_res: expr) => {
            match $sl_res {
                Some(s) => ExprRes::new(s, true),
                None => $c.allocate_temporary_()?,
            }
        };
    }

    macro_rules! get_closing {
        ($t: expr) => {
            if $t == Tok::LParen {
                Tok::RParen
            } else {
                Tok::RBracket
            }
        };
    }

    /// Push argument `a` onto the `call_args` stack.
    fn mk_push_arg_instr(arg: &ExprRes) -> Instr {
        if arg.temporary {
            I::PushCallArgMove(arg.slot) // can move
        } else {
            // could be a variable passed several time as argument,
            // we cannot move it
            I::PushCallArgCpy(arg.slot)
        }
    }

    impl<'a, 'b, 'c> Parser<'a, 'b, 'c> {
        /// Create a new parser for source string `s`.
        pub fn new(ctx: &'a mut k::Ctx, lexer: &'c mut lexer::Lexer<'b>) -> Self {
            Self { ctx, lexer }
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

        /// Parse a toplevel statement in the string passed at creation time.
        ///
        /// Returns `Ok(None)` if no more statements could be read.
        /// Otherwise returns `Ok((chunk, lexer))`.
        pub(super) fn parse_top_statement(mut self) -> Result<Option<Chunk>> {
            let t = self.lexer.cur();
            let loc = self.lexer.loc();

            macro_rules! newcompiler {
                () => {
                    Compiler {
                        instrs: vec![],
                        locals: vec![],
                        n_slots: 0,
                        name: None,
                        slots: vec![],
                        parent: None,
                    }
                };
            };

            match t {
                Tok::Eof => Ok(None),
                Tok::Id(_)
                | Tok::QuotedString(..)
                | Tok::QuotedExpr(..)
                | Tok::Int(..)
                | Tok::ColonId(..) => {
                    let mut c = newcompiler!();
                    let r = self.parse_expr_(&mut c, None)?;
                    c.emit_instr_(I::Ret(r.slot));
                    Ok(Some(c.into_chunk()))
                }
                Tok::LBrace | Tok::LBracket => {
                    let mut c = newcompiler!();
                    let r = self.parse_expr_(&mut c, None)?;
                    c.emit_instr_(I::Ret(r.slot));
                    Ok(Some(c.into_chunk()))
                }
                Tok::LParen => {
                    let closing = get_closing!(t);
                    self.lexer.next();
                    if let Tok::Id("defn") = self.lexer.cur() {
                        self.lexer.next();

                        // function name
                        let f_name: RStr =
                            cur_tok_as_id_(&mut self.lexer, "expected function name")?.into();
                        self.next_tok_();

                        // get bound variables
                        let b_closing = match self.cur_tok_() {
                            Tok::LParen => Tok::RParen,
                            Tok::LBracket => Tok::RBracket,
                            _ => {
                                return Err(perror!(
                                    self.lexer.loc(),
                                    "expect '(' or '[' after `defn <id>`"
                                ))
                            }
                        };
                        self.next_tok_();

                        // parse function
                        let sub_c = self.parse_fn_args_and_body_(
                            Some(f_name.clone()),
                            b_closing,
                            closing,
                            None,
                        )?;

                        // define the function.
                        logdebug!("define {} as {:?}", &f_name, sub_c);
                        self.ctx.define_meta_chunk(f_name, sub_c);
                        Ok(Some(Chunk::retnil()))
                    } else {
                        let mut c = newcompiler!();
                        let r = self.parse_expr_app_(&mut c, None)?;
                        c.emit_instr_(I::Ret(r.slot));
                        Ok(Some(c.into_chunk()))
                    }
                }
                Tok::RParen => {
                    return Err(perror!(loc, "non-closed ')'"));
                }
                Tok::RBracket => {
                    return Err(perror!(loc, "non-closed ']'"));
                }
                Tok::RBrace => {
                    return Err(perror!(loc, "non-closed '}}'"));
                }
                Tok::Invalid(c) => {
                    return Err(perror!(loc, "invalid character '{}'", c));
                }
            }
        }

        fn parse_fn_args_and_body_(
            &mut self,
            f_name: Option<RStr>,
            var_closing: Tok,
            closing: Tok,
            parent: Option<&Compiler>,
        ) -> Result<Chunk> {
            let mut vars: Vec<RStr> = vec![];

            while self.cur_tok_() != var_closing {
                let e = cur_tok_as_id_(
                    &mut self.lexer,
                    "expected a bound variable or closing delimiter",
                )?
                .into();
                self.next_tok_();
                logdebug!("add var {:?}", e);
                vars.push(e);
            }
            self.eat_(var_closing, "expected closing delimiter after variables")?;

            // make a compiler for this chunk.
            let mut c = Compiler {
                instrs: vec![],
                locals: vec![],
                n_slots: 0,
                name: f_name.clone(),
                slots: vec![],
                parent,
            };
            // add variables to `sub_c`
            for x in vars {
                let sl_x = c.allocate_top_slot_(CompilerSlotState::Activated)?;
                c.slots[sl_x.0 as usize].var_name = Some(x);
            }
            let res = self.parse_expr_seq_(&mut c, closing, None)?;

            // return value
            c.emit_instr_(I::Ret(res.slot));
            c.free(&res);

            Ok(c.into_chunk())
        }

        /// Parse an application-type expression, closed with `closing`.
        ///
        /// Put the result into slot `sl_res` if provided.
        fn parse_expr_app_(
            &mut self,
            c: &mut Compiler,
            sl_res: Option<SlotIdx>,
        ) -> Result<ExprRes> {
            let loc = self.lexer.loc();
            let id = cur_tok_as_id_(&mut self.lexer, "expect an identifier after opening")?;
            logdebug!("parse expr app id={:?}", id);

            if let Some(binop_instr) = binary_op_(id) {
                // binary operator
                self.next_tok_();

                let a = self.parse_expr_(c, None)?;
                let b = self.parse_expr_(c, None)?;
                self.eat_(Tok::RParen, "expected closing ')' in infix application")?;

                // free before allocating result
                c.free(&a);
                c.free(&b);
                let res = get_res!(c, sl_res);

                c.emit_instr_(binop_instr(a.slot, b.slot, res.slot));
                Ok(res)
            } else if let Some(unop_instr) = unary_op_(id) {
                // unary op
                self.next_tok_();
                let e = self.parse_expr_(c, sl_res)?;
                self.eat_(Tok::RParen, "expected closing ')' after `not`")?;
                // `e := not e`
                c.emit_instr_(unop_instr(e.slot, e.slot));
                Ok(e)
            } else if id == "if" {
                self.next_tok_();
                let res = get_res!(c, sl_res);
                let res_test = self.parse_expr_(c, None)?;

                let jump_if_false = c.reserve_jump_();

                // parse `then`
                let _e_then = self.parse_expr_(c, Some(res.slot))?;
                // jump above `else`
                let jump_after_then = c.reserve_jump_();

                // jump here if test is false to execute `else`
                c.emit_jump(jump_if_false, |off| I::JumpIfFalse(res_test.slot, off))?;
                c.free(&res_test);

                // parse `else`
                let _e_else = self.parse_expr_(c, Some(res.slot))?;

                // jump here after `then` is done.
                c.emit_jump(jump_after_then, |off| I::Jump(off))?;

                self.eat_(Tok::RParen, "expected closing ')' after 'if'")?;
                Ok(res)
            } else if id == "let" {
                // local definitions.
                self.next_tok_();

                let b_closing = match self.cur_tok_() {
                    Tok::LParen => Tok::RParen,
                    Tok::LBracket => Tok::RBracket,
                    _ => return Err(perror!(loc, "expecting opening '[' or '(' after 'let'")),
                };
                self.next_tok_();

                let mut locals = vec![];
                loop {
                    let x: RStr = cur_tok_as_id_(&mut self.lexer, "expected variable name")?.into();
                    let sl_x = c.allocate_var_(x)?;
                    locals.push(sl_x.clone());
                    self.next_tok_();
                    self.parse_expr_(c, Some(sl_x.slot))?;
                    // now the variable is defined.
                    c.get_slot_(sl_x.slot).state = CompilerSlotState::Activated;

                    if self.cur_tok_() == b_closing {
                        break;
                    }
                }
                self.eat_(b_closing, "expected block of bound variables to end")?;

                let res = get_res!(c, sl_res);
                let res = self.parse_expr_seq_(c, Tok::RParen, Some(res.slot))?;
                // deallocate locals
                for x in locals {
                    c.deallocate_slot_(x.slot);
                }
                Ok(res)
            } else if id == "list" {
                // parse into a list
                self.lexer.next();
                self.parse_list_(c, sl_res, Tok::RParen)
            } else if id == "do" {
                self.next_tok_();
                // parse a series of expressions.
                self.parse_expr_seq_(c, Tok::RParen, sl_res)
            } else if id == "become" {
                self.next_tok_();

                // there is not truly a result for this frame, so this is fake.
                let mut res = ExprRes::new(SlotIdx(u8::MAX), false);
                res.exited = true;

                logdebug!("parse tail-application");

                let id_f =
                    cur_tok_as_id_(&mut self.lexer, "expected function name after `become`")?;
                let f = c.allocate_temporary_()?;
                resolve_id_into_slot_(&mut self.ctx, c, id_f, loc, f.slot)?;
                self.lexer.next();
                logdebug!(".. function is {:?} := {:?}", f, c.get_slot_(f.slot));

                // parse arguments
                let len = self.parse_expr_list_(c, Tok::RParen, &|c, a| {
                    c.emit_instr_(mk_push_arg_instr(&a));
                    c.free(&a);
                })?;
                if len > u8::MAX as usize {
                    return Err(perror!(
                        self.lexer.loc(),
                        "maximum number of arguments exceeded"
                    ));
                }

                c.emit_instr_(I::Become(f.slot));
                c.free(&f);
                Ok(res)
            } else {
                // make a function call.

                let res = match sl_res {
                    None => c.allocate_temporary_()?,
                    Some(sl) => ExprRes::new(sl, false),
                };
                logdebug!("parse application (res: {:?})", res);

                let f = c.allocate_temporary_()?;
                resolve_id_into_slot_(&mut self.ctx, c, id, loc, f.slot)?;
                self.lexer.next();
                logdebug!(".. function is {:?} := {:?}", f, c.get_slot_(f.slot));

                // parse arguments
                let len = self.parse_expr_list_(c, Tok::RParen, &|c, a| {
                    c.emit_instr_(mk_push_arg_instr(&a));
                    c.free(&a);
                })?;
                if len > u8::MAX as usize {
                    return Err(perror!(
                        self.lexer.loc(),
                        "maximum number of arguments exceeded"
                    ));
                }

                c.emit_instr_(I::Call(f.slot, res.slot));
                c.free(&f);
                Ok(res)
            }
        }

        /// Parse a list of expressions, return how many were parsed.
        fn parse_expr_list_(
            &mut self,
            c: &mut Compiler,
            closing: Tok,
            f: &dyn Fn(&mut Compiler, &ExprRes),
        ) -> Result<usize> {
            let mut n = 0;
            let mut has_exited = false;
            loop {
                if self.cur_tok_() == closing {
                    break;
                } else if has_exited {
                    // we just called `return` or `become`, this is unreachable
                    return Err(perror!(self.lexer.loc(), "unreachable expression"));
                }

                let arg = self.parse_expr_(c, None)?;
                has_exited = arg.exited;
                f(c, &arg);

                n += 1;
                if n > u8::MAX as usize {
                    return Err(perror!(
                        self.lexer.loc(),
                        "maximum number of arguments exceeded"
                    ));
                }
            }
            self.eat_(closing, "expected closing delimiter")?;
            Ok(n)
        }

        /// Parse a list, either from `(list …)` or `[…]`.
        fn parse_list_(
            &mut self,
            c: &mut Compiler,
            sl_res: Option<SlotIdx>,
            closing: Tok,
        ) -> Result<ExprRes> {
            let res = get_res!(c, sl_res);
            logdebug!("parse list (sl_res {:?}, res {:?})", sl_res, res);

            c.emit_instr_(I::LoadNil(res.slot));

            let mut items = vec![];
            while self.lexer.cur() != closing {
                let x = self.parse_expr_(c, None)?;
                items.push(x);
            }
            for x in items.into_iter().rev() {
                c.emit_instr_(I::Cons(x.slot, res.slot, res.slot));
                c.free(&x);
            }
            self.lexer.eat_(closing, "list must be closed")?;
            Ok(res)
        }

        /// Parse a series of expressions.
        ///
        fn parse_expr_seq_(
            &mut self,
            c: &mut Compiler,
            closing: Tok,
            sl_res: Option<SlotIdx>,
        ) -> Result<ExprRes> {
            let res = get_res!(c, sl_res);
            loop {
                if self.cur_tok_() == closing {
                    break; // done
                }
                self.parse_expr_(c, Some(res.slot))?;
            }
            self.eat_(closing, "unclosed sequence")?;

            Ok(res)
        }

        fn parse_infix_(&mut self, c: &mut Compiler, sl_res: Option<SlotIdx>) -> Result<ExprRes> {
            logdebug!("parse infix expr");
            let a = self.parse_expr_(c, None)?;

            let loc = self.lexer.loc();
            let Self { ctx, lexer, .. } = self;
            if let Tok::Id(op) = lexer.cur() {
                if let Some(binop_instr) = binary_op_(op) {
                    // infix primitive operator.
                    // emit `b = a op b`
                    lexer.next();
                    let b = self.parse_expr_(c, sl_res)?;
                    self.eat_(Tok::RBrace, "expected '}' to close infix '{'-expr")?;

                    c.emit_instr_(binop_instr(a.slot, b.slot, b.slot));
                    c.free(&a);
                    Ok(b)
                } else {
                    // infix function
                    let f = c.allocate_temporary_on_top_()?;
                    resolve_id_into_slot_(ctx, c, &op, loc, f.slot)?;

                    lexer.next();
                    let b = self.parse_expr_(c, sl_res)?;
                    self.eat_(Tok::RBrace, "expected '}' to close infix '{'-expr")?;

                    c.emit_instr_(mk_push_arg_instr(&a));
                    c.emit_instr_(mk_push_arg_instr(&b));
                    c.emit_instr_(I::Call(f.slot, b.slot));
                    c.free(&a);
                    c.free(&f);
                    Ok(b)
                }
            } else {
                return Err(perror!(self.lexer.loc(), "expected an infix operator"));
            }
        }

        /// Parse an expression and return its result's slot.
        ///
        /// `sl_res` is an optional pre-provided slot.
        fn parse_expr_(&mut self, c: &mut Compiler, sl_res: Option<SlotIdx>) -> Result<ExprRes> {
            logdebug!("parse expr (cur {:?})", self.lexer.cur());
            logtrace!("> slots {:?}", c.slots);

            let Self { ctx, lexer, .. } = self;
            let loc = lexer.loc();
            match lexer.cur() {
                Tok::LParen => {
                    lexer.next();
                    self.parse_expr_app_(c, sl_res)
                }
                Tok::LBracket => {
                    lexer.next();
                    self.parse_list_(c, sl_res, Tok::RBracket)
                }
                Tok::LBrace => {
                    // infix: `{a x b}` is `[0]; a; b; [0]=x; call`
                    lexer.next();
                    self.parse_infix_(c, sl_res)
                }
                Tok::Int(i) => {
                    lexer.next();
                    let res = get_res!(c, sl_res);
                    if i >= i16::MIN as i64 && i <= i16::MAX as i64 {
                        c.emit_instr_(I::LoadInteger(i as i16, res.slot))
                    } else {
                        let lidx = c.allocate_local_(Value::Int(i))?;
                        c.emit_instr_(I::LoadLocal(lidx, res.slot));
                    }
                    Ok(res)
                }
                Tok::Id("nil") => {
                    lexer.next();
                    let res = get_res!(c, sl_res);
                    c.emit_instr_(I::LoadNil(res.slot));
                    Ok(res)
                }
                Tok::Id("true") => {
                    lexer.next();
                    let res = get_res!(c, sl_res);
                    c.emit_instr_(I::LoadBool(true, res.slot));
                    Ok(res)
                }
                Tok::Id("false") => {
                    lexer.next();
                    let res = get_res!(c, sl_res);
                    c.emit_instr_(I::LoadBool(false, res.slot));
                    Ok(res)
                }
                Tok::Id(id) => {
                    let res = get_res!(c, sl_res);
                    if let Some(sl_var) = c.find_slot_of_var(id) {
                        if let Some(sl_r) = sl_res {
                            if sl_r != sl_var {
                                // must copy
                                c.emit_instr_(I::Move(sl_var, sl_r));
                            }
                        } else {
                            // return the existing variable instead.
                            self.next_tok_();
                            c.free(&res);
                            return Ok(ExprRes::new(sl_var, false));
                        }
                    } else {
                        resolve_id_into_slot_(ctx, c, id, loc, res.slot)?;
                    }
                    lexer.next();
                    Ok(res)
                }
                Tok::ColonId(s) => {
                    let lidx = c.allocate_local_(Value::Sym(s.into()))?;
                    self.next_tok_();
                    let res = get_res!(c, sl_res);
                    c.emit_instr_(I::LoadLocal(lidx, res.slot));
                    Ok(res)
                }
                Tok::QuotedString(s) => {
                    let lidx = c.allocate_local_(Value::Str(s.into()))?;
                    self.next_tok_();
                    let res = get_res!(c, sl_res);
                    c.emit_instr_(I::LoadLocal(lidx, res.slot));
                    Ok(res)
                }
                Tok::QuotedExpr(e) => {
                    if e.as_bytes().contains(&b'?') {
                        // TODO: interpolation
                        return Err(perror!(loc, "unimplemented: interpolating exprs"));
                    }
                    let e = syntax::parse_expr(self.ctx, e)
                        .map_err(|e| perror!(loc, "while parsing expression: {}", e))?;
                    // TODO: reuse local if `e` is there already
                    let lidx = c.allocate_local_(Value::Expr(e))?;
                    self.next_tok_();
                    let res = get_res!(c, sl_res);
                    c.emit_instr_(I::LoadLocal(lidx, res.slot));
                    Ok(res)
                }
                Tok::RParen | Tok::RBracket | Tok::RBrace => {
                    return Err(perror!(loc, "invalid closing delimiter"))
                }
                Tok::Invalid(c) => return Err(perror!(loc, "invalid char {}", c)),

                Tok::Eof => return Err(perror!(loc, "unexpected EOF when parsing expr")),
            }
        }

        /// Expect the token `t`, and consume it; or return an error.
        fn eat_(&mut self, t: lexer::Tok, errmsg: &str) -> Result<()> {
            self.lexer.eat_(t, errmsg)
        }
    }
}

macro_rules! get_arg_as {
    ($f: ident, $what: literal, $p: pat, $v: expr, $ret_ty: ty) => {
        macro_rules! $f {
            ($args: expr, $idx: expr) => {
                match &$args[$idx as usize] {
                    $p => $v,
                    _ => {
                        return Err(Error::new(concat!("type error: expected ", $what)));
                    }
                }
            };
        }
    };
}

get_arg_as!(get_arg_int, "int", Value::Int(i), i, i64);
//get_arg_as!(get_arg_nil, "nil", (_i @ Value::Nil), _i, ());
//get_arg_as!(get_arg_bool, "bool", Value::Bool(i), *i, bool);
get_arg_as!(get_arg_str, "string", Value::Str(i), &*i, &str);
//get_as_of!(get_arg_codearray, "code array", Value::CodeArray(i), i, CodeArray);
get_arg_as!(get_arg_expr, "expr", Value::Expr(i), i, &k::Expr);
get_arg_as!(get_arg_thm, "thm", Value::Thm(i), i, k::Thm);
//get_as_of!(get_slot_sym, "sym", Value::Sym(i), i, k::Ref<str>);

macro_rules! defbuiltin {
    ($name: literal, $help:literal, $run:expr) => {
        InstrBuiltin {
            name: $name,
            help: $help,
            run: $run,
        }
    };
}

macro_rules! check_arity {
    ($what: expr, $args: expr, $n: literal) => {
        if $args.len() != $n {
            return Err(Error::new(concat!(
                "arity mismatch in ",
                $what,
                ": expected ",
                stringify!($n),
                " args"
            )));
        }
    };
}

mod basic_primitives {
    use super::*;

    /// Builtin functions.
    pub(super) const BUILTINS: &'static [&'static InstrBuiltin] = &[
        &defbuiltin!("print", "print a value.", |_, args: &[Value]| {
            for x in args {
                println!("print: {}", x)
            }
            Ok(Value::Nil)
        }),
        &defbuiltin!(
            "help",
            "print help for an identifier.",
            |_, args: &[Value]| -> Result<_> {
                check_arity!("help", args, 1);
                let _s = get_arg_str!(args, 0);
                // TODO: actually display help
                Ok(Value::Nil)
            }
        ),
        &defbuiltin!(
            "eval",
            "Takes a string, and returns the value yielded by evaluating it.",
            |ctx, args: &[Value]| -> Result<_> {
                check_arity!("eval", args, 1);
                let s = get_arg_str!(args, 0);
                logdebug!("evaluate `{}`", s);
                let mut vm = VM::new(ctx);
                // evaluate `s` in a new VM.
                let v = vm.run(s).map_err(|e| {
                    e.set_source(Error::new_string(format!("while evaluating {}", s)))
                })?;
                Ok(v)
            }
        ),
        &defbuiltin!(
            "load_file",
            "Takes a string `f`, and returns content of file `f` as a string.",
            |_ctx, args: &[Value]| -> Result<_> {
                check_arity!("load_file", args, 1);
                let s = get_arg_str!(args, 0);
                let content = match std::fs::read_to_string(&*s as &str) {
                    Ok(x) => x.into(),
                    Err(e) => {
                        // TODO: some kind of exception handling
                        return Err(Error::new_string(format!("cannot load file `{}: {}", s, e)));
                    }
                };
                Ok(Value::Str(content))
            }
        ),
        &defbuiltin!(
            "show_chunk",
            "shows the bytecode of a chunk",
            |ctx, args: &[Value]| -> Result<_> {
                check_arity!("show_chunk", args, 1);
                let s = get_arg_str!(args, 0);
                if let Some(c) = ctx.find_meta_chunk(s) {
                    println!("{:?}", c);
                }
                Ok(().into())
            }
        ),
    ];
}

/// Primitives of the meta-language related to theorem proving.
mod logic_builtins {
    use super::*;

    /// Builtin functions for manipulating expressions and theorems.
    pub(super) const BUILTINS: &'static [&'static InstrBuiltin] = &[
        &defbuiltin!(
            "defconst",
            "Defines a logic constant. Takes `(nc, nth, expr_rhs)` and returns
            the tuple `{c . th}` where `c` is the constant, with name `nc`,
            and `th` is the defining theorem with name `nth`",
            |ctx, args: &[Value]| {
                check_arity!("defconst", args, 3);
                let nc: k::Symbol = get_arg_str!(args, 0).into();
                let nthm = get_arg_str!(args, 1);
                let rhs = get_arg_expr!(args, 2);
                let def = algo::thm_new_poly_definition(ctx, &nc.name(), rhs.clone())?;
                ctx.define_lemma(nthm, def.thm.clone());
                Ok(Value::cons(Value::Expr(def.c), Value::Thm(def.thm)))
            }
        ),
        &defbuiltin!(
            "defthm",
            "Defines a theorem. Takes `(name, th)`.",
            |ctx, args| {
                check_arity!("defthm", args, 2);
                let th = get_arg_thm!(args, 1);
                let name = get_arg_str!(args, 0);
                ctx.define_lemma(&*name, th.clone());
                Ok(Value::Nil)
            }
        ),
        &defbuiltin!("expr_ty", "Get the type of an expression.", |_ctx, args| {
            check_arity!("expr_ty", args, 1);
            let e = get_arg_expr!(args, 0);
            if e.is_kind() {
                return Err(Error::new("cannot get type of `kind`"));
            }
            Ok(Value::Expr(e.ty().clone()))
        }),
        &defbuiltin!(
            "findconst",
            "Find the constant with given name.",
            |ctx, args| {
                check_arity!("findconst", args, 1);
                let name = get_arg_str!(args, 0);
                let e = ctx
                    .find_const(&name)
                    .ok_or_else(|| Error::new("unknown constant"))?
                    .0
                    .clone();
                Ok(Value::Expr(e))
            }
        ),
        &defbuiltin!(
            "axiom",
            "Takes a boolean expression and makes it into an axiom.
            Might fail if `pledge_no_new_axiom` was called earlier.",
            |ctx, args| {
                check_arity!("axiom", args, 1);
                let e = get_arg_expr!(args, 0);
                let th = ctx.thm_axiom(vec![], e.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "assume",
            "Takes a boolean expression and returns the theorem `e|-e`.",
            |ctx, args| {
                check_arity!("assume", args, 1);
                let e = get_arg_expr!(args, 0);
                let th = ctx.thm_assume(e.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "refl",
            "Takes an expression `e` and returns the theorem `|-e=e`.",
            |ctx, args| {
                check_arity!("refl", args, 1);
                let e = get_arg_expr!(args, 0);
                let th = ctx.thm_refl(e.clone());
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "sym",
            "Takes a theorem `A|- t=u` and returns the theorem `A|- u=t`.",
            |ctx, args| {
                check_arity!("sym", args, 1);
                let th1 = get_arg_thm!(args, 0);
                let th = algo::thm_sym(ctx, th1.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "trans",
            "Transitivity", // TODO Takes ` theorem `A|- t=u` and returns the theorem `A|- u=t`.",
            |ctx, args| {
                check_arity!("trans", args, 2);
                let th1 = get_arg_thm!(args, 0).clone();
                let th2 = get_arg_thm!(args, 1).clone();
                let th = ctx.thm_trans(th1, th2)?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "congr",
            "Congruence. Takes `A|- f=g` and `B|- t=u`, returns `A,B|- f t=g u`",
            |ctx, args| {
                check_arity!("congr", args, 2);
                let th1 = get_arg_thm!(args, 0).clone();
                let th2 = get_arg_thm!(args, 1).clone();
                let th = ctx.thm_congr(th1, th2)?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "decl",
            "Declare a symbol. Takes a symbol `n`, and a type.",
            |ctx, args| {
                check_arity!("decl", args, 2);
                let name = get_arg_str!(args, 0);
                let ty = get_arg_expr!(args, 1);
                let e = ctx.mk_new_const(k::Symbol::from_str(name), ty.clone())?;
                Ok(Value::Expr(e))
            }
        ),
        &defbuiltin!(
            "set_infix",
            "Make a symbol infix.

            Takes a symbol `n`, and a pair of integers `i`,`j` as left and right
            precedences.",
            |ctx, args| {
                check_arity!("set_infix", args, 3);
                let c = get_arg_str!(args, 0);
                let i = get_arg_int!(args, 1);
                let j = get_arg_int!(args, 2);
                let f = syntax::Fixity::Infix((*i as u16, *j as u16));
                ctx.set_fixity(&*c, f);
                Ok(Value::Nil)
            }
        ),
        &defbuiltin!("set_binder", "Make a symbol a binder.", |ctx, args| {
            check_arity!("set_binder", args, 2);
            let c = get_arg_str!(args, 0);
            let i = get_arg_int!(args, 1);
            let f = syntax::Fixity::Binder((0, *i as u16));
            ctx.set_fixity(&*c, f);
            Ok(Value::Nil)
        }),
        &defbuiltin!(
            "abs",
            "Takes `x`, `ty`, and `A|- t=u`, and returns
            the theorem `A|- \\x:ty. t = \\x:ty. u`.",
            |ctx, args| {
                check_arity!("abs", args, 3);
                let v = get_arg_str!(args, 0);
                let ty = get_arg_expr!(args, 1);
                let th = get_arg_thm!(args, 2);
                let v = k::Var::from_str(&*v, ty.clone());
                let th = ctx.thm_abs(&v, th.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "abs_expr",
            "Takes expr `x`, and `A|- t=u`, and returns
            the theorem `A|- \\x:ty. t = \\x:ty. u`.",
            |ctx, args| {
                check_arity!("abs_expr", args, 2);
                let e = get_arg_expr!(args, 0);
                let v = e
                    .as_var()
                    .ok_or_else(|| Error::new("abs_expr: expression must be a variable"))?;
                let th = get_arg_thm!(args, 1);
                let th = ctx.thm_abs(v, th.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "concl",
            "Takes a theorem `A |- t`, and returns `t`.",
            |_ctx, args| {
                check_arity!("concl", args, 1);
                let th = get_arg_thm!(args, 0);
                Ok(Value::Expr(th.concl().clone()))
            }
        ),
        &defbuiltin!(
            "hol_prelude",
            "Returns the builtin HOL prelude, as a string.",
            |_ctx, args| {
                check_arity!("hol_prelude", args, 0);
                Ok(Value::Str(super::SRC_PRELUDE_HOL.into()))
            }
        ),
        &defbuiltin!(
            "pledge_no_new_axiom",
            "Prevent any further calls to `axiom` to succeed.",
            |ctx, args| {
                check_arity!("pledge_no_new_axiom", args, 0);
                ctx.pledge_no_new_axiom();
                Ok(Value::Nil)
            }
        ),
        &defbuiltin!(
            "congr_ty",
            "Congruence rule on a type argument.",
            |ctx, args| {
                check_arity!("congr_ty", args, 2);
                let th1 = get_arg_thm!(args, 0);
                let ty = get_arg_expr!(args, 1);
                let th = ctx.thm_congr_ty(th1.clone(), &ty)?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!("cut", "Cut rule.", |ctx, args| {
            check_arity!("cut", args, 2);
            let th1 = get_arg_thm!(args, 0);
            let th2 = get_arg_thm!(args, 1);
            let th = ctx.thm_cut(th1.clone(), th2.clone())?;
            Ok(Value::Thm(th))
        }),
        &defbuiltin!(
            "bool_eq",
            "Boolean equality. Takes `A|- t=u` and `B|- t`, returns `A,B|- u`.",
            |ctx, args| {
                check_arity!("bool_eq", args, 2);
                let th1 = get_arg_thm!(args, 0);
                let th2 = get_arg_thm!(args, 1);
                let th = ctx.thm_bool_eq(th1.clone(), th2.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "bool_eq_intro",
            "Boolean equality introduction.
            Takes `A, t|- u` and `B,u |- t`, returns `A,B|- t=u`.",
            |ctx, args| {
                check_arity!("bool_eq_intro", args, 2);
                let th1 = get_arg_thm!(args, 0);
                let th2 = get_arg_thm!(args, 1);
                let th = ctx.thm_bool_eq_intro(th1.clone(), th2.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "beta_conv",
            "Beta-conversion rule.
            Takes expr `(\\x. t) u`, returns `|- (\\x. t) u = t[u/x]`.",
            |ctx, args| {
                check_arity!("beta_conv", args, 1);
                let e = get_arg_expr!(args, 0);
                let th = ctx.thm_beta_conv(e)?;
                Ok(Value::Thm(th))
            }
        ),
    ];

    // TODO: defty

    /* TODO

        // th1 th2 -- mp(th1,th2)
        fn run(&self, st: &mut State) -> Result<()> {
            match self {
                R::Findthm => {
                    let name = st.pop1_sym()?;
                    let th = st
                        .ctx
                        .find_lemma(&name)
                        .ok_or_else(|| Error::new("unknown theorem"))?
                        .clone();
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
pub fn run_code(ctx: &mut Ctx, s: &str) -> Result<Value> {
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
            r#" ("a" "b"[mul 2}"d" { 3 - 1 } def) 2  "#,
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
                T::Id("-"),
                T::Int(1),
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

    macro_rules! check_eval {
        ($e:expr, $val:expr) => {{
            let mut ctx = Ctx::new();
            let mut vm = VM::new(&mut ctx);
            let res_e = vm.run($e)?;

            assert_eq!(res_e, $val.into());
        }};
    }

    #[test]
    fn test_eval() -> Result<()> {
        check_eval!("1", 1);
        check_eval!("true", true);
        check_eval!("false", false);
        check_eval!("nil", ());
        check_eval!("(+ 1 2)", 3);
        check_eval!("(let [x 1] {x + 2})", 3);
        check_eval!(
            "(list 1 2 3)",
            Value::list(&[Value::Int(1), Value::Int(2), Value::Int(3)])
        );
        check_eval!("(defn f [x] {1 + x})", Value::Nil);
        check_eval!("(defn f [x] {1 + x}) (f 9)", 10);
        check_eval!("(do true 1)", 1);
        check_eval!("(if true 1 2)", 1);
        check_eval!("(if false 1 2)", 2);
        check_eval!("(let [x {1 + 1}] (if {x == 1} 10 20))", 20);
        check_eval!("(let [x {1 + 1}] (if {x == 2} 10 20))", 10);
        check_eval!("{1 . {:b . nil}}", vec![1.into(), Value::Sym("b".into())]);
        check_eval!("[1 :b]", vec![1.into(), Value::Sym("b".into())]);
        check_eval!(":a", Value::Sym("a".into()));
        check_eval!("(not true)", false);
        check_eval!("(not false)", true);
        check_eval!("{1 != 2}", true);
        check_eval!("{1 == 2}", false);

        Ok(())
    }

    #[test]
    fn test_eval_arith() -> Result<()> {
        check_eval!("(let [a 2 b 4] {a + {{4  * b} - {{a / 2} % 3}}})", 17);
        Ok(())
    }

    #[test]
    fn test_infix_fun() -> Result<()> {
        check_eval!("(defn f [x y] (+ x (* 2 y))) {1 f 10}", 21);
        check_eval!(
            "(defn f [x y] (+ x (* 10 y))) {1 f {2 f 33}}",
            1 + 10 * (2 + 10 * 33)
        );
        Ok(())
    }

    #[test]
    fn test_more_eval() -> Result<()> {
        check_eval!(
            "(list \"coucou\" :abc)",
            vec![Value::Str("coucou".into()), Value::Sym("abc".into())]
        );
        check_eval!(
            "(defn f [x] (+ x 1)) (defn g [x] {(f x) * 2}) (+ 1 (g 10))",
            23
        );
        check_eval!("(let [x 1 y 2] {x + y})", 3);
        check_eval!(
            "(if {1 > 2} (let [x :a y :b] x) (let [x :b] \"oh?\" x))",
            Value::Sym("b".into())
        );
        check_eval!("(if {1 < 2} (let [x 1 y :b] nil x) (let [x :b] x))", 1);
        check_eval!("(car [1 2])", 1);
        check_eval!("(car (cdr [1 2]))", 2);
        check_eval!("(cdr (cdr [1 2]))", ());
        check_eval!("(pair? [1 2])", true);
        check_eval!("(pair? nil)", false);
        check_eval!("(pair? {1 . 2})", true);
        Ok(())
    }

    #[test]
    fn test_become() -> Result<()> {
        check_eval!(
            "
            (defn f [x y] (if {x == 0} y (become f {x - 1} {y + 1})))
            (f 1000 0)",
            1000
        );
        Ok(())
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
    */

    #[test]
    fn test_load_hol_prelude() -> Result<()> {
        let mut ctx = k::Ctx::new();
        load_prelude_hol(&mut ctx)?;
        load_prelude_hol(&mut ctx)?; // can we load it twice?
        Ok(())
    }
}
