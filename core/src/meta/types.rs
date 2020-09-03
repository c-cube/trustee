//! Types for the meta-language.

use {
    crate::{
        algo::conv,
        kernel_of_trust::{self as k, Ctx},
        rptr::RPtr,
        rstr::RStr,
        Error, Result,
    },
    std::{fmt, i16, io, u8},
};

/// A position in a file or string.
pub use crate::position::Position;

/// # Values
///
/// A value of the language.
#[derive(Debug, Clone)]
pub enum Value {
    Nil,
    Int(i64),
    Bool(bool),
    /// A symbol, like `:foo` or `:a`.
    Sym(k::Symbol),
    /// A raw string literal. Obtained by parsing a source file or using
    /// an embedded rust string literal.
    Str(RStr),
    Expr(k::Expr),
    /// Cons: a pair of values. This is the basis for lists.
    Cons(RPtr<(Value, Value)>),
    /// A theorem.
    Thm(k::Thm),
    /// A converter.
    Conv(RPtr<conv::BasicConverter>),
    /// An executable closure (chunks + upvalues).
    Closure(Closure),
    /// A builtin instruction implemented in rust.
    Builtin(&'static InstrBuiltin),
    /// A position as a value.
    Pos(RPtr<Position>),
    /// An error as a value.
    Error(RPtr<Error>),
}

// TODO: convert into stack VM
/// ## Instructions
///
/// An instruction of the language.
///
/// Each instruction's last argument is the index of the slot to put the result
/// into. Abbreviations:
/// - `sl` is the slots
/// - `args` is the VM's argument stack.
/// - `upv` is the closure's array of upvalues
/// - `$3` is argument number 3 (numbered from 0)`
#[derive(Debug, Copy, Clone)]
pub(super) enum Instr {
    /// copy `sl[$0]` into `sl[$1]`
    Copy(SlotIdx, SlotIdx),
    /// Local a local value into a slot. `sl[$1] = locals[$0]`
    LoadLocal(LocalIdx, SlotIdx),
    /// Put the given (small) integer `$0` into `sl[$1]`
    LoadInteger(i16, SlotIdx),
    /// Load the current chunk into `sl[$0]`
    LoadSelfClosure(SlotIdx),
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
    /// puts `is-nil sl[$0]` into `sl[$1]`
    IsNil(SlotIdx, SlotIdx),
    /// puts `is-cons sl[$0]` into `sl[$1]`
    IsCons(SlotIdx, SlotIdx),
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
    /// Set `sl[$1]` to `ctx[local[$0]]`
    GetGlob(LocalIdx, SlotIdx),
    /// Set `ctx[local[$0]]` to value `$1`
    SetGlob(LocalIdx, SlotIdx),
    /// Set `sl[$1]` to content of `upv[$0]`
    LoadUpvalue(UpvalueIdx, SlotIdx),
    /// Push a value from `sl[$0]` into the upvalue stack
    PushLocalToUpvalue(SlotIdx),
    /// Push a value from `upv[$0]` into the upvalue stack
    PushUpvalueToUpvalue(UpvalueIdx),
    /// Create a closure from the upvalue stack and the (empty) closure
    /// in `local[$0]`, and put the resulting closure in `sl[$1]`
    CreateClosure(LocalIdx, SlotIdx),
    /// Call chunk `sl[$0]` with arguments in `stack[sl[$0]+1 … sl[$0]+1+$1]`
    /// and put the result into `sl[$2]`.
    ///
    /// `$1` is the number of arguments the function takes.
    Call(SlotIdx, u8, SlotIdx),
    /* TODO
    /// Call builtin function at index `$0` with `$1` arguments,
    /// and put the result into `sl[$2]`.
    CallBuiltin(u8, u8, SlotIdx),
    */
    /// Tail-call into chunk `sl[$0]` with `$1` arguments.
    /// Does not return.
    Become(SlotIdx, u8),
    /// Return from current chunk with value `sl[$0]`.
    Ret(SlotIdx),
    /// Trace value from `sl[$1]` with location in `local[$0]`.
    Trace(LocalIdx, SlotIdx),
    /// Fail with the error in `local[$0]`.
    Fail(LocalIdx),
    /// Unrecoverable error.
    Trap,
}

/// Index in the array of slots.
#[derive(Copy, Clone, PartialEq)]
pub(super) struct SlotIdx(pub(super) u8);

/// Index in the array of locals.
#[derive(Copy, Clone, PartialEq)]
pub(super) struct LocalIdx(pub(super) u8);

/// Index in the array of upvalues.
#[derive(Copy, Clone, PartialEq)]
pub(super) struct UpvalueIdx(pub(super) u8);

#[must_use]
#[derive(Debug)]
pub(super) struct JumpPosition(pub(super) usize);

/// A custom instruction implemented in rust.
///
/// This is the most direct way of writing efficient inference rules or
/// tactics directly in rust.
pub struct InstrBuiltin {
    /// Name of the instruction. The instruction is invoked by its name.
    ///
    /// The name should be consistent with lexical conventions (no whitespaces,
    /// brackets, backquotes, etc.)
    pub name: &'static str,

    /// Execute the instruction with the given `ctx` on the given arguments.
    pub run: fn(ctx: BuiltinEvalCtx, args: &[Value]) -> Result<Value>,

    /// A one-line help text for this instruction.
    pub help: &'static str,
}

#[derive(Debug, Clone)]
/// A full location in a file or a string.
pub struct Location {
    pub start: Position,
    pub end: Position,
    pub file_name: Option<String>,
}

/// A closure, i.e. a function (chunk) associated with some captured values.
#[derive(Clone)]
pub struct Closure(pub(super) k::Ref<ClosureImpl>);

pub(super) struct ClosureImpl {
    pub(super) c: Chunk,
    pub(super) upvalues: Option<Box<[Value]>>,
}

/// A chunk of code.
///
/// Each derived rule, expression, etc. is compiled to a self-contained chunk.
/// Chunks can be evaluated several times.
#[derive(Clone)]
pub struct Chunk(pub(super) k::Ref<ChunkImpl>);

pub(super) struct ChunkImpl {
    /// Instructions to execute.
    pub(super) instrs: Box<[Instr]>,
    /// Local values, typically closures, theorems, or terms,
    /// used during the evaluation.
    pub(super) locals: Box<[Value]>,
    /// Number of arguments required.
    pub(super) n_args: u8,
    /// Number of captured variables, if any. Used if the chunk is a proper closure.
    pub(super) n_captured: u8,
    /// Total number of local slots required (arguments included).
    pub(super) n_slots: u32,
    /// Name of this chunk, if any.
    pub(super) name: Option<RStr>,
    /// Documentation, if any.
    pub(super) docstring: Option<RStr>,
    /// Debug info: location.
    pub(super) loc: Location,
}

/// Opaque printer to stdout.
pub struct BuiltinPrinter<'a, 'b>(pub &'a mut Option<&'b mut dyn FnMut(&str)>);

/// Context passed to a builtin function.
pub struct BuiltinEvalCtx<'a, 'b> {
    pub out: BuiltinPrinter<'a, 'b>,
    pub ctx: &'a mut Ctx,
}

mod impls {
    use super::*;

    impl<'a, 'b> BuiltinPrinter<'a, 'b> {
        /// Print `s` on the VM's output, if any.
        pub fn print<'c>(&'c mut self, s: &'c str) {
            if let Some(out) = self.0 {
                out(s)
            }
        }
    }

    impl Location {
        pub(crate) fn nil_loc() -> Self {
            Self {
                start: Position { line: 1, col: 1 },
                end: Position { line: 1, col: 1 },
                file_name: None,
            }
        }
    }

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

        pub fn as_str(&self) -> Option<&RStr> {
            match self {
                Value::Str(s) => Some(s),
                _ => None,
            }
        }

        pub fn as_cons(&self) -> Option<(&Value, &Value)> {
            match self {
                Value::Cons(p) => Some((&p.0, &p.1)),
                _ => None,
            }
        }

        pub fn as_closure(&self) -> Option<&Closure> {
            match self {
                Value::Closure(c) => Some(c),
                _ => None,
            }
        }

        pub fn as_bool(&self) -> Option<bool> {
            match self {
                Value::Bool(b) => Some(*b),
                _ => None,
            }
        }

        pub fn as_expr(&self) -> Option<&k::Expr> {
            match self {
                Value::Expr(e) => Some(e),
                _ => None,
            }
        }

        pub fn as_thm(&self) -> Option<&k::Thm> {
            match self {
                Value::Thm(th) => Some(th),
                _ => None,
            }
        }
    }

    impl fmt::Debug for Chunk {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            let full = out.alternate();
            let s = self.print(full, None).map_err(|_| fmt::Error)?;
            write!(out, "{}", s)
        }
    }

    impl fmt::Debug for Closure {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            let full = out.alternate();
            let s = self.print(full, None).map_err(|_| fmt::Error)?;
            write!(out, "{}", s)
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
    impl fmt::Debug for UpvalueIdx {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            write!(out, "upv[{}]", self.0)
        }
    }

    impl fmt::Display for Location {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            if let Some(file) = &self.file_name {
                write!(f, "{}-{} in {}", self.start, self.end, file)
            } else {
                write!(f, "{}-{}", self.start, self.end)
            }
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
                n_args: 0,
                n_captured: 0,
                loc: Location::nil_loc(),
                docstring: None,
            }))
        }

        pub(super) fn print(&self, full: bool, ic: Option<usize>) -> io::Result<String> {
            use std::io::Write;

            let mut v = vec![];
            let out = &mut v;
            if full {
                write!(out, "chunk [\n")?;
                write!(out, "  name: {:?}\n", &self.0.name)?;
                write!(out, "  n-slots: {}\n", self.0.n_slots)?;
                write!(out, "  ================================\n")?;
                for (i, v) in self.0.locals.iter().enumerate() {
                    write!(out, "  local[{:6}]: {}\n", i, &v)?;
                }
                write!(out, "  ================================\n")?;
                for (i, c) in self.0.instrs.iter().enumerate() {
                    // account for ic being current instr+1.
                    let active = ic.filter(|x| *x == i + 1).is_some();
                    let prefix = if active { ">" } else { " " };
                    write!(out, "  instr[{}{:5}]: {:?}\n", prefix, i, &c)?;
                }
                write!(out, "]\n")?;
            } else {
                if self.0.name.is_none() {
                    write!(out, "<anon chunk>")?;
                } else {
                    write!(out, "<chunk {:?}>", &self.0.name.as_ref().unwrap())?;
                }
            }
            Ok(String::from_utf8(v).unwrap())
        }
    }

    impl Closure {
        /// Make a new closure.
        pub fn new(c: Chunk, upvalues: Option<Box<[Value]>>) -> Self {
            Closure(k::Ref::new(ClosureImpl { c, upvalues }))
        }

        /// Closure that just returns `nil`.
        pub fn retnil() -> Self {
            Self::new(Chunk::retnil(), None)
        }

        /// Get the upvalues.
        pub fn upvalues(&self) -> &[Value] {
            match &self.0.upvalues {
                None => &[],
                Some(v) => &v[..],
            }
        }

        /// Name of the chunk.
        pub fn name(&self) -> Option<&str> {
            self.0.c.0.name.as_deref()
        }

        /// Docstring of the chunk, if any.
        pub fn docstring(&self) -> Option<&str> {
            self.0.c.0.docstring.as_deref()
        }

        /// Underlying bytecode chunk.
        pub fn chunk(&self) -> &Chunk {
            &self.0.c
        }

        pub(crate) fn print(&self, full: bool, ic: Option<usize>) -> io::Result<String> {
            use std::io::Write;

            let mut v = vec![];
            let out = &mut v;

            write!(out, "closure [\n")?;
            for (i, x) in self.upvalues().iter().enumerate() {
                write!(out, "  up[{:5}] = {}\n", i, x)?;
            }
            write!(out, "{}", self.0.c.print(full, ic)?)?;
            write!(out, "]\n")?;
            Ok(String::from_utf8(v).unwrap())
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
                Value::Conv(_) => write!(out, "<converter>"),
                Value::Cons(..) => {
                    let mut args = vec![];
                    let mut cur = self;

                    while let Value::Cons(v) = cur {
                        args.push(v.0.clone());
                        cur = &v.1;
                    }

                    if let Value::Nil = cur {
                        // proper list
                        write!(out, "(list")?;
                        for x in args {
                            if out.alternate() {
                                writeln!(out, "")?;
                            }
                            write!(out, " {}", x)?;
                        }
                        write!(out, ")")?
                    } else {
                        // conses
                        let n = args.len();
                        for x in args {
                            write!(out, "(cons {} ", x)?;
                        }
                        write!(out, "{}", cur)?;
                        for _x in 0..n {
                            write!(out, ")")?;
                        }
                    }
                    Ok(())
                }
                Value::Str(s) => write!(out, "{:?}", s),
                Value::Expr(e) => write!(out, "`{}`", e),
                Value::Thm(th) => write!(out, "{}", th),
                Value::Closure(cl) => {
                    let nup = cl.upvalues().len();
                    if let Some(n) = &cl.0.c.0.name {
                        write!(out, "<closure[{}] {:?}>", nup, n)
                    } else {
                        write!(out, "<closure[{}]>", nup)
                    }
                }
                Value::Builtin(b) => write!(out, "<builtin {}>", b.name),
                Value::Pos(p) => write!(out, "<position {}>", p),
                Value::Error(e) => write!(out, "<error {}>", e),
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
                (Thm(t1), Thm(t2)) => t1 == t2,
                (Closure(c1), Closure(c2)) => {
                    std::ptr::eq(&c1.0.c.0 as *const _, &c2.0.c.0) && c1.upvalues() == c2.upvalues()
                }
                (Builtin(b1), Builtin(b2)) => b1.name == b2.name,
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

    impl From<conv::BasicConverter> for Value {
        fn from(c: conv::BasicConverter) -> Self {
            Value::Conv(RPtr::new(c))
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
}
