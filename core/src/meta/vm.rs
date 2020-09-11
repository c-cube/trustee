//! The virtual machine for the meta-language.

use super::lexer;
use super::types::*;
use {
    crate::{kernel_of_trust::Ctx, rptr::RPtr, rstr::RStr, Error, Result},
    std::io,
};

/// The meta-language virtual machine.
pub struct VM<'a> {
    /// The logical context underlying the VM.
    ///
    /// The context provides means to build expressions, theorems (following
    /// the logic deduction rules), and stores maps from names to
    /// constants, theorems, and chunks.
    pub ctx: &'a mut Ctx,
    /// The stack where values live.
    stack: Box<[Value; STACK_SIZE]>,
    /// Stack of upvalues for the next closure to create.
    upvalue_stack: Vec<Value>,
    /// Control stack, for function calls.
    ctrl_stack: Vec<StackFrame>,
    /// In case of error, the error message lives here.
    result: Result<Value>,
    /// Abstraction over stdout, or a redirection of stdout to capture `print`.
    stdout: Option<&'a mut dyn FnMut(&str)>,
    /// Callback for tracing events
    on_trace: Option<&'a mut dyn FnMut(&Position, Value)>,
    on_error: Option<&'a mut dyn FnMut(&Error)>,
}

/// Maximum stack size
const STACK_SIZE: usize = 32 * 1024;

/// A stack frame.
///
/// Each call to a chunk (function) has its own stack frame that points to
/// a slice of `vm.stack` of its given number of locals.
#[derive(Debug)]
struct StackFrame {
    /// Offset in `vm.stack` where this frame starts.
    /// The size of the stack is determined by `chunk.n_slots`.
    start: u32,
    /// Instruction pointer within `chunk`.
    ic: u32,
    /// Closure being executed.
    closure: Closure,
    /// Offset to put the returned value into.
    res_offset: u32,
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
get_slot_as!(get_slot_bool, "bool", Value::Bool(i), *i, bool);
get_slot_as!(get_slot_expr, "expr", Value::Expr(e), e, Expr);

macro_rules! abs_offset {
    ($sf: expr, $i: expr) => {
        ($sf.start as usize) + ($i.0 as usize)
    };
}

#[allow(unsafe_code)]
impl<'a> VM<'a> {
    /// Create a new VM using the given context.
    pub fn new(ctx: &'a mut Ctx) -> Self {
        use std::mem::{transmute, MaybeUninit};

        // create the stack.
        // See https://doc.rust-lang.org/nightly/std/mem/union.MaybeUninit.html
        let mut stack: Box<[MaybeUninit<Value>; STACK_SIZE]> =
            Box::new(unsafe { MaybeUninit::uninit().assume_init() });

        for x in &mut stack[..] {
            *x = MaybeUninit::new(Value::Nil);
        }
        let stack = unsafe { transmute::<_, Box<[Value; STACK_SIZE]>>(stack) };

        Self {
            ctx,
            stack,
            upvalue_stack: vec![],
            ctrl_stack: vec![],
            result: Ok(Value::Nil),
            stdout: None,
            on_trace: None,
            on_error: None,
        }
    }

    /// Set a callback for stdout events.
    ///
    /// When `print` is called, this function is passed the result.
    pub fn set_stdout(&mut self, out: &'a mut dyn FnMut(&str)) {
        self.stdout = Some(out);
    }

    /// Set a callback for trace events.
    ///
    /// Traced values, along with the tracing position, are passed to
    /// the function during evaluation.
    pub fn set_on_trace(&mut self, f: &'a mut dyn FnMut(&Position, Value)) {
        self.on_trace = Some(f);
    }

    /// Main execution loop.
    fn exec_loop_(&mut self) -> Result<Value> {
        use Instr as I;
        while let Some(sf) = self.ctrl_stack.last_mut() {
            assert!((sf.ic as usize) < sf.closure.0.c.0.instrs.len());
            let instr = sf.closure.0.c.0.instrs[sf.ic as usize];
            crate::logtrace!(
                "exec loop: ic={} start={} instr=`{:?}`",
                sf.ic,
                sf.start,
                instr
            );

            sf.ic += 1; // ready for next iteration
            match instr {
                I::Copy(s0, s1) => {
                    let s0 = abs_offset!(sf, s0);
                    let s1 = abs_offset!(sf, s1);
                    self.stack[s1] = self.stack[s0].clone();
                }
                I::LoadLocal(l0, s1) => {
                    let s1 = abs_offset!(sf, s1);
                    self.stack[s1] = sf.closure.0.c.0.locals[l0.0 as usize].clone();
                }
                I::LoadUpvalue(up0, s1) => {
                    let s1 = abs_offset!(sf, s1);
                    self.stack[s1] = sf.closure.upvalues()[up0.0 as usize].clone();
                }
                I::LoadSelfClosure(s0) => {
                    let s0 = abs_offset!(sf, s0);
                    self.stack[s0] = Value::Closure(sf.closure.clone());
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
                    let v =
                        Value::Cons(RPtr::new((self.stack[s0].clone(), self.stack[s1].clone())));
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
                I::IsNil(s0, s1) => {
                    let b = match &self.stack[abs_offset!(sf, s0)] {
                        Value::Nil => true,
                        _ => false,
                    };
                    self.stack[abs_offset!(sf, s1)] = Value::Bool(b);
                }
                I::IsCons(s0, s1) => {
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
                I::PatSubstGet(s0, vidx, s2) => {
                    let s = match &self.stack[abs_offset!(sf, s0)] {
                        Value::PatSubst(s) => s.clone(),
                        _ => {
                            self.result =
                                Err(Error::new("pat-subst-get called on a non-substitution"));
                            break;
                        }
                    };
                    let e = s[vidx].clone();
                    self.stack[abs_offset!(sf, s2)] = Value::Expr(e);
                }
                I::Jump(offset) => {
                    crate::logtrace!("jump from ic={} with offset {}", sf.ic, offset);
                    sf.ic = (sf.ic as isize + offset as isize) as u32
                }
                I::JumpIfTrue(s0, offset) => {
                    let s0 = get_slot_bool!(self, abs_offset!(sf, s0));
                    if s0 {
                        crate::logtrace!("jump from ic={} with offset {}", sf.ic, offset);
                        sf.ic = (sf.ic as isize + offset as isize) as u32
                    }
                }
                I::JumpIfFalse(s0, offset) => {
                    let s0 = get_slot_bool!(self, abs_offset!(sf, s0));
                    if !s0 {
                        crate::logtrace!("jump from ic={} with offset {}", sf.ic, offset);
                        sf.ic = (sf.ic as isize + offset as isize) as u32
                    }
                }
                I::JumpIfNil(s0, offset) => {
                    let s0 = &self.stack[abs_offset!(sf, s0)];
                    if s0.is_nil() {
                        crate::logtrace!("jump from ic={} with offset {}", sf.ic, offset);
                        sf.ic = (sf.ic as isize + offset as isize) as u32
                    }
                }
                I::PatMatch(l0, s1, s2) => {
                    let p = match &sf.closure.0.c.0.locals[l0.0 as usize] {
                        Value::Pattern(p) => p,
                        _ => {
                            return Err(Error::new("match: need a pattern"));
                        }
                    };
                    let e1 = get_slot_expr!(self, abs_offset!(sf, s1));
                    let s2 = abs_offset!(sf, s2);
                    if let Some(s) = p.match_(e1) {
                        let v = Value::PatSubst(RPtr::new(s));
                        self.stack[s2] = v;
                    } else {
                        self.stack[s2] = Value::Nil;
                    }
                }
                I::GetGlob(x, s1) => {
                    let l = match &sf.closure.0.c.0.locals[x.0 as usize] {
                        Value::Str(s) => s,
                        _ => return Err(Error::new("get: expected a string")),
                    };
                    let s1 = abs_offset!(sf, s1);
                    match self.ctx.find_meta_value(l) {
                        Some(v) => self.stack[s1] = v.clone(),
                        None => return Err(Error::new("cannot find global")),
                    }
                }
                I::SetGlob(x, s1) => {
                    let l = match &sf.closure.0.c.0.locals[x.0 as usize] {
                        Value::Str(s) => s,
                        _ => return Err(Error::new("set: expected a string")),
                    };
                    let s1 = abs_offset!(sf, s1);
                    self.ctx.set_meta_value(l.clone(), self.stack[s1].clone())
                }
                I::PushLocalToUpvalue(s0) => {
                    let s0 = abs_offset!(sf, s0);
                    self.upvalue_stack.push(self.stack[s0].clone())
                }
                I::PushUpvalueToUpvalue(up0) => {
                    let u = sf.closure.upvalues()[up0.0 as usize].clone();
                    self.upvalue_stack.push(u)
                }
                I::CreateClosure(l0, s1) => {
                    // find chunk
                    let c0 = match &sf.closure.0.c.0.locals[l0.0 as usize] {
                        Value::Closure(c) => c,
                        _ => return Err(Error::new("set: expected a string")),
                    };
                    debug_assert_eq!(c0.upvalues().len(), 0); // proper chunk
                    let s1 = abs_offset!(sf, s1);
                    let cl = {
                        if self.upvalue_stack.is_empty() {
                            c0.clone()
                        } else {
                            let v: Vec<_> = self.upvalue_stack.drain(..).collect();
                            let up = Some(v.into_boxed_slice());
                            Closure::new(c0.0.c.clone(), up)
                        }
                    };
                    self.stack[s1] = Value::Closure(cl);
                }
                I::Call(sl_f, n_args, sl_ret) => {
                    let sl_f = abs_offset!(sf, sl_f);
                    let offset_ret = abs_offset!(sf, sl_ret);

                    let Self {
                        stack, ctx, stdout, ..
                    } = self;
                    match &stack[sl_f] {
                        Value::Builtin(b) => {
                            crate::logtrace!("call builtin {:?} with {} args", &b.name, n_args);
                            let args = &stack[sl_f + 1..sl_f + 1 + n_args as usize];
                            crate::logtrace!("  args: {:?}", &args);
                            let out = BuiltinPrinter(stdout);
                            let ctx = BuiltinEvalCtx { ctx, out };
                            let f = &(b.run);
                            let res = f(ctx, &args);
                            match res {
                                Ok(ret_value) => {
                                    crate::logtrace!(
                                        "return[offset {}]: {}",
                                        offset_ret,
                                        ret_value
                                    );
                                    self.stack[offset_ret] = ret_value;
                                }
                                Err(mut e) => {
                                    // TODO: proper stack trace instead
                                    e.set_source(Error::new_string(format!(
                                        "while calling {}",
                                        b.name
                                    )));
                                    self.result = Err(e);
                                    break;
                                }
                            }
                        }
                        Value::Closure(cl) => {
                            if cl.0.c.0.n_args != n_args {
                                return Err(Error::new_string(format!(
                                    "arity mismatch when calling {}",
                                    cl.0.c.0.name.as_deref().unwrap_or("<anon>")
                                )));
                            }

                            // push frame for `cl`
                            let cl = cl.clone();
                            self.exec_closure_(cl, (sl_f + 1) as u32, offset_ret as u32)?;
                        }
                        _ => {
                            self.result = Err(Error::new("cannot call value"));
                            break;
                        }
                    }
                }
                I::Become(sl_f, n_args) => {
                    if self.ctrl_stack.is_empty() {
                        self.result = Err(Error::new("tailcall from empty stack"));
                        break;
                    }

                    let Self {
                        ctrl_stack,
                        ctx,
                        stdout,
                        stack,
                        ..
                    } = self;

                    // reuse last stack frame.
                    let sf = ctrl_stack.last_mut().unwrap();

                    // fetch function
                    let offset_f = abs_offset!(sf, sl_f);
                    let offset_ret = sf.res_offset;

                    let f = &stack[offset_f];
                    if let Value::Closure(cl) = f {
                        let cl = cl.clone();

                        // get function + arguments to the beginning of the frame
                        let stack_frame = &mut stack[sf.start as usize
                            ..sf.start as usize + sf.closure.0.c.0.n_slots as usize];

                        // move arguments to the beginning of the frame
                        let shift_left_by = sl_f.0 as usize;
                        if shift_left_by > 0 {
                            for i in 0..(n_args as usize) {
                                stack_frame.swap(i, i + 1 + shift_left_by);
                            }
                        }

                        // update stack frame
                        sf.closure = cl;
                        sf.ic = 0;
                    } else if let Value::Builtin(b) = f {
                        crate::logtrace!("call builtin {:?}", &b.name);
                        let args = &stack[offset_f + 1..offset_f + 1 + n_args as usize];
                        let f = &b.run;
                        let out = BuiltinPrinter(stdout);
                        let ctx = BuiltinEvalCtx { ctx, out };
                        match f(ctx, &args) {
                            Ok(ret_value) => {
                                self.stack[offset_ret as usize] = ret_value;
                                // remove last frame
                                self.ctrl_stack.pop().unwrap();
                            }
                            Err(e) => {
                                self.result = Err(e);
                                break;
                            }
                        }
                    } else {
                        self.result = Err(Error::new("cannot call value"));
                        break;
                    }
                }
                I::Ret(sl_v) => {
                    let off_v = abs_offset!(sf, sl_v);
                    crate::logtrace!("ret sl_v={:?} abs_offset={} sf={:?}", sl_v, off_v, &sf);

                    // pop frame, get return address and frame offset
                    let res_offset;
                    if let Some(sf) = self.ctrl_stack.pop() {
                        res_offset = sf.res_offset;
                    } else {
                        self.result = Err(Error::new("stack underflow"));
                        break;
                    };

                    if res_offset as usize >= self.stack.len() {
                        self.result = Err(Error::new("invalid res offset"));
                        break;
                    }

                    let ret_val = self.stack[off_v].clone();

                    if self.ctrl_stack.is_empty() {
                        self.result = Ok(ret_val); // no more frames, will return
                    } else {
                        self.stack[res_offset as usize] = ret_val;
                    }
                }
                I::Trace(l0, s1) => {
                    if let Some(f) = &mut self.on_trace {
                        let pos = match &sf.closure.0.c.0.locals[l0.0 as usize] {
                            Value::Pos(p) => p,
                            _ => {
                                self.result = Err(Error::new("trace: expected a position"));
                                break;
                            }
                        };
                        let v = self.stack[abs_offset!(sf, s1)].clone();
                        crate::logtrace!("trace {:?} at {:?}", v, pos);
                        f(&*pos, v)
                    }
                }
                I::Fail(l0) => {
                    let e = match &sf.closure.0.c.0.locals[l0.0 as usize] {
                        Value::Error(e) => e,
                        _ => {
                            self.result = Err(Error::new("fail: expected an error"));
                            break;
                        }
                    };
                    if let Some(f) = &mut self.on_error {
                        f(&e)
                    }
                    // fail with the given error
                    self.result = Err(e.get_cloned());
                    break;
                }
                I::Trap => {
                    self.result = Err(Error::new("executed `trap`"));
                    break;
                }
            }
        }

        let mut r = Ok(Value::Nil);
        std::mem::swap(&mut r, &mut self.result);

        if let Err(e) = &mut r {
            e.set_source(Error::new("VM main loop"));
        }
        r
    }

    /// Print the current state of the VM in case of error.
    fn print_trace_(&self, out: &mut dyn io::Write, full: bool) -> io::Result<()> {
        let mut sf_i = self.ctrl_stack.len();
        write!(out, "===== begin stack trace =====\n")?;
        while sf_i > 0 {
            sf_i -= 1;
            let sf = &self.ctrl_stack[sf_i];
            let stack_i = sf.start as usize;
            let next_stack_i = (sf.start + sf.closure.0.c.0.n_slots) as usize;
            write!(
                out,
                "in closure {:?} (at {})\n",
                sf.closure.0.c.0.name, sf.closure.0.c.0.loc
            )?;
            if full {
                write!(
                    out,
                    "  frame[i={}, start={}, ic={}]\n",
                    sf_i, sf.start, sf.ic
                )?;
                // TODO: only print `ic-5..ic+5` window?
                write!(out, "  frame.chunk\n")?;
                let s = sf.closure.print(true, Some(sf.ic as usize))?;
                write!(out, "{}stack frame [\n", s)?;
                for i in stack_i..next_stack_i {
                    write!(out, "  st[{:5}] = {}\n", i, &self.stack[i])?;
                }
                write!(out, "]\n")?;
            }
        }
        write!(out, "===== end stack trace =====\n")?;
        Ok(())
    }

    /// Call closure `c` with arguments in `self.call_args`,
    /// put result into slot `offset`.
    fn exec_closure_(&mut self, cl: Closure, start_offset: u32, res_offset: u32) -> Result<()> {
        crate::logtrace!(
            "call closure (name={:?}, start_offset={}, res_offset={})",
            &cl.0.c.0.name,
            start_offset,
            res_offset
        );
        crate::logtrace!("callee: {:#?}", &cl);

        if (start_offset + cl.0.c.0.n_slots) as usize > STACK_SIZE {
            return Err(Error::new("stack overflow"));
        }

        self.ctrl_stack.push(StackFrame {
            ic: 0,
            closure: cl,
            start: start_offset,
            res_offset,
        });
        Ok(())
    }

    /// Call closure `c`
    pub fn exec_closure(&mut self, c: Closure, args: &[Value]) -> Result<Value> {
        if c.0.c.0.n_args as usize != args.len() {
            return Err(Error::new("arity mismatch"));
        }
        for i in 0..args.len() {
            self.stack[i] = args[i].clone();
        }
        self.exec_closure_(c, 0, 0)?;
        self.exec_loop_()
    }

    /// Call closure `c` without arguments.
    pub fn exec_top_closure_(&mut self, c: Closure) -> Result<Value> {
        if c.0.c.0.n_args as usize != 0 {
            return Err(Error::new("arity mismatch"));
        }
        self.exec_closure_(c, 0, 0)?;
        self.exec_loop_()
    }

    /// Reset execution state.
    fn reset(&mut self) {
        for i in 0..STACK_SIZE {
            self.stack[i] = Value::Nil
        }
        self.ctrl_stack.clear();
        self.result = Ok(Value::Nil);
    }

    /// Parse and execute the first top-level expression from the given code.
    pub fn run_lexer_one(&mut self, lexer: &mut lexer::Lexer) -> Result<Option<Value>> {
        use super::parser::*;

        self.reset();
        let p = Parser::new(self.ctx, lexer);

        match p.parse_top_expr() {
            Err(e) => {
                crate::logerr!("error while parsing: {}", e);
                return Err(e);
            }
            Ok(Some(c)) => {
                crate::logtrace!("chunk: {:?}", &c);
                debug_assert_eq!(c.0.n_captured, 0); // no parent to capture from
                let cl = Closure::new(c, None);
                match self.exec_top_closure_(cl) {
                    Ok(x) => Ok(Some(x)),
                    Err(e) => {
                        let mut s = vec![];
                        // only print full stacktrace if `TRUSTEE_TRACE=1`
                        // or if variable "print_full_traces" is true.
                        let full_tr = self
                            .ctx
                            .find_meta_value("print_full_traces")
                            .and_then(|v| v.as_bool())
                            .unwrap_or(false)
                            || std::env::var("TRUSTEE_TRACE").ok().as_deref() == Some("1");
                        self.print_trace_(&mut s, full_tr).unwrap();
                        crate::logerr!(
                            "error during execution:\n>> {}\n{}",
                            e,
                            std::str::from_utf8(&s).unwrap_or("<err>")
                        );

                        return Err(e);
                    }
                }
            }
            Ok(None) => Ok(None),
        }
    }

    /// Parse and execute the given code.
    pub fn run(&mut self, s: &str, file_name: Option<RStr>) -> Result<Value> {
        crate::logdebug!("meta.run {}", s);
        let mut lexer = lexer::Lexer::new(s, file_name);
        let mut last_r = Value::Nil;

        while let Some(r) = self.run_lexer_one(&mut lexer)? {
            last_r = r;
        }
        Ok(last_r)
    }
}
