//! Parser + on-the-fly compiler for the meta-language.

use super::builtins;
use super::{lexer, lexer::Tok, types::*};
use crate::{logdebug, logtrace, perror};
use {
    crate::{
        kernel_of_trust::{self as k, Ctx},
        rptr::RPtr,
        rstr::RStr,
        syntax, Error, Result,
    },
    std::{fmt, i16, marker::PhantomData, u8},
};

//  TODO: actually use tracepoints to emit `Trace`

use Instr as I;

/// The parser for the meta-language.
pub struct Parser<'a, 'b, 'c> {
    pub(crate) lexer: &'c mut lexer::Lexer<'b>,
    ctx: &'a mut k::Ctx,
    /// Where to trace, if anywhere.
    trace_points: Vec<Position>,
}

/// Lexical scope, used to control local variables.
enum LexScope {
    /// Slots for local variables, introduced by `{ … }` or most
    /// defining constructs (`def …`, `defn …`, etc.).
    Local(Vec<SlotIdx>),
    /// Local scope for evaluating function call arguments, cannot use `def`
    /// in there as we need strict stack discipline. `def` will fail.
    CallArgs,
}

/// Compiler for a given chunk.
struct Compiler<'a> {
    /// Current instructions for the chunk.
    instrs: Vec<Instr>,
    /// Local values for the chunk.
    locals: Vec<Value>,
    /// Captured variables from outer scopes, with their names.
    captured: Vec<RStr>,
    /// Local lexical scopes, each containing local variables.
    /// The `push` and `pop` operations must be balanced.
    lex_scopes: Vec<LexScope>,
    /// Number of input arguments. invariant: `<= n_slots`.
    n_args: u8,
    /// Maximum size `slots` ever took, including `n_args`.
    n_slots: u32,
    /// Name for the future chunk.
    name: Option<RStr>,
    /// Docstring for the future chunk.
    docstring: Option<RStr>,
    slots: Vec<CompilerSlot>,
    /// Parent compiler, used to resolve values from outer scopes.
    parent: Option<*mut Compiler<'a>>,
    /// Variance: covariant.
    /// If 'a: 'b, a compiler for 'a can be casted into a compiler for 'b
    /// as it just lives shorter.
    phantom: PhantomData<&'a ()>,
    /// Last result in a `def`.
    last_res: Option<ExprRes>,
    file_name: Option<RStr>,
    start: Position,
    end: Position,
}

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
#[must_use]
#[derive(Clone, Copy, Debug)]
struct ExprRes {
    /// Where the result lives.
    pub(super) slot: SlotIdx,
    /// Was the slot allocated for this expression?
    pub(super) temporary: bool,
    /// Does this actually return? If true, it means evaluation exited.
    pub(super) exited: bool,
}

/// Token used to remember to close scopes.
#[must_use]
struct Scope(usize);

#[derive(Copy, Clone)]
enum VarSlot {
    /// Local variable
    Local(SlotIdx),
    /// Upvalue
    Captured(UpvalueIdx),
}

/// Resolve the ID as a chunk or builtin, and put it into `sl`.
fn resolve_id_into_slot_(
    ctx: &mut Ctx,
    c: &mut Compiler,
    s: &str,
    loc: Position,
    sl: SlotIdx,
) -> Result<()> {
    if let Some(var) = c.find_slot_of_var(s)? {
        // local or captured variable
        match var {
            VarSlot::Local(f_var_slot) => {
                assert_ne!(f_var_slot, sl);
                c.emit_instr_(I::Copy(f_var_slot, sl));
            }
            VarSlot::Captured(upidx) => c.emit_instr_(I::LoadUpvalue(upidx, sl)),
        }
    } else if c.name.as_ref().filter(|n| n.get() == s).is_some() {
        // call current function
        c.emit_instr_(I::LoadSelfClosure(sl))
    } else if let Some(b) = builtins::basic_primitives::BUILTINS
        .iter()
        .find(|b| b.name == s)
    {
        let lidx = c.allocate_local_(Value::Builtin(b))?;
        c.emit_instr_(I::LoadLocal(lidx, sl));
    } else if let Some(b) = builtins::logic_builtins::BUILTINS
        .iter()
        .find(|b| b.name == s)
    {
        let lidx = c.allocate_local_(Value::Builtin(b))?;
        c.emit_instr_(I::LoadLocal(lidx, sl));
    } else if let Some(v) = ctx.find_meta_value(s) {
        // look in the `ctx` current set of values
        let lidx = c.allocate_local_(v.clone())?;
        c.emit_instr_(I::LoadLocal(lidx, sl));
    } else {
        return Err(perror!(loc, "unknown identifier '{}'", s));
    }
    Ok(())
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

impl<'a, 'b, 'c> Parser<'a, 'b, 'c> {
    /// Create a new parser for source string `s`.
    pub fn new(ctx: &'a mut k::Ctx, lexer: &'c mut lexer::Lexer<'b>) -> Self {
        Self {
            ctx,
            lexer,
            trace_points: vec![],
        }
    }

    /// Add a trace point at the given position.
    pub fn add_tracepoint(&mut self, p: Position) {
        self.trace_points.push(p)
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

    /// Parse a toplevel expression in the string passed at creation time.
    ///
    /// Returns `Ok(None)` if no more statements could be read.
    /// Otherwise returns `Ok((chunk, lexer))`.
    pub(super) fn parse_top_expr(mut self) -> Result<Option<Chunk>> {
        let t = self.lexer.cur();
        let start = self.lexer.loc();

        match t {
            Tok::Eof => Ok(None),
            _ => {
                let mut c = Compiler {
                    instrs: vec![],
                    locals: vec![],
                    captured: vec![],
                    n_slots: 0,
                    n_args: 0,
                    lex_scopes: vec![],
                    name: None,
                    docstring: None,
                    slots: vec![],
                    parent: None,
                    phantom: PhantomData,
                    start,
                    last_res: None,
                    end: start,
                    file_name: self.lexer.file_name.clone(),
                };
                let res = get_res!(c, None);
                let r = self.parse_expr_(&mut c, Some(res.slot));
                c.end = self.lexer.loc();
                match r {
                    Ok(r) => {
                        c.emit_instr_(I::Ret(r.slot));
                    }
                    Err(e) => {
                        // build error message
                        c.instrs.clear();
                        let loc = Location {
                            start: c.start,
                            end: c.end,
                            file_name: c.file_name.clone(),
                        };
                        let err = RPtr::new(MetaError { err: e, loc });
                        let l0 = c.allocate_local_(Value::Error(err))?;
                        // emit instruction to fail
                        c.emit_instr_(I::Fail(l0))
                    }
                }
                Ok(Some(c.into_chunk()))
            }
        }
    }

    /// Parse a list of arguments and the body of a function.
    ///
    /// Does not parse the preceeding `fn` or `defn`.
    fn parse_fn_args_and_body_(
        &mut self,
        f_name: Option<RStr>,
        var_closing: Tok<'b>,
        closing: Tok<'b>,
        parent: Option<&mut Compiler>,
    ) -> Result<Chunk> {
        let mut vars: Vec<RStr> = vec![];

        let loc = self.lexer.loc();
        while self.cur_tok_() != var_closing {
            let e = cur_tok_as_id_(
                &mut self.lexer,
                "expected a bound variable or closing delimiter",
            )?
            .into();
            self.next_tok_();
            logtrace!("add var {:?}", e);
            vars.push(e);
        }
        self.eat_(var_closing, "expected closing delimiter after variables")?;
        if vars.len() > u8::MAX as usize {
            return Err(perror!(loc, "maximum number of arguments exceeded"));
        }

        let ch = {
            let start = self.lexer.loc();
            let parent = match parent {
                None => None,
                Some(p) => Some(p as &mut _ as *mut _),
            };

            // make a compiler for this chunk.
            let mut c: Compiler<'_> = Compiler {
                instrs: vec![],
                locals: vec![],
                captured: vec![],
                n_slots: 0,
                n_args: vars.len() as u8,
                name: f_name.clone(),
                docstring: None,
                lex_scopes: vec![],
                slots: vec![],
                parent,
                phantom: PhantomData,
                start,
                last_res: None,
                end: start,
                file_name: self.lexer.file_name.clone(),
            };
            // add variables to `sub_c`
            for x in vars {
                let sl_x = c.allocate_var_(x)?;
                c.get_slot_(sl_x.slot).state = CompilerSlotState::Activated;
            }
            logtrace!("compiling {:?}: slots for args: {:?}", &f_name, &c.slots);

            let res = self.parse_expr_seq_(&mut c, closing, None)?;

            // return value
            c.emit_instr_(I::Ret(res.slot));
            c.free(&res);
            c.into_chunk()
        };

        Ok(ch)
    }

    /// After a '(', see if we have `(doc "str")`
    fn try_parse_doc(&mut self) -> Result<Option<RStr>> {
        let loc = self.lexer.loc();
        if let Tok::Id("doc") = self.cur_tok_() {
            // docstring
            self.next_tok_();
            let s = if let Tok::QuotedString(s) = self.cur_tok_() {
                s.into()
            } else {
                return Err(perror!(loc, "`doc` expects a string"));
            };
            self.lexer.next();
            self.eat_(Tok::RParen, "missing ')' after `doc`")?;

            Ok(Some(s))
        } else {
            Ok(None)
        }
    }

    /// Parse an application-type expression, closed with `closing`.
    ///
    /// Put the result into slot `sl_res` if provided.
    fn parse_expr_app_(&mut self, c: &mut Compiler, sl_res: Option<SlotIdx>) -> Result<ExprRes> {
        let loc = self.lexer.loc();
        let id = cur_tok_as_id_(&mut self.lexer, "expect an identifier after opening")?;
        logtrace!("parse expr app id={:?}", id);

        if let Some((binop_instr, assoc)) = binary_op_(id) {
            // primitive binary operator.
            // emit `res = a op b`
            self.next_tok_();
            let res = get_res!(c, sl_res);

            let a = self.parse_expr_(c, None)?;
            let b = self.parse_expr_(c, None)?;
            c.emit_instr_(binop_instr(a.slot, b.slot, res.slot));

            if let BinOpAssoc::LAssoc = assoc {
                // parse more arguments, like in `(+ a b c)`
                loop {
                    if self.cur_tok_() == Tok::RParen {
                        break;
                    }

                    // parse next operand: `res = res op b`
                    let b = self.parse_expr_(c, Some(b.slot))?;
                    c.emit_instr_(binop_instr(res.slot, b.slot, res.slot));
                }
            }

            self.eat_(Tok::RParen, "expected closing ')' in application")?;

            c.free(&a);
            c.free(&b);

            Ok(res)
        } else if let Some(unop_instr) = unary_op_(id) {
            // unary op
            self.next_tok_();
            let e = self.parse_expr_(c, None)?;
            self.eat_(Tok::RParen, "expected closing ')' after `not`")?;
            // `e := not e`
            c.free(&e);
            let res = get_res!(c, sl_res);
            c.emit_instr_(unop_instr(e.slot, res.slot));
            Ok(res)
        } else if id == "if" {
            self.next_tok_();
            let res = get_res!(c, sl_res);
            let res_test = self.parse_expr_(c, None)?;

            let jump_if_false = c.reserve_jump_();

            // parse `then`
            let scope = c.push_local_scope();
            let _e_then = self.parse_expr_(c, Some(res.slot))?;
            c.pop_local_scope(scope);
            // jump above `else`
            let jump_after_then = c.reserve_jump_();

            // jump here if test is false to execute `else`
            c.emit_jump(jump_if_false, |off| I::JumpIfFalse(res_test.slot, off))?;
            c.free(&res_test);

            // parse `else`
            let scope = c.push_local_scope();
            let _e_else = self.parse_expr_(c, Some(res.slot))?;
            c.pop_local_scope(scope);

            // jump here after `then` is done.
            c.emit_jump(jump_after_then, |off| I::Jump(off))?;

            self.eat_(Tok::RParen, "expected closing ')' after 'if'")?;
            Ok(res)
        } else if id == "def" {
            // definition in current local scope, or global
            self.next_tok_();

            let x: RStr =
                cur_tok_as_id_(&mut self.lexer, "expected variable name after `def`")?.into();
            let sl_x = c.allocate_var_(x.clone())?;
            self.next_tok_();

            let scope = c.push_local_scope();
            let _e = self.parse_expr_seq_(c, Tok::RParen, Some(sl_x.slot))?;
            c.pop_local_scope(scope);

            // now the variable is usable
            c.get_slot_(sl_x.slot).state = CompilerSlotState::Activated;

            Ok(sl_x)
        } else if id == "set" {
            self.next_tok_();

            // parse a variable name
            let x = cur_tok_as_id_(self.lexer, "expect variable name after 'set'")?;
            let sl_x = c.allocate_local_(Value::Str(x.into()))?;
            self.next_tok_();

            let scope = c.push_local_scope();
            let r = self.parse_expr_seq_(c, Tok::RParen, sl_res)?;
            c.pop_local_scope(scope);
            c.emit_instr_(I::SetGlob(sl_x, r.slot));
            Ok(r)
        } else if id == "and" {
            // control operator, need special handling
            self.next_tok_();

            // we build:
            // e1; if false goto :f
            // e2; if false goto :f
            // res = true; goto :end
            // f: res = false
            // end:

            let res = get_res!(c, sl_res);
            let e1 = self.parse_expr_(c, Some(res.slot))?;
            let j1_false = c.reserve_jump_();

            let e2 = self.parse_expr_(c, Some(res.slot))?;
            let j2_false = c.reserve_jump_();

            c.emit_instr_(I::LoadBool(true, res.slot));
            let j_true = c.reserve_jump_();

            // if e1 is false, jump here and return false
            c.emit_jump(j1_false, |off| I::JumpIfFalse(e1.slot, off))?;
            c.emit_jump(j2_false, |off| I::JumpIfFalse(e2.slot, off))?;
            c.emit_instr_(I::LoadBool(false, res.slot));

            c.emit_jump(j_true, |off| I::Jump(off))?;

            self.eat_(Tok::RParen, "missing ')' after and")?;
            Ok(res)
        } else if id == "or" {
            // control operator, need special handling
            self.next_tok_();

            // we build:
            // e1; if true goto :t
            // e2; if true goto :t
            // res = false; goto :end
            // t: res = true
            // end:

            let res = get_res!(c, sl_res);
            let e1 = self.parse_expr_(c, Some(res.slot))?;
            let j1_true = c.reserve_jump_();

            let e2 = self.parse_expr_(c, Some(res.slot))?;
            let j2_true = c.reserve_jump_();

            c.emit_instr_(I::LoadBool(false, res.slot));
            let j_false = c.reserve_jump_();

            c.emit_jump(j1_true, |off| I::JumpIfTrue(e1.slot, off))?;
            c.emit_jump(j2_true, |off| I::JumpIfTrue(e2.slot, off))?;
            c.emit_instr_(I::LoadBool(true, res.slot));

            c.emit_jump(j_false, |off| I::Jump(off))?;

            self.eat_(Tok::RParen, "missing ')' after or")?;
            Ok(res)
        } else if id == "fail" {
            self.next_tok_();
            // emit failure
            let l = if let Tok::QuotedString(s) = self.cur_tok_() {
                c.allocate_local_(Value::Str(RStr::from(s)))?
            } else {
                return Err(Error::new("after `fail`, expect a string literal"));
            };
            self.eat_(Tok::RParen, "missing ')' after 'fail'")?;

            c.emit_instr_(I::Fail(l));
            let res = get_res!(c, sl_res); // will not be used
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

            let scope = c.push_local_scope();
            loop {
                let x: RStr = cur_tok_as_id_(&mut self.lexer, "expected variable name")?.into();
                let sl_x = c.allocate_var_(x)?;
                self.next_tok_();
                let _ = self.parse_expr_(c, Some(sl_x.slot))?;
                // now the variable is defined.
                c.get_slot_(sl_x.slot).state = CompilerSlotState::Activated;

                if self.cur_tok_() == b_closing {
                    break;
                }
            }
            self.eat_(b_closing, "expected block of bound variables to end")?;

            let res = get_res!(c, sl_res);
            let res = self.parse_expr_seq_(c, Tok::RParen, Some(res.slot))?;
            c.pop_local_scope(scope); // deallocate locals

            Ok(res)
        } else if id == "fn" {
            // anonymous function
            self.next_tok_();
            let res = get_res!(c, sl_res);

            // parse function
            let b_closing = match self.cur_tok_() {
                Tok::LParen => Tok::RParen,
                Tok::LBracket => Tok::RBracket,
                _ => return Err(perror!(self.lexer.loc(), "expect '(' or '[' after `fn`")),
            };
            self.next_tok_();

            let (loc_sub, n_captured) = {
                // compile anonymous function in an inner compiler
                let sub_c = self.parse_fn_args_and_body_(
                    None, // nameless
                    b_closing,
                    Tok::RParen,
                    Some(c),
                )?;
                let n_captured = sub_c.0.n_captured;

                // push function into a local
                let loc_sub = c.allocate_local_(Value::Closure(Closure::new(sub_c, None)))?;
                (loc_sub, n_captured)
            };

            if n_captured > 0 {
                // `sub_c` is a true closure, close over captured vars
                c.emit_instr_(I::CreateClosure(loc_sub, res.slot));
            } else {
                // just copy the chunk
                c.emit_instr_(I::LoadLocal(loc_sub, res.slot))
            }

            Ok(res)
        } else if id == "defn" {
            // function name
            self.next_tok_();

            let f_name: RStr = cur_tok_as_id_(&mut self.lexer, "expected function name")?.into();
            self.next_tok_();

            let res = c.allocate_var_(f_name.clone())?;

            // parse function
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

            let sub_c =
                self.parse_fn_args_and_body_(Some(f_name.clone()), b_closing, Tok::RParen, None)?;

            // define the function.
            logdebug!("define {} as {:#?}", &f_name, sub_c);
            let sub_c = Closure::new(sub_c, None);

            if c.is_in_local_scope() {
                let loc = c.allocate_local_(Value::Closure(sub_c))?;
                c.emit_instr_(I::LoadLocal(loc, res.slot));
            } else {
                self.ctx.set_meta_value(f_name, Value::Closure(sub_c));
                c.emit_instr_(I::LoadNil(res.slot));
            }

            Ok(res)
        } else if id == "list" {
            // parse into a list
            self.lexer.next();
            self.parse_list_(c, sl_res, Tok::RParen)
        } else if id == "get" {
            self.next_tok_();
            // parse a variable name
            let x = cur_tok_as_id_(self.lexer, "expect variable name after 'set'")?;
            let sl_x = c.allocate_local_(Value::Str(x.into()))?;
            let res = get_res!(c, sl_res);
            c.emit_instr_(I::GetGlob(sl_x, res.slot));
            Ok(res)
        } else if id == "become" {
            self.next_tok_();

            // there is not truly a result for this frame, so this is fake.
            let mut res = ExprRes::new(SlotIdx(u8::MAX), false);
            res.exited = true;

            logtrace!("parse tail-application");

            let id_f = cur_tok_as_id_(&mut self.lexer, "expected function name after `become`")?;
            let f = c.allocate_temporary_on_top_()?;
            resolve_id_into_slot_(&mut self.ctx, c, id_f, loc, f.slot)?;
            self.lexer.next();
            logtrace!(".. function is {:?} := {:?}", f, c.get_slot_(f.slot));

            // parse arguments
            let mut args = vec![];
            let len = self.parse_expr_list_(
                c,
                Tok::RParen,
                &|c| Ok(Some(c.allocate_top_slot_(CompilerSlotState::Activated)?)),
                &mut |_c, a| args.push(a.clone()),
            )?;
            if len > u8::MAX as usize {
                return Err(perror!(
                    self.lexer.loc(),
                    "maximum number of arguments exceeded"
                ));
            }

            c.emit_instr_(I::Become(f.slot, len as u8));

            for a in args {
                c.free(&a);
            }
            c.free(&f);
            Ok(res)
        } else {
            // make a function call.

            let res = get_res!(c, sl_res);
            logtrace!("parse application (res: {:?})", res);

            let scope = c.enter_call_args(); // forbid `def`

            // use `res` if it's top of stack, otherwise allocate a temp
            let (f, f_temp) = if c.is_top_of_stack_(res.slot) {
                (res, false)
            } else {
                let slot = c.allocate_temporary_on_top_()?;
                (slot, true)
            };
            resolve_id_into_slot_(&mut self.ctx, c, id, loc, f.slot)?;
            self.lexer.next();
            logtrace!(".. function is {:?} := {:?}", f, c.get_slot_(f.slot));

            // parse arguments
            let mut args = vec![];
            let len = self.parse_expr_list_(
                c,
                Tok::RParen,
                &|c| Ok(Some(c.allocate_temporary_on_top_()?.slot)),
                &mut |_c, a| args.push(a.clone()),
            )?;

            if len > u8::MAX as usize {
                return Err(perror!(
                    self.lexer.loc(),
                    "maximum number of arguments exceeded"
                ));
            }

            c.exit_call_args(scope);

            c.emit_instr_(I::Call(f.slot, len as u8, res.slot));
            // free temporary slots on top of stack
            c.deallocate_top_slots_(if f_temp { len + 1 } else { len });
            Ok(res)
        }
    }

    /// Parse a list of expressions, return how many were parsed.
    fn parse_expr_list_(
        &mut self,
        c: &mut Compiler,
        closing: Tok<'b>,
        pre: &dyn Fn(&mut Compiler) -> Result<Option<SlotIdx>>,
        post: &mut dyn FnMut(&mut Compiler, &ExprRes),
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

            let sl = pre(c)?;
            let arg = self.parse_expr_(c, sl)?;
            has_exited = arg.exited;
            post(c, &arg);

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
        closing: Tok<'b>,
    ) -> Result<ExprRes> {
        let res = get_res!(c, sl_res);
        logtrace!("parse list (sl_res {:?}, res {:?})", sl_res, res);

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
    fn parse_expr_seq_(
        &mut self,
        c: &mut Compiler,
        closing: Tok,
        sl_res: Option<SlotIdx>,
    ) -> Result<ExprRes> {
        let res = get_res!(c, sl_res);
        let mut first = true;
        let mut init = false;
        let loc = self.lexer.loc();

        loop {
            if self.cur_tok_() == closing {
                break; // done
            }
            let allow_doc = first;
            let r = self.parse_expr_or_doc_(c, allow_doc, res.slot)?;
            // make sure we return a value
            init = init || r.is_some();
            first = false;
        }
        self.eat_(closing, "unclosed sequence")?;

        if !init {
            return Err(perror!(
                loc,
                "no value is returned (is there only `doc` in here?)"
            ));
        }

        Ok(res)
    }

    fn parse_expr_or_doc_(
        &mut self,
        c: &mut Compiler,
        allow_doc: bool,
        sl_res: SlotIdx,
    ) -> Result<Option<ExprRes>> {
        if let Tok::LParen = self.cur_tok_() {
            self.next_tok_();

            if allow_doc && c.docstring.is_none() {
                if let Some(doc) = self.try_parse_doc()? {
                    c.docstring = Some(doc);
                    return Ok(None);
                }
            }

            Ok(Some(self.parse_expr_app_(c, Some(sl_res))?))
        } else {
            Ok(Some(self.parse_expr_(c, Some(sl_res))?))
        }
    }

    /// Parse an expression and return its result's slot.
    ///
    /// `sl_res` is an optional pre-provided slot.
    fn parse_expr_(&mut self, c: &mut Compiler, sl_res: Option<SlotIdx>) -> Result<ExprRes> {
        logtrace!("parse expr (cur {:?})", self.lexer.cur());
        logtrace!("> slots {:?}", c.slots);

        let Self { ctx, lexer, .. } = self;
        let loc = lexer.loc();
        let r = match lexer.cur() {
            Tok::LParen => {
                lexer.next();
                self.parse_expr_app_(c, sl_res)
            }
            Tok::LBracket => {
                lexer.next();
                self.parse_list_(c, sl_res, Tok::RBracket)
            }
            Tok::LBrace => {
                // see: `do`
                // parse a series of expressions.
                self.next_tok_();
                let scope = c.push_local_scope();
                let r = self.parse_expr_seq_(c, Tok::RBrace, sl_res)?;
                c.pop_local_scope(scope);
                Ok(r)
            }
            Tok::Trace => {
                // parse expression, and trace it.
                let loc = self.lexer.loc();
                self.next_tok_();

                let r = self.parse_expr_(c, sl_res)?;

                // put location in locals.
                let l_loc = c.allocate_local_(Value::Pos(RPtr::new(loc)))?;
                c.emit_instr_(I::Trace(l_loc, r.slot));
                Ok(r)
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
                if let Some(var) = c.find_slot_of_var(id)? {
                    match var {
                        VarSlot::Local(sl_var) => {
                            if let Some(sl_r) = sl_res {
                                if sl_r != sl_var {
                                    // must copy
                                    c.emit_instr_(I::Copy(sl_var, sl_r));
                                }
                            } else {
                                // return the existing variable instead.
                                self.next_tok_();
                                c.free(&res);
                                return Ok(ExprRes::new(sl_var, false));
                            }
                        }
                        VarSlot::Captured(upidx) => {
                            // copy from upvalue
                            self.next_tok_();
                            let res = get_res!(c, sl_res);
                            c.emit_instr_(I::LoadUpvalue(upidx, res.slot));
                            return Ok(res);
                        }
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
        };
        if let Ok(res) = r {
            c.last_res = Some(res);
        }
        r
    }

    /// Expect the token `t`, and consume it; or return an error.
    fn eat_(&mut self, t: lexer::Tok, errmsg: &str) -> Result<()> {
        self.lexer.eat_(t, errmsg)
    }
}

enum BinOpAssoc {
    LAssoc,
    NonAssoc,
}

impl<'a> Compiler<'a> {
    /// Convert the compiler's state into a proper chunk.
    fn into_chunk(self) -> Chunk {
        let loc = Location {
            start: self.start,
            end: self.end,
            file_name: self.file_name,
        };
        let c = ChunkImpl {
            instrs: self.instrs.into_boxed_slice(),
            locals: self.locals.into_boxed_slice(),
            n_args: self.n_args,
            n_slots: self.n_slots,
            n_captured: self.captured.len() as u8,
            name: self.name,
            docstring: self.docstring,
            loc,
        };
        Chunk(k::Ref::new(c))
    }

    #[inline]
    fn get_slot_(&mut self, i: SlotIdx) -> &mut CompilerSlot {
        &mut self.slots[i.0 as usize]
    }

    fn enter_call_args(&mut self) -> Scope {
        crate::logtrace!("enter call args scope");
        self.lex_scopes.push(LexScope::CallArgs);
        Scope(self.lex_scopes.len())
    }

    fn is_in_local_scope(&self) -> bool {
        self.parent.is_some() || self.lex_scopes.len() > 0
    }

    fn exit_call_args(&mut self, sc: Scope) {
        crate::logtrace!("exit call args scope");
        if self.lex_scopes.len() != sc.0 {
            panic!(
                "unbalanced scopes in call args (expect len {}, got {})",
                sc.0,
                self.lex_scopes.len()
            );
        }
        match self.lex_scopes.pop() {
            Some(LexScope::CallArgs) => (),
            _ => panic!("unbalanced scope in call args"),
        }
    }

    fn push_local_scope(&mut self) -> Scope {
        crate::logtrace!("push local scope");
        self.lex_scopes.push(LexScope::Local(vec![]));
        Scope(self.lex_scopes.len())
    }

    fn pop_local_scope(&mut self, sc: Scope) {
        crate::logtrace!("pop local scope");
        if self.lex_scopes.len() != sc.0 {
            panic!(
                "unbalanced scopes (expect len {}, got {})",
                sc.0,
                self.lex_scopes.len()
            );
        }
        match self.lex_scopes.pop() {
            Some(LexScope::Local(sl)) => {
                for x in sl {
                    self.deallocate_slot_(x)
                }
            }
            _ => panic!("compiler: unbalanced scopes"),
        }
    }

    /// Ensure the value is in `self.locals`, return its index.
    fn allocate_local_(&mut self, v: Value) -> Result<LocalIdx> {
        crate::logtrace!("compiler(name={:?}): push local {}", self.name, v);

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
    fn emit_instr_(&mut self, i: Instr) {
        crate::logtrace!(
            "compiler(name={:?}, n_locals={}): emit instr {:?}",
            self.name,
            self.locals.len(),
            i
        );
        self.instrs.push(i)
    }

    /// Reserve space for a jump instruction that will be emitted later.
    fn reserve_jump_(&mut self) -> JumpPosition {
        let off = self.instrs.len();
        crate::logtrace!(
            "compiler(name={:?}, n_locals={}): reserve jump at offset {}",
            self.name,
            self.locals.len(),
            off
        );

        self.instrs.push(I::Trap); // reserve space
        JumpPosition(off)
    }

    /// Set the jump instruction for a previously reserved jump slot.
    fn emit_jump(&mut self, pos: JumpPosition, mk_i: impl FnOnce(i16) -> Instr) -> Result<()> {
        let i = if let I::Trap = self.instrs[pos.0] {
            let j_offset = self.instrs.len() as isize - pos.0 as isize - 1;
            if j_offset < i16::MIN as isize || j_offset > i16::MAX as isize {
                return Err(Error::new("jump is too long"));
            }
            mk_i(j_offset as i16)
        } else {
            panic!("jump already edited at pos {}", pos.0);
        };

        crate::logtrace!(
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

    /// Deallocate the `n` top slots.
    ///
    /// Panics if any of these is a variable.
    fn deallocate_top_slots_(&mut self, n: usize) {
        for _i in 0..n {
            let sl = self
                .slots
                .pop()
                .expect("compiler: deallocating non-existing slot");
            if sl.var_name.is_some() {
                panic!("deallocating top slot that is a named var")
            }
        }
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
    fn allocate_var_(&mut self, name: RStr) -> Result<ExprRes> {
        let slot = self.allocate_any_slot_(CompilerSlotState::NotActivatedYet)?;
        self.get_slot_(slot).var_name = Some(name);
        if let Some(LexScope::CallArgs) = self.lex_scopes.last() {
            return Err(Error::new(
                "cannot bind variable in the list of arguments of a function call",
            ));
        } else if let Some(LexScope::Local(scope)) = self.lex_scopes.last_mut() {
            scope.push(slot); // push into local scope
        }
        Ok(ExprRes::new(slot, false))
    }

    /// Allocate a slot on the stack, anywhere, to hold a temporary result.
    fn allocate_temporary_(&mut self) -> Result<ExprRes> {
        let slot = self.allocate_any_slot_(CompilerSlotState::Activated)?;
        Ok(ExprRes::new(slot, true))
    }

    fn allocate_temporary_on_top_(&mut self) -> Result<ExprRes> {
        let slot = self.allocate_top_slot_(CompilerSlotState::Activated)?;
        Ok(ExprRes::new(slot, true))
    }

    /// Check if `sl` is the top slot.
    fn is_top_of_stack_(&self, sl: SlotIdx) -> bool {
        if sl.0 as usize + 1 == self.slots.len() {
            true
        } else {
            self.slots[sl.0 as usize..]
                .iter()
                .all(|s| s.state == CompilerSlotState::Unused)
        }
    }

    /// Free expression result.
    fn free(&mut self, e: &ExprRes) {
        if e.temporary {
            self.deallocate_slot_(e.slot)
        }
    }

    /// Deallocate that slot, it becomes available for further use.
    fn deallocate_slot_(&mut self, sl: SlotIdx) {
        if sl.0 as usize + 1 == self.slots.len() {
            // just pop the slot
            self.slots.pop().unwrap();
        } else {
            let sl = self.get_slot_(sl);
            sl.var_name = None;
            sl.state = CompilerSlotState::Unused;
        }
    }

    /// Find slot for the given variable `v`.
    #[allow(unsafe_code)] // used for making `parent` pointers covariant
    fn find_slot_of_var(&mut self, v: &str) -> Result<Option<VarSlot>> {
        for (i, s) in self.slots.iter().enumerate().rev() {
            if s.state != CompilerSlotState::Activated {
                continue; // slot is not actually ready yet
            }
            if let Some(v2) = &s.var_name {
                if v2.get() == v {
                    return Ok(Some(VarSlot::Local(SlotIdx(i as u8))));
                }
            }
        }
        // look in already captured variables
        for (i, s) in self.captured.iter().enumerate() {
            if v == s.get() {
                return Ok(Some(VarSlot::Captured(UpvalueIdx(i as u8))));
            }
        }
        // look in parent scope to see if we close over `v`
        if let Some(parent) = self.parent {
            // here we convert into a local `&mut Compiler`, but it's
            // safe because we only use it locally to find captured
            // variables.
            //
            // It needs to be mutable because `find_slot_of_var` is
            // called recursively on it, possibly modifying its set of captured
            // variables. For example, in
            // `(defn f [x]
            //    (def g (fn [y]
            //      (print "in g")
            //      (def h (fn [] (print x))))))`
            // when we reach `h` we must capture `x` from `g` which captures
            // it from `f`.
            let parent = unsafe { &mut *parent };
            crate::logtrace!("look for {} in parent scope", v);
            if let Some(parent_var) = parent.find_slot_of_var(v)? {
                crate::logtrace!("found {} in parent scope", v);
                // capture `v` from parent scope
                if self.captured.len() > u8::MAX as usize {
                    return Err(Error::new("too many captured variables"));
                }
                let upidx = UpvalueIdx(self.captured.len() as u8);
                crate::logtrace!("capture var {} from parent (upidx {})", v, upidx.0);
                self.captured.push(v.into());
                match parent_var {
                    VarSlot::Local(sl) => parent.emit_instr_(I::PushLocalToUpvalue(sl)),
                    VarSlot::Captured(u) => parent.emit_instr_(I::PushUpvalueToUpvalue(u)),
                }
                return Ok(Some(VarSlot::Captured(upidx)));
            }
        }

        Ok(None) // not in scope
    }
}

/// A builtin binary operator
fn binary_op_(
    s: &str,
) -> Option<(
    &'static dyn Fn(SlotIdx, SlotIdx, SlotIdx) -> Instr,
    BinOpAssoc,
)> {
    macro_rules! ret {
        ($i: expr, $a: expr) => {
            Some(((&|s1, s2, s3| $i(s1, s2, s3)), $a))
        };
    };
    macro_rules! ret_swap {
        ($i: expr, $a: expr) => {
            Some(((&|s1, s2, s3| $i(s2, s1, s3)), $a))
        };
    };
    if s == "+" {
        ret!(I::Add, BinOpAssoc::LAssoc)
    } else if s == "-" {
        ret!(I::Sub, BinOpAssoc::LAssoc)
    } else if s == "*" {
        ret!(I::Mul, BinOpAssoc::LAssoc)
    } else if s == "/" {
        ret!(I::Div, BinOpAssoc::LAssoc)
    } else if s == "%" {
        ret!(I::Mod, BinOpAssoc::NonAssoc)
    } else if s == "cons" {
        ret!(I::Cons, BinOpAssoc::NonAssoc)
    } else if s == "==" {
        ret!(I::Eq, BinOpAssoc::NonAssoc)
    } else if s == "!=" {
        ret!(I::Neq, BinOpAssoc::NonAssoc)
    } else if s == "<" {
        ret!(I::Lt, BinOpAssoc::NonAssoc)
    } else if s == "<=" {
        ret!(I::Leq, BinOpAssoc::NonAssoc)
    } else if s == ">" {
        ret_swap!(I::Lt, BinOpAssoc::NonAssoc)
    } else if s == ">=" {
        ret_swap!(I::Leq, BinOpAssoc::NonAssoc)
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
    } else if s == "nil?" {
        ret!(I::IsNil)
    } else if s == "cons?" {
        ret!(I::IsCons)
    } else if s == "car" {
        ret!(I::Car)
    } else if s == "cdr" {
        ret!(I::Cdr)
    } else {
        None
    }
}

/// Extract current token as an identifier.
fn cur_tok_as_id_<'a>(lexer: &'a mut lexer::Lexer, errmsg: &'static str) -> Result<&'a str> {
    match lexer.cur() {
        Tok::Id(s) => Ok(s),
        _ => Err(crate::perror!(lexer.loc(), "{}", errmsg)),
    }
}

mod impls {
    use super::*;

    impl fmt::Debug for CompilerSlot {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            let s = match self.state {
                CompilerSlotState::Activated => "a",
                CompilerSlotState::NotActivatedYet => "n",
                CompilerSlotState::Unused => "_",
            };
            write!(out, "(slot:{} n:{:?})", s, self.var_name)
        }
    }

    impl ExprRes {
        /// Make a new expression result.
        pub(super) fn new(sl: SlotIdx, temporary: bool) -> Self {
            Self {
                slot: sl,
                temporary,
                exited: false,
            }
        }
    }
}
