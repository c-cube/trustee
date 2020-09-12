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

use compiler::Compiler;
use Instr as I;

/// The parser for the meta-language.
pub struct Parser<'a, 'b, 'c> {
    pub(crate) lexer: &'c mut lexer::Lexer<'b>,
    ctx: &'a mut k::Ctx,
    /// Pool of compiler states that can be re-used
    comps: Box<[Option<Box<compiler::CompilerState>>]>,
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

/// Token used to remember to close scopes.
#[must_use]
struct Scope(usize);

/// Token used to remember to deallocate temporary slots.
#[must_use]
#[derive(Debug)]
struct TempSlot(SlotIdx);

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
    if s == "nil" {
        c.emit_instr(I::LoadNil(sl));
    } else if s == "true" {
        c.emit_instr(I::LoadBool(true, sl));
    } else if s == "false" {
        c.emit_instr(I::LoadBool(false, sl));
    } else if let Some(var) = c.find_slot_of_var(s)? {
        // local or captured variable
        match var {
            VarSlot::Local(f_var_slot) => {
                assert_ne!(f_var_slot, sl);
                c.emit_instr(I::Copy(f_var_slot, sl));
            }
            VarSlot::Captured(upidx) => c.emit_instr(I::LoadUpvalue(upidx, sl)),
        }
    } else if c.name.as_ref().filter(|n| n.get() == s).is_some() {
        // call current function
        c.emit_instr(I::LoadSelfClosure(sl))
    } else if let Some(b) = builtins::basic_primitives::BUILTINS
        .iter()
        .find(|b| b.name == s)
    {
        let lidx = c.allocate_local(Value::Builtin(b))?;
        c.emit_instr(I::LoadLocal(lidx, sl));
    } else if let Some(b) = builtins::logic_builtins::BUILTINS
        .iter()
        .find(|b| b.name == s)
    {
        let lidx = c.allocate_local(Value::Builtin(b))?;
        c.emit_instr(I::LoadLocal(lidx, sl));
    } else if let Some(v) = ctx.find_meta_value(s) {
        // look in the `ctx` current set of values
        let lidx = c.allocate_local(v.clone())?;
        c.emit_instr(I::LoadLocal(lidx, sl));
    } else {
        return Err(perror!(loc, "unknown identifier '{}'", s));
    }
    Ok(())
}

/// A delayed "jump" instruction, to emit when we know the offset
struct JumpInstrEmit {
    pos: JumpPosition,
    match_res: SlotIdx,
    f: &'static dyn Fn(SlotIdx, i16) -> Instr,
}

impl JumpInstrEmit {
    fn new(
        pos: JumpPosition,
        match_res: SlotIdx,
        f: &'static dyn Fn(SlotIdx, i16) -> Instr,
    ) -> Self {
        Self { pos, match_res, f }
    }

    fn jump_if_false(pos: JumpPosition, res: SlotIdx) -> Self {
        Self::new(pos, res, &|sl, i| I::JumpIfFalse(sl, i))
    }
}

impl<'a, 'b, 'c> Parser<'a, 'b, 'c> {
    /// Create a new parser for source string `s`.
    pub fn new(ctx: &'a mut k::Ctx, lexer: &'c mut lexer::Lexer<'b>) -> Self {
        let mut comps = vec![];
        comps.resize_with(8, || None); // size of cache
        Self {
            ctx,
            lexer,
            comps: comps.into_boxed_slice(),
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

    /// Obtain or reuse a compiler state.
    fn obtain_compiler_state(&mut self) -> Box<compiler::CompilerState> {
        for x in self.comps.iter_mut() {
            if x.is_some() {
                let c = x.take().unwrap();
                return c;
            }
        }
        Box::new(compiler::CompilerState::new())
    }

    /// Cache this compiler state for further reuse.
    fn recycle_compiler_state(&mut self, mut st: Box<compiler::CompilerState>) {
        for x in self.comps.iter_mut() {
            if x.is_none() {
                st.reset(); // ensure it's clean before reusing it
                *x = Some(st);
                return;
            }
        }
        // all full, just discard st
        drop(st)
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
                let st = self.obtain_compiler_state();
                let mut c = Compiler::new(st, start, None, self.lexer.file_name.clone());

                // slot for the result
                let (tmp_res, res) = c.allocate_temporary_slot()?;
                let e_succeed = self.parse_expr_(&mut c, res);
                c.end = self.lexer.loc();
                match e_succeed {
                    Ok(()) => {
                        c.emit_instr(I::Ret(res));
                    }
                    Err(mut e) => {
                        // build context error message
                        c.clear_all_instr();
                        let loc = Location {
                            start: c.start,
                            end: c.end,
                            file_name: c.file_name.as_ref().map(|f| f.to_string()),
                        };
                        let wrap_err = Error::new_meta("parse top expr".to_string(), loc);
                        e.set_source(wrap_err);
                        let l0 = c.allocate_local(Value::Error(RPtr::new(e)))?;
                        // emit instruction to fail
                        c.emit_instr(I::Fail(l0))
                    }
                }
                c.free(tmp_res);
                let (ch, st) = c.into_chunk();
                self.recycle_compiler_state(st);
                Ok(Some(ch))
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
            let st = self.obtain_compiler_state();
            let mut c: Compiler<'_> =
                Compiler::new(st, start, parent, self.lexer.file_name.clone());
            c.n_args = vars.len() as u8;
            c.name = f_name.clone();
            // add variables to `sub_c`
            for x in vars {
                let sl_x = c.allocate_var(x)?;
                c.activate_var(sl_x);
            }
            logtrace!("compiling {:?}: slots for args: {:?}", &f_name, c.slots());

            let (tmp_res, res) = c.allocate_temporary_slot()?;
            self.parse_expr_seq_(&mut c, closing, res)?;

            // return value
            c.emit_instr(I::Ret(res));
            c.free(tmp_res);
            let (ch, st) = c.into_chunk();
            self.recycle_compiler_state(st);
            ch
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

    /// Parse a pattern in a `match` branch, possibly adding bindings to
    /// a local scope if `matchee` matches the pattern.
    ///
    /// Returns a vector of jumps to emit if the pattern fails.
    fn parse_pattern_(&mut self, c: &mut Compiler, matchee: SlotIdx) -> Result<Vec<JumpInstrEmit>> {
        let loc = self.lexer.loc();
        let tok = self.lexer.cur();

        match tok {
            Tok::QuotedExpr(s) => {
                // TODO: support patterns with interpolation? maybe not here?
                let p = syntax::parse_pattern(self.ctx, s)?;
                self.next_tok_();
                let pat = RPtr::new(p);

                let (tmp_match_res, match_res) = c.allocate_temporary_slot()?;

                let l0 = c.allocate_local(Value::Pattern(pat.clone()))?;
                // match `matchee` with `pat`
                c.emit_instr(I::PatMatch(l0, matchee, match_res));

                let jp_fail = c.reserve_jump();

                // jump succeeded, so we push the pattern's substitution
                // bindings into the local scope.
                for (name, idx) in pat.iter_vars() {
                    crate::logtrace!("allocate local var {:?} from pattern", name);
                    let var_sl = c.allocate_var(name.into())?;
                    c.emit_instr(I::PatSubstGet(match_res, idx, var_sl));
                    c.activate_var(var_sl);
                }

                let jpe =
                    JumpInstrEmit::new(jp_fail, match_res, &|slot, off| I::JumpIfNil(slot, off));

                // match result is not needed anymore
                c.free(tmp_match_res);

                Ok(vec![jpe])
            }
            Tok::Int(i) => {
                self.next_tok_();
                // compute `matchee == i`

                // store `i` into a local slot.
                let (tmp_i, sl_i) = c.allocate_temporary_slot()?;
                if i.abs() < i16::MAX as i64 {
                    c.emit_instr(I::LoadInteger(i as i16, sl_i));
                } else {
                    // use a local
                    let l0 = c.allocate_local(Value::Int(i))?;
                    c.emit_instr(I::LoadLocal(l0, sl_i));
                }
                c.emit_instr(I::Eq(sl_i, matchee, sl_i));
                // if false, jump away
                let jp_false = c.reserve_jump();
                let jpe = JumpInstrEmit::jump_if_false(jp_false, sl_i);

                c.free(tmp_i);
                Ok(vec![jpe])
            }
            Tok::Id("nil") => {
                self.next_tok_();
                let (tmp_i, sl_i) = c.allocate_temporary_slot()?;
                c.emit_instr(I::IsNil(matchee, sl_i));
                let jp_false = c.reserve_jump();
                let jpe = JumpInstrEmit::jump_if_false(jp_false, sl_i);
                c.free(tmp_i);
                Ok(vec![jpe])
            }
            Tok::Id("true") => {
                self.next_tok_();
                let (tmp_i, sl_i) = c.allocate_temporary_slot()?;
                c.emit_instr(I::EqBool(true, matchee, sl_i));
                let jp_false = c.reserve_jump();
                let jpe = JumpInstrEmit::jump_if_false(jp_false, sl_i);
                c.free(tmp_i);
                Ok(vec![jpe])
            }
            Tok::Id("false") => {
                self.next_tok_();
                let (tmp_i, sl_i) = c.allocate_temporary_slot()?;
                c.emit_instr(I::EqBool(false, matchee, sl_i));
                let jp_false = c.reserve_jump();
                let jpe = JumpInstrEmit::jump_if_false(jp_false, sl_i);
                c.free(tmp_i);
                Ok(vec![jpe])
            }
            Tok::Id("_") => {
                self.next_tok_();
                Ok(vec![]) // automatic success
            }
            Tok::Id(name) => {
                // bind variable
                crate::logtrace!("allocate local var {:?} from pattern", name);
                let var_sl = c.allocate_var(name.into())?;
                self.next_tok_();
                c.emit_instr(I::Copy(matchee, var_sl));
                c.activate_var(var_sl);
                // no possible failure here, matches anything!
                Ok(vec![])
            }
            Tok::LBracket => {
                self.next_tok_();
                // list literal

                let mut jp_fail_v = vec![];
                let (tmp0, sl0) = c.allocate_temporary_slot()?; // used for list elements
                let mut cur = matchee;

                loop {
                    let tok = self.lexer.cur();

                    let (tmp_x, x) = c.allocate_temporary_slot()?;

                    if matches!(tok, Tok::RBracket) {
                        self.next_tok_();

                        // check we have nil
                        c.emit_instr(I::IsNil(cur, x));
                        let jp_false = c.reserve_jump();
                        let jpe = JumpInstrEmit::jump_if_false(jp_false, x);
                        jp_fail_v.push(jpe);

                        c.free(tmp_x);

                        break;
                    }

                    // check we have `cons`
                    c.emit_instr(I::IsCons(cur, x));

                    // if not cons, jump out
                    let jpe = c.reserve_jump();
                    jp_fail_v.push(JumpInstrEmit::jump_if_false(jpe, x));

                    c.free(tmp_x);

                    // match head to sub-pattern
                    let (tmp_hd, hd) = c.allocate_temporary_slot()?;
                    c.emit_instr(I::Car(cur, hd));
                    let v = self.parse_pattern_(c, hd)?;
                    jp_fail_v.extend(v);
                    c.free(tmp_hd);

                    // recurse with `cur` being the tail of the list
                    c.emit_instr(I::Cdr(cur, sl0));
                    cur = sl0;
                }

                c.free(tmp0);
                Ok(jp_fail_v)
            }
            Tok::LParen => {
                self.next_tok_();
                let loc = self.lexer.loc();
                let tok = self.lexer.cur();

                if let Tok::Id("cons") = tok {
                    self.next_tok_();
                    let mut jp_fail_v = vec![];

                    let (tmp_i, sl_i) = c.allocate_temporary_slot()?;
                    c.emit_instr(I::IsCons(matchee, sl_i));

                    // if not cons, jump out
                    let jpe = c.reserve_jump();
                    jp_fail_v.push(JumpInstrEmit::jump_if_false(jpe, sl_i));

                    c.free(tmp_i);

                    // match head to sub-pattern
                    let (tmp_hd, hd) = c.allocate_temporary_slot()?;
                    c.emit_instr(I::Car(matchee, hd));
                    let v = self.parse_pattern_(c, hd)?;
                    jp_fail_v.extend(v);
                    c.free(tmp_hd);

                    // match tail to sub-pattern
                    let (tmp_tl, tl) = c.allocate_temporary_slot()?;
                    c.emit_instr(I::Cdr(matchee, tl));
                    let v = self.parse_pattern_(c, tl)?;
                    jp_fail_v.extend(v);
                    c.free(tmp_tl);

                    self.eat_(
                        Tok::RParen,
                        "expect two sub-patterns after `cons`, then `)`",
                    )?;

                    Ok(jp_fail_v)
                } else {
                    Err(perror!(loc, "unknown composite pattern head: {:?}", tok))
                }
            }
            _ => {
                return Err(perror!(
                    loc,
                    "expected a pattern in each case, got {:?}",
                    self.lexer.cur()
                ))
            }
        }
    }

    /// Either parse a local variable and return it; or parse an expression
    /// into a local scope and return the scope.
    fn parse_expr_or_get_var_(&mut self, c: &mut Compiler) -> Result<(Option<TempSlot>, SlotIdx)> {
        let Self { ctx, lexer, .. } = self;
        let loc = lexer.loc();

        if let Tok::Id(id) = lexer.cur() {
            if let Some(var) = c.find_slot_of_var(id)? {
                match var {
                    VarSlot::Local(sl_var) => {
                        // here we can directly use the slot for `var`
                        lexer.next();
                        return Ok((None, sl_var));
                    }
                    _ => (),
                }
            }
            // allocate a slot and resolve into it
            let (tmp, res) = c.allocate_temporary_slot()?;
            resolve_id_into_slot_(ctx, c, id, loc, res)?;
            lexer.next();
            Ok((Some(tmp), res))
        } else {
            // allocate a slot and parse expression into it
            let (tmp, res) = c.allocate_temporary_slot()?;
            self.parse_expr_(c, res)?;
            Ok((Some(tmp), res))
        }
    }

    /// Parse an application-type expression, closed with `closing`.
    ///
    /// Put the result into slot `res`. Consumes the closing delimiter.
    fn parse_expr_app_(&mut self, c: &mut Compiler, res: SlotIdx) -> Result<()> {
        let loc = self.lexer.token_start_pos();
        let id = cur_tok_as_id_(&mut self.lexer, "expect an identifier after opening")?;
        logtrace!("parse expr app id={:?}", id);

        if let Some((binop_instr, assoc)) = binary_op_(id) {
            // primitive binary operator.
            // emit `res = a op b`
            self.next_tok_();

            let (tmp_a, a) = self.parse_expr_or_get_var_(c)?;
            let (tmp_b, b) = self.parse_expr_or_get_var_(c)?;
            c.emit_instr(binop_instr(a, b, res));
            c.free_opt(tmp_b);
            c.free_opt(tmp_a);

            if let BinOpAssoc::LAssoc = assoc {
                // parse more arguments, like in `(+ a b c)`
                loop {
                    if self.cur_tok_() == Tok::RParen {
                        break;
                    }

                    // parse next operand: `res = res op b`
                    let (tmp_b, b) = self.parse_expr_or_get_var_(c)?;
                    c.emit_instr(binop_instr(res, b, res));
                    c.free_opt(tmp_b);
                }
            }

            self.eat_(Tok::RParen, "expected closing ')' after binary operator")?;
        } else if let Some(unop_instr) = unary_op_(id) {
            // unary op
            self.next_tok_();

            let (tmp_e, e) = self.parse_expr_or_get_var_(c)?;
            // `e := not e`
            c.emit_instr(unop_instr(e, res));
            c.free_opt(tmp_e);

            self.eat_(Tok::RParen, "expected closing ')' after unary operator")?;
        } else if id == "if" {
            self.next_tok_();

            let (tmp_cond, cond) = self.parse_expr_or_get_var_(c)?;

            let jump_if_false = c.reserve_jump();

            // parse `then` into `res`
            let scope = c.push_local_scope();
            self.parse_expr_(c, res)?;
            c.pop_local_scope(scope);
            // jump above `else`
            let jump_after_then = c.reserve_jump();

            // jump here if test is false to execute `else`
            c.emit_jump(jump_if_false, |off| I::JumpIfFalse(cond, off))?;
            c.free_opt(tmp_cond);

            // parse `else` into `res`
            let scope = c.push_local_scope();
            self.parse_expr_(c, res)?;
            c.pop_local_scope(scope);

            // jump here after `then` is done.
            c.emit_jump(jump_after_then, |off| I::Jump(off))?;

            self.eat_(Tok::RParen, "expected closing ')' after 'if'")?;
        } else if id == "match" {
            // match on expressions
            self.next_tok_();

            // expression to match
            let (tmp_e, e) = self.parse_expr_or_get_var_(c)?;

            // parse a series of `(<pat> <expr>+)` finished by `(else <expr>+))`

            let mut jumps_if_succeeded = vec![]; // accumulate success conditions
            let mut prev_jump_if_failed: Option<Vec<JumpInstrEmit>> = None; // previous's iteration jump to the current one
            loop {
                let loc = self.lexer.loc();
                let t = self.cur_tok_();
                if let Tok::LParen = t {
                    self.next_tok_();
                // another case in the match
                } else if let Tok::RParen = t {
                    return Err(perror!(loc, "match must end with a `(else <expr>+)` case"));
                } else {
                    return Err(perror!(
                        loc,
                        "expect `(else <expr>+)` or `(\"expr pat\" <expr>+)` in `match`, got {:?}",
                        t
                    ));
                }

                // jump here if previous case failed. There can be multiple ways
                // the previous case failed.
                if let Some(jps) = prev_jump_if_failed.take() {
                    for jpe in jps {
                        let JumpInstrEmit { pos, match_res, f } = jpe;
                        c.emit_jump(pos, |off| f(match_res, off))?;
                    }
                }

                // create match and subsequent bindings
                let tok = self.cur_tok_();
                if let Tok::Id("else") = tok {
                    // last case, unconditional
                    self.next_tok_();
                    self.parse_expr_seq_(c, Tok::RParen, res)?;
                    break;
                } else if let Tok::Id("case") = tok {
                    self.next_tok_()
                } else {
                    return Err(perror!(loc, "expect `else` or `case` in a match branch"));
                };

                let scope = c.push_local_scope();

                // parse a pattern in the new scope.
                let jumps_if_false_p = self.parse_pattern_(c, e)?;

                // if matching failed, we'll go to the next case
                prev_jump_if_failed = Some(jumps_if_false_p);

                let _ = self.parse_expr_seq_(c, Tok::RParen, res)?;
                c.pop_local_scope(scope); // match result gets out of scope

                // then jump to the end.
                let jp = c.reserve_jump();
                jumps_if_succeeded.push(jp);
            }
            self.eat_(Tok::RParen, "expected closing ')' after 'match'")?;

            // all successful jumps come directly here
            for jp in jumps_if_succeeded {
                c.emit_jump(jp, |off| I::Jump(off))?;
            }
            c.free_opt(tmp_e);
        } else if id == "def" {
            // definition in current local scope, or global
            self.next_tok_();

            let name_x: RStr =
                cur_tok_as_id_(&mut self.lexer, "expected variable name after `def`")?.into();
            let x = c.allocate_var(name_x.clone())?;
            self.next_tok_();

            let scope = c.push_local_scope();
            self.parse_expr_seq_(c, Tok::RParen, x)?;
            c.pop_local_scope(scope);

            // now the variable is usable
            c.activate_var(x);
        } else if id == "set" {
            self.next_tok_();

            // parse a variable name
            let x_name = cur_tok_as_id_(self.lexer, "expect variable name after 'set'")?;
            let x_loc = c.allocate_local(Value::Str(x_name.into()))?;
            self.next_tok_();

            let scope = c.push_local_scope();
            self.parse_expr_seq_(c, Tok::RParen, res)?;
            c.pop_local_scope(scope);
            c.emit_instr(I::SetGlob(x_loc, res));
        } else if id == "and" {
            // control operator, need special handling
            self.next_tok_();

            // we build:
            // e1; if false goto :f
            // e2; if false goto :f
            // res = true; goto :end
            // f: res = false
            // end:

            self.parse_expr_(c, res)?;
            let j1_false = c.reserve_jump();

            self.parse_expr_(c, res)?;
            let j2_false = c.reserve_jump();

            c.emit_instr(I::LoadBool(true, res));
            let j_true = c.reserve_jump();

            // if e1 is false, jump here and return false
            c.emit_jump(j1_false, |off| I::JumpIfFalse(res, off))?;
            c.emit_jump(j2_false, |off| I::JumpIfFalse(res, off))?;
            c.emit_instr(I::LoadBool(false, res));

            c.emit_jump(j_true, |off| I::Jump(off))?;

            self.eat_(Tok::RParen, "missing ')' after and")?;
        } else if id == "or" {
            // control operator, need special handling
            self.next_tok_();

            // we build:
            // e1; if true goto :t
            // e2; if true goto :t
            // res = false; goto :end
            // t: res = true
            // end:

            self.parse_expr_(c, res)?;
            let j1_true = c.reserve_jump();

            self.parse_expr_(c, res)?;
            let j2_true = c.reserve_jump();

            c.emit_instr(I::LoadBool(false, res));
            let j_false = c.reserve_jump();

            c.emit_jump(j1_true, |off| I::JumpIfTrue(res, off))?;
            c.emit_jump(j2_true, |off| I::JumpIfTrue(res, off))?;
            c.emit_instr(I::LoadBool(true, res));

            c.emit_jump(j_false, |off| I::Jump(off))?;

            self.eat_(Tok::RParen, "missing ')' after or")?;
        } else if id == "fail" {
            let start = loc;

            self.next_tok_();
            // emit failure. Takes a string message or nothing.
            let err = match self.cur_tok_() {
                Tok::QuotedString(s) => {
                    let s = s.to_string();
                    self.next_tok_();
                    s
                }
                Tok::RParen => "failure".to_string(),
                _ => {
                    return Err(Error::new("after `fail`, expect a string literal"));
                }
            };
            let end = self.lexer.loc();
            self.eat_(Tok::RParen, "missing ')' after 'fail'")?;

            // build a meta-error and emit `Fail()` with it as parameter.
            let loc = Location {
                start,
                end,
                file_name: c.file_name.as_ref().map(|s| s.to_string()),
            };
            let merr = Error::new_meta(err, loc);
            let l = c.allocate_local(Value::Error(RPtr::new(merr)))?;
            c.emit_instr(I::Fail(l));
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
                let x_name: RStr =
                    cur_tok_as_id_(&mut self.lexer, "expected variable name")?.into();
                let x = c.allocate_var(x_name)?;
                self.next_tok_();
                self.parse_expr_(c, x)?;
                // now the variable is defined.
                c.activate_var(x);

                if self.cur_tok_() == b_closing {
                    break;
                }
            }
            self.eat_(b_closing, "expected block of bound variables to end")?;

            self.parse_expr_seq_(c, Tok::RParen, res)?;
            c.pop_local_scope(scope); // deallocate locals
        } else if id == "fn" {
            // anonymous function
            self.next_tok_();

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
                let loc_sub = c.allocate_local(Value::Closure(Closure::new(sub_c, None)))?;
                (loc_sub, n_captured)
            };

            if n_captured > 0 {
                // `sub_c` is a true closure, close over captured vars
                c.emit_instr(I::CreateClosure(loc_sub, res));
            } else {
                // just copy the chunk
                c.emit_instr(I::LoadLocal(loc_sub, res))
            }
        } else if id == "defn" {
            // function name
            self.next_tok_();

            let f_name: RStr = cur_tok_as_id_(&mut self.lexer, "expected function name")?.into();
            self.next_tok_();

            let res = c.allocate_var(f_name.clone())?;

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
                let loc = c.allocate_local(Value::Closure(sub_c))?;
                c.emit_instr(I::LoadLocal(loc, res));
            } else {
                self.ctx.set_meta_value(f_name, Value::Closure(sub_c));
                c.emit_instr(I::LoadNil(res));
            }
        } else if id == "list" {
            // parse into a list
            self.lexer.next();
            self.parse_list_(c, res, Tok::RParen)?;
        } else if id == "get" {
            self.next_tok_();
            // parse a variable name
            let x_name = cur_tok_as_id_(self.lexer, "expect variable name after 'set'")?;
            let x_loc = c.allocate_local(Value::Str(x_name.into()))?;
            c.emit_instr(I::GetGlob(x_loc, res));
        } else if id == "become" {
            self.next_tok_();

            logtrace!("parse tail-call");

            let id_f = cur_tok_as_id_(&mut self.lexer, "expected function name after `become`")?;
            let f = c.allocate_temporary_on_top()?;
            resolve_id_into_slot_(&mut self.ctx, c, id_f, loc, f.0)?;
            self.lexer.next();

            // parse arguments
            let mut args = vec![];
            let len = self.parse_call_args_list_(c, &mut |_c, a| args.push(a))?;
            if len > u8::MAX as usize {
                return Err(perror!(
                    self.lexer.loc(),
                    "maximum number of arguments exceeded"
                ));
            }

            c.emit_instr(I::Become(f.0, len as u8));

            // free all temporaries
            for a in args {
                c.free(a);
            }
            c.free(f);
        } else {
            // make a function call.
            logtrace!("parse application (res: {:?})", res);

            let scope = c.enter_call_args(); // forbid `def`

            // use `res` if it's top of stack, otherwise allocate a temp
            let (f, f_temp) = if c.is_top_of_stack_(res) {
                (res, false)
            } else {
                let slot = c.allocate_temporary_on_top()?;
                (slot.0, true)
            };
            resolve_id_into_slot_(&mut self.ctx, c, id, loc, f)?;
            self.lexer.next();

            // parse arguments
            let len = self.parse_call_args_list_(c, &mut |_c, _a| ())?;

            if len > u8::MAX as usize {
                return Err(perror!(
                    self.lexer.loc(),
                    "maximum number of arguments exceeded"
                ));
            }

            c.exit_call_args(scope);

            c.emit_instr(I::Call(f, len as u8, res));
            // free temporary slots on top of stack
            c.deallocate_top_slots(if f_temp { len + 1 } else { len });
        };
        Ok(())
    }

    /// Parse a list of expressions as parameters to a function,
    /// return how many were parsed.
    fn parse_call_args_list_(
        &mut self,
        c: &mut Compiler,
        f: &mut dyn FnMut(&mut Compiler, TempSlot),
    ) -> Result<usize> {
        let mut n = 0;
        loop {
            if self.cur_tok_() == Tok::RParen {
                self.next_tok_();
                break;
            }

            let sl = c.allocate_temporary_on_top()?;
            self.parse_expr_(c, sl.0)?;
            f(c, sl);

            n += 1;
            if n > u8::MAX as usize {
                return Err(perror!(
                    self.lexer.loc(),
                    "maximum number of arguments exceeded"
                ));
            }
        }
        Ok(n)
    }

    /// Parse a list, either from `(list …)` or `[…]`.
    fn parse_list_(&mut self, c: &mut Compiler, res: SlotIdx, closing: Tok<'b>) -> Result<()> {
        logtrace!("parse list (sl_res {:?}, res {:?})", res, res);

        c.emit_instr(I::LoadNil(res));

        let mut tmp_slots = vec![];
        while self.lexer.cur() != closing {
            let (tmp_x, x) = c.allocate_temporary_slot()?;
            self.parse_expr_(c, x)?;
            tmp_slots.push(tmp_x);
        }
        for tmp in tmp_slots.into_iter().rev() {
            c.emit_instr(I::Cons(tmp.0, res, res));
            c.free(tmp);
        }
        self.lexer.eat_(closing, "list must be closed")?;
        Ok(())
    }

    /// Parse a series of expressions.
    fn parse_expr_seq_(&mut self, c: &mut Compiler, closing: Tok, res: SlotIdx) -> Result<()> {
        let mut first = true;
        let mut init = false;
        let loc = self.lexer.loc();

        loop {
            let tok = self.cur_tok_();
            if tok == closing {
                break; // done
            }
            let allow_doc = first;
            let ret_val = self.parse_expr_or_doc_(c, allow_doc, res)?;
            // make sure we return a value
            init = init || ret_val;
            first = false;
        }
        self.eat_(closing, "unclosed sequence")?;

        if !init {
            return Err(perror!(
                loc,
                "no value is returned (is there only `doc` in here?)"
            ));
        }

        Ok(())
    }

    /// Parse expression or `doc` statement.
    ///
    /// Returns `true` if an expression was parsed, `false` if a documentation
    /// statement was.
    fn parse_expr_or_doc_(
        &mut self,
        c: &mut Compiler,
        allow_doc: bool,
        res: SlotIdx,
    ) -> Result<bool> {
        if let Tok::LParen = self.cur_tok_() {
            self.next_tok_();

            if allow_doc && c.docstring.is_none() {
                if let Some(doc) = self.try_parse_doc()? {
                    c.docstring = Some(doc);
                    return Ok(false);
                }
            }
            self.parse_expr_app_(c, res)?;
            Ok(true)
        } else {
            self.parse_expr_(c, res)?;
            Ok(true)
        }
    }

    /// Parse an expression and return its result's slot.
    ///
    /// `sl_res` is an optional pre-provided slot.
    fn parse_expr_(&mut self, c: &mut Compiler, res: SlotIdx) -> Result<()> {
        logtrace!("parse expr (cur {:?})", self.lexer.cur());
        logtrace!("> slots {:?}", c.slots());

        let Self { ctx, lexer, .. } = self;
        let loc = lexer.loc();
        let tok = lexer.cur();
        match tok {
            Tok::LParen => {
                lexer.next();
                self.parse_expr_app_(c, res)?;
            }
            Tok::LBracket => {
                lexer.next();
                self.parse_list_(c, res, Tok::RBracket)?;
            }
            Tok::LBrace => {
                // parse a series of expressions, in a new local scope.
                self.next_tok_();
                let scope = c.push_local_scope();
                self.parse_expr_seq_(c, Tok::RBrace, res)?;
                c.pop_local_scope(scope);
            }
            Tok::Trace => {
                // parse expression, and trace it.
                let loc = self.lexer.loc();
                self.next_tok_();

                self.parse_expr_(c, res)?;

                // put location in locals.
                let l_loc = c.allocate_local(Value::Pos(RPtr::new(loc)))?;
                c.emit_instr(I::Trace(l_loc, res));
            }
            Tok::Int(i) => {
                lexer.next();
                if i >= i16::MIN as i64 && i <= i16::MAX as i64 {
                    c.emit_instr(I::LoadInteger(i as i16, res))
                } else {
                    let lidx = c.allocate_local(Value::Int(i))?;
                    c.emit_instr(I::LoadLocal(lidx, res));
                }
            }
            Tok::Id(id) => {
                resolve_id_into_slot_(ctx, c, id, loc, res)?;
                lexer.next();
            }
            Tok::ColonId(s) => {
                let lidx = c.allocate_local(Value::Sym(s.into()))?;
                self.next_tok_();
                c.emit_instr(I::LoadLocal(lidx, res));
            }
            Tok::QuotedString(s) => {
                let lidx = c.allocate_local(Value::Str(s.into()))?;
                self.next_tok_();
                c.emit_instr(I::LoadLocal(lidx, res));
            }
            Tok::QuotedExpr(e) => {
                if e.as_bytes().contains(&b'?') {
                    // TODO: interpolation
                    return Err(perror!(loc, "unimplemented: interpolating exprs"));
                }
                let e = syntax::parse_expr(self.ctx, e)
                    .map_err(|e| perror!(loc, "while parsing expression: {}", e))?;
                let lidx = c.allocate_local(Value::Expr(e))?;
                self.next_tok_();
                c.emit_instr(I::LoadLocal(lidx, res));
            }
            Tok::RParen | Tok::RBracket | Tok::RBrace => {
                return Err(perror!(loc, "unexpected closing delimiter {:?}", tok))
            }
            Tok::Invalid(c) => return Err(perror!(loc, "invalid char {}", c)),

            Tok::Eof => return Err(perror!(loc, "unexpected EOF when parsing expr")),
        };
        Ok(())
    }

    /// Expect the token `t`, and consume it; or return an error.
    fn eat_(&mut self, t: lexer::Tok, errmsg: &str) -> Result<()> {
        self.lexer.eat_(t, errmsg)
    }
}

#[derive(Debug)]
enum BinOpAssoc {
    LAssoc,
    NonAssoc,
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

mod compiler {
    use super::*;

    /// Compiler for a given chunk.
    pub(super) struct Compiler<'a> {
        st: Box<CompilerState>,
        /// Number of input arguments. invariant: `<= n_slots`.
        pub n_args: u8,
        /// Maximum size `slots` ever took, including `n_args`.
        pub n_slots: u32,
        /// Name for the future chunk.
        pub name: Option<RStr>,
        /// Docstring for the future chunk.
        pub docstring: Option<RStr>,
        /// Parent compiler, used to resolve values from outer scopes.
        parent: Option<*mut Compiler<'a>>,
        /// Variance: covariant.
        /// If 'a: 'b, a compiler for 'a can be casted into a compiler for 'b
        /// as it just lives shorter.
        phantom: PhantomData<&'a ()>,
        /// Last result in a `def`.
        pub file_name: Option<RStr>,
        pub start: Position,
        pub end: Position,
    }

    /// A part of the `Compiler` type that can be re-used.
    #[must_use]
    pub(super) struct CompilerState {
        /// Current instructions for the chunk.
        instrs: Vec<Instr>,
        /// Local values for the chunk.
        locals: Vec<Value>,
        /// Captured variables from outer scopes, with their names.
        captured: Vec<RStr>,
        /// Local lexical scopes, each containing local variables.
        /// The `push` and `pop` operations must be balanced.
        lex_scopes: Vec<LexScope>,
        /// Slots for representing the stack.
        slots: Vec<CompilerSlot>,
    }

    pub struct CompilerSlot {
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

    impl CompilerState {
        /// Create a new state.
        pub fn new() -> Self {
            Self {
                instrs: Vec::with_capacity(32),
                locals: Vec::with_capacity(32),
                captured: vec![],
                lex_scopes: Vec::with_capacity(16),
                slots: Vec::with_capacity(16),
            }
        }

        /// Reset all data, so this can be reused.
        pub fn reset(&mut self) {
            let CompilerState {
                instrs,
                locals,
                captured,
                lex_scopes,
                slots,
            } = self;
            instrs.clear();
            locals.clear();
            captured.clear();
            lex_scopes.clear();
            slots.clear();
        }
    }

    impl<'a> Compiler<'a> {
        /// Create a new compiler.
        pub fn new(
            st: Box<CompilerState>,
            start: Position,
            parent: Option<*mut Compiler<'a>>,
            file_name: Option<RStr>,
        ) -> Self {
            Compiler {
                st,
                n_slots: 0,
                n_args: 0,
                name: None,
                docstring: None,
                parent,
                phantom: PhantomData,
                start,
                end: start,
                file_name,
            }
        }

        /// Convert the compiler's state into a proper chunk.
        /// Also return the underlying compiler state.
        pub fn into_chunk(mut self) -> (Chunk, Box<CompilerState>) {
            let loc = Location {
                start: self.start,
                end: self.end,
                file_name: self.file_name.map(|s| s.to_string()),
            };
            let mut instrs = vec![];
            std::mem::swap(&mut self.st.instrs, &mut instrs);
            let mut locals = vec![];
            std::mem::swap(&mut self.st.locals, &mut locals);
            let c = ChunkImpl {
                instrs: instrs.into_boxed_slice(),
                locals: locals.into_boxed_slice(),
                n_args: self.n_args,
                n_slots: self.n_slots,
                n_captured: self.st.captured.len() as u8,
                name: self.name,
                docstring: self.docstring,
                loc,
            };
            (Chunk(k::Ref::new(c)), self.st)
        }

        /// View current slots.
        #[allow(unused)]
        pub fn slots(&self) -> &[CompilerSlot] {
            &self.st.slots[..]
        }

        /// Clear all instructions.
        ///
        /// This is useful in case of error.
        pub fn clear_all_instr(&mut self) {
            self.st.instrs.clear();
        }

        #[inline]
        fn get_slot_(&mut self, i: SlotIdx) -> &mut CompilerSlot {
            &mut self.st.slots[i.0 as usize]
        }

        /// Start parsing a list of arguments for a function call.
        ///
        /// This forbids `(def …)` as we need to respect the strict stack
        /// discipline of pushing exactly one result on the stack for each
        /// parsed argument.
        ///
        /// This **must** be paired with a call to `exit_call_args`.
        pub fn enter_call_args(&mut self) -> Scope {
            crate::logtrace!("enter call args scope");
            self.st.lex_scopes.push(LexScope::CallArgs);
            Scope(self.st.lex_scopes.len())
        }

        /// Are we in a local lexical scope?
        ///
        /// This is useful to know if `(def …)` is allowed.
        pub fn is_in_local_scope(&self) -> bool {
            self.parent.is_some() || self.st.lex_scopes.len() > 0
        }

        /// Exit a list of call arguments.
        ///
        /// This **must** be paired with a call to `enter_call_args`.
        pub fn exit_call_args(&mut self, sc: Scope) {
            crate::logtrace!("exit call args scope");
            if self.st.lex_scopes.len() != sc.0 {
                panic!(
                    "unbalanced scopes in call args (expect len {}, got {})",
                    sc.0,
                    self.st.lex_scopes.len()
                );
            }
            match self.st.lex_scopes.pop() {
                Some(LexScope::CallArgs) => (),
                _ => panic!("unbalanced scope in call args"),
            }
        }

        /// Create a local lexical scope, in which local lexical bindings
        /// are allowed (using `(def x …)`).
        ///
        /// This **must** be paired with `pop_local_scope`.
        pub fn push_local_scope(&mut self) -> Scope {
            crate::logtrace!("push local scope");
            self.st.lex_scopes.push(LexScope::Local(vec![]));
            Scope(self.st.lex_scopes.len())
        }

        /// Exit a lexical scope introduced by `push_local_scope`.
        pub fn pop_local_scope(&mut self, sc: Scope) {
            crate::logtrace!("pop local scope");
            if self.st.lex_scopes.len() != sc.0 {
                panic!(
                    "unbalanced scopes (expect len {}, got {})",
                    sc.0,
                    self.st.lex_scopes.len()
                );
            }
            match self.st.lex_scopes.pop() {
                Some(LexScope::Local(sl)) => {
                    for x in sl {
                        self.deallocate_slot_(x)
                    }
                }
                _ => panic!("compiler: unbalanced scopes"),
            }
        }

        /// Ensure the value is in `self.locals`, return its index.
        pub fn allocate_local(&mut self, v: Value) -> Result<LocalIdx> {
            crate::logtrace!("compiler(name={:?}): push local {}", self.name, v);

            // see if `v` is a local already.
            if let Some((i, _)) = self.st.locals.iter().enumerate().find(|(_, v2)| *v2 == &v) {
                return Ok(LocalIdx(i as u8));
            }

            // else push a new local
            let i = self.st.locals.len();
            if i > u8::MAX as usize {
                return Err(Error::new("maximum number of locals exceeded"));
            }
            self.st.locals.push(v);
            Ok(LocalIdx(i as u8))
        }

        /// Emit instruction.
        pub fn emit_instr(&mut self, i: Instr) {
            crate::logtrace!("compiler(name={:?}): emit instr {:?}", self.name, i);
            self.st.instrs.push(i)
        }

        /// Reserve space for a jump instruction that will be emitted later.
        ///
        /// This insert a placeholder instruction that will, later, be filled
        /// with an actual jump. The `JumpPosition` token must be consumed
        /// to fill this placeholder.
        pub fn reserve_jump(&mut self) -> JumpPosition {
            let off = self.st.instrs.len();
            crate::logtrace!(
                "compiler(name={:?}): reserve jump at offset {}",
                self.name,
                off
            );

            self.st.instrs.push(I::Trap); // reserve space; fail if jump is never emitted
            JumpPosition(off)
        }

        /// Set the jump instruction for a previously reserved jump slot.
        pub fn emit_jump(
            &mut self,
            pos: JumpPosition,
            mk_i: impl FnOnce(i16) -> Instr,
        ) -> Result<()> {
            let i = if let I::Trap = self.st.instrs[pos.0] {
                let j_offset = self.st.instrs.len() as isize - pos.0 as isize - 1;
                if j_offset < i16::MIN as isize || j_offset > i16::MAX as isize {
                    return Err(Error::new("jump is too long"));
                }
                mk_i(j_offset as i16)
            } else {
                panic!("jump already edited at pos {}", pos.0);
            };

            crate::logtrace!(
                "compiler(name={:?}): emit jump {:?} at offset {}",
                self.name,
                i,
                pos.0
            );
            self.st.instrs[pos.0] = i;
            Ok(())
        }

        /// Allocate a slot on top of the stack.
        fn allocate_top_slot_(&mut self, st: CompilerSlotState) -> Result<SlotIdx> {
            assert_ne!(st, CompilerSlotState::Unused);
            let i = self.st.slots.len();
            if i > u8::MAX as usize {
                return Err(Error::new("maximum number of slots exceeded"));
            }
            self.n_slots = self.n_slots.max(i as u32 + 1);

            let sl = CompilerSlot {
                var_name: None,
                state: st,
            };
            self.st.slots.push(sl);
            Ok(SlotIdx(i as u8))
        }

        /// Deallocate the `n` top slots.
        ///
        /// Panics if any of these is a variable.
        pub fn deallocate_top_slots(&mut self, n: usize) {
            for _i in 0..n {
                let sl = self
                    .st
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
                .st
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
        pub fn allocate_var(&mut self, name: RStr) -> Result<SlotIdx> {
            let slot = self.allocate_any_slot_(CompilerSlotState::NotActivatedYet)?;
            self.get_slot_(slot).var_name = Some(name);
            if let Some(LexScope::CallArgs) = self.st.lex_scopes.last() {
                return Err(Error::new(
                    "cannot bind variable in the list of arguments of a function call",
                ));
            } else if let Some(LexScope::Local(scope)) = self.st.lex_scopes.last_mut() {
                scope.push(slot); // push into local scope
            }
            Ok(slot)
        }

        /// Activate the given (variable) slot.
        ///
        /// Fails if the slot is not a variable.
        pub fn activate_var(&mut self, v: SlotIdx) {
            let s = self.get_slot_(v);
            assert!(s.var_name.is_some());
            s.state = CompilerSlotState::Activated;
        }

        /// Allocate a slot on the stack, anywhere, to hold a temporary result.
        pub fn allocate_temporary_slot(&mut self) -> Result<(TempSlot, SlotIdx)> {
            let slot = self.allocate_any_slot_(CompilerSlotState::Activated)?;
            Ok((TempSlot(slot), slot))
        }

        /// Allocate a slot on top of the stack.
        ///
        /// This must be used when parsing the arguments of a function call,
        /// to respect the call convention of having a stack of the
        /// form [… f x1 x2 … xn] when calling `f` with arguments `(x1…xn)`.
        pub fn allocate_temporary_on_top(&mut self) -> Result<TempSlot> {
            let slot = self.allocate_top_slot_(CompilerSlotState::Activated)?;
            Ok(TempSlot(slot))
        }

        /// Check if `sl` is the top slot.
        pub fn is_top_of_stack_(&self, sl: SlotIdx) -> bool {
            if sl.0 as usize + 1 == self.st.slots.len() {
                true
            } else {
                self.st.slots[sl.0 as usize..]
                    .iter()
                    .all(|s| s.state == CompilerSlotState::Unused)
            }
        }

        /// Deallocate that slot, it becomes available for further use.
        fn deallocate_slot_(&mut self, sl: SlotIdx) {
            if sl.0 as usize + 1 == self.st.slots.len() {
                // just pop the slot
                self.st.slots.pop().unwrap();
            } else {
                let sl = self.get_slot_(sl);
                sl.var_name = None;
                sl.state = CompilerSlotState::Unused;
            }
        }

        /// Free expression result.
        ///
        /// It must be a temporary. A named variable will only be removed when we exit the
        /// corresponding scope.
        pub fn free(&mut self, tmp: TempSlot) {
            let i = tmp.0;
            let sl = self.get_slot_(i);
            assert!(sl.var_name.is_none()); // must be temporary
            self.deallocate_slot_(i)
        }

        /// Free expression result, if present.
        pub fn free_opt(&mut self, x: Option<TempSlot>) {
            if let Some(t) = x {
                self.free(t)
            }
        }

        /// Find slot for the given variable `v`.
        #[allow(unsafe_code)] // used for making `parent` pointers covariant
        pub fn find_slot_of_var(&mut self, v: &str) -> Result<Option<VarSlot>> {
            for (i, s) in self.st.slots.iter().enumerate().rev() {
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
            for (i, s) in self.st.captured.iter().enumerate() {
                if v == s.get() {
                    return Ok(Some(VarSlot::Captured(UpvalueIdx(i as u8))));
                }
            }
            // look in parent scope to see if we close over `v`
            if let Some(parent) = self.parent {
                // NOTE: safety:
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
                    if self.st.captured.len() > u8::MAX as usize {
                        return Err(Error::new("too many captured variables"));
                    }
                    let upidx = UpvalueIdx(self.st.captured.len() as u8);
                    crate::logtrace!("capture var {} from parent (upidx {})", v, upidx.0);
                    self.st.captured.push(v.into());
                    match parent_var {
                        VarSlot::Local(sl) => parent.emit_instr(I::PushLocalToUpvalue(sl)),
                        VarSlot::Captured(u) => parent.emit_instr(I::PushUpvalueToUpvalue(u)),
                    }
                    return Ok(Some(VarSlot::Captured(upidx)));
                }
            }

            Ok(None) // not in scope
        }
    }

    impl fmt::Debug for CompilerSlot {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            let s = match self.state {
                CompilerSlotState::Activated => "[active]",
                CompilerSlotState::NotActivatedYet => "[_]",
                CompilerSlotState::Unused => "ø",
            };
            write!(out, "(slot{} n:{:?})", s, self.var_name)
        }
    }
}
