//! Builtins that come with the meta-language.

use super::types::*;

use crate::{algo, algo::conv, kernel_of_trust as k, rstr::RStr, syntax, Error, Result};

/// Name and help of all the builtin constructs.
pub fn all_builtin_names_and_help() -> impl Iterator<Item = (&'static str, &'static str)> {
    let i1 = basic_primitives::BUILTINS.iter().map(|b| (b.name, b.help));
    let i2 = logic_builtins::BUILTINS.iter().map(|b| (b.name, b.help));
    i1.chain(i2)
}

/// Names of all the builtin constructs.
pub fn all_builtin_names() -> impl Iterator<Item = &'static str> {
    all_builtin_names_and_help().map(|t| t.0)
}

#[macro_export]
/// Define a builtin instruction using a name, help string, and a statically known function.
///
/// Usage: `defbuiltin!("foo", "foo help", |ctx, _, args| { … })`.
macro_rules! defbuiltin {
    ($name: literal, $help:literal, $run:expr) => {
        crate::meta::InstrBuiltin {
            name: $name,
            help: $help,
            run: $run,
        }
    };
}

#[macro_export]
/// `check_arity!("context", args, 2)` or `check_arity!("context", args, >= 2)` performs a basic
/// arity check. To be used in `defbuiltin`.
macro_rules! check_arity {
    ($what: expr, $args: expr, >= $n: literal) => {
        if $args.len() < $n {
            return Err(crate::Error::new(concat!(
                "arity mismatch in ",
                $what,
                ": expected at least ",
                stringify!($n),
                " args"
            )));
        }
    };

    ($what: expr, $args: expr, $n: literal) => {
        if $args.len() != $n {
            return Err(crate::Error::new(concat!(
                "arity mismatch in ",
                $what,
                ": expected ",
                stringify!($n),
                " args"
            )));
        }
    };
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

/* TODO: with a stack-based VM, have `callBuiltin(offset, n_args)` directly
 * index into that array, and remove `Value::Builtin`
const BUILTINS: &'static [&'static InstrBuiltin] = {
    let a1 = basic_primitives::BUILTINS;
    let a2 = logic_builtins::BUILTINS;
    let v = vec![];
    v.extend_from_slice(&a1);
    v.extend_from_slice(&a2);
    &v[..]
};
*/

pub(super) mod basic_primitives {
    use super::*;

    /// Builtin functions.
    pub(crate) const BUILTINS: &'static [&'static InstrBuiltin] = &[
        &defbuiltin!("print", "print value(s).", |mut ctx,
                                                  args: &[Value]|
         -> Result<Value> {
            for x in args {
                ctx.out.print(&format!("{}", x))
            }
            Ok(Value::Nil)
        }),
        &defbuiltin!(
            "help",
            "print help for an identifier.",
            |mut ctx, args: &[Value]| -> Result<_> {
                check_arity!("help", args, 1);
                let s = get_arg_str!(args, 0).get();

                if let Some(b) = basic_primitives::BUILTINS.iter().find(|b| b.name == s) {
                    ctx.out.print(b.help);
                } else if let Some(b) = logic_builtins::BUILTINS.iter().find(|b| b.name == s) {
                    ctx.out.print(b.help);
                };
                Ok(Value::Nil)
            }
        ),
        &defbuiltin!(
            "eval",
            "Takes a string, and returns the value yielded by evaluating it.",
            |ctx, args: &[Value]| -> Result<_> {
                check_arity!("eval", args, 1);
                let s = get_arg_str!(args, 0);
                crate::logdebug!("evaluate `{}`", s);
                let mut vm = crate::meta::vm::VM::new(ctx.ctx);
                // evaluate `s` in a new VM. Directly use `s` for the file name.
                let v = vm
                    .run(s, Some(s.clone()))
                    .map_err(|e| e.with_source(Error::new("<eval>")))?;
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
            "show",
            "return a string representing the argument value",
            |_ctx, args: &[Value]| -> Result<_> {
                check_arity!("show", args, 1);
                let v = &args[0];
                let s = format!("{}", v);
                Ok(Value::Str(RStr::from_string(s)))
            }
        ),
        &defbuiltin!(
            "show_chunk",
            "shows the bytecode of a closure",
            |mut ctx, args: &[Value]| -> Result<_> {
                check_arity!("show_chunk", args, 1);
                let s = get_arg_str!(args, 0);
                if let Some(c) = ctx.ctx.find_meta_value(s).and_then(|v| v.as_closure()) {
                    ctx.out.print(&format!("{:?}", c))
                }
                Ok(().into())
            }
        ),
    ];
}

/// Primitives of the meta-language related to theorem proving.
pub(super) mod logic_builtins {
    use super::*;

    /// Builtin functions for manipulating expressions and theorems.
    pub(crate) const BUILTINS: &'static [&'static InstrBuiltin] = &[
        &defbuiltin!(
            "set_glob",
            "`(set_glob \"x\" v)` binds `v` in the toplevel table.\n\
            Later, `(get \"x\")` or simply `x` will retrieve it.",
            |ctx, args: &[Value]| {
                check_arity!("set_glob", args, 2);
                let s = get_arg_str!(args, 0);
                let v = args[1].clone();
                ctx.ctx.set_meta_value(s.clone(), v);
                Ok(Value::Nil)
            }
        ),
        &defbuiltin!(
            "get_glob",
            "`(get_glob \"x\")` retrieves the toplevel value \"x\".",
            |ctx, args: &[Value]| {
                check_arity!("get_glob", args, 1);
                let s = get_arg_str!(args, 0);
                match ctx.ctx.find_meta_value(s) {
                    Some(v) => Ok(v.clone()),
                    None => Err(Error::new("value not found")),
                }
            }
        ),
        &defbuiltin!(
            "defconst",
            "Defines a logic constant. Takes `(nc, nth, expr_rhs)` and returns\
            the tuple `{c . th}` where `c` is the constant, with name `nc`,\n\
            and `th` is the defining theorem with name `nth`",
            |ctx, args: &[Value]| {
                check_arity!("defconst", args, 3);
                let nc: k::Symbol = get_arg_str!(args, 0).into();
                let nthm = get_arg_str!(args, 1);
                let rhs = get_arg_expr!(args, 2);
                let def = algo::thm_new_poly_definition(ctx.ctx, &nc.name(), rhs.clone())?;
                ctx.ctx.define_lemma(nthm.clone(), def.thm.clone());
                Ok(Value::cons(Value::Expr(def.c), Value::Thm(def.thm)))
            }
        ),
        &defbuiltin!(
            "defthm",
            "Defines a theorem. Takes `(name, th)`.",
            |ctx, args| {
                check_arity!("defthm", args, 2);
                let name = get_arg_str!(args, 0);
                let th = get_arg_thm!(args, 1);
                ctx.ctx.define_lemma(name.clone(), th.clone());
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
                    .ctx
                    .find_const(&name)
                    .ok_or_else(|| Error::new("unknown constant"))?
                    .0
                    .clone();
                Ok(Value::Expr(e))
            }
        ),
        &defbuiltin!("findthm", "looks up a theorem by name", |ctx, args| {
            check_arity!("findthm", args, 1);
            let s = get_arg_str!(args, 0);
            match ctx.ctx.find_lemma(s) {
                Some(t) => Ok(Value::Thm(t.clone())),
                None => Err(Error::new("cannot find theorem")),
            }
        }),
        &defbuiltin!(
            "axiom",
            "Takes a boolean expression and makes it into an axiom.\n\
            Might fail if `pledge_no_new_axiom` was called earlier.",
            |ctx, args| {
                check_arity!("axiom", args, 1);
                let e = get_arg_expr!(args, 0);
                let th = ctx.ctx.thm_axiom(vec![], e.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "assume",
            "Takes a boolean expression and returns the theorem `e|-e`.",
            |ctx, args| {
                check_arity!("assume", args, 1);
                let e = get_arg_expr!(args, 0);
                let th = ctx.ctx.thm_assume(e.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "refl",
            "Takes an expression `e` and returns the theorem `|-e=e`.",
            |ctx, args| {
                check_arity!("refl", args, 1);
                let e = get_arg_expr!(args, 0);
                let th = ctx.ctx.thm_refl(e.clone());
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "sym",
            "Takes a theorem `A|- t=u` and returns the theorem `A|- u=t`.",
            |ctx, args| {
                check_arity!("sym", args, 1);
                let th1 = get_arg_thm!(args, 0);
                let th = algo::thm_sym(ctx.ctx, th1.clone())?;
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
                let th = ctx.ctx.thm_trans(th1, th2)?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "congr",
            "Congruence. Takes `A|- f=g` and `B|- t=u`, returns `A,B|- f t=g u`.\n\
            `(congr C1…Cn)` is like `(…((congr C1 C2) C3)…Cn)`.",
            |ctx, args| {
                check_arity!("congr", args, >= 2);
                let mut th_res = get_arg_thm!(args, 0).clone();
                for i in 1..args.len() {
                    let th2 = get_arg_thm!(args, i).clone();
                    th_res = ctx.ctx.thm_congr(th_res, th2)?;
                }
                Ok(Value::Thm(th_res))
            }
        ),
        &defbuiltin!(
            "decl",
            "Declare a symbol. Takes a symbol `n`, and a type.",
            |ctx, args| {
                check_arity!("decl", args, 2);
                let name = get_arg_str!(args, 0);
                let ty = get_arg_expr!(args, 1);
                let e = ctx
                    .ctx
                    .mk_new_const(k::Symbol::from_str(name), ty.clone())?;
                Ok(Value::Expr(e))
            }
        ),
        &defbuiltin!(
            "set_infix",
            "Make a symbol infix.\n\
            \n\
            Takes a symbol `n`, and a pair of integers `i`,`j` as left and right\
            precedences.",
            |ctx, args| {
                check_arity!("set_infix", args, 3);
                let c = get_arg_str!(args, 0);
                let i = get_arg_int!(args, 1);
                let j = get_arg_int!(args, 2);
                let f = syntax::Fixity::Infix((*i as u16, *j as u16));
                ctx.ctx.set_fixity(&*c, f)?;
                Ok(Value::Nil)
            }
        ),
        &defbuiltin!("set_prefix", "Make a symbol prefix.", |ctx, args| {
            check_arity!("set_prefix", args, 2);
            let c = get_arg_str!(args, 0);
            let i = get_arg_int!(args, 1);
            let f = syntax::Fixity::Prefix((*i as u16, *i as u16));
            ctx.ctx.set_fixity(&*c, f)?;
            Ok(Value::Nil)
        }),
        &defbuiltin!("set_binder", "Make a symbol a binder.", |ctx, args| {
            check_arity!("set_binder", args, 2);
            let c = get_arg_str!(args, 0);
            let i = get_arg_int!(args, 1);
            let f = syntax::Fixity::Binder((0, *i as u16));
            ctx.ctx.set_fixity(&*c, f)?;
            Ok(Value::Nil)
        }),
        &defbuiltin!(
            "abs",
            "Takes `x`, `ty`, and `A|- t=u`, and returns\
            the theorem `A|- \\x:ty. t = \\x:ty. u`.",
            |ctx, args| {
                check_arity!("abs", args, 3);
                let v = get_arg_str!(args, 0);
                let ty = get_arg_expr!(args, 1);
                let th = get_arg_thm!(args, 2);
                let v = k::Var::from_str(&*v, ty.clone());
                let th = ctx.ctx.thm_abs(&v, th.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "absv",
            "Takes expr `x`, and `A|- t=u`, and returns\n\
            the theorem `A|- \\x:ty. t = \\x:ty. u`.",
            |ctx, args| {
                check_arity!("absv", args, 2);
                let e = get_arg_expr!(args, 0);
                let v = e
                    .as_var()
                    .ok_or_else(|| Error::new("absv: expression must be a variable"))?;
                let th = get_arg_thm!(args, 1);
                let th = ctx.ctx.thm_abs(v, th.clone())?;
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
            "e_abs",
            "Takes `x` and `body` and returns `\\x. body`",
            |ctx, args| {
                check_arity!("e_abs", args, 2);
                let x = match get_arg_expr!(args, 0).as_var() {
                    Some(v) => v,
                    None => return Err(Error::new("e.abs expects a variable")),
                };
                let b = get_arg_expr!(args, 1);
                Ok(ctx.ctx.mk_lambda(x.clone(), b.clone())?.into())
            }
        ),
        &defbuiltin!(
            "e_app",
            "Takes `f` and `t` and returns `f t`",
            |ctx, args| {
                check_arity!("e_app", args, 2);
                let a = get_arg_expr!(args, 0);
                let b = get_arg_expr!(args, 1);
                Ok(ctx.ctx.mk_app(a.clone(), b.clone())?.into())
            }
        ),
        &defbuiltin!("e_app_lhs", "Takes `f t` and returns `f`", |_ctx, args| {
            check_arity!("e_app_lhs", args, 1);
            let e = get_arg_expr!(args, 0);
            if let k::EApp(f, _) = e.view() {
                Ok(Value::Expr(f.clone()))
            } else {
                Err(Error::new("app_lhs: expression is not an application"))
            }
        }),
        &defbuiltin!("e_app_rhs", "Takes `f t` and returns `t`", |_ctx, args| {
            check_arity!("e_app_lhs", args, 1);
            let e = get_arg_expr!(args, 0);
            if let k::EApp(_, t) = e.view() {
                Ok(Value::Expr(t.clone()))
            } else {
                Err(Error::new("app_rhs: expression is not an application"))
            }
        }),
        &defbuiltin!(
            "hol_prelude",
            "Returns the builtin HOL prelude, as a string.",
            |_ctx, args| {
                check_arity!("hol_prelude", args, 0);
                Ok(Value::Str(crate::meta::SRC_PRELUDE_HOL.into()))
            }
        ),
        &defbuiltin!(
            "pledge_no_new_axiom",
            "Prevent any further calls to `axiom` to succeed.",
            |ctx, args| {
                check_arity!("pledge_no_new_axiom", args, 0);
                ctx.ctx.pledge_no_new_axiom();
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
                let th = ctx.ctx.thm_congr_ty(th1.clone(), &ty)?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "cut",
            "Cut rule.\n\
            `cut (F1 |- b) (F2, b |- c)` is `F1, F2 |- c`.\n\
            `cut C_1…C_n d` is `cut C1 (cut C2 … (cut C_n d) …)).`",
            |ctx, args| {
                check_arity!("cut", args, >= 2);
                let mut th_res = get_arg_thm!(args, args.len() - 1).clone();
                for i in 0..args.len() - 1 {
                    let th1 = get_arg_thm!(args, i).clone();
                    th_res = ctx.ctx.thm_cut(th1, th_res)?;
                }
                Ok(Value::Thm(th_res))
            }
        ),
        &defbuiltin!(
            "bool_eq",
            "Boolean equality. Takes `A|- t` and `B|- t=u`, returns `A,B|- u`.",
            |ctx, args| {
                check_arity!("bool_eq", args, 2);
                let th1 = get_arg_thm!(args, 0);
                let th2 = get_arg_thm!(args, 1);
                let th = ctx.ctx.thm_bool_eq(th1.clone(), th2.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "bool_eq_intro",
            "Boolean equality introduction.\n\
            Takes `A, t|- u` and `B,u |- t`, returns `A,B|- t=u`.",
            |ctx, args| {
                check_arity!("bool_eq_intro", args, 2);
                let th1 = get_arg_thm!(args, 0);
                let th2 = get_arg_thm!(args, 1);
                let th = ctx.ctx.thm_bool_eq_intro(th1.clone(), th2.clone())?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "beta_conv",
            "Beta-conversion rule.\n\
            Takes expr `(\\x. t) u`, returns `|- (\\x. t) u = t[u/x]`.",
            |ctx, args| {
                check_arity!("beta_conv", args, 1);
                let e = get_arg_expr!(args, 0);
                let th = ctx.ctx.thm_beta_conv(e)?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "subst",
            "Instantiate a theorem with a substitution.\n\
            \n\
            Shape: `(subst th \"x1\" e1 \"x2\" e2)`.\n",
            |ctx, args| {
                check_arity!("instantiate", args, >= 1);
                let th = get_arg_thm!(args, 0);

                let mut subst = vec![];
                let mut args = &args[1..];
                if args.len() % 2 != 0 {
                    return Err(Error::new(
                        "subst requires an even number of arguments after the theorem",
                    ));
                }

                while args.len() > 0 {
                    let x = get_arg_str!(args, 0);
                    let e = get_arg_expr!(args, 1);
                    subst.push((k::Var::from_rstr(x, e.ty().clone()), e.clone()));
                    args = &args[2..];
                }

                let th = ctx.ctx.thm_instantiate(th.clone(), &subst)?;
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "rw",
            "Rewrite with a combination of `beta_conv` and theorem names.\n\
            \n\
            Shape: `(rw th_to_rewrite :beta th1 th2)`.\n\
            Each rule is either an equational theorem, or `:beta`.",
            |ctx, args| {
                check_arity!("rw", args, >= 1);
                let th = get_arg_thm!(args, 0);

                let mut beta = false;
                let mut rw_rules = algo::rw_rule::RewriteRuleSet::new();
                for x in &args[1..] {
                    match x {
                        Value::Sym(s) if s.name() == "beta" => {
                            beta = true;
                        }
                        Value::Thm(th) => {
                            let rule = algo::RewriteRule::new(&th)?;
                            rw_rules.add_rule(rule)
                        }
                        _ => {
                            return Err(Error::new(
                                "expected `:beta` or an equational theorem in `rw`",
                            ))
                        }
                    }
                }

                // build a converter from beta/rules, then apply it bottom-up
                let th = if beta && !rw_rules.is_empty() {
                    let mut cs = conv::SeqConverter::new();
                    cs.add(conv::BasicConverter::beta_repeat());
                    cs.add(conv::BasicConverter::wrap(rw_rules));
                    let rw = algo::rw::BottomUpRwConv(&cs);
                    conv::thm_conv_concl(ctx.ctx, th.clone(), &rw)?
                } else if beta {
                    let rw = algo::rw::BottomUpRwConv(&conv::BetaReduceRepeat);
                    conv::thm_conv_concl(ctx.ctx, th.clone(), &rw)?
                } else if !rw_rules.is_empty() {
                    let rw = algo::rw::BottomUpRwConv(&rw_rules);
                    conv::thm_conv_concl(ctx.ctx, th.clone(), &rw)?
                } else {
                    return Ok(Value::Thm(th.clone())); // no rw
                };
                Ok(Value::Thm(th))
            }
        ),
        &defbuiltin!(
            "parse_expr",
            r#"`(parse_expr "? /\ ?" e1 e2)` parses the expression
            given as the first argument, interpolating each '?' with
            the corresponding of the following arguments."#,
            |ctx, args| {
                check_arity!("parse_with", args, >= 1);
                let e = get_arg_str!(args, 0);
                let n_args = e.as_bytes().iter().filter(|&&x| x == b'?').count();

                // check arity
                if args[1..].len() != n_args {
                    return Err(Error::new_string(format!(
                        "interpolating expression requires {} arguments,\
                            but here it receives {}",
                        n_args,
                        args[1..].len()
                    )));
                }

                // convert arguments to expressions
                let mut e_args = vec![];
                for i in 0..n_args {
                    e_args.push(get_arg_expr!(args, i + 1).clone());
                }

                let e = syntax::parse_expr_with_args(ctx.ctx, e, &e_args[..])?;
                Ok(e.into())
            }
        ),
        &defbuiltin!(
            "def_ty",
            r#"define a new type.
            `(def_ty "name" "from" "to" `|- Phi (witness:tau)`)` creates a new type
            from base type `tau`, named "name", with conversion functions `from`
            and `to`.

            The theorem is used to provide both the base type `tau`,
            an existence witness `witness : tau`, and the refinement predicate
            `Phi` that defines the subset of `tau`.

            Returns `[newty, abs, repr, abs_thm, repr_thm]`"#,
            |ctx, args| {
                check_arity!("def_ty", args, 4);
                let name = get_arg_str!(args, 0);
                let n1 = get_arg_str!(args, 1);
                let n2 = get_arg_str!(args, 2);
                let th = get_arg_thm!(args, 3);

                let ty = ctx.ctx.thm_new_basic_type_definition(
                    name.into(),
                    n1.into(),
                    n2.into(),
                    th.clone(),
                )?;

                let res: Vec<Value> = vec![
                    ty.tau.into(),
                    ty.c_abs.into(),
                    ty.c_repr.into(),
                    ty.abs_thm.into(),
                    ty.repr_thm.into(),
                ];

                Ok(res.into())
            }
        ),
        &defbuiltin!(
            "ac_rw",
            r#"rewrite module AC.

            Takes axioms `|- assoc(f)` and `|- comm(f)`, and a theorem `th`,
            and rewrites `th`'s conclusion using the axioms."#,
            |ctx, args| {
                check_arity!("ac_rw", args, 3);
                let assoc = get_arg_thm!(args, 0).clone();
                let comm = get_arg_thm!(args, 1).clone();
                let th = get_arg_thm!(args, 2).clone();

                let c = algo::ac_rw::ACConv::new(ctx.ctx, assoc, comm)?;
                let c = algo::rw::BottomUpRwConv::new(&c); // rewrite deeply

                let r = conv::thm_conv_concl(ctx.ctx, th, &c)?;
                Ok(r.into())
            }
        ),
    ];
}
