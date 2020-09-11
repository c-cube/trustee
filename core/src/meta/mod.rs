//! Meta-language.
//!
//! The meta-language is a tiny lisp-like stack language that manipulates
//! expressions, goals, theorems, and other values. It is designed to be
//! used both interactively and as an efficient way of storing proofs.

use crate::{kernel_of_trust::Ctx, rstr::RStr, Result};

pub mod builtins;
pub mod lexer;
pub mod parser;
pub mod types;
pub(crate) mod vm;

pub use builtins::{all_builtin_names, all_builtin_names_and_help};
pub use lexer::Position;
pub use types::{InstrBuiltin, Location, Value};
pub use vm::VM;

use types::*;

// TODO: accept `?` tokens, with a list of externally passed args.
//  This enables: `run_with_args("(mp ? some_def)", &[my_thm])`

/// Standard prelude for HOL logic
pub const SRC_PRELUDE_HOL: &'static str = include_str!("prelude.trustee");

/// Run the given code in a fresh VM.
///
/// This has some overhead, if you want to execute a lot of code efficienty
/// (e.g. in a CLI) consider creating a `VM` and re-using it.
pub fn run_code(ctx: &mut Ctx, s: &str, file_name: Option<RStr>) -> Result<Value> {
    let mut vm = vm::VM::new(ctx);
    vm.run(s, file_name)
}

pub fn call_closure(ctx: &mut Ctx, f: &Closure, args: &[Value]) -> Result<Value> {
    let mut vm = vm::VM::new(ctx);
    vm.exec_closure(f.clone(), args)
}

/// Load the HOL prelude into this context.
///
/// This uses a temporary VM. See `run_code` for more details.
pub fn load_prelude_hol(ctx: &mut Ctx) -> Result<()> {
    let loaded = ctx
        .find_meta_value("hol_prelude_loaded")
        .and_then(|v| v.as_bool())
        .unwrap_or(false);
    if !loaded {
        run_code(ctx, SRC_PRELUDE_HOL, Some("prelude.trustee".into()))?;
    }
    Ok(())
}

// Some tests that use the main API.
#[cfg(test)]
mod test {
    use super::*;
    use crate::kernel_of_trust as k;
    use vm::VM;

    macro_rules! eval {
        ($ctx: expr, $e:expr) => {{
            let mut vm = VM::new(&mut $ctx);
            vm.run($e, None)
        }};
        ($e:expr) => {{
            let mut ctx = Ctx::new();
            eval!(ctx, $e)
        }};
    }

    macro_rules! check_eval {
        ($ctx: expr, $e:expr, $val:expr) => {{
            let res_e = eval!($ctx, $e)?;
            assert_eq!(res_e, $val.into());
        }};
        ($e:expr, $val:expr) => {{
            let res_e = eval!($e)?;
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
        check_eval!("(let [x 1] (+ x 2))", 3);
        check_eval!(
            "(list 1 2 3)",
            Value::list(&[Value::Int(1), Value::Int(2), Value::Int(3)])
        );
        check_eval!("(defn f [x] (+ 1 x))", Value::Nil);
        check_eval!("(defn f [x] (+ 1 x)) (f 9)", 10);
        check_eval!("(+ 1 2 3 4 5)", 1 + 2 + 3 + 4 + 5);
        check_eval!("(- 1 2 3 4 5)", 1 - 2 - 3 - 4 - 5);
        check_eval!("{ true 1 }", 1);
        check_eval!("(if true 1 2)", 1);
        check_eval!("(if false 1 2)", 2);
        check_eval!("(let [x (+ 1 1)] (if (== x 1) 10 20))", 20);
        check_eval!("(let [x (+ 1 1)] (if (== x 2) 10 20))", 10);
        check_eval!(
            "(cons 1 (cons :b nil))",
            vec![1.into(), Value::Sym("b".into())]
        );
        check_eval!("[1 :b]", vec![1.into(), Value::Sym("b".into())]);
        check_eval!(":a", Value::Sym("a".into()));
        check_eval!("(!= 1 2)", true);
        check_eval!("(== 1 2)", false);

        Ok(())
    }

    #[test]
    fn test_eval_arith() -> Result<()> {
        check_eval!("(let [a 2 b 4] (+ a (- (* 4 b) (% (/ a 2) 3))))", 17);
        Ok(())
    }

    #[test]
    fn test_fact() -> Result<()> {
        check_eval!(
            "(defn fact [x] (if (<= x 1) 1 (* x (fact (- x 1))))) (list (fact 5) (fact 6))",
            vec![120, 720i64]
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
            "(defn f [x] (+ x 1)) (defn g [x] (* (f x) 2)) (+ 1 (g 10))",
            23
        );
        check_eval!("(let [x 1 y 2] (+ x y))", 3);
        check_eval!(
            "(if (> 1 2) (let [x :a y :b] x) (let [x :b] \"oh?\" x))",
            Value::Sym("b".into())
        );
        check_eval!("(if (< 1 2) (let [x 1 y :b] nil x) (let [x :b] x))", 1);
        check_eval!("(car [1 2])", 1);
        check_eval!("(car (cdr [1 2]))", 2);
        check_eval!("(cdr (cdr [1 2]))", ());
        check_eval!("(cons? [1 2])", true);
        check_eval!("(cons? nil)", false);
        check_eval!("(cons? (cons 1 2))", true);
        Ok(())
    }

    #[test]
    fn test_become() -> Result<()> {
        check_eval!(
            "
            (defn f [x y] (if (== x 0) y (become f (- x 1) (+ 1 y))))
            (f 1000 0)",
            1000
        );
        check_eval!(
            "(defn f [x y z w] (if (== x 0) (+ y (* 10 (+ z (* 10 w))))
                               (become f (- x 1) (+ y 1) (+ z 1) (+ w 1))))
            (f 100 0 0 0)",
            {
                let y = 100;
                let z = 100;
                let w = 100;
                y + 10 * (z + 10 * w)
            }
        );
        check_eval!(
            "(defn f [x y z w] (if (!= x 0)
                (become f (- x 1) (+ y 1) (+ z 1) (+ w 1))
                (+ y (* 10 (+ z (* 10 w))))))
            (f 100 0 0 0)",
            {
                let y = 100;
                let z = 100;
                let w = 100;
                y + 10 * (z + 10 * w)
            }
        );
        check_eval!(
            "(defn f [x y z w] (if (== x 0) (+ y (* 10 (+ z (* 10 w))))
                               (become f (- x 1) (+ y 1) (+ z 1) (+ w 1))))
            (f 10000 0 0 0)",
            {
                let y = 10000;
                let z = 10000;
                let w = 10000;
                y + 10 * (z + 10 * w)
            }
        );
        Ok(())
    }

    // check that `def` in a call argument does not lead to a compiler error
    #[test]
    fn test_call_def() -> Result<()> {
        check_eval!("(defn f [x y] (+ 1 (+ x y)))  (f 1 1)", 3);
        // `def` is forbidden here
        assert!(eval!("(defn f [x y] (+ 1 (+ x y)))  (f (def y 1) y)").is_err());
        check_eval!("(defn f [x y] (+ 1 (+ x y))) { (def x 5) (f x x) }", 11);
        check_eval!("(defn f [x y] (+ 1 (+ x y))) (f (let [x 2] x) 10)", 13);
        Ok(())
    }

    #[test]
    fn test_scope_do() -> Result<()> {
        check_eval!("{ (def x 1) (def y 2) (+ x y) }", 3);
        check_eval!("{ (def x 1) { (def x 2) nil} x}", 1);
        check_eval!("{ (def x 1) { (def x 2) x}}", 2);
        check_eval!("{ (def x 1) { (def y 10) { (def x (+ 1 y)) x }}}", 11);
        check_eval!("(let [x 1] (print x) (def y (+ 10 x)) y)", 11);
        Ok(())
    }

    #[test]
    fn test_scope_brace() -> Result<()> {
        check_eval!("{ (def x 1) (def y 2) (+ x y) }", 3);
        check_eval!("{ (def x 1) { (def x 2) nil} x}", 1);
        check_eval!("{ (def x 1) { (def x 2) x}}", 2);
        check_eval!("{ (def x 1) { (def y 10) { (def x (+ 1 y)) x}}}", 11);
        check_eval!("(let [x 1] (print x) (def y (+ 10 x)) y)", 11);
        Ok(())
    }

    #[test]
    fn test_bool() -> Result<()> {
        check_eval!("true", true);
        check_eval!("false", false);
        check_eval!("(not true)", false);
        check_eval!("(not false)", true);
        check_eval!("(and true false)", false);
        check_eval!("(and false true)", false);
        check_eval!("(and true true)", true);
        check_eval!("(and false false)", false);
        check_eval!("(or false true)", true);
        check_eval!("(or true false)", true);
        check_eval!("(or false false)", false);
        check_eval!("(or true true)", true);

        // TODO: test short circuit property when we have `ref`

        Ok(())
    }

    #[test]
    fn test_parse_expr() -> Result<()> {
        let mut ctx = k::Ctx::new();
        let prelude = r#"
        (decl "a" `bool`)
        (decl "b" `bool`)
        (decl "f" `bool->bool->bool`)
        "#;
        run_code(&mut ctx, prelude, None)?;
        let v1 = run_code(&mut ctx, "(parse_expr \"(f ? ?)\" `a` `b`)", None)?;
        let v2 = run_code(&mut ctx, "`f a b`", None)?;
        assert_eq!(v1, v2);
        Ok(())
    }

    #[test]
    fn test_closures() -> Result<()> {
        check_eval!("(let [f (fn [x] (+ 1 x))] (f 41))", 42);
        check_eval!(
            "{ (def x 1)
               (def f (fn [y] (+ x y)))
               (f 41) }",
            42
        );
        check_eval!(
            "(defn fold [f acc l]
              (print l)
              (if (nil? l) acc
               (become fold f (f acc (car l)) (cdr l))))
             { (def off 1)
               (fold (fn [acc x] (+ acc x off)) 0 [1 2 3 4]) }",
            {
                let off = 1;
                let acc = 0;
                let acc = acc + 1 + off;
                let acc = acc + 2 + off;
                let acc = acc + 3 + off;
                let acc = acc + 4 + off;
                acc
            }
        );
        check_eval!(
            "(defn map [f l] (if (nil? l) nil (cons (f (car l)) (map f (cdr l)))))
            (let [y 1] (map (fn [x] (+ y x)) [1 2 3 4]))",
            Value::list(&[2i64.into(), 3.into(), 4.into(), 5.into()])
        );
        Ok(())
    }

    #[test]
    fn test_load_hol_prelude() -> Result<()> {
        let mut ctx = k::Ctx::new();
        load_prelude_hol(&mut ctx)?;
        load_prelude_hol(&mut ctx)?; // can we load it twice?
        Ok(())
    }

    #[test]
    fn test_arity_err() -> Result<()> {
        let mut ctx = k::Ctx::new();
        run_code(&mut ctx, "(defn f [x y] (+ x y))", None)?;
        let v = run_code(&mut ctx, "(f 1 2)", None)?;
        assert_eq!(v, 3.into());

        {
            let v2 = run_code(&mut ctx, "(f 1)", None);
            assert!(v2.is_err());
            let v2_err = format!("{}", v2.unwrap_err());
            assert!(v2_err.contains("arity"));
        }

        {
            let v3 = run_code(&mut ctx, "(f 1 2 3)", None);
            assert!(v3.is_err());
            let v3_err = format!("{}", v3.unwrap_err());
            assert!(v3_err.contains("arity"));
        }

        Ok(())
    }

    #[test]
    fn test_set() -> Result<()> {
        check_eval!("(set x 1) (set y 2) (+ x y)", 3);
        check_eval!("{ (set x 1) } (+ x 10)", 11);
        Ok(())
    }

    const PRELUDE: &'static str = r#"
            (decl "tau" `type`)
            (decl "a0" `tau`)
            (decl "b0" `tau`)
            (decl "c0" `tau`)
            (decl "f1" `tau -> tau`)
            (decl "g1" `tau -> tau`)
            (decl "f2" `tau -> tau -> tau`)
            (decl "p0" `bool`)
            (decl "q0" `bool`)
            (decl "r0" `bool`)
            (decl "p1" `tau -> bool`)
            (decl "q1" `tau -> bool`)
            (decl "p2" `tau -> tau -> bool`)
            "#;

    #[test]
    fn test_mp() -> Result<()> {
        let mut ctx = k::Ctx::new();
        load_prelude_hol(&mut ctx)?;
        run_code(&mut ctx, PRELUDE, None)?;
        let v = run_code(&mut ctx, "(MP (assume `p0 ==> q0`) (assume `p0`))", None)?;
        assert_eq!(v.as_thm().expect("thm").concl().clone().to_string(), "q0");
        Ok(())
    }

    #[test]
    fn test_docstr() -> Result<()> {
        check_eval!("(defn f [x] (doc \"hello f\") x) (f 1)", 1);
        assert!(eval!("(defn f [x] (doc \"hello f\"))").is_err());
        Ok(())
    }

    #[test]
    fn test_capture_stdout() -> Result<()> {
        let mut ctx = Ctx::new();
        let mut vm = VM::new(&mut ctx);
        let mut r = None;
        let mut out = |s: &str| r = Some(s.trim().to_string());
        vm.set_stdout(&mut out);
        vm.run("(print 42)", None)?;
        assert_eq!(r.as_deref(), Some("42"));
        Ok(())
    }

    #[test]
    fn test_rw() -> Result<()> {
        let mut ctx = k::Ctx::new();
        load_prelude_hol(&mut ctx)?;
        run_code(&mut ctx, PRELUDE, None)?;
        run_code(
            &mut ctx,
            r#"(defthm "F1" (axiom `f2 (x:tau) (g1 (y:tau)) = f1 y`))
                (defthm "TH" (axiom `p1 (f2 a0 (g1 c0))`))
                "#,
            None,
        )?;
        let v = run_code(&mut ctx, "(rw TH F1)", None)?;
        assert_eq!(
            v.as_thm().expect("thm").concl().clone(),
            crate::syntax::parse_expr(&mut ctx, "p1 (f1 c0)")?
        );
        Ok(())
    }

    #[allow(non_snake_case)]
    #[test]
    fn test_match() -> Result<()> {
        let mut ctx = k::Ctx::new();
        load_prelude_hol(&mut ctx)?;
        let eT = eval!(ctx, "T")?;
        let eF = eval!(ctx, "F")?;
        check_eval!(ctx, r#"(match `T /\ F` (else 1))"#, 1);
        check_eval!(ctx, r#"(match `T /\ F` ("_" 2) (else 1))"#, 2);
        check_eval!(
            ctx,
            r#"(match `T /\ F` ("/\ ?a ?b" [a b]) (else 1))"#,
            vec![eT.clone(), eF.clone()]
        );
        check_eval!(
            ctx,
            r#"(match `T /\ F` ("/\ ?a ?b" (def h [b a]) h) (else 1))"#,
            vec![eF.clone(), eT.clone()]
        );
        Ok(())
    }
}
