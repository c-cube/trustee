//! # Patterns
//!
//! Patterns are useful for representing expression _shapes_, that can be matched
//! against actual expressions to extract some bindings.
//!
//! For example, the pattern `"(f (g ?a) ?b)"` will match `(f (g (g x)) foo)`
//! and bind `?a` to `(g x)`, and `?b? to `foo`.

use crate::{Ctx, Error, Expr, Result};

pub type Ty = Expr;

/// A pattern. It is represented as a flattened term-like structure,
/// a bit like a "flatterm" in ATP terms.
pub struct Pattern {
    pub meta_vars: Vec<String>,
    pub nodes: Vec<PatternView>,
}

/// A single node of the pattern.
///
/// This should match a single node of an expression.
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum PatternView {
    /// First occurrence of a meta-variable
    Var(VarIdx),
    /// Non-linear occurrence of a meta-variable
    EqVar(VarIdx),
    /// Expression to match verbatim
    Const(Expr),
    /// Application
    App(PatternIdx, PatternIdx),
    /// Any term
    Wildcard,
    // TODO? Lam(Ty, PatternIdx),
}

/// A pattern meta-variable.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct VarIdx(u8);

/// An index in the pattern's structure.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub struct PatternIdx(u8);

impl Pattern {
    /// Allocate a new pattern node with given view.
    fn alloc_(&mut self, v: PatternView) -> Result<PatternIdx> {
        let i = self.nodes.len();
        if i > u8::MAX as usize {
            return Err(Error::new("pattern is too long"));
        }
        self.nodes.push(v);
        Ok(PatternIdx(i as u8))
    }

    /// Find or reuse meta-variable with name `s`.
    fn alloc_meta_(&mut self, s: &str) -> Result<PatternIdx> {
        if let Some((i, _)) = self.meta_vars.iter().enumerate().find(|(_, x)| &**x == s) {
            // non linear use of that meta
            let i = VarIdx(i as u8);
            self.alloc_(PatternView::EqVar(i))
        } else {
            let i = self.meta_vars.len();
            if i > u8::MAX as usize {
                return Err(Error::new("too many meta variables in pattern"));
            }
            let i = VarIdx(i as u8);
            self.meta_vars.push(s.to_string());
            self.alloc_(PatternView::Var(i))
        }
    }
}

/// Parse a pattern from the given string.
pub fn parse_pattern(ctx: &mut Ctx, s: &str) -> Result<Pattern> {
    let mut p = parser::Parser::new(s, &[]);
    p.parse(ctx)
}

/// Parse a pattern with interpolating arguments.
///
/// Items in the pattern that are a `?` construct will be replaced by
/// the corresponding expression from `args`. The number of `?` must match
/// the length of `args`.
pub fn parse_pattern_with_args(ctx: &mut Ctx, s: &str, args: &[Expr]) -> Result<Pattern> {
    let mut p = parser::Parser::new(s, args);
    p.parse(ctx)
}

mod parser {
    use super::*;
    use crate::{
        syntax::{Lexer, Tok},
        Error,
    };

    pub struct Parser<'a> {
        lexer: Lexer<'a>,
        /// Interpolation arguments.
        args: &'a [Expr],
    }

    impl<'a> Parser<'a> {
        pub fn new(src: &'a str, args: &'a [Expr]) -> Self {
            let lexer = Lexer::new(src);
            Self { lexer, args }
        }

        fn parse_app_(
            &mut self,
            ctx: &mut Ctx,
            p: &mut Pattern,
            hd: PatternIdx,
        ) -> Result<PatternIdx> {
            let mut cur_p = hd;
            loop {
                let t = self.lexer.cur();
                if t == Tok::RPAREN {
                    break;
                }

                let p2 = self.parse_(ctx, p)?;
                cur_p = p.alloc_(PatternView::App(cur_p, p2))?;
            }
            Ok(cur_p)
        }

        fn parse_(&mut self, ctx: &mut Ctx, p: &mut Pattern) -> Result<PatternIdx> {
            let t = self.lexer.cur();
            let p = match t {
                Tok::LPAREN => {
                    self.lexer.next();
                    let hd = self.parse_(ctx, p)?;
                    let p = self.parse_app_(ctx, p, hd)?;
                    self.lexer.eat(Tok::RPAREN, "after '('-prefixed pattern")?;
                    p
                }
                Tok::QUESTION_MARK => {
                    self.lexer.next();
                    if self.args.is_empty() {
                        return Err(Error::new_string(format!(
                            "no interpolation argument available at {:?}",
                            self.lexer.cur_pos()
                        )));
                    }

                    // consume one interpolation arg
                    let e = self.args[0].clone();
                    self.args = &self.args[1..];

                    p.alloc_(PatternView::Const(e))?
                }
                Tok::QUESTION_MARK_STR(s) => {
                    self.lexer.next();
                    p.alloc_meta_(s)?
                }
                Tok::SYM("_") => {
                    self.lexer.next();
                    p.alloc_(PatternView::Wildcard)?
                }
                Tok::SYM(s) => {
                    self.lexer.next();
                    if let Some(e) = ctx.find_const(s) {
                        // use constant as-is
                        p.alloc_(PatternView::Const(e.0.clone()))?
                    } else {
                        return Err(Error::new_string(format!(
                            "unknown constant `{}` at {:?}",
                            s,
                            self.lexer.cur_pos()
                        )));
                    }
                }
                Tok::RPAREN
                | Tok::COLON
                | Tok::DOT
                | Tok::QUOTED_STR(_)
                | Tok::LET
                | Tok::IN
                | Tok::DOLLAR_SYM(_)
                | Tok::NUM(_)
                | Tok::EOF => {
                    return Err(Error::new_string(format!(
                        "unexpected token {:?} at {:?}",
                        t,
                        self.lexer.cur_pos()
                    )))
                }
            };
            Ok(p)
        }

        pub fn parse(&mut self, ctx: &mut Ctx) -> Result<Pattern> {
            let mut p = Pattern {
                nodes: vec![],
                meta_vars: vec![],
            };
            self.parse_(ctx, &mut p)?;
            Ok(p)
        }
    }
}

// TODO: actual matching, maybe move pattern into `algo`?
// TODO: better tests

#[cfg(test)]
mod test {
    use super::*;
    use crate::meta;

    #[test]
    fn test1() -> Result<()> {
        let mut ctx = Ctx::new();
        meta::load_prelude_hol(&mut ctx)?;
        let s = r#"(/\ ?a (~ ?b))"#;
        let p = parse_pattern(&mut ctx, &s)?;
        assert_eq!(p.nodes.len(), 7);
        Ok(())
    }
}
