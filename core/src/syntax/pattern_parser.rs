pub use crate::algo::Pattern;
use crate::{
    algo::{pattern::PatternBuilder, PatternIdx, PatternView},
    Ctx, Expr, Result,
};

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
            p: &mut PatternBuilder,
            hd: PatternIdx,
        ) -> Result<PatternIdx> {
            let mut cur_p = hd;
            loop {
                let t = self.lexer.cur();
                if t == Tok::RPAREN {
                    break;
                }

                let p2 = self.parse_(ctx, p)?;
                cur_p = p.alloc_node(PatternView::App(cur_p, p2))?;
            }
            Ok(cur_p)
        }

        fn parse_(&mut self, ctx: &mut Ctx, p: &mut PatternBuilder) -> Result<PatternIdx> {
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

                    p.alloc_node(PatternView::Const(e))?
                }
                Tok::QUESTION_MARK_STR(s) => {
                    self.lexer.next();
                    p.alloc_meta(s)?
                }
                Tok::WILDCARD => {
                    self.lexer.next();
                    p.alloc_wildcard()?
                }
                Tok::SYM(s) => {
                    self.lexer.next();
                    if let Some(e) = ctx.find_const(s) {
                        // use constant as-is
                        p.alloc_node(PatternView::Const(e.0.clone()))?
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
                Tok::ERROR(c) => {
                    return Err(Error::new_string(format!(
                        "invalid char {:?} (utf8: {:?}) at {:?}",
                        c,
                        std::str::from_utf8(&[c]),
                        self.lexer.cur_pos()
                    )));
                }
            };
            Ok(p)
        }

        pub fn parse(&mut self, ctx: &mut Ctx) -> Result<Pattern> {
            let mut pb = PatternBuilder::new();
            let root = self.parse_(ctx, &mut pb)?;
            let p = pb.into_pattern(root);
            Ok(p)
        }
    }
}

// TODO: more tests

#[cfg(test)]
mod test {
    use super::*;
    use crate::meta;

    #[test]
    fn test_parse1() -> Result<()> {
        let mut ctx = Ctx::new();
        meta::load_prelude_hol(&mut ctx)?;
        let s = r#"(/\ ?a (~ ?b))"#;
        let p = parse_pattern(&mut ctx, &s)?;
        assert_eq!(p.len(), 7);
        assert_eq!(p.n_vars(), 2);
        Ok(())
    }

    #[test]
    fn test_parse_wildcard() -> Result<()> {
        let mut ctx = Ctx::new();
        meta::load_prelude_hol(&mut ctx)?;
        let s = r#"(/\ _ _)"#;
        let p = parse_pattern(&mut ctx, &s)?;
        assert_eq!(p.len(), 5);
        assert_eq!(p.n_vars(), 2);
        Ok(())
    }
}
