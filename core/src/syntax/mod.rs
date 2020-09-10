//! A basic syntax for parsing and printing terms.
//!
//! This syntax is optional and is not needed at all when using the kernel.
//! We follow https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
//! for the main parser and terminology.

pub mod fixity;
pub mod lexer;
pub mod parser;
pub mod pattern;
pub mod printer;

pub use fixity::Fixity;
pub use lexer::Position;
use lexer::{Lexer, Tok};
pub use parser::{parse_expr, parse_expr_with_args, ParseOutput, Parser};
pub use pattern::{parse_pattern, parse_pattern_with_args, Pattern};
pub use printer::print_expr;
