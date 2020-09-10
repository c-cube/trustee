//! A basic syntax for parsing and printing terms.
//!
//! This syntax is optional and is not needed at all when using the kernel,
//! but can be very convenient for building terms.
//! We follow https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html
//! for the main parser and terminology.

pub mod expr_parser;
pub mod fixity;
pub mod lexer;
pub mod pattern_parser;
pub mod printer;

pub use expr_parser::{parse_expr, parse_expr_with_args, ParseOutput, Parser};
pub use fixity::Fixity;
pub use lexer::Position;
use lexer::{Lexer, Tok};
pub use pattern_parser::{parse_pattern, parse_pattern_with_args};
pub use printer::print_expr;
