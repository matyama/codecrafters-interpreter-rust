mod error;
mod interpreter;
mod ir;
mod lexer;
mod parser;
mod resolver;
mod span;
mod token;

pub use interpreter::{evaluate, interpret};
pub use ir::{Ast, Expr};
pub use lexer::Lexer;
pub use resolver::resolve;
pub use token::EOF;
