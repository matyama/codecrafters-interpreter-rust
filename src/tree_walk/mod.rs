mod interpreter;
mod ir;
mod parser;
mod resolver;

pub use interpreter::{evaluate, interpret};
pub use ir::{Ast, Expr};
pub use resolver::resolve;
