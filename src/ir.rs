use crate::expr::Expr;
use crate::span::Span;

// TODO: move expr here as well
#[derive(Debug)]
#[repr(transparent)]
pub struct Program(pub(crate) Vec<Stmt>);

impl IntoIterator for Program {
    type Item = Stmt;
    type IntoIter = <Vec<Stmt> as IntoIterator>::IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

// TODO: represent statements as S-expressions
#[derive(Debug)]
pub enum Stmt {
    Expr(Expr),
    Print(Print),
}

impl From<Expr> for Stmt {
    #[inline]
    fn from(expr: Expr) -> Self {
        Self::Expr(expr)
    }
}

impl From<Print> for Stmt {
    #[inline]
    fn from(print: Print) -> Self {
        Self::Print(print)
    }
}

#[derive(Debug)]
pub struct Print {
    pub(crate) expr: Expr,
    #[allow(dead_code)]
    pub(crate) span: Span,
}
