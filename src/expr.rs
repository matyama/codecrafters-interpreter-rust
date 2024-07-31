use std::fmt::Display;

use crate::token::{Token, TokenType};

#[derive(Default, Clone, Debug)]
pub enum Literal {
    Str(String),
    Num(f64),
    Bool(bool),
    #[default]
    None,
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Str(s) => write!(f, "{s}"),
            Self::Num(n) if n.fract() > 0.0 => write!(f, "{n}"),
            Self::Num(n) => write!(f, "{n:.1}"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::None => write!(f, "nil"),
        }
    }
}

impl From<&Token> for Literal {
    fn from(token: &Token) -> Self {
        use crate::token::Literal::*;
        match token.ty {
            TokenType::Nil => Self::None,
            TokenType::False => Self::Bool(false),
            TokenType::True => Self::Bool(true),
            _ => match &token.literal {
                None => Self::None,
                Some(Str(s)) => Self::Str(s.clone()),
                Some(Num(n)) => Self::Num(*n),
            },
        }
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Grouping(pub(crate) Box<Expr>);

#[derive(Debug)]
pub struct Unary {
    pub(crate) op: Token,
    pub(crate) rhs: Box<Expr>,
}

#[derive(Debug)]
pub struct Binary {
    pub(crate) lhs: Box<Expr>,
    pub(crate) op: Token,
    pub(crate) rhs: Box<Expr>,
}

#[derive(Debug)]
pub enum Expr {
    Binary(Binary),
    Grouping(Grouping),
    Literal(Literal),
    Unary(Unary),
}

impl Expr {
    #[inline]
    pub fn group(expr: Expr) -> Self {
        Self::Grouping(Grouping(Box::new(expr)))
    }

    #[inline]
    pub fn unary(op: Token, rhs: Expr) -> Self {
        Self::Unary(Unary {
            op,
            rhs: Box::new(rhs),
        })
    }

    #[inline]
    pub fn binary(lhs: Expr, op: Token, rhs: Expr) -> Self {
        Self::Binary(Binary {
            lhs: Box::new(lhs),
            op,
            rhs: Box::new(rhs),
        })
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Binary(Binary { lhs, op, rhs }) => write!(f, "({} {lhs} {rhs})", op.lexeme),
            Self::Grouping(Grouping(expr)) => write!(f, "(group {expr})"),
            Self::Literal(lit) => write!(f, "{lit}"),
            Self::Unary(Unary { op, rhs }) => write!(f, "({} {rhs})", op.lexeme),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pretty_print() {
        let expr = Expr::binary(
            Expr::unary(
                Token {
                    ty: TokenType::Minus,
                    lexeme: "-".to_string(),
                    literal: None,
                    line: 1,
                },
                Expr::Literal(Literal::Num(123.0)),
            ),
            Token {
                ty: TokenType::Star,
                lexeme: "*".to_string(),
                literal: None,
                line: 1,
            },
            Expr::group(Expr::Literal(Literal::Num(45.67))),
        );

        assert_eq!("(* (- 123.0) (group 45.67))", expr.to_string());
    }
}
