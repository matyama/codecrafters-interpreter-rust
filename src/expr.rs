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

// TODO: try Box -> <'a>
#[derive(Debug)]
pub enum Expr {
    Binary {
        lhs: Box<Expr>,
        op: Token,
        rhs: Box<Expr>,
    },

    Grouping(Box<Expr>),

    Literal(Literal),

    Unary {
        op: Token,
        rhs: Box<Expr>,
    },
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Binary { lhs, op, rhs } => write!(f, "({} {lhs} {rhs})", op.lexeme),
            Self::Grouping(expr) => write!(f, "(group {expr})"),
            Self::Literal(lit) => write!(f, "{lit}"),
            Self::Unary { op, rhs } => write!(f, "({} {rhs})", op.lexeme),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pretty_print() {
        let expr = Expr::Binary {
            lhs: Box::new(Expr::Unary {
                op: Token {
                    ty: TokenType::Minus,
                    lexeme: "-".to_string(),
                    literal: None,
                    line: 1,
                },
                rhs: Box::new(Expr::Literal(Literal::Num(123.0))),
            }),
            op: Token {
                ty: TokenType::Star,
                lexeme: "*".to_string(),
                literal: None,
                line: 1,
            },
            rhs: Box::new(Expr::Grouping(Box::new(Expr::Literal(Literal::Num(45.67))))),
        };

        assert_eq!("(* (- 123.0) (group 45.67))", expr.to_string());
    }
}
