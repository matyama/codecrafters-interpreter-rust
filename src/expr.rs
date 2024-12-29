use std::fmt::Display;

use crate::span::Span;
use crate::token::{LexToken, Token};

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

impl From<&LexToken<'_>> for Literal {
    fn from(token: &LexToken) -> Self {
        use crate::token::{Keyword::*, Literal::*};

        match &token.token {
            Token::Keyword(True) => Self::Bool(true),
            Token::Keyword(False) => Self::Bool(false),
            Token::Keyword(Nil) => Self::None,
            Token::Literal(Str(s)) => Self::Str(s.to_string()),
            Token::Literal(Num(n)) => Self::Num(*n),
            _ => Self::None,
        }
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Grouping(pub(crate) Box<Expr>);

#[derive(Debug)]
pub struct Operator {
    // TODO: try to borrow the lexeme (or use LexToken instead of Operator)
    pub(crate) lexeme: String,
    pub(crate) token: OperatorToken,
    pub(crate) span: Span,
}

impl From<&LexToken<'_>> for Option<Operator> {
    fn from(token: &LexToken<'_>) -> Self {
        Some(Operator {
            lexeme: token.lexeme.to_string(),
            token: Into::<Option<OperatorToken>>::into(&token.token)?,
            span: token.span.clone(),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperatorToken {
    // arithmetic operators
    Plus,
    Minus,
    Star,
    Slash,

    // unary operators
    Bang,

    // relational operators
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,
}

impl From<&Token<'_>> for Option<OperatorToken> {
    fn from(token: &Token<'_>) -> Self {
        match token {
            Token::Plus => Some(OperatorToken::Plus),
            Token::Minus => Some(OperatorToken::Minus),
            Token::Star => Some(OperatorToken::Star),
            Token::Slash => Some(OperatorToken::Slash),
            Token::Bang => Some(OperatorToken::Bang),
            Token::BangEqual => Some(OperatorToken::BangEqual),
            Token::Equal => Some(OperatorToken::Equal),
            Token::EqualEqual => Some(OperatorToken::EqualEqual),
            Token::Greater => Some(OperatorToken::Greater),
            Token::GreaterEqual => Some(OperatorToken::GreaterEqual),
            Token::Less => Some(OperatorToken::Less),
            Token::LessEqual => Some(OperatorToken::LessEqual),
            _ => None,
        }
    }
}

// TODO: single generic n-ary operator with `args: Vec<Expr>`
#[derive(Debug)]
pub struct Unary {
    pub(crate) op: Operator,
    pub(crate) rhs: Box<Expr>,
}

#[derive(Debug)]
pub struct Binary {
    pub(crate) lhs: Box<Expr>,
    pub(crate) op: Operator,
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
    pub fn unary(op: Operator, rhs: Expr) -> Self {
        Self::Unary(Unary {
            op,
            rhs: Box::new(rhs),
        })
    }

    #[inline]
    pub fn binary(lhs: Expr, op: Operator, rhs: Expr) -> Self {
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
                Operator {
                    lexeme: String::from("-"),
                    token: OperatorToken::Minus,
                    span: Span {
                        offset: 0,
                        length: 1,
                        lineno: 1,
                        lineof: 0,
                    },
                },
                Expr::Literal(Literal::Num(123.0)),
            ),
            Operator {
                lexeme: String::from("*"),
                token: OperatorToken::Star,
                span: Span {
                    offset: 0,
                    length: 1,
                    lineno: 1,
                    lineof: 7,
                },
            },
            Expr::group(Expr::Literal(Literal::Num(45.67))),
        );

        assert_eq!("(* (- 123.0) (group 45.67))", expr.to_string());
    }
}
