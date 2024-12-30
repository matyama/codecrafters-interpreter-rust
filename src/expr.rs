use std::fmt::Display;

use crate::span::Span;
use crate::token::{LexToken, Token};

/// Atomic expression (literal values)
#[derive(Default, Clone, Debug)]
pub enum Literal {
    #[default]
    Nil,
    Bool(bool),
    Num(f64),
    Str(String),
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nil => write!(f, "nil"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Num(n) if n.fract() > 0.0 => write!(f, "{n}"),
            Self::Num(n) => write!(f, "{n:.1}"),
            Self::Str(s) => write!(f, "{s}"),
        }
    }
}

impl From<&Token<'_>> for Literal {
    fn from(token: &Token<'_>) -> Self {
        use crate::token::{Keyword::*, Literal::*};
        match token {
            Token::Keyword(True) => Self::Bool(true),
            Token::Keyword(False) => Self::Bool(false),
            Token::Keyword(Nil) => Self::Nil,
            Token::Literal(Str(s)) => Self::Str(s.to_string()),
            Token::Literal(Num(n)) => Self::Num(*n),
            _ => Self::Nil,
        }
    }
}

#[derive(Debug)]
pub struct Atom {
    pub literal: Literal,
    pub span: Span,
}

impl From<&LexToken<'_>> for Atom {
    fn from(token: &LexToken) -> Self {
        Self {
            literal: Literal::from(&token.token),
            span: token.span.clone(),
        }
    }
}

impl Display for Atom {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.literal.fmt(f)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operator {
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

    // grouping operators
    LeftParen,
}

impl Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Plus => f.write_str("+"),
            Self::Minus => f.write_str("-"),
            Self::Star => f.write_str("*"),
            Self::Slash => f.write_str("/"),
            Self::Bang => f.write_str("!"),
            Self::BangEqual => f.write_str("!="),
            Self::Equal => f.write_str("="),
            Self::EqualEqual => f.write_str("=="),
            Self::Greater => f.write_str(">"),
            Self::GreaterEqual => f.write_str(">="),
            Self::Less => f.write_str("<"),
            Self::LessEqual => f.write_str("<="),
            Self::LeftParen => f.write_str("group"),
        }
    }
}

impl From<&Token<'_>> for Option<Operator> {
    fn from(token: &Token<'_>) -> Self {
        match token {
            Token::Plus => Some(Operator::Plus),
            Token::Minus => Some(Operator::Minus),
            Token::Star => Some(Operator::Star),
            Token::Slash => Some(Operator::Slash),
            Token::Bang => Some(Operator::Bang),
            Token::BangEqual => Some(Operator::BangEqual),
            Token::Equal => Some(Operator::Equal),
            Token::EqualEqual => Some(Operator::EqualEqual),
            Token::Greater => Some(Operator::Greater),
            Token::GreaterEqual => Some(Operator::GreaterEqual),
            Token::Less => Some(Operator::Less),
            Token::LessEqual => Some(Operator::LessEqual),
            Token::LeftParen => Some(Operator::LeftParen),
            _ => None,
        }
    }
}

/// Cons-case of an S-[Expr] representing a generic `n`-ary operation
#[derive(Debug)]
pub struct Cons {
    pub op: Operator,
    pub args: Vec<Expr>,
    pub span: Span,
}

/// An [S-expression][sexpr] representation of program's expressions.
///
/// [sexpr]: https://en.wikipedia.org/wiki/S-expression
#[derive(Debug)]
pub enum Expr {
    Atom(Atom),
    Cons(Cons),
}

impl Expr {
    #[inline]
    pub fn span(&self) -> &Span {
        match self {
            Self::Atom(Atom { ref span, .. }) => span,
            Self::Cons(Cons { ref span, .. }) => span,
        }
    }

    #[inline]
    pub fn group(expr: Expr, span: Span) -> Self {
        Self::unary(Operator::LeftParen, expr, span)
    }

    #[inline]
    pub fn unary(op: Operator, rhs: Expr, span: Span) -> Self {
        Self::Cons(Cons {
            op,
            args: vec![rhs],
            span,
        })
    }

    #[inline]
    pub fn binary(op: Operator, lhs: Expr, rhs: Expr, span: Span) -> Self {
        Self::Cons(Cons {
            op,
            args: vec![lhs, rhs],
            span,
        })
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Atom(atom) => write!(f, "{atom}"),
            Self::Cons(Cons { op, args, .. }) => {
                write!(f, "({op}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                f.write_str(")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pretty_print() {
        const DUMMY_SPAN: Span = Span {
            offset: 0,
            length: 0,
            lineno: 0,
            lineof: 0,
        };

        let expr = Expr::binary(
            Operator::Star,
            Expr::unary(
                Operator::Minus,
                Expr::Atom(Atom {
                    literal: Literal::Num(123.0),
                    span: DUMMY_SPAN.clone(),
                }),
                DUMMY_SPAN.clone(),
            ),
            Expr::group(
                Expr::Atom(Atom {
                    literal: Literal::Num(45.67),
                    span: DUMMY_SPAN.clone(),
                }),
                DUMMY_SPAN.clone(),
            ),
            DUMMY_SPAN.clone(),
        );

        assert_eq!("(* (- 123.0) (group 45.67))", expr.to_string());
    }
}
