use std::fmt::Display;
use std::ops::Add;
use std::rc::Rc;

use crate::span::Span;
use crate::token::{Keyword, LexToken, Token};

// TODO: find a better story for representing strings (and var identifiers)
/// Atomic expression (literal values and variables)
#[derive(Clone, Default, Debug)]
pub enum Literal {
    #[default]
    Nil,
    Bool(bool),
    Num(f64),
    Str(Rc<String>),
    Var(String),
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nil => write!(f, "nil"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Num(n) if n.fract() > 0.0 => write!(f, "{n}"),
            Self::Num(n) => write!(f, "{n:.1}"),
            Self::Str(s) => write!(f, "{s}"),
            Self::Var(x) => write!(f, "{x}"),
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
            Token::Literal(Str(s)) => Self::Str(Rc::new(s.to_string())),
            Token::Literal(Num(n)) => Self::Num(*n),
            Token::Literal(Ident(x)) => Self::Var(x.to_string()),
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

impl Add<Span> for Atom {
    type Output = Self;

    #[inline]
    fn add(mut self, span: Span) -> Self::Output {
        self.span += span;
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operator {
    // arithmetic operators
    Plus,
    Minus,
    Star,
    Slash,

    // logic operators
    And,
    Or,
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

    // invoking function-like objects
    Call,
}

impl Display for Operator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Plus => f.write_str("+"),
            Self::Minus => f.write_str("-"),
            Self::Star => f.write_str("*"),
            Self::Slash => f.write_str("/"),
            Self::And => f.write_str("and"),
            Self::Or => f.write_str("or"),
            Self::Bang => f.write_str("!"),
            Self::BangEqual => f.write_str("!="),
            Self::Equal => f.write_str("="),
            Self::EqualEqual => f.write_str("=="),
            Self::Greater => f.write_str(">"),
            Self::GreaterEqual => f.write_str(">="),
            Self::Less => f.write_str("<"),
            Self::LessEqual => f.write_str("<="),
            Self::LeftParen => f.write_str("group"),
            Self::Call => Ok(()),
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
            Token::Keyword(Keyword::And) => Some(Operator::And),
            Token::Keyword(Keyword::Or) => Some(Operator::Or),
            Token::Bang => Some(Operator::Bang),
            Token::BangEqual => Some(Operator::BangEqual),
            Token::Equal => Some(Operator::Equal),
            Token::EqualEqual => Some(Operator::EqualEqual),
            Token::Greater => Some(Operator::Greater),
            Token::GreaterEqual => Some(Operator::GreaterEqual),
            Token::Less => Some(Operator::Less),
            Token::LessEqual => Some(Operator::LessEqual),
            Token::LeftParen => Some(Operator::LeftParen),
            // NOTE: Operator::Call must be constructed explicitly
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

impl Add<Span> for Cons {
    type Output = Self;

    #[inline]
    fn add(mut self, span: Span) -> Self::Output {
        self.span += span;
        self
    }
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

impl Add<Span> for Expr {
    type Output = Self;

    #[inline]
    fn add(self, span: Span) -> Self::Output {
        match self {
            Self::Atom(atom) => Self::Atom(atom + span),
            Self::Cons(cons) => Self::Cons(cons + span),
        }
    }
}

/// [Expr]ession wrapper indicating a valid *r-value* (i.e, assignment target)
#[derive(Debug)]
#[repr(transparent)]
pub struct AssignTarget(Expr);

impl TryFrom<Expr> for AssignTarget {
    type Error = Expr;

    fn try_from(expr: Expr) -> Result<Self, Self::Error> {
        // TODO: support other kinds of assignment targets than just a variable identifier
        match expr {
            var @ Expr::Atom(Atom {
                literal: Literal::Var(_),
                ..
            }) => Ok(AssignTarget(var)),
            expr => Err(expr),
        }
    }
}

impl From<AssignTarget> for Expr {
    #[inline]
    fn from(AssignTarget(expr): AssignTarget) -> Self {
        expr
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Program(pub(crate) Vec<Decl>);

/// Declarations
#[derive(Debug)]
pub enum Decl {
    Var(Var),
    Stmt(Stmt),
}

impl Decl {
    #[inline]
    pub fn span(&self) -> &Span {
        match self {
            Self::Var(Var { span, .. }) => span,
            Self::Stmt(stmt) => stmt.span(),
        }
    }
}

impl From<Var> for Decl {
    #[inline]
    fn from(var: Var) -> Self {
        Self::Var(var)
    }
}

impl From<Stmt> for Decl {
    #[inline]
    fn from(stmt: Stmt) -> Self {
        Self::Stmt(stmt)
    }
}

/// Variable declaration of the form: `var <IDENTIFIER> (=<EXPRESSION>)?;`
#[derive(Debug)]
pub struct Var {
    // TODO: more efficient variable representation
    pub ident: String,
    pub expr: Option<Expr>,
    pub span: Span,
}

// TODO: represent statements as S-expressions
#[derive(Debug)]
pub enum Stmt {
    Block(Block),
    If(If),
    While(While),
    Expr(Expr),
    Print(Print),
}

impl Stmt {
    #[inline]
    pub fn span(&self) -> &Span {
        match self {
            Self::Block(Block { span, .. }) => span,
            Self::If(If { span, .. }) => span,
            Self::While(While { span, .. }) => span,
            Self::Expr(expr) => expr.span(),
            Self::Print(Print { span, .. }) => span,
        }
    }
}

impl From<Block> for Stmt {
    #[inline]
    fn from(block: Block) -> Self {
        Self::Block(block)
    }
}

impl From<If> for Stmt {
    #[inline]
    fn from(if_stmt: If) -> Self {
        Self::If(if_stmt)
    }
}

impl From<While> for Stmt {
    #[inline]
    fn from(while_stmt: While) -> Self {
        Self::While(while_stmt)
    }
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
pub struct Block {
    pub(crate) decls: Vec<Decl>,
    pub(crate) span: Span,
}

#[derive(Debug)]
pub struct If {
    pub(crate) cond: Expr,
    pub(crate) then_branch: Box<Stmt>,
    pub(crate) else_branch: Option<Box<Stmt>>,
    pub(crate) span: Span,
}

#[derive(Debug)]
pub struct While {
    pub(crate) cond: Expr,
    pub(crate) body: Box<Stmt>,
    pub(crate) span: Span,
}

#[derive(Debug)]
pub struct Print {
    pub(crate) expr: Expr,
    pub(crate) span: Span,
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
