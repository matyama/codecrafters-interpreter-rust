use std::collections::HashMap;
use std::fmt::Display;
use std::ops::Add;
use std::rc::Rc;

use crate::span::Span;
use crate::token::{Keyword, Token};

#[derive(Debug)]
pub struct Ast<T> {
    pub(crate) tree: T,
    pub(crate) meta: Metadata,
}

impl<T> AsRef<T> for Ast<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.tree
    }
}

// TODO: more efficient identifier representation (at least Rc)
#[derive(Debug)]
pub struct Ident {
    pub(crate) id: u64,
    pub(crate) name: String,
    pub(crate) span: Span,
}

impl Ident {
    #[inline]
    pub fn name(&self) -> &str {
        &self.name
    }

    #[inline]
    pub fn span(&self) -> &Span {
        &self.span
    }
}

// TODO: find a better story for representing strings (and var identifiers)
/// Atomic expression (literal values and variables)
#[derive(Clone, Default, Debug)]
pub enum Literal {
    #[default]
    Nil,
    Bool(bool),
    Num(f64),
    Str(Rc<String>),
    Ident(u64, String),
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Nil => write!(f, "nil"),
            Self::Bool(b) => write!(f, "{b}"),
            Self::Num(n) if n.fract() > 0.0 => write!(f, "{n}"),
            Self::Num(n) => write!(f, "{n:.1}"),
            Self::Str(s) => write!(f, "{s}"),
            Self::Ident(_, x) => write!(f, "{x}"),
        }
    }
}

#[derive(Debug)]
pub struct Atom {
    pub literal: Literal,
    pub span: Span,
}

impl Atom {
    #[inline]
    fn is_ident(&self) -> bool {
        matches!(
            self,
            Self {
                literal: Literal::Ident(..),
                ..
            }
        )
    }
}

impl From<Ident> for Atom {
    #[inline]
    fn from(Ident { id, name, span }: Ident) -> Self {
        Self {
            literal: Literal::Ident(id, name),
            span,
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

    // property access
    Dot,
}

impl Display for Operator {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_ref())
    }
}

impl AsRef<str> for Operator {
    fn as_ref(&self) -> &str {
        match self {
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Slash => "/",
            Self::And => "and",
            Self::Or => "or",
            Self::Bang => "!",
            Self::BangEqual => "!=",
            Self::Equal => "=",
            Self::EqualEqual => "==",
            Self::Greater => ">",
            Self::GreaterEqual => ">=",
            Self::Less => "<",
            Self::LessEqual => "<=",
            Self::LeftParen => "group",
            Self::Call => "",
            Self::Dot => ".",
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
            Token::Dot => Some(Operator::Dot),
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
    pub(crate) fn is_ident(&self) -> bool {
        matches!(self, Self::Atom(atom) if atom.is_ident())
    }

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

impl From<Atom> for Expr {
    #[inline]
    fn from(atom: Atom) -> Self {
        Self::Atom(atom)
    }
}

impl From<Ident> for Expr {
    #[inline]
    fn from(ident: Ident) -> Self {
        Self::Atom(Atom::from(ident))
    }
}

/// [Expr]ession wrapper indicating a valid *l-value* (i.e, assignment target)
#[derive(Debug)]
#[repr(transparent)]
pub struct AssignTarget(Expr);

impl TryFrom<Expr> for AssignTarget {
    type Error = Expr;

    fn try_from(expr: Expr) -> Result<Self, Self::Error> {
        match &expr {
            // target is a variable (e.g, x = 42)
            Expr::Atom(Atom {
                literal: Literal::Ident(..),
                ..
            }) => Ok(Self(expr)),

            // target is a get expression (e.g., obj.field.subfield = 42)
            Expr::Cons(Cons {
                op: Operator::Dot,
                args,
                ..
            }) if matches!(args.as_slice(), [_, y] if y.is_ident()) => Ok(Self(expr)),

            _ => Err(expr),
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
    Class(Class),
    Fun(Fun),
    Var(Var),
    Stmt(Stmt),
}

impl Decl {
    #[inline]
    pub fn span(&self) -> &Span {
        match self {
            Self::Class(Class { span, .. }) => span,
            Self::Fun(Fun { span, .. }) => span,
            Self::Var(Var { span, .. }) => span,
            Self::Stmt(stmt) => stmt.span(),
        }
    }
}

impl From<Class> for Decl {
    #[inline]
    fn from(class: Class) -> Self {
        Self::Class(class)
    }
}

impl From<Fun> for Decl {
    #[inline]
    fn from(fun: Fun) -> Self {
        Self::Fun(fun)
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

/// Class declaration of the form: `class <IDENTIFIER> (< <IDENTIFIER>)?  { <FUNCTION>* )`
#[derive(Debug)]
pub struct Class {
    #[allow(dead_code)]
    pub id: u64,
    pub name: String,
    pub superclass: Option<Rc<Expr>>,
    pub methods: Vec<Rc<Function>>,
    pub span: Span,
}

/// Function declaration of the form: `fun <IDENTIFIER> (<PARAMETERS>?) <BODY>`
#[derive(Debug)]
pub struct Fun {
    pub func: Rc<Function>,
    pub span: Span,
}

/// Function declaration of the form: `<IDENTIFIER> (<PARAMETERS>?) <BODY>`
#[derive(Debug)]
pub struct Function {
    #[allow(dead_code)]
    pub id: u64,
    pub name: String,
    pub params: Vec<Ident>,
    pub body: Block,
    pub span: Span,
}

/// Variable declaration of the form: `var <IDENTIFIER> (=<EXPRESSION>)?;`
#[derive(Debug)]
pub struct Var {
    pub ident: Ident,
    pub expr: Option<Expr>,
    pub span: Span,
}

#[derive(Debug)]
pub enum Stmt {
    Block(Block),
    If(If),
    While(While),
    Expr(Expr),
    Print(Print),
    Return(Return),
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
            Self::Return(Return { span, .. }) => span,
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

impl From<Return> for Stmt {
    #[inline]
    fn from(ret: Return) -> Self {
        Self::Return(ret)
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

#[derive(Debug)]
pub struct Return {
    pub(crate) value: Option<Expr>,
    pub(crate) span: Span,
}

// NOTE: Alternatively, this could be part of the IR and computed during parsing. The benefit of
// storing it as a separate data structure is that it's easy to lookup/update/discard information.
/// Metadata associated to various parts of the AST.
#[derive(Debug, Default)]
pub struct Metadata {
    // XXX: Vec<String> assuming sequential IDs
    /// Identifier names indexed by their unique IDs
    pub(crate) idents: HashMap<u64, String>,

    /// Variable resolution: a mapping from variable names to their _definition distance_
    ///
    /// The mapping stores for each variable the number of scopes between the current to the one
    /// where the variable was defined.
    pub(crate) locals: HashMap<u64, usize>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pretty_print() {
        const DUMMY_SPAN: Span = Span::empty();

        let expr = Expr::binary(
            Operator::Star,
            Expr::unary(
                Operator::Minus,
                Expr::Atom(Atom {
                    literal: Literal::Num(123.0),
                    span: DUMMY_SPAN,
                }),
                DUMMY_SPAN,
            ),
            Expr::group(
                Expr::Atom(Atom {
                    literal: Literal::Num(45.67),
                    span: DUMMY_SPAN,
                }),
                DUMMY_SPAN,
            ),
            DUMMY_SPAN,
        );

        assert_eq!("(* (- 123.0) (group 45.67))", expr.to_string());
    }
}
