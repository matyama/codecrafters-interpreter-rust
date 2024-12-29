use std::any::Any;
use std::fmt::Display;
use std::process::{ExitCode, Termination};

use crate::expr::{Binary, Expr, Grouping, Literal, Unary};
use crate::{Report, Span};

#[derive(Debug)]
#[repr(transparent)]
pub struct Object(Box<dyn Any>);

impl Object {
    #[inline]
    pub fn new<T: 'static>(value: T) -> Self {
        Self(Box::new(value))
    }

    pub fn map<T: 'static>(mut self, f: impl FnOnce(&mut T)) -> Result<Self, Self> {
        match self.0.downcast_mut::<T>() {
            Some(v) => {
                f(v);
                Ok(self)
            }
            None => Err(self),
        }
    }

    pub fn combine<T: 'static, U: 'static>(
        self,
        other: Self,
        f: impl Fn(&T, &T) -> U,
    ) -> Result<Self, (Self, Self)> {
        match (self.0.downcast_ref::<T>(), other.0.downcast_ref::<T>()) {
            (Some(lhs), Some(rhs)) => Ok(Self::new(f(lhs, rhs))),
            _ => Err((self, other)),
        }
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(s) = self.0.downcast_ref::<String>() {
            return write!(f, "{s}");
        }

        if let Some(n) = self.0.downcast_ref::<f64>() {
            return write!(f, "{n}");
        }

        if let Some(b) = self.0.downcast_ref::<bool>() {
            return write!(f, "{b}");
        }

        Err(std::fmt::Error)
    }
}

impl PartialEq for Object {
    fn eq(&self, other: &Self) -> bool {
        let lhs = self.0.downcast_ref::<String>();
        let rhs = other.0.downcast_ref::<String>();

        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            return lhs == rhs;
        }

        let lhs = self.0.downcast_ref::<f64>();
        let rhs = other.0.downcast_ref::<f64>();

        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            return lhs == rhs;
        }

        let lhs = self.0.downcast_ref::<bool>();
        let rhs = other.0.downcast_ref::<bool>();

        if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
            return lhs == rhs;
        }

        false
    }
}

impl Eq for Object {}

// NOTE: Here we model the nature of Lox as a dynamically typed language.
#[derive(Debug)]
pub enum Value {
    Object(Object),
    Nil,
}

impl Value {
    #[inline]
    pub fn obj<T: 'static>(obj: T) -> Self {
        Self::Object(Object::new(obj))
    }

    /// Implements Ruby's rule: `false` and `nil` are false and everything else is true
    fn into_bool(self) -> bool {
        match self {
            Self::Object(Object(obj)) => obj.downcast::<bool>().map_or(true, |b| *b),
            Self::Nil => false,
        }
    }

    pub fn map<T: 'static>(self, f: impl FnOnce(&mut T)) -> Result<Self, Self> {
        match self {
            Self::Object(obj) => obj.map::<T>(f).map(Self::Object).map_err(Self::Object),
            Self::Nil => Err(self),
        }
    }

    pub fn combine<T: 'static, U: 'static>(
        self,
        other: Self,
        f: impl Fn(&T, &T) -> U,
    ) -> Result<Self, (Self, Self)> {
        match (self, other) {
            (Self::Object(lhs), Self::Object(rhs)) => lhs
                .combine(rhs, f)
                .map(Self::Object)
                .map_err(|(lhs, rhs)| (Self::Object(lhs), Self::Object(rhs))),
            (lhs, rhs) => Err((lhs, rhs)),
        }
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Nil, Self::Nil) => true,
            (Self::Nil, _) | (_, Self::Nil) => false,
            (Self::Object(lhs), Self::Object(rhs)) => lhs == rhs,
        }
    }
}

impl Eq for Value {}

impl Display for Value {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Object(obj) => obj.fmt(f),
            Self::Nil => write!(f, "nil"),
        }
    }
}

pub trait Interpret {
    fn interpret(self) -> Result<Value, RuntimeError>;
}

impl Interpret for Expr {
    #[inline]
    fn interpret(self) -> Result<Value, RuntimeError> {
        match self {
            Self::Binary(binary) => binary.interpret(),
            Self::Grouping(group) => group.interpret(),
            Self::Literal(lit) => lit.interpret(),
            Self::Unary(unary) => unary.interpret(),
        }
    }
}

impl Interpret for Grouping {
    #[inline]
    fn interpret(self) -> Result<Value, RuntimeError> {
        self.0.interpret()
    }
}

impl Interpret for Literal {
    #[inline]
    fn interpret(self) -> Result<Value, RuntimeError> {
        Ok(match self {
            Self::Str(s) => Value::obj(s),
            Self::Num(n) => Value::obj(n),
            Self::Bool(b) => Value::obj(b),
            Self::None => Value::Nil,
        })
    }
}

impl Interpret for Unary {
    fn interpret(self) -> Result<Value, RuntimeError> {
        use crate::expr::OperatorToken::*;

        let value = self.rhs.interpret()?;

        match self.op.token {
            Bang => Ok(Value::obj(!value.into_bool())),

            Minus => value.map::<f64>(|v| *v = -*v).map_err(|_| {
                RuntimeError::new(
                    &self.op.lexeme,
                    self.op.span.lineno,
                    "Operand must be a number.",
                )
            }),

            ty => unreachable!("unary token type: {ty:?}"),
        }
    }
}

impl Interpret for Binary {
    fn interpret(self) -> Result<Value, RuntimeError> {
        use crate::expr::OperatorToken::*;

        let lhs = self.lhs.interpret()?;
        let rhs = self.rhs.interpret()?;

        match self.op.token {
            Minus => lhs.combine::<f64, f64>(rhs, |x, y| x - y).map_err(|_| {
                RuntimeError::new(
                    &self.op.lexeme,
                    self.op.span.lineno,
                    "Operands must be numbers.",
                )
            }),

            Plus => {
                let Value::Object(Object(mut lhs)) = lhs else {
                    return Err(RuntimeError::new(
                        &self.op.lexeme,
                        self.op.span.lineno,
                        "Operands must be two numbers or two strings.",
                    ));
                };

                let Value::Object(Object(rhs)) = rhs else {
                    return Err(RuntimeError::new(
                        &self.op.lexeme,
                        self.op.span.lineno,
                        "Operands must be two numbers or two strings.",
                    ));
                };

                if let (Some(lhs), Some(rhs)) =
                    (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>())
                {
                    return Ok(Value::obj(lhs + rhs));
                }

                match (lhs.downcast_mut::<String>(), rhs.downcast_ref::<String>()) {
                    (Some(left), Some(right)) => {
                        left.push_str(right);
                        Ok(Value::Object(Object(lhs)))
                    }
                    _ => Err(RuntimeError::new(
                        &self.op.lexeme,
                        self.op.span.lineno,
                        "Operands must be two numbers or two strings.",
                    )),
                }
            }

            Slash => lhs.combine::<f64, f64>(rhs, |x, y| x / y).map_err(|_| {
                RuntimeError::new(
                    &self.op.lexeme,
                    self.op.span.lineno,
                    "Operands must be numbers.",
                )
            }),

            Star => lhs.combine::<f64, f64>(rhs, |x, y| x * y).map_err(|_| {
                RuntimeError::new(
                    &self.op.lexeme,
                    self.op.span.lineno,
                    "Operands must be numbers.",
                )
            }),

            Greater => lhs.combine::<f64, bool>(rhs, |x, y| x > y).map_err(|_| {
                RuntimeError::new(
                    &self.op.lexeme,
                    self.op.span.lineno,
                    "Operands must be numbers.",
                )
            }),

            GreaterEqual => lhs.combine::<f64, bool>(rhs, |x, y| x >= y).map_err(|_| {
                RuntimeError::new(
                    &self.op.lexeme,
                    self.op.span.lineno,
                    "Operands must be numbers.",
                )
            }),

            Less => lhs.combine::<f64, bool>(rhs, |x, y| x < y).map_err(|_| {
                RuntimeError::new(
                    &self.op.lexeme,
                    self.op.span.lineno,
                    "Operands must be numbers.",
                )
            }),

            LessEqual => lhs.combine::<f64, bool>(rhs, |x, y| x <= y).map_err(|_| {
                RuntimeError::new(
                    &self.op.lexeme,
                    self.op.span.lineno,
                    "Operands must be numbers.",
                )
            }),

            BangEqual => Ok(Value::obj(lhs != rhs)),
            EqualEqual => Ok(Value::obj(lhs == rhs)),

            ty => unreachable!("binary token type: {ty:?}"),
        }
    }
}

#[derive(Debug)]
pub struct RuntimeError;

impl RuntimeError {
    #[inline]
    pub fn new(token: &str, line: usize, msg: impl Display) -> Self {
        Self.error(Span::Token(token, line), &msg);
        Self
    }
}

impl Report for RuntimeError {
    fn report(&mut self, line: usize, _location: &str, msg: impl Display) {
        eprintln!("{msg}\n[line {line}]");
    }

    #[inline]
    fn error(&mut self, span: Span<'_>, msg: impl Display) {
        match span {
            Span::Eof(line) | Span::Token(_, line) => self.report(line, "", msg),
        }
    }
}

impl Termination for RuntimeError {
    #[inline]
    fn report(self) -> ExitCode {
        ExitCode::from(70)
    }
}
