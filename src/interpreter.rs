use std::any::Any;
use std::fmt::Display;

use crate::error::{IntoRuntimeError as _, RuntimeError};
use crate::expr::{Atom, Cons, Expr, Literal, Operator};

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
            Self::Atom(atom) => atom.interpret(),
            Self::Cons(cons) => cons.interpret(),
        }
    }
}

impl Interpret for Atom {
    #[inline]
    fn interpret(self) -> Result<Value, RuntimeError> {
        self.literal.interpret()
    }
}

impl Interpret for Literal {
    #[inline]
    fn interpret(self) -> Result<Value, RuntimeError> {
        Ok(match self {
            Self::Str(s) => Value::obj(s),
            Self::Num(n) => Value::obj(n),
            Self::Bool(b) => Value::obj(b),
            Self::Nil => Value::Nil,
        })
    }
}

impl Interpret for Cons {
    fn interpret(mut self) -> Result<Value, RuntimeError> {
        let binary_args = |mut args: Vec<Expr>| match (args.pop(), args.pop()) {
            (Some(rhs), Some(lhs)) => Some((lhs, rhs)),
            _ => None,
        };

        match self.op {
            Operator::Bang => match self.args.pop() {
                Some(rhs) => {
                    let value = rhs.interpret()?;
                    Ok(Value::obj(!value.into_bool()))
                }
                None => Err(self.span.into_error("Operand must be an expression.")),
            },

            Operator::Plus => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self
                        .span
                        .into_error("Operands must be two numbers or two strings."));
                };

                let Value::Object(Object(mut lhs)) = lhs.interpret()? else {
                    return Err(self
                        .span
                        .into_error("Operands must be two numbers or two strings."));
                };

                let Value::Object(Object(rhs)) = rhs.interpret()? else {
                    return Err(self
                        .span
                        .into_error("Operands must be two numbers or two strings."));
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
                    _ => Err(self
                        .span
                        .into_error("Operands must be two numbers or two strings.")),
                }
            }

            Operator::Minus => match (self.args.pop(), self.args.pop()) {
                (Some(rhs), None) => {
                    let rhs = rhs.interpret()?;
                    rhs.map::<f64>(|v| *v = -*v)
                        .map_err(|_| self.span.into_error("Operand must be a number."))
                }
                (Some(rhs), Some(lhs)) => {
                    let lhs = lhs.interpret()?;
                    let rhs = rhs.interpret()?;

                    lhs.combine::<f64, f64>(rhs, |x, y| x - y)
                        .map_err(|_| self.span.into_error("Operands must be numbers."))
                }
                _ => Err(self
                    .span
                    .into_error("Operands must be two numbers or two strings.")),
            },

            Operator::Slash => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.interpret()?;
                let rhs = rhs.interpret()?;

                lhs.combine::<f64, f64>(rhs, |x, y| x / y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::Star => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.interpret()?;
                let rhs = rhs.interpret()?;

                lhs.combine::<f64, f64>(rhs, |x, y| x * y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::Greater => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.interpret()?;
                let rhs = rhs.interpret()?;

                lhs.combine::<f64, bool>(rhs, |x, y| x > y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::GreaterEqual => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.interpret()?;
                let rhs = rhs.interpret()?;

                lhs.combine::<f64, bool>(rhs, |x, y| x >= y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::Less => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.interpret()?;
                let rhs = rhs.interpret()?;

                lhs.combine::<f64, bool>(rhs, |x, y| x < y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::LessEqual => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.interpret()?;
                let rhs = rhs.interpret()?;

                lhs.combine::<f64, bool>(rhs, |x, y| x <= y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::BangEqual => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.interpret()?;
                let rhs = rhs.interpret()?;

                Ok(Value::obj(lhs != rhs))
            }

            Operator::EqualEqual => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.interpret()?;
                let rhs = rhs.interpret()?;

                Ok(Value::obj(lhs == rhs))
            }

            Operator::LeftParen => match self.args.pop() {
                Some(expr) => expr.interpret(),
                None => Err(self.span.into_error("Operand must be an expression.")),
            },

            op => unimplemented!("interpret {op:?}"),
        }
    }
}
