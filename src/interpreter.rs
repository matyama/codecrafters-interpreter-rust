use std::any::Any;
use std::fmt::Display;

use crate::expr::{Binary, Expr, Grouping, Literal, Unary};
use crate::token::TokenType;

// NOTE: Here we model the nature of Lox as a dynamically typed language.
#[derive(Debug)]
pub enum Value {
    Object(Box<dyn Any>),
    Nil,
}

impl Value {
    /// Implements Ruby's rule: `false` and `nil` are false and everything else is true
    fn into_bool(self) -> bool {
        match self {
            Self::Object(obj) => obj.downcast::<bool>().map_or(true, |b| *b),
            Self::Nil => false,
        }
    }

    fn eq(self, rhs: Self) -> bool {
        match (self, rhs) {
            (Self::Nil, Self::Nil) => true,
            (Self::Nil, _) | (_, Self::Nil) => false,
            (Self::Object(_lhs), Self::Object(_rhs)) => todo!("implement"),
        }
    }
}

impl<T: 'static> From<Option<T>> for Value {
    #[inline]
    fn from(value: Option<T>) -> Self {
        value.map_or(Self::Nil, |v| Self::Object(Box::new(v)))
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self::Object(obj) = self else {
            return write!(f, "nil");
        };

        if let Some(s) = obj.downcast_ref::<String>() {
            return write!(f, "{s}");
        }

        if let Some(n) = obj.downcast_ref::<f64>() {
            return write!(f, "{n}");
        }

        if let Some(b) = obj.downcast_ref::<bool>() {
            return write!(f, "{b}");
        }

        Err(std::fmt::Error)
    }
}

pub trait Interpret {
    fn interpret(self) -> Result<Value, RuntimeError>;
}

impl Interpret for Expr {
    #[inline]
    fn interpret(self) -> Result<Value, RuntimeError> {
        match self {
            Expr::Binary(binary) => binary.interpret(),
            Expr::Grouping(group) => group.interpret(),
            Expr::Literal(lit) => lit.interpret(),
            Expr::Unary(unary) => unary.interpret(),
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
            Self::Str(s) => Value::from(Some(s)),
            Self::Num(n) => Value::from(Some(n)),
            Self::Bool(b) => Value::from(Some(b)),
            Self::None => Value::Nil,
        })
    }
}

impl Interpret for Unary {
    fn interpret(self) -> Result<Value, RuntimeError> {
        let value = self.rhs.interpret()?;

        match self.op.ty {
            TokenType::Bang => Ok(Value::from(Some(!value.into_bool()))),

            TokenType::Minus => {
                let Value::Object(mut v) = value else {
                    return Err(RuntimeError);
                };

                match v.downcast_mut::<f64>() {
                    Some(v) => *v = -*v,
                    None => panic!("failed at {v:?}"),
                }

                Ok(Value::Object(v))
            }

            ty => unreachable!("unary token type: {ty}"),
        }
    }
}

impl Interpret for Binary {
    fn interpret(self) -> Result<Value, RuntimeError> {
        let lhs = self.lhs.interpret()?;
        let rhs = self.rhs.interpret()?;

        match self.op.ty {
            TokenType::Minus => {
                let Value::Object(lhs) = lhs else {
                    return Err(RuntimeError);
                };

                let Value::Object(rhs) = rhs else {
                    return Err(RuntimeError);
                };

                match (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>()) {
                    (Some(lhs), Some(rhs)) => Ok(Value::from(Some(lhs - rhs))),
                    (lhs, rhs) => panic!("failed at {lhs:?} - {rhs:?}"),
                }
            }

            TokenType::Plus => {
                let Value::Object(lhs) = lhs else {
                    return Err(RuntimeError);
                };

                let Value::Object(rhs) = rhs else {
                    return Err(RuntimeError);
                };

                if let (Some(lhs), Some(rhs)) =
                    (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>())
                {
                    return Ok(Value::from(Some(lhs + rhs)));
                }

                match (lhs.downcast::<String>(), rhs.downcast::<String>()) {
                    (Ok(mut lhs), Ok(rhs)) => {
                        lhs.push_str(rhs.as_str());
                        Ok(Value::Object(lhs))
                    }
                    (lhs, rhs) => panic!("failed at {lhs:?} - {rhs:?}"),
                }
            }

            TokenType::Slash => {
                let Value::Object(lhs) = lhs else {
                    return Err(RuntimeError);
                };

                let Value::Object(rhs) = rhs else {
                    return Err(RuntimeError);
                };

                match (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>()) {
                    (Some(lhs), Some(rhs)) => Ok(Value::from(Some(lhs / rhs))),
                    (lhs, rhs) => panic!("failed at {lhs:?} / {rhs:?}"),
                }
            }

            TokenType::Star => {
                let Value::Object(lhs) = lhs else {
                    return Err(RuntimeError);
                };

                let Value::Object(rhs) = rhs else {
                    return Err(RuntimeError);
                };

                match (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>()) {
                    (Some(lhs), Some(rhs)) => Ok(Value::from(Some(lhs * rhs))),
                    (lhs, rhs) => panic!("failed at {lhs:?} * {rhs:?}"),
                }
            }

            TokenType::Greater => {
                let Value::Object(lhs) = lhs else {
                    return Err(RuntimeError);
                };

                let Value::Object(rhs) = rhs else {
                    return Err(RuntimeError);
                };

                match (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>()) {
                    (Some(lhs), Some(rhs)) => Ok(Value::from(Some(lhs > rhs))),
                    (lhs, rhs) => panic!("failed at {lhs:?} > {rhs:?}"),
                }
            }

            TokenType::GreaterEqual => {
                let Value::Object(lhs) = lhs else {
                    return Err(RuntimeError);
                };

                let Value::Object(rhs) = rhs else {
                    return Err(RuntimeError);
                };

                match (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>()) {
                    (Some(lhs), Some(rhs)) => Ok(Value::from(Some(lhs >= rhs))),
                    (lhs, rhs) => panic!("failed at {lhs:?} >= {rhs:?}"),
                }
            }

            TokenType::Less => {
                let Value::Object(lhs) = lhs else {
                    return Err(RuntimeError);
                };

                let Value::Object(rhs) = rhs else {
                    return Err(RuntimeError);
                };

                match (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>()) {
                    (Some(lhs), Some(rhs)) => Ok(Value::from(Some(lhs < rhs))),
                    (lhs, rhs) => panic!("failed at {lhs:?} < {rhs:?}"),
                }
            }

            TokenType::LessEqual => {
                let Value::Object(lhs) = lhs else {
                    return Err(RuntimeError);
                };

                let Value::Object(rhs) = rhs else {
                    return Err(RuntimeError);
                };

                match (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>()) {
                    (Some(lhs), Some(rhs)) => Ok(Value::from(Some(lhs <= rhs))),
                    (lhs, rhs) => panic!("failed at {lhs:?} <= {rhs:?}"),
                }
            }

            TokenType::BangEqual => Ok(Value::from(Some(!Value::eq(lhs, rhs)))),
            TokenType::EqualEqual => Ok(Value::from(Some(Value::eq(lhs, rhs)))),

            ty => unreachable!("binary token type: {ty}"),
        }
    }
}

// TODO: logging
#[derive(Debug)]
pub struct RuntimeError;
