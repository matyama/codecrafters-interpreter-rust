use std::any::Any;
use std::collections::HashMap;
use std::fmt::Display;
use std::rc::Rc;

use crate::error::{IntoRuntimeError as _, RuntimeError};
use crate::ir::{Atom, Cons, Decl, Expr, Literal, Operator, Print, Program, Stmt, Var};
use crate::span::Span;

#[inline]
pub fn evaluate(expr: Expr) -> Result<Value, RuntimeError> {
    let mut cx = Context::default();
    expr.evaluate(&mut cx)
}

#[inline]
pub fn interpret(prog: Program) -> Result<(), RuntimeError> {
    let mut cx = Context::default();
    prog.interpret(&mut cx)
}

// TODO: GC with tracing to collect cyclic object graphs
/// Dynamically typed, reference-counted, non-nil runtime value
#[derive(Clone, Debug)]
#[repr(transparent)]
pub struct Object(Rc<dyn Any>);

impl Object {
    #[inline]
    pub fn new<T: 'static>(value: T) -> Self {
        Self(Rc::new(value))
    }

    pub fn map<T: 'static>(self, f: impl FnOnce(&T) -> T) -> Result<Self, Self> {
        match self.0.downcast_ref::<T>() {
            Some(v) => Ok(Self::new(f(v))),
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
#[derive(Clone, Debug, Default)]
pub enum Value {
    Object(Object),
    #[default]
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
            Self::Object(Object(obj)) => obj.downcast_ref::<bool>().map_or(true, |b| *b),
            Self::Nil => false,
        }
    }

    pub fn map<T: 'static>(self, f: impl FnOnce(&T) -> T) -> Result<Self, Self> {
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

#[derive(Debug)]
struct Binding {
    val: Value,
    #[allow(dead_code)]
    span: Span,
}

// TODO: variable scoping
#[derive(Debug, Default)]
struct Context {
    /// (global) bindings of variable names to their values
    bindings: HashMap<String, Binding>,
}

impl Context {
    #[inline]
    fn define_var(&mut self, var: String, val: Option<Value>, span: Span) {
        self.bindings.insert(
            var,
            Binding {
                val: val.unwrap_or_default(),
                span,
            },
        );
    }

    fn get_val<V>(&self, var: V, span: Span) -> Result<Value, RuntimeError>
    where
        V: AsRef<str> + Display,
    {
        match self.bindings.get(var.as_ref()) {
            Some(Binding { val, .. }) => Ok(val.clone()),
            None => Err(span.into_error(format!("Undefined variable '{var}'."))),
        }
    }
}

trait Evaluate {
    fn evaluate(self, cx: &mut Context) -> Result<Value, RuntimeError>;
}

impl Evaluate for Expr {
    #[inline]
    fn evaluate(self, cx: &mut Context) -> Result<Value, RuntimeError> {
        match self {
            Self::Atom(atom) => atom.evaluate(cx),
            Self::Cons(cons) => cons.evaluate(cx),
        }
    }
}

impl Evaluate for Atom {
    #[inline]
    fn evaluate(self, cx: &mut Context) -> Result<Value, RuntimeError> {
        Ok(match self.literal {
            Literal::Var(x) => cx.get_val(x, self.span)?,
            Literal::Str(s) => Value::obj(s),
            Literal::Num(n) => Value::obj(n),
            Literal::Bool(b) => Value::obj(b),
            Literal::Nil => Value::Nil,
        })
    }
}

impl Evaluate for Cons {
    fn evaluate(mut self, cx: &mut Context) -> Result<Value, RuntimeError> {
        let binary_args = |mut args: Vec<Expr>| match (args.pop(), args.pop()) {
            (Some(rhs), Some(lhs)) => Some((lhs, rhs)),
            _ => None,
        };

        match self.op {
            Operator::Bang => match self.args.pop() {
                Some(rhs) => {
                    let value = rhs.evaluate(cx)?;
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

                let Value::Object(Object(lhs)) = lhs.evaluate(cx)? else {
                    return Err(self
                        .span
                        .into_error("Operands must be two numbers or two strings."));
                };

                let Value::Object(Object(rhs)) = rhs.evaluate(cx)? else {
                    return Err(self
                        .span
                        .into_error("Operands must be two numbers or two strings."));
                };

                if let (Some(lhs), Some(rhs)) =
                    (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>())
                {
                    return Ok(Value::obj(lhs + rhs));
                }

                match (lhs.downcast_ref::<String>(), rhs.downcast_ref::<String>()) {
                    (Some(left), Some(right)) => {
                        let mut s = String::with_capacity(left.len() + right.len());
                        s.push_str(left);
                        s.push_str(right);
                        Ok(Value::obj(s))
                    }
                    _ => Err(self
                        .span
                        .into_error("Operands must be two numbers or two strings.")),
                }
            }

            Operator::Minus => match (self.args.pop(), self.args.pop()) {
                (Some(rhs), None) => {
                    let rhs = rhs.evaluate(cx)?;
                    rhs.map::<f64>(|v| -*v)
                        .map_err(|_| self.span.into_error("Operand must be a number."))
                }
                (Some(rhs), Some(lhs)) => {
                    let lhs = lhs.evaluate(cx)?;
                    let rhs = rhs.evaluate(cx)?;

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

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, f64>(rhs, |x, y| x / y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::Star => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, f64>(rhs, |x, y| x * y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::Greater => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, bool>(rhs, |x, y| x > y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::GreaterEqual => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, bool>(rhs, |x, y| x >= y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::Less => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, bool>(rhs, |x, y| x < y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::LessEqual => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, bool>(rhs, |x, y| x <= y)
                    .map_err(|_| self.span.into_error("Operands must be numbers."))
            }

            Operator::BangEqual => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                Ok(Value::obj(lhs != rhs))
            }

            Operator::EqualEqual => {
                let Some((lhs, rhs)) = binary_args(self.args) else {
                    return Err(self.span.into_error("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                Ok(Value::obj(lhs == rhs))
            }

            Operator::LeftParen => match self.args.pop() {
                Some(expr) => expr.evaluate(cx),
                None => Err(self.span.into_error("Operand must be an expression.")),
            },

            op => unimplemented!("interpret {op:?}"),
        }
    }
}

trait Interpret {
    fn interpret(self, cx: &mut Context) -> Result<(), RuntimeError>;
}

impl Interpret for Program {
    #[inline]
    fn interpret(self, cx: &mut Context) -> Result<(), RuntimeError> {
        self.into_iter().try_for_each(|decl| decl.interpret(cx))
    }
}

impl Interpret for Decl {
    #[inline]
    fn interpret(self, cx: &mut Context) -> Result<(), RuntimeError> {
        match self {
            Self::Var(var) => var.interpret(cx),
            Self::Stmt(stmt) => stmt.interpret(cx),
        }
    }
}

impl Interpret for Var {
    fn interpret(self, cx: &mut Context) -> Result<(), RuntimeError> {
        let value = self.expr.map(|expr| expr.evaluate(cx)).transpose()?;
        cx.define_var(self.ident, value, self.span);
        Ok(())
    }
}

impl Interpret for Stmt {
    #[inline]
    fn interpret(self, cx: &mut Context) -> Result<(), RuntimeError> {
        match self {
            Self::Expr(expr) => expr.evaluate(cx).map(|_| ()),
            Self::Print(print) => print.interpret(cx),
        }
    }
}

impl Interpret for Print {
    fn interpret(self, cx: &mut Context) -> Result<(), RuntimeError> {
        let value = self.expr.evaluate(cx)?;
        println!("{value}");
        Ok(())
    }
}
