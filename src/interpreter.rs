use std::any::Any;
use std::collections::hash_map::{Entry, HashMap};
use std::fmt::Display;
use std::io::Write;
use std::ptr::NonNull;
use std::rc::Rc;

use crate::error::{RuntimeError, ThrowRuntimeError as _};
use crate::ir::{
    Atom, Block, Cons, Decl, Expr, If, Literal, Operator, Print, Program, Stmt, Var, While,
};
use crate::span::Span;

#[inline]
pub fn evaluate<W: Write>(expr: Expr, writer: &mut W) -> Result<Value, RuntimeError> {
    let mut globals = Environment::global();
    let mut cx = Context::new(&mut globals, writer);
    expr.evaluate(&mut cx)
}

#[inline]
pub fn interpret<W: Write>(prog: Program, writer: &mut W) -> Result<(), RuntimeError> {
    let mut globals = Environment::global();
    let mut cx = Context::new(&mut globals, writer);
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
        macro_rules! try_eq {
            ($t:ty) => {
                let lhs = self.0.downcast_ref::<$t>();
                let rhs = other.0.downcast_ref::<$t>();

                if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
                    return lhs == rhs;
                }
            };
        }

        try_eq!(String);
        try_eq!(f64);
        try_eq!(bool);

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
    pub fn new<T: 'static>(obj: T) -> Self {
        Self::obj(Rc::new(obj))
    }

    #[inline]
    pub fn obj<T: 'static>(obj: Rc<T>) -> Self {
        Self::Object(Object(obj))
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

impl From<&Value> for bool {
    /// Implements Ruby's rule: `false` and `nil` are false and everything else is true
    fn from(value: &Value) -> Self {
        match value {
            Value::Object(Object(obj)) => obj.downcast_ref::<bool>().map_or(true, |b| *b),
            Value::Nil => false,
        }
    }
}

impl From<Value> for bool {
    #[inline]
    fn from(value: Value) -> Self {
        Self::from(&value)
    }
}

trait Call: std::fmt::Debug + Display {
    fn arity(&self) -> usize;

    fn call(&self, args: Vec<Value>, cx: &mut Context) -> Result<Value, RuntimeError>;
}

fn clock(args: Vec<Value>, _cx: &mut Context) -> Result<Value, RuntimeError> {
    debug_assert!(args.is_empty(), "'clock()' takes no arguments");

    // XXX: turn this into a RuntimeError (i.e., require span)
    let elapsed = std::time::UNIX_EPOCH
        .elapsed()
        .map(|elapsed| elapsed.as_secs() as f64)
        .map(Value::new)
        .expect("time went backwards");

    Ok(elapsed)
}

#[derive(Debug)]
struct Native {
    func: fn(Vec<Value>, &mut Context) -> Result<Value, RuntimeError>,
    arity: usize,
}

impl Display for Native {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("<native fn>")
    }
}

impl Call for Native {
    #[inline]
    fn arity(&self) -> usize {
        self.arity
    }

    #[inline]
    fn call(&self, args: Vec<Value>, cx: &mut Context) -> Result<Value, RuntimeError> {
        debug_assert_eq!(args.len(), self.arity);
        (self.func)(args, cx)
    }
}

#[derive(Debug)]
#[repr(transparent)]
struct Callable(Box<dyn Call + 'static>);

impl Display for Callable {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl Call for Callable {
    #[inline]
    fn arity(&self) -> usize {
        self.0.arity()
    }

    #[inline]
    fn call(&self, args: Vec<Value>, cx: &mut Context) -> Result<Value, RuntimeError> {
        self.0.call(args, cx)
    }
}

#[derive(Debug, Default)]
struct Environment {
    /// (global) bindings of variable names to their values
    bindings: HashMap<String, Value>,
    /// parent context (`None` indicates the global scope)
    enclosing: Option<NonNull<Environment>>,
}

impl Environment {
    fn global() -> Self {
        let mut globals = Self::default();

        // initialize global environment with native functions
        {
            let clock = Callable(Box::new(Native {
                func: clock,
                arity: 0,
            }));

            globals.define("clock", Some(Value::new(clock)));
        }

        globals
    }

    /// ### Safety
    ///
    /// The caller must ensure that `&mut self` remains valid for the lifetime of the returned
    /// scoped [Context].
    unsafe fn scope(&mut self) -> Self {
        Self {
            bindings: HashMap::new(),
            enclosing: NonNull::new(self as *mut Self),
        }
    }

    #[inline]
    fn define(&mut self, var: &str, val: Option<Value>) {
        self.bindings
            .insert(var.to_string(), val.unwrap_or_default());
    }

    /// Register new assignment `var := val` and return new `val`
    fn assign(&mut self, var: &str, val: Value, span: &Span) -> Result<Value, RuntimeError> {
        let mut var = var.to_string();
        let mut env = self;
        loop {
            match env.bindings.entry(var) {
                Entry::Occupied(mut entry) => {
                    let _ = entry.insert(val);
                    // NOTE: objects are ref-counted, so this should be cheap
                    break Ok(entry.get().clone());
                }
                Entry::Vacant(entry) => {
                    var = entry.into_key();

                    let Some(mut enclosing) = env.enclosing else {
                        break Err(span.throw(format!("Undefined variable '{var}'.")));
                    };

                    // SAFETY: Scope contexts are created from an exclusive reference to the parent
                    // environment, which remains valid until the block is fully interpreted.
                    env = unsafe { enclosing.as_mut() };
                }
            }
        }
    }

    fn get(&self, var: &str, span: &Span) -> Result<Value, RuntimeError> {
        let mut env = self;

        loop {
            match env.bindings.get(var) {
                // NOTE: objects are ref-counted, so this should be cheap
                Some(val) => break Ok(val.clone()),

                None => {
                    let Some(enclosing) = env.enclosing else {
                        break Err(span.throw(format!("Undefined variable '{var}'.")));
                    };

                    // SAFETY: Scope contexts are created from an exclusive reference to the parent
                    // environment, which remains valid until the block is fully interpreted.
                    env = unsafe { enclosing.as_ref() };
                }
            }
        }
    }
}

struct Context<'a> {
    environment: Environment,
    globals: &'a mut Environment,
    writer: &'a mut dyn Write,
}

impl<'a> Context<'a> {
    fn new<W: Write>(globals: &'a mut Environment, writer: &'a mut W) -> Self {
        Self {
            // SAFETY: we keep &mut globals around for the whole lifetime of this context
            environment: unsafe { globals.scope() },
            globals,
            writer,
        }
    }
}

trait Evaluate {
    fn evaluate(&self, cx: &mut Context) -> Result<Value, RuntimeError>;
}

impl Evaluate for Expr {
    #[inline]
    fn evaluate(&self, cx: &mut Context) -> Result<Value, RuntimeError> {
        match self {
            Self::Atom(atom) => atom.evaluate(cx),
            Self::Cons(cons) => cons.evaluate(cx),
        }
    }
}

impl Evaluate for Atom {
    #[inline]
    fn evaluate(&self, cx: &mut Context) -> Result<Value, RuntimeError> {
        Ok(match &self.literal {
            Literal::Var(x) => cx.environment.get(x, &self.span)?,
            Literal::Str(s) => Value::obj(Rc::clone(s)),
            Literal::Num(n) => Value::new(*n),
            Literal::Bool(b) => Value::new(*b),
            Literal::Nil => Value::Nil,
        })
    }
}

impl Evaluate for Cons {
    fn evaluate(&self, cx: &mut Context) -> Result<Value, RuntimeError> {
        #[inline]
        fn binary_args(args: &[Expr]) -> Option<(&Expr, &Expr)> {
            match args {
                [lhs, rhs] => Some((lhs, rhs)),
                _ => None,
            }
        }

        match self.op {
            Operator::Equal => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be l-value and r-value."));
                };

                // TODO: generalize to regions/places/locations where values can be assigned to
                let Expr::Atom(Atom {
                    literal: Literal::Var(var),
                    ..
                }) = lhs
                else {
                    return Err(self.span.throw("Operands must be l-value and r-value."));
                };

                let val = rhs.evaluate(cx)?;

                // NOTE: assignment evaluates to the expression (rhs) value
                //  - This is for cases such as `var a = b = 1;`
                cx.environment.assign(var, val, &self.span)
            }

            Operator::Bang => match self.args.as_slice() {
                [rhs] => {
                    let value = rhs.evaluate(cx)?;
                    Ok(Value::new(!bool::from(value)))
                }
                _ => Err(self.span.throw("Operand must be an expression.")),
            },

            Operator::And => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be two expressions."));
                };

                let lhs = lhs.evaluate(cx)?;

                if bool::from(&lhs) {
                    rhs.evaluate(cx)
                } else {
                    Ok(lhs)
                }
            }

            Operator::Or => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be two expressions."));
                };

                let lhs = lhs.evaluate(cx)?;

                if bool::from(&lhs) {
                    Ok(lhs)
                } else {
                    rhs.evaluate(cx)
                }
            }

            Operator::Plus => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self
                        .span
                        .throw("Operands must be two numbers or two strings."));
                };

                let Value::Object(Object(lhs)) = lhs.evaluate(cx)? else {
                    return Err(self
                        .span
                        .throw("Operands must be two numbers or two strings."));
                };

                let Value::Object(Object(rhs)) = rhs.evaluate(cx)? else {
                    return Err(self
                        .span
                        .throw("Operands must be two numbers or two strings."));
                };

                if let (Some(lhs), Some(rhs)) =
                    (lhs.downcast_ref::<f64>(), rhs.downcast_ref::<f64>())
                {
                    return Ok(Value::new(lhs + rhs));
                }

                match (lhs.downcast_ref::<String>(), rhs.downcast_ref::<String>()) {
                    (Some(left), Some(right)) => {
                        let mut s = String::with_capacity(left.len() + right.len());
                        s.push_str(left);
                        s.push_str(right);
                        Ok(Value::new(s))
                    }
                    _ => Err(self
                        .span
                        .throw("Operands must be two numbers or two strings.")),
                }
            }

            Operator::Minus => match self.args.as_slice() {
                [rhs] => {
                    let rhs = rhs.evaluate(cx)?;
                    rhs.map::<f64>(|v| -*v)
                        .map_err(|_| self.span.throw("Operand must be a number."))
                }
                [lhs, rhs] => {
                    let lhs = lhs.evaluate(cx)?;
                    let rhs = rhs.evaluate(cx)?;

                    lhs.combine::<f64, f64>(rhs, |x, y| x - y)
                        .map_err(|_| self.span.throw("Operands must be numbers."))
                }
                _ => Err(self
                    .span
                    .throw("Operands must be two numbers or two strings.")),
            },

            Operator::Slash => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, f64>(rhs, |x, y| x / y)
                    .map_err(|_| self.span.throw("Operands must be numbers."))
            }

            Operator::Star => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, f64>(rhs, |x, y| x * y)
                    .map_err(|_| self.span.throw("Operands must be numbers."))
            }

            Operator::Greater => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, bool>(rhs, |x, y| x > y)
                    .map_err(|_| self.span.throw("Operands must be numbers."))
            }

            Operator::GreaterEqual => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, bool>(rhs, |x, y| x >= y)
                    .map_err(|_| self.span.throw("Operands must be numbers."))
            }

            Operator::Less => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, bool>(rhs, |x, y| x < y)
                    .map_err(|_| self.span.throw("Operands must be numbers."))
            }

            Operator::LessEqual => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                lhs.combine::<f64, bool>(rhs, |x, y| x <= y)
                    .map_err(|_| self.span.throw("Operands must be numbers."))
            }

            Operator::BangEqual => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                Ok(Value::new(lhs != rhs))
            }

            Operator::EqualEqual => {
                let Some((lhs, rhs)) = binary_args(&self.args) else {
                    return Err(self.span.throw("Operands must be numbers."));
                };

                let lhs = lhs.evaluate(cx)?;
                let rhs = rhs.evaluate(cx)?;

                Ok(Value::new(lhs == rhs))
            }

            Operator::LeftParen => match self.args.as_slice() {
                [expr] => expr.evaluate(cx),
                _ => Err(self.span.throw("Operand must be an expression.")),
            },

            // XXX: unify with LeftParen (i.e., use LeftParen for both groups and fun calls)
            //  - issue: impl Display for Operator (`(group <arg0>)` vs `(<arg0>)`)
            Operator::Call => {
                let arg0 = match self.args.as_slice() {
                    [expr, ..] => expr.evaluate(cx)?,
                    _ => return Err(self.span.throw("Operand must be an expression.")),
                };

                let Value::Object(Object(arg0)) = arg0 else {
                    return Err(self.span.throw("Can only call functions and classes."));
                };

                let Some(callee) = arg0.downcast_ref::<Callable>() else {
                    return Err(self.span.throw("Can only call functions and classes."));
                };

                // evaluate arguments
                let mut args = Vec::with_capacity(self.args.len() - 1);
                for arg in self.args.iter().skip(1) {
                    let arg = arg.evaluate(cx)?;
                    args.push(arg);
                }

                if args.len() != callee.arity() {
                    let error = format!(
                        "Expected {} arguments but got {}.",
                        callee.arity(),
                        args.len(),
                    );
                    return Err(self.span.throw(error));
                }

                // NOTE: due to function calls, evaluate may have side-effects
                callee.call(args, cx)
            }
        }
    }
}

trait Interpret {
    fn interpret(&self, cx: &mut Context) -> Result<(), RuntimeError>;
}

impl Interpret for Program {
    #[inline]
    fn interpret(&self, cx: &mut Context) -> Result<(), RuntimeError> {
        self.0.iter().try_for_each(|decl| decl.interpret(cx))
    }
}

impl Interpret for Decl {
    #[inline]
    fn interpret(&self, cx: &mut Context) -> Result<(), RuntimeError> {
        match self {
            Self::Var(var) => var.interpret(cx),
            Self::Stmt(stmt) => stmt.interpret(cx),
        }
    }
}

impl Interpret for Var {
    fn interpret(&self, cx: &mut Context) -> Result<(), RuntimeError> {
        let value = self
            .expr
            .as_ref()
            .map(|expr| expr.evaluate(cx))
            .transpose()?;

        cx.environment.define(&self.ident, value);
        Ok(())
    }
}

impl Interpret for Stmt {
    #[inline]
    fn interpret(&self, cx: &mut Context) -> Result<(), RuntimeError> {
        match self {
            Self::Block(block) => block.interpret(cx),
            Self::If(if_stmt) => if_stmt.interpret(cx),
            Self::While(while_stmt) => while_stmt.interpret(cx),
            Self::Expr(expr) => expr.evaluate(cx).map(|_| ()),
            Self::Print(print) => print.interpret(cx),
        }
    }
}

impl Interpret for Block {
    #[inline]
    fn interpret(&self, cx: &mut Context) -> Result<(), RuntimeError> {
        let mut local = Context {
            // SAFETY: `local` remains valid for the remainder of this block's interpretation
            environment: unsafe { cx.environment.scope() },
            globals: cx.globals,
            writer: cx.writer,
        };

        self.decls
            .iter()
            .try_for_each(|decl| decl.interpret(&mut local))
    }
}

impl Interpret for If {
    fn interpret(&self, cx: &mut Context) -> Result<(), RuntimeError> {
        let cond = self.cond.evaluate(cx)?;

        if cond.into() {
            self.then_branch.interpret(cx)?;
        } else if let Some(ref else_branch) = self.else_branch {
            else_branch.interpret(cx)?;
        }

        Ok(())
    }
}

impl Interpret for While {
    fn interpret(&self, cx: &mut Context) -> Result<(), RuntimeError> {
        while self.cond.evaluate(cx)?.into() {
            self.body.interpret(cx)?;
        }
        Ok(())
    }
}

impl Interpret for Print {
    fn interpret(&self, cx: &mut Context) -> Result<(), RuntimeError> {
        let value = self.expr.evaluate(cx)?;
        writeln!(cx.writer, "{value}").map_err(move |error| self.span.throw(error))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::io::BufWriter;

    #[test]
    fn scoped_blocks() {
        let input = include_str!("../tests/ui/run/scopes/test_case_1.lox");
        let expected = include_str!("../tests/ui/run/scopes/test_case_1.out");

        let mut writer = BufWriter::new(Vec::new());

        let program = input.parse().expect("valid program");
        interpret(program, &mut writer).expect("no runtime error");

        let buf = writer.into_inner().expect("failed to flush");
        let actual = String::from_utf8(buf).expect("UTF-8 interpreter output");

        assert_eq!(expected, actual);
    }
}
