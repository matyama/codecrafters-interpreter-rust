use std::any::Any;
use std::cell::RefCell;
use std::collections::hash_map::{Entry, HashMap};
use std::fmt::Display;
use std::io::Write;
use std::mem;
use std::ops::ControlFlow;
use std::rc::Rc;

use crate::error::{RuntimeError, ThrowRuntimeError as _};
use crate::span::Span;
use crate::token::{SUPER, THIS};

use super::ir::{self, Atom, Cons, Expr, Literal, Operator, Program};

type RcCell<T> = Rc<RefCell<T>>;

#[inline]
pub fn evaluate<W: Write>(ast: ir::Ast<Expr>, writer: &mut W) -> Result<Value, RuntimeError> {
    let ir::Ast { tree, meta } = ast;
    let mut cx = Context::new(meta, writer);
    tree.evaluate(&mut cx)
}

#[inline]
pub fn interpret<W: Write>(ast: ir::Ast<Program>, writer: &mut W) -> Result<(), RuntimeError> {
    let ir::Ast { tree, meta } = ast;
    let mut cx = Context::new(meta, writer);
    tree.interpret(&mut cx).map(|_| ())
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

    fn downcast_display(&self) -> Option<&dyn Display> {
        match self {
            Self::Object(Object(obj)) => {
                if let Some(f) = obj.downcast_ref::<Native>() {
                    return Some(f);
                }

                if let Some(f) = obj.downcast_ref::<Function>() {
                    return Some(f);
                }

                if let Some(class) = obj.downcast_ref::<Class>() {
                    return Some(class);
                }

                if let Some(instance) = obj.downcast_ref::<Instance>() {
                    return Some(instance);
                }

                None
            }
            Self::Nil => None,
        }
    }

    fn downcast_callable(&self) -> Option<Rc<dyn Call>> {
        match self {
            Self::Object(Object(obj)) => {
                if let Ok(f) = Rc::clone(obj).downcast::<Native>() {
                    return Some(f);
                }

                if let Ok(f) = Rc::clone(obj).downcast::<Function>() {
                    return Some(f);
                }

                if let Ok(class) = Rc::clone(obj).downcast::<Class>() {
                    return Some(class);
                }

                None
            }
            Self::Nil => None,
        }
    }

    fn downcast_class(&self) -> Option<Rc<Class>> {
        match self {
            Self::Object(Object(obj)) => Rc::clone(obj).downcast::<Class>().ok(),
            Self::Nil => None,
        }
    }

    fn downcast_instance(&self) -> Option<Rc<Instance>> {
        match self {
            Self::Object(Object(obj)) => Rc::clone(obj).downcast::<Instance>().ok(),
            Self::Nil => None,
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

    fn call(self: Rc<Self>, args: Vec<Value>, cx: &mut Context) -> Result<Value, RuntimeError>;
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

/// Built-in (native) function
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
    fn call(self: Rc<Self>, args: Vec<Value>, cx: &mut Context) -> Result<Value, RuntimeError> {
        debug_assert_eq!(args.len(), self.arity);
        (self.func)(args, cx)
    }
}

#[derive(Debug)]
struct Function {
    /// representation of function's parameters and body
    declaration: Rc<ir::Function>,
    /// environment holding the surrounding variables where the function is declared
    closure: RcCell<Environment>,
    /// flag indicating whether this function/method is a constructor `init()`
    initializer: bool,
}

impl Function {
    /// Bind new implicit variable called `this` to given `instance`.
    ///
    /// This method wraps the closure in `self` by a new environment which contains the implicit
    /// definition: `var this = instance;`.
    fn bind(self: Rc<Self>, instance: Rc<Instance>) -> Self {
        let closure = Environment::scope(Rc::clone(&self.closure));
        closure
            .borrow_mut()
            .define(THIS, Some(Value::obj(instance)));

        Self {
            declaration: Rc::clone(&self.declaration),
            closure,
            initializer: self.initializer,
        }
    }
}

impl Display for Function {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<fn {}>", self.declaration.name)
    }
}

impl Call for Function {
    #[inline]
    fn arity(&self) -> usize {
        self.declaration.params.len()
    }

    fn call(self: Rc<Self>, args: Vec<Value>, cx: &mut Context) -> Result<Value, RuntimeError> {
        // create fresh environment (initialized from this function's closure)
        let environment = Environment::scope(Rc::clone(&self.closure));

        let prev = mem::replace(&mut cx.environment, environment);

        // associate all parameters with their corresponding argument values
        {
            let mut env = cx.environment.borrow_mut();
            for (param, value) in self.declaration.params.iter().zip(args) {
                env.define(param.name(), Some(value));
            }
        }

        // execute function's body under the appropriate context
        let result = self.declaration.body.interpret(cx).and_then(|v| match v {
            // NOTE: Lox defined the implicit return value from an initializer to be the instance
            ControlFlow::Break(_) | ControlFlow::Continue(_) if self.initializer => {
                Environment::get_at(Rc::clone(&self.closure), 0, THIS, &self.declaration.span)
            }
            ControlFlow::Break(v) => Ok(v),
            ControlFlow::Continue(()) => Ok(Value::Nil),
        });

        // restore previous environment before returning
        cx.environment = prev;

        result
    }
}

// TODO: Challenge 1 & 2 (https://craftinginterpreters.com/classes.html#challenges)
//  - Add support for _static_ methods that can be called directly on the class object itself.
//  - Extend Lox to support getter methods.
#[derive(Debug)]
struct Class {
    name: String,
    superclass: Option<Rc<Class>>,
    methods: HashMap<String, Rc<Function>>,
}

impl Class {
    const INIT: &'static str = "init";

    fn find_method(&self, name: &str) -> Option<Rc<Function>> {
        self.methods.get(name).cloned().or_else(|| {
            // if not found here, try to look for it up in the inheritance hierarchy
            self.superclass
                .as_ref()
                .and_then(|superclass| superclass.find_method(name))
        })
    }
}

impl Display for Class {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Call for Class {
    #[inline]
    fn arity(&self) -> usize {
        self.find_method(Self::INIT).map_or(0, |init| init.arity())
    }

    fn call(self: Rc<Self>, args: Vec<Value>, cx: &mut Context) -> Result<Value, RuntimeError> {
        let instance = Rc::new(Instance {
            class: Rc::clone(&self),
            fields: RefCell::new(HashMap::new()),
        });

        // bind and call the constructor (if defined)
        if let Some(init) = self.find_method(Self::INIT) {
            let instance = Rc::clone(&instance);
            let init = Rc::new(init.bind(instance));
            let _ = init.call(args, cx)?;
        }

        Ok(Value::obj(instance))
    }
}

#[derive(Debug)]
struct Instance {
    class: Rc<Class>,
    fields: RefCell<HashMap<String, Value>>,
}

impl Instance {
    fn get(self: Rc<Self>, name: &str, span: &Span) -> Result<Value, RuntimeError> {
        self.fields
            .borrow()
            .get(name)
            .cloned()
            .or_else(|| {
                let this = Rc::clone(&self);
                self.class
                    .find_method(name)
                    .map(|method| method.bind(this))
                    .map(Value::new)
            })
            .ok_or_else(|| RuntimeError {
                span: *span,
                source: format!("Undefined property '{name}'.").into(),
            })
    }

    fn set(&self, name: &str, value: Value) {
        let _ = self.fields.borrow_mut().insert(name.to_string(), value);
    }
}

impl Display for Instance {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} instance", self.class.name)
    }
}

// TODO: Challenge 4 (https://craftinginterpreters.com/resolving-and-binding.html#challenges)
//
// Our resolver calculates which environment the variable is found in, but it’s still looked up by
// name in that map. A more efficient environment representation would store local variables in an
// array and look them up by index.
//
// Extend the resolver to associate a unique index for each local variable declared in a scope.
// When resolving a variable access, look up both the scope the variable is in and its index and
// store that. In the interpreter, use that to quickly access a variable by its index instead of
// using a map.

#[derive(Debug, Default)]
struct Environment {
    /// (global) bindings of variable names to their values
    bindings: HashMap<String, Value>,
    /// parent context (`None` indicates the global scope)
    enclosing: Option<RcCell<Environment>>,
}

impl Environment {
    fn global() -> Self {
        let mut globals = Self::default();

        // initialize global environment with native functions
        {
            let clock = Native {
                func: clock,
                arity: 0,
            };

            globals.define("clock", Some(Value::new(clock)));
        }

        globals
    }

    fn scope(enclosing: RcCell<Self>) -> RcCell<Self> {
        Rc::new(RefCell::new(Self {
            bindings: HashMap::new(),
            enclosing: Some(enclosing),
        }))
    }

    #[inline]
    fn define(&mut self, var: &str, val: Option<Value>) {
        self.bindings
            .insert(var.to_string(), val.unwrap_or_default());
    }

    /// Register new assignment `var := val` and return new `val`
    fn assign(
        mut this: RcCell<Self>,
        var: &str,
        val: Value,
        span: &Span,
    ) -> Result<Value, RuntimeError> {
        let mut var = var.to_string();
        loop {
            let mut env = this.borrow_mut();

            match env.bindings.entry(var) {
                Entry::Occupied(mut entry) => {
                    let _ = entry.insert(val);
                    // NOTE: objects are ref-counted, so this should be cheap
                    break Ok(entry.get().clone());
                }
                Entry::Vacant(entry) => {
                    var = entry.into_key();

                    let enclosing = env
                        .enclosing
                        .clone()
                        .ok_or_else(|| span.throw(format!("Undefined variable '{var}'.")))?;

                    drop(env);
                    this = enclosing;
                }
            }
        }
    }

    fn assign_at(
        this: RcCell<Self>,
        dist: usize,
        var: &str,
        val: Value,
        span: &Span,
    ) -> Result<Value, RuntimeError> {
        let Some(env) = Self::ancestor(this, dist) else {
            return Err(span.throw(format!("Undefined variable '{var}'.")));
        };

        let mut env = env.borrow_mut();

        match env.bindings.entry(var.to_string()) {
            Entry::Occupied(mut entry) => {
                let _ = entry.insert(val);
                // NOTE: objects are ref-counted, so this should be cheap
                Ok(entry.get().clone())
            }
            Entry::Vacant(entry) => Ok(entry.insert(val).clone()),
        }
    }

    fn get(mut this: RcCell<Self>, var: &str, span: &Span) -> Result<Value, RuntimeError> {
        loop {
            let env = this.borrow();
            match env.bindings.get(var) {
                // NOTE: objects are ref-counted, so this should be cheap
                Some(val) => break Ok(val.clone()),

                None => {
                    let enclosing = env
                        .enclosing
                        .clone()
                        .ok_or_else(|| span.throw(format!("Undefined variable '{var}'.")))?;

                    drop(env);
                    this = enclosing;
                }
            }
        }
    }

    fn get_at(
        this: RcCell<Self>,
        dist: usize,
        var: &str,
        span: &Span,
    ) -> Result<Value, RuntimeError> {
        Self::ancestor(this, dist)
            .and_then(|env| env.borrow().bindings.get(var).cloned())
            .ok_or_else(|| span.throw(format!("Undefined variable '{var}'.")))
    }

    fn ancestor(mut this: RcCell<Self>, dist: usize) -> Option<RcCell<Self>> {
        for _ in 0..dist {
            let env = this.borrow();
            let enclosing = this.borrow().enclosing.clone()?;
            drop(env);
            this = enclosing;
        }
        Some(this)
    }
}

struct Context<'a> {
    environment: RcCell<Environment>,
    globals: RcCell<Environment>,
    locals: HashMap<u64, usize>,
    // TODO: use this in lookup and possibly Environment
    #[allow(dead_code)]
    idents: HashMap<u64, String>,
    writer: &'a mut dyn Write,
}

impl<'a> Context<'a> {
    fn new<W: Write>(meta: ir::Metadata, writer: &'a mut W) -> Self {
        let globals = Rc::new(RefCell::new(Environment::global()));
        Self {
            environment: Rc::clone(&globals),
            globals,
            locals: meta.locals,
            idents: meta.idents,
            writer,
        }
    }

    fn lookup(&self, id: u64, name: &str, span: &Span) -> Result<Value, RuntimeError> {
        if let Some(&dist) = self.locals.get(&id) {
            Environment::get_at(Rc::clone(&self.environment), dist, name, span)
        } else {
            Environment::get(Rc::clone(&self.globals), name, span)
        }
    }
}

impl std::fmt::Debug for Context<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Context")
            .field("environment", &self.environment)
            .field("globals", &self.globals)
            .finish_non_exhaustive()
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
    fn evaluate(&self, cx: &mut Context) -> Result<Value, RuntimeError> {
        match &self.literal {
            Literal::Ident(id, name) => cx.lookup(*id, name, &self.span),
            Literal::Str(s) => Ok(Value::obj(Rc::clone(s))),
            Literal::Num(n) => Ok(Value::new(*n)),
            Literal::Bool(b) => Ok(Value::new(*b)),
            Literal::Nil => Ok(Value::Nil),
        }
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

                match lhs {
                    // variable assignment (e.g., x = 42)
                    Expr::Atom(Atom {
                        literal: Literal::Ident(id, var),
                        ..
                    }) => {
                        let val = rhs.evaluate(cx)?;

                        // NOTE: assignment evaluates to the expression (rhs) value
                        //  - This is for cases such as `var a = b = 1;`

                        if let Some(&dist) = cx.locals.get(id) {
                            let env = Rc::clone(&cx.environment);
                            Environment::assign_at(env, dist, var, val, &self.span)
                        } else {
                            let env = Rc::clone(&cx.globals);
                            Environment::assign(env, var, val, &self.span)
                        }
                    }

                    // set expression (e.g., obj.prop = 42)
                    Expr::Cons(Cons {
                        op: Operator::Dot,
                        args,
                        ..
                    }) => match args.as_slice() {
                        [obj, Expr::Atom(Atom {
                            literal: Literal::Ident(_, prop),
                            span,
                        })] => {
                            let Some(obj) = obj.evaluate(cx)?.downcast_instance() else {
                                return Err(span.throw("Only instances have fields."));
                            };

                            let val = rhs.evaluate(cx)?;

                            obj.set(prop, val.clone());

                            Ok(val)
                        }
                        _ => Err(self.span.throw("Operands must be l-value and r-value.")),
                    },

                    _ => Err(self.span.throw("Operands must be l-value and r-value.")),
                }
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

                let Some(callee) = arg0.downcast_callable() else {
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

            Operator::Dot => match binary_args(&self.args) {
                // calling superclass methods
                Some((
                    ir::Expr::Atom(ir::Atom {
                        literal: ir::Literal::Ident(id, name),
                        ..
                    }),
                    ir::Expr::Atom(ir::Atom {
                        literal: ir::Literal::Ident(_, method),
                        ..
                    }),
                )) if name == SUPER => {
                    // lookup `super` class definition
                    let Some(&dist) = cx.locals.get(id) else {
                        return Err(self.span.throw("Undefined reference to 'super'."));
                    };

                    let superclass =
                        Environment::get_at(Rc::clone(&cx.environment), dist, SUPER, &self.span)?;

                    let Some(superclass) = superclass.downcast_class() else {
                        return Err(self.span.throw("Operand 'super' must be a class."));
                    };

                    // lookup `this` in an environment that is inside the env. where `super` is
                    let object = Environment::get_at(
                        Rc::clone(&cx.environment),
                        dist - 1,
                        THIS,
                        &self.span,
                    )?;

                    let Some(instance) = object.downcast_instance() else {
                        return Err(self.span.throw("Only instances can bind methods."));
                    };

                    // lookup the `super` method and bind it to `this`
                    let method = superclass.find_method(method).ok_or_else(|| {
                        self.span.throw(format!("Undefined property '{method}'."))
                    })?;

                    Ok(Value::new(method.bind(instance)))
                }

                // property access
                Some((obj, prop)) => {
                    let obj = obj.evaluate(cx)?;

                    let Some(instance) = obj.downcast_instance() else {
                        return Err(self.span.throw("Only instances have properties."));
                    };

                    match prop {
                        Expr::Atom(Atom {
                            literal: Literal::Ident(_, name),
                            span,
                        }) => instance.get(name, span),

                        expr => Err(expr.span().throw("Invalid property type.")),
                    }
                }

                None => Err(self.span.throw("Operands must be two expressions.")),
            },
        }
    }
}

trait Interpret {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError>;
}

impl Interpret for Program {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        for decl in self.0.iter() {
            if let ret @ ControlFlow::Break(_) = decl.interpret(cx)? {
                return Ok(ret);
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

impl Interpret for ir::Decl {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        match self {
            Self::Class(class) => class.interpret(cx),
            Self::Fun(fun) => fun.interpret(cx),
            Self::Var(var) => var.interpret(cx),
            Self::Stmt(stmt) => stmt.interpret(cx),
        }
    }
}

impl Interpret for ir::Class {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        let superclass = if let Some(ref superclass) = self.superclass {
            match superclass.evaluate(cx)?.downcast_class() {
                None => return Err(self.span.throw("Superclass must be a class.")),
                superclass => superclass,
            }
        } else {
            None
        };

        cx.environment.borrow_mut().define(&self.name, None);

        let closure = if let Some(superclass) = superclass.as_ref().cloned() {
            // bind `super` to the superclass inside a new wrapping environment
            let env = Environment::scope(Rc::clone(&cx.environment));
            env.borrow_mut().define(SUPER, Some(Value::obj(superclass)));
            env
        } else {
            Rc::clone(&cx.environment)
        };

        let methods = HashMap::from_iter(self.methods.iter().cloned().map(|method| {
            let initializer = method.name == Class::INIT;
            (
                method.name.clone(),
                Rc::new(Function {
                    declaration: method,
                    closure: Rc::clone(&closure),
                    initializer,
                }),
            )
        }));

        let class = Value::new(Class {
            // XXX: Rc::clone(&self.name)
            name: self.name.to_string(),
            superclass,
            methods,
        });

        Environment::assign(Rc::clone(&cx.environment), &self.name, class, &self.span)
            .map(|_| ControlFlow::Continue(()))
    }
}

impl Interpret for ir::Fun {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        let ident = &self.func.name;

        // capture the environment in which the function is declared
        let func = Function {
            declaration: Rc::clone(&self.func),
            closure: Rc::clone(&cx.environment),
            initializer: false,
        };

        cx.environment
            .borrow_mut()
            .define(ident, Some(Value::new(func)));

        Ok(ControlFlow::Continue(()))
    }
}

impl Interpret for ir::Var {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        let value = self
            .expr
            .as_ref()
            .map(|expr| expr.evaluate(cx))
            .transpose()?;

        cx.environment.borrow_mut().define(self.ident.name(), value);
        Ok(ControlFlow::Continue(()))
    }
}

impl Interpret for ir::Stmt {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        match self {
            Self::Block(block) => block.interpret(cx),
            Self::If(if_stmt) => if_stmt.interpret(cx),
            Self::While(while_stmt) => while_stmt.interpret(cx),
            Self::Expr(expr) => expr.evaluate(cx).map(|_| ControlFlow::Continue(())),
            Self::Print(print) => print.interpret(cx),
            Self::Return(ret) => ret.interpret(cx),
        }
    }
}

impl Interpret for ir::Block {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        let environment = Environment::scope(Rc::clone(&cx.environment));

        let prev = mem::replace(&mut cx.environment, environment);

        for decl in self.decls.iter() {
            if let ret @ ControlFlow::Break(_) = decl.interpret(cx)? {
                let _ = mem::replace(&mut cx.environment, prev);
                return Ok(ret);
            }
        }

        let _ = mem::replace(&mut cx.environment, prev);
        Ok(ControlFlow::Continue(()))
    }
}

impl Interpret for ir::If {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        if self.cond.evaluate(cx)?.into() {
            self.then_branch.interpret(cx)
        } else if let Some(ref else_branch) = self.else_branch {
            else_branch.interpret(cx)
        } else {
            Ok(ControlFlow::Continue(()))
        }
    }
}

impl Interpret for ir::While {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        while self.cond.evaluate(cx)?.into() {
            if let ret @ ControlFlow::Break(_) = self.body.interpret(cx)? {
                return Ok(ret);
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

impl Interpret for ir::Print {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        let value = self.expr.evaluate(cx)?;

        // NOTE: Call instances can be printed, but panic if behind a Value::Object / Any
        if let Some(value) = value.downcast_display() {
            writeln!(cx.writer, "{value}")
        } else {
            writeln!(cx.writer, "{value}")
        }
        .map(ControlFlow::Continue)
        .map_err(move |error| self.span.throw(error))
    }
}

impl Interpret for ir::Return {
    fn interpret(&self, cx: &mut Context) -> Result<ControlFlow<Value>, RuntimeError> {
        self.value
            .as_ref()
            .map(|v| v.evaluate(cx))
            .transpose()
            .map(|v| v.unwrap_or_default())
            .map(ControlFlow::Break)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tree_walk::resolver::resolve;
    use std::io::BufWriter;

    #[test]
    fn scoped_blocks() {
        let input = include_str!("../../tests/ui/run/scopes/test_case_1.lox");
        let expected = include_str!("../../tests/ui/run/scopes/test_case_1.out");

        let mut writer = BufWriter::new(Vec::new());

        let ast = input
            .parse()
            .and_then(|ast| resolve(input, ast))
            .expect("valid program");

        interpret(ast, &mut writer).expect("no runtime error");

        let buf = writer.into_inner().expect("failed to flush");
        let actual = String::from_utf8(buf).expect("UTF-8 interpreter output");

        assert_eq!(expected, actual);
    }
}
