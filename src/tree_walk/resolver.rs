use std::collections::hash_map::{Entry, HashMap};
use std::mem;
use std::ops::{Deref, DerefMut};

use crate::error::{ErrLoc, SyntaxError};
use crate::span::Span;
use crate::token::{Keyword, SUPER, THIS};

use super::ir;

pub fn resolve<T: Resolve>(source: &str, ast: ir::Ast<T>) -> Result<ir::Ast<T>, SyntaxError> {
    let ir::Ast { tree, meta } = ast;

    let mut cx = Context::new(source, meta);
    tree.resolve(&mut cx)?;

    Ok(ir::Ast {
        tree,
        meta: cx.meta,
    })
}

/// Block scope containing a mapping from identifier names to their initialization state
#[derive(Debug, Default)]
#[repr(transparent)]
struct Scope(HashMap<String, bool>);

impl Scope {
    /// Returns true if given name is in this scope and has not been initialized
    ///
    /// I.e., the key `name` is present and the associated value is `false`.
    #[inline]
    fn is_undefined(&self, name: &str) -> bool {
        !self.get(name).unwrap_or(&true)
    }
}

impl Deref for Scope {
    type Target = HashMap<String, bool>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Scope {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Clone, Copy, Debug, Default)]
enum FunctionType {
    #[default]
    None,
    Function,
    Initializer,
    Method,
}

#[derive(Debug, Default)]
enum ClassType {
    #[default]
    None,
    Class,
    SubClass,
}

// Optimization for single deferred identifier, so we don't have to allocate
#[derive(Debug)]
enum Deferred {
    Ident(u64, usize),
    Idents(Vec<(u64, usize)>),
}

#[derive(Debug)]
pub(crate) struct Context<'a> {
    source: &'a str,

    /// Stack of local block [Scope]s.
    ///
    /// Variables declared at the top level in the global scope are not tracked. I.e., if a
    /// variable cannot be found here, it can be assumed to be global.
    scopes: Vec<Scope>,

    // TODO: limit to function identifiers only
    /// Set of identifier names with deferred resolution
    ///
    /// The mapping is from identifier name to a pair of AST node id and resolution scope depth.
    /// This mapping is used to resolve calls to functions with an unresolved (not yet at least)
    /// declaration which, however, appears in later parts of the AST (possibly at a lower depth).
    ///
    /// An example of this can be two mutually recursive functions, where by necessity the
    /// declaration of one follows the declaration of the other.
    deferred: HashMap<String, Deferred>,

    /// Field indicating whether the code being currently resolved is inside a function declaration
    current_fn: FunctionType,

    /// Field indicating whether the code being currently resolved is inside a class declaration
    current_class: ClassType,

    /// Metadata associated with AST nodes
    meta: ir::Metadata,
}

impl<'a> Context<'a> {
    #[inline]
    pub(crate) fn new(source: &'a str, meta: ir::Metadata) -> Self {
        Self {
            source,
            scopes: Vec::new(),
            deferred: HashMap::new(),
            current_fn: FunctionType::default(),
            current_class: ClassType::default(),
            meta,
        }
    }

    /// Run given function inside [`Scope`]ed context if the condition `guard()` is true.
    ///
    /// Note that the function is _always_ executed within this context, the guard condition only
    /// determines whether a new [`Scope`] is created before (and destroyed after) calling `f`.
    fn with_scope_if<F, G, R>(&mut self, guard: G, mut f: F) -> R
    where
        F: FnMut(&mut Self) -> R,
        G: Fn() -> bool,
    {
        let scoped = guard();
        if scoped {
            self.scopes.push(Scope::default());
        }
        let result = f(self);
        if scoped {
            self.scopes.pop();
        }
        result
    }

    /// Run given function inside [`Scope`]ed context
    fn with_scope<F, R>(&mut self, mut f: F) -> R
    where
        F: FnMut(&mut Self) -> R,
    {
        self.scopes.push(Scope::default());
        let result = f(self);
        self.scopes.pop();
        result
    }

    /// Adds `name` to the innermost scope (shadowing any outer one with the same name).
    ///
    /// From this point, the variable will exist in the scope, but is marked as _unavailable_
    /// (i.e., not having its initializer expression resolved yet).
    fn declare(&mut self, name: &str, span: &Span) -> Result<(), SyntaxError> {
        if let Some(scope) = self.scopes.last_mut() {
            match scope.entry(name.to_string()) {
                // lox does not allow re-declaring the same var in local scopes (local shadowing)
                Entry::Occupied(entry) => {
                    return Err(SyntaxError::new(
                        self.source,
                        *span,
                        "Already a variable with this name in this scope.",
                        ErrLoc::at(entry.key()),
                    ));
                }
                Entry::Vacant(entry) => {
                    let _ = entry.insert(false);
                }
            }
        }

        Ok(())
    }

    /// Mark `name` in the innermost scope as being initialized.
    fn define(&mut self, name: &str) {
        if let Some(scope) = self.scopes.last_mut() {
            let Some(initialized) = scope.get_mut(name) else {
                panic!("defining a '{name}' that has not been declared");
            };
            *initialized = true;
        }
    }

    /// Marks `name` in the innermost [`Scope`] as initialized.
    ///
    /// This method does nothing if there is no scope.
    fn inject(&mut self, name: impl ToString) {
        if let Some(scope) = self.scopes.last_mut() {
            let _ = scope.insert(name.to_string(), true);
        }
    }

    #[inline]
    fn is_undefined(&self, name: &str) -> bool {
        self.scopes.last().is_some_and(|s| s.is_undefined(name))
    }

    fn resolve_local(&mut self, id: u64, name: &str) {
        // find the number of scopes between the current scope and where the variable is defined
        let dist = self.scopes.iter().rev().enumerate().find_map(|(i, s)| {
            if s.contains_key(name) {
                Some(i)
            } else {
                None
            }
        });

        if let Some(dist) = dist {
            self.meta.locals.insert(id, dist);
        } else {
            // TODO: limit inserts to function calls only
            // Depending on the AST traversal, function calls might precede corresponding function
            // declaration (at a lower depth), so defer resolution by registering current depth.
            self.defer_local(id, name, self.scopes.len());
        }
    }

    fn defer_local(&mut self, id: u64, name: &str, depth: usize) {
        match self.deferred.entry(name.to_string()) {
            Entry::Vacant(e) => {
                e.insert(Deferred::Ident(id, depth));
            }
            Entry::Occupied(mut e) => match e.get_mut() {
                Deferred::Ident(i, d) => {
                    let ids = vec![(*i, *d), (id, depth)];
                    e.insert(Deferred::Idents(ids));
                }
                Deferred::Idents(ids) => {
                    ids.push((id, depth));
                }
            },
        }
    }

    fn resolve_deferred(&mut self, name: &str) {
        let Some(deferred) = self.deferred.get_mut(name) else {
            return;
        };

        // respect lexical scoping, i.e., resolve only if the call happens "below" this fn def
        let def_depth = self.scopes.len();

        match deferred {
            Deferred::Ident(_, call_depth) if def_depth <= *call_depth => {
                // function can be declared only once in any scope, so remove the deferred entry
                let Some(Deferred::Ident(id, call_depth)) = self.deferred.remove(name) else {
                    unreachable!("got the entry before");
                };

                if let Entry::Vacant(e) = self.meta.locals.entry(id) {
                    // locals store the distance to the declaration
                    e.insert(call_depth - def_depth);
                }
            }

            Deferred::Ident(..) => {}

            Deferred::Idents(ids) => {
                let mut i = 0;
                while let Some((_, call_depth)) = ids.get(i) {
                    if def_depth <= *call_depth {
                        let (id, call_depth) = ids.swap_remove(i);
                        if let Entry::Vacant(e) = self.meta.locals.entry(id) {
                            // locals store the distance to the declaration
                            e.insert(call_depth - def_depth);
                        }
                    } else {
                        i += 1;
                    }
                }

                match ids.as_slice() {
                    [] => {
                        self.deferred.remove(name);
                    }
                    [(call_depth, id)] => *deferred = Deferred::Ident(*call_depth, *id),
                    _ => {}
                }
            }
        }
    }

    fn resolve_fn(
        &mut self,
        params: &[ir::Ident],
        body: &ir::Block,
        ty: FunctionType,
    ) -> Result<(), SyntaxError> {
        let enclosing_fn = mem::replace(&mut self.current_fn, ty);

        let result = self.with_scope(|cx| {
            for ir::Ident { name, span, .. } in params.iter() {
                cx.declare(name, span)?;
                cx.define(name);
            }

            // statically analyze function's body (note: at runtime this is deferred until called)
            body.resolve(cx)
        });

        self.current_fn = enclosing_fn;

        result
    }
}

// TODO: Challenge 3 (https://craftinginterpreters.com/resolving-and-binding.html#challenges)
//
// Extend the resolver to report an error if a local variable is never used.

pub(crate) trait Resolve {
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError>;
}

impl Resolve for ir::Expr {
    #[inline]
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        match self {
            Self::Atom(atom) => atom.resolve(cx),
            Self::Cons(cons) => cons.resolve(cx),
        }
    }
}

impl Resolve for ir::Atom {
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        let ir::Literal::Ident(id, ref name) = self.literal else {
            // literals other than variables don't require resolving
            return Ok(());
        };

        // check if the variable is being accessed inside its own initializer
        if cx.is_undefined(name) {
            return Err(SyntaxError::new(
                cx.source,
                self.span,
                "Can't read local variable in its own initializer.",
                ErrLoc::at(name),
            ));
        }

        match cx.current_class {
            ClassType::None if matches!(name.as_str(), SUPER | THIS) => {
                return Err(SyntaxError::new(
                    cx.source,
                    self.span,
                    format!("Can't use '{name}' outside of a class."),
                    ErrLoc::at(name),
                ));
            }
            ClassType::Class if name == SUPER => {
                return Err(SyntaxError::new(
                    cx.source,
                    self.span,
                    "Can't use 'super' in a class with no superclass.",
                    ErrLoc::at(name),
                ))
            }
            _ => {}
        }

        cx.resolve_local(id, name);

        Ok(())
    }
}

impl Resolve for ir::Cons {
    #[inline]
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        use ir::Operator::*;

        match self.op {
            Equal => match self.args.as_slice() {
                // variable assignment operator
                [ir::Expr::Atom(ir::Atom {
                    literal: ir::Literal::Ident(id, name),
                    ..
                }), value] => {
                    // first resolve the assigned value in case it references other variables
                    value.resolve(cx)?;

                    // resolve the variable that’s being assigned to
                    cx.resolve_local(*id, name);

                    Ok(())
                }

                // set expression: property itself is dynamically evaluated
                [ir::Expr::Cons(ir::Cons { op: Dot, args, .. }), value] => {
                    let [obj, _prop] = args.as_slice() else {
                        return Err(SyntaxError::new(
                            cx.source,
                            self.span,
                            "Operand must be a set expression",
                            ErrLoc::at(self.op),
                        ));
                    };

                    // first resolve the assigned value in case it references other variables
                    value.resolve(cx)?;

                    // then resolve the object in `obj.prop`
                    obj.resolve(cx)
                }

                _ => Err(SyntaxError::new(
                    cx.source,
                    self.span,
                    "Operands must be l-value and r-value.",
                    ErrLoc::at(self.op),
                )),
            },

            // properties are looked up dynamically (resolving object in `obj.prop`)
            Dot => self.args.iter().take(1).try_for_each(|arg| arg.resolve(cx)),

            // resolve all arguments for all the other operators
            _ => self.args.iter().try_for_each(|arg| arg.resolve(cx)),
        }
    }
}

impl Resolve for ir::Program {
    #[inline]
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        self.0.iter().try_for_each(|decl| decl.resolve(cx))
    }
}

impl Resolve for ir::Decl {
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        match self {
            Self::Class(class) => class.resolve(cx),
            Self::Fun(fun) => fun.resolve(cx),
            Self::Var(var) => var.resolve(cx),
            Self::Stmt(stmt) => stmt.resolve(cx),
        }
    }
}

impl Resolve for ir::Class {
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        let enclosing_class = mem::replace(&mut cx.current_class, ClassType::Class);

        // define class name in the surrounding scope
        cx.declare(&self.name, &self.span)?;
        cx.define(&self.name);

        match self.superclass.as_deref() {
            // detect and prevent inheritance loops: `class A < A {}`
            Some(ir::Expr::Atom(ir::Atom {
                literal: ir::Literal::Ident(_, super_name),
                ..
            })) if super_name == &self.name => {
                return Err(SyntaxError::new(
                    cx.source,
                    self.span,
                    "A class can't inherit from itself.",
                    ErrLoc::at(super_name),
                ));
            }

            // resolve superclass
            Some(superclass) => {
                cx.current_class = ClassType::SubClass;
                superclass.resolve(cx)?
            }

            // no inheritance relation
            None => {}
        }

        let result = cx.with_scope_if(
            || self.superclass.is_some(),
            |cx| {
                // inject `super` as an implicit variable into this scope
                cx.inject(Keyword::Super);

                cx.with_scope(|cx| {
                    // inject `this` as an implicit variable into this scope
                    cx.inject(Keyword::This);

                    for method in self.methods.iter() {
                        // determine declaration type
                        let ty = match method.name.as_str() {
                            "init" => FunctionType::Initializer,
                            _ => FunctionType::Method,
                        };

                        // resolve method's body
                        cx.resolve_fn(&method.params, &method.body, ty)?;

                        // resolve any deferred calls referring to this method declaration
                        cx.resolve_deferred(&method.name);
                    }

                    Ok(())
                })
            },
        );

        cx.current_class = enclosing_class;

        result
    }
}

impl Resolve for ir::Fun {
    #[inline]
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        self.func.resolve(cx)
    }
}

impl Resolve for ir::Function {
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        // define function's name in the surrounding scope
        cx.declare(&self.name, &self.span)?;
        cx.define(&self.name);

        // resolve function's body
        cx.resolve_fn(&self.params, &self.body, FunctionType::Function)?;

        // resolve any deferred calls referring to this function declaration
        cx.resolve_deferred(&self.name);

        Ok(())
    }
}

impl Resolve for ir::Stmt {
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        match self {
            Self::Block(block) => block.resolve(cx),
            Self::If(if_stmt) => if_stmt.resolve(cx),
            Self::While(while_stmt) => while_stmt.resolve(cx),
            Self::Expr(expr) => expr.resolve(cx),
            Self::Print(print) => print.resolve(cx),
            Self::Return(return_stmt) => return_stmt.resolve(cx),
        }
    }
}

impl Resolve for ir::Var {
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        let ir::Ident { name, span, .. } = &self.ident;

        cx.declare(name, span)?;

        if let Some(ref init) = self.expr {
            init.resolve(cx)?;
        }

        cx.define(name);

        Ok(())
    }
}

impl Resolve for ir::Block {
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        cx.with_scope(|cx| {
            for decl in self.decls.iter() {
                decl.resolve(cx)?;
            }
            Ok(())
        })
    }
}

impl Resolve for ir::If {
    // NOTE: static analysis ignores control flow (contrary to interpretation)
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        self.cond.resolve(cx)?;
        self.then_branch.resolve(cx)?;
        if let Some(ref else_branch) = self.else_branch {
            else_branch.resolve(cx)?;
        }
        Ok(())
    }
}

impl Resolve for ir::While {
    // NOTE: static analysis ignores control flow (contrary to interpretation)
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        self.cond.resolve(cx)?;
        self.body.resolve(cx)
    }
}

impl Resolve for ir::Print {
    #[inline]
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        self.expr.resolve(cx)
    }
}

impl Resolve for ir::Return {
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        match cx.current_fn {
            FunctionType::None => {
                return Err(SyntaxError::new(
                    cx.source,
                    self.span,
                    "Can't return from top-level code.",
                    ErrLoc::at(Keyword::Return),
                ));
            }

            FunctionType::Initializer if self.value.is_some() => {
                return Err(SyntaxError::new(
                    cx.source,
                    self.span,
                    "Can't return a value from an initializer.",
                    ErrLoc::at(Keyword::Return),
                ));
            }

            _ => {}
        }

        if let Some(ref value) = self.value {
            value.resolve(cx)
        } else {
            Ok(())
        }
    }
}
