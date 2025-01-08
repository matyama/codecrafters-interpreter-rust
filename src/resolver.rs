use std::collections::hash_map::{Entry, HashMap};
use std::mem;
use std::ops::{Deref, DerefMut};

use crate::error::{ErrLoc, SyntaxError};
use crate::ir;
use crate::span::Span;
use crate::token::Keyword;

pub fn resolve<T: Resolve>(source: &str, ast: ir::Ast<T>) -> Result<ir::Ast<T>, SyntaxError> {
    let ir::Ast { tree, meta } = ast;

    let mut cx = Context::new(source, meta);
    tree.resolve(&mut cx)?;

    Ok(ir::Ast {
        tree,
        meta: cx.meta,
    })
}

/// Block scope containing a mapping from variable names to their initialization state
#[derive(Debug, Default)]
#[repr(transparent)]
struct Scope(HashMap<String, bool>);

impl Scope {
    /// Returns true if given variable is in this scope and has not been initialized
    ///
    /// I.e., the key `var` is present and the associated value is `false`.
    #[inline]
    fn is_undefined(&self, var: &str) -> bool {
        !self.get(var).unwrap_or(&true)
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
}

#[derive(Debug)]
pub(crate) struct Context<'a> {
    source: &'a str,

    /// Stack of local block [Scope]s.
    ///
    /// Variables declared at the top level in the global scope are not tracked. I.e., if a
    /// variable cannot be found here, it can be assumed to be global.
    scopes: Vec<Scope>,

    /// Field indicating whether the code being currently resolved is inside a function declaration
    current_fn: FunctionType,

    /// Metadata associated with AST nodes
    meta: ir::Metadata,
}

impl<'a> Context<'a> {
    #[inline]
    pub(crate) fn new(source: &'a str, meta: ir::Metadata) -> Self {
        Self {
            source,
            scopes: Vec::new(),
            current_fn: FunctionType::default(),
            meta,
        }
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

    /// Adds variable `var` to the innermost scope (shadowing any outer one with the same name).
    ///
    /// From this point, the variable will exist in the scope, but is marked as _unavailable_
    /// (i.e., not having its initializer expression resolved yet).
    fn declare(&mut self, var: &str, span: &Span) -> Result<(), SyntaxError> {
        if let Some(scope) = self.scopes.last_mut() {
            match scope.entry(var.to_string()) {
                // lox does not allow re-declaring the same var in local scopes (local shadowing)
                Entry::Occupied(entry) => {
                    return Err(SyntaxError::new(
                        self.source,
                        span.clone(),
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

    /// Mark variable `var` in the innermost scope as being initialized.
    fn define(&mut self, var: &str) {
        if let Some(scope) = self.scopes.last_mut() {
            let Some(initialized) = scope.get_mut(var) else {
                panic!("defining an '{var}' that has not been declared");
            };
            *initialized = true;
        }
    }

    #[inline]
    fn is_undefined(&self, var: &str) -> bool {
        self.scopes.first().is_some_and(|s| s.is_undefined(var))
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
                self.span.clone(),
                "Can't read local variable in its own initializer.",
                ErrLoc::at(name),
            ));
        }

        cx.resolve_local(id, name);

        Ok(())
    }
}

impl Resolve for ir::Cons {
    #[inline]
    fn resolve(&self, cx: &mut Context) -> Result<(), SyntaxError> {
        self.args.iter().try_for_each(|arg| arg.resolve(cx))?;

        // handle assignment operator
        if matches!(self.op, ir::Operator::Equal) {
            match self.args.as_slice() {
                [ir::Expr::Atom(ir::Atom {
                    literal: ir::Literal::Ident(id, name),
                    ..
                }), value] => {
                    // first resolve the assigned value in case it references other variables
                    value.resolve(cx)?;

                    // resolve the variable that’s being assigned to
                    cx.resolve_local(*id, name);
                }
                _ => {
                    return Err(SyntaxError::new(
                        cx.source,
                        self.span.clone(),
                        "Operands must be l-value and r-value.",
                        ErrLoc::at(self.op),
                    ));
                }
            }
        }

        Ok(())
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
            Self::Fun(fun) => fun.resolve(cx),
            Self::Var(var) => var.resolve(cx),
            Self::Stmt(stmt) => stmt.resolve(cx),
        }
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
        cx.resolve_fn(&self.params, &self.body, FunctionType::Function)
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
        if matches!(cx.current_fn, FunctionType::None) {
            return Err(SyntaxError::new(
                cx.source,
                self.span.clone(),
                "Can't return from top-level code.",
                ErrLoc::at(Keyword::Return),
            ));
        }

        if let Some(ref value) = self.value {
            value.resolve(cx)
        } else {
            Ok(())
        }
    }
}
