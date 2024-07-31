use std::fmt::Display;
use std::process::{ExitCode, Termination};

use crate::expr::{Expr, Literal};
use crate::token::{Token, TokenType, Tokens};
use crate::{Report, Span};

macro_rules! rule {

    // models: expression → equality ;
    ($head:ident -> $rule:ident ;) => {
        fn $head(&mut self) -> Result<Expr, ParseError> {
            self.$rule()
        }
    };

    // models: equality → comparison ( ( "!=" | "==" ) comparison )* ;
    ($($head:ident -> $lhs:ident (($ty0:ident $(| $ty:ident)*) $rhs:ident)$_:tt ;)+) => {
        $(
            fn $head(&mut self) -> Result<Expr, ParseError> {
                let mut expr = self.$lhs()?;

                while let TokenType::$ty0 $(| TokenType::$ty)* = self.peek_ty() {
                    let op = self.advance();
                    let rhs = self.$rhs()?;
                    expr = Expr::binary(expr, op, rhs);
                }

                Ok(expr)
            }
        )+
    };

    // models: unary → ( "!" | "-" ) unary | primary ;
    ($($head:ident -> ($ty0:ident $(| $ty:ident)*) $rhs:ident | $primary:ident ;)+) => {
        $(
            fn $head(&mut self) -> Result<Expr, ParseError> {
                if let TokenType::$ty0 $(| TokenType::$ty)* = self.peek_ty() {
                    let op = self.advance();
                    let rhs = self.$rhs()?;
                    Ok(Expr::unary(op, rhs))
                } else {
                    self.$primary()
                }
            }
        )+
    };

    // models: primary → NUMBER | STRING | "true" | "false" | "nil" | "(" expression ")" ;
    ($head:ident -> $ty0:ident $(| $ty:ident)* | ( $group:ident ) ;) => {
        fn $head(&mut self) -> Result<Expr, ParseError> {
            match self.peek() {
                token if matches!(token.ty, TokenType::$ty0 $(| TokenType::$ty)*) => {
                    let lit = Literal::from(token);
                    self.current += 1;
                    Ok(Expr::Literal(lit))
                }

                token if matches!(token.ty, TokenType::LeftParen) => {
                    self.current += 1;
                    let expr = self.$group()?;

                    match self.peek() {
                        token if matches!(token.ty, TokenType::RightParen) => {
                            self.current += 1;
                            Ok(Expr::group(expr))
                        }
                        token => Err(ParseError::new(token, "Expect ')' after expression.")),
                    }
                }

                token => Err(ParseError::new(token, "Expect expression.")),
            }
        }
    }

}

/// Recursive descent parser for the Lox language
pub struct Parser {
    tokens: Tokens,
    current: usize,
}

impl Parser {
    #[inline]
    pub fn new(tokens: Tokens) -> Self {
        Self { tokens, current: 0 }
    }

    #[inline]
    fn peek(&self) -> &Token {
        &self.tokens[self.current]
    }

    #[inline]
    fn peek_ty(&self) -> TokenType {
        self.peek().ty
    }

    fn advance(&mut self) -> Token {
        let token = self.peek().clone();
        self.current += 1;
        token
    }

    /// Parse a sequence of tokens according to the following grammar:
    /// ```
    /// expression     → equality ;
    /// equality       → comparison ( ( "!=" | "==" ) comparison )* ;
    /// comparison     → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    /// term           → factor ( ( "-" | "+" ) factor )* ;
    /// factor         → unary ( ( "/" | "*" ) unary )* ;
    /// unary          → ( "!" | "-" ) unary
    ///                | primary ;
    /// primary        → NUMBER | STRING | "true" | "false" | "nil"
    ///                | "(" expression ")" ;
    /// ```
    #[inline]
    pub fn parse(mut self) -> Result<Expr, ParseError> {
        self.expression()
    }

    rule! {
        expression -> equality ;
    }

    rule! {
        equality   -> comparison ( (BangEqual | EqualEqual) comparison)* ;
        comparison -> term ( (Greater | GreaterEqual | Less | LessEqual) term )* ;
        term       -> factor ( (Minus | Plus) factor)* ;
        factor     -> unary ( (Slash | Star ) unary )* ;
    }

    rule! {
        unary      -> (Bang | Minus) unary | primary ;
    }

    rule! {
        primary    -> Number | String | True | False | Nil | ( expression ) ;
    }
}

#[derive(Debug)]
pub struct ParseError;

impl ParseError {
    #[inline]
    fn new(token: &Token, msg: impl Display) -> Self {
        Self.error(Span::Token(token), msg);
        Self
    }
}

impl Report for ParseError {
    fn report(&mut self, line: usize, location: &str, msg: impl Display) {
        eprintln!("[line {line}] Error{location}: {msg}");
    }

    #[inline]
    fn error(&mut self, span: Span<'_>, msg: impl Display) {
        match span {
            Span::Line(line) => self.report(line, "", msg),
            Span::Token(token) if matches!(token.ty, TokenType::EOF) => {
                self.report(token.line, " at end", msg)
            }
            Span::Token(token) => {
                let location = format!(" at '{}'", token.lexeme);
                self.report(token.line, &location, msg);
            }
        }
    }
}

impl Termination for ParseError {
    #[inline]
    fn report(self) -> ExitCode {
        ExitCode::from(65)
    }
}
