use std::fmt::Display;
use std::process::{ExitCode, Termination};

use crate::expr::{Expr, Literal};
use crate::token::{Token, TokenType, Tokens};
use crate::{Report, Span};

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

    // expression → equality ;
    fn expression(&mut self) -> Result<Expr, ParseError> {
        self.equality()
    }

    // equality → comparison ( ( "!=" | "==" ) comparison )* ;
    fn equality(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.comparison()?;

        while let TokenType::BangEqual | TokenType::EqualEqual = self.peek_ty() {
            let op = self.advance();
            let rhs = self.comparison()?;

            expr = Expr::Binary {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Ok(expr)
    }

    // comparison → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    fn comparison(&mut self) -> Result<Expr, ParseError> {
        use TokenType::*;

        let mut expr = self.term()?;

        while let Greater | GreaterEqual | Less | LessEqual = self.peek_ty() {
            let op = self.advance();
            let rhs = self.term()?;

            expr = Expr::Binary {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Ok(expr)
    }

    // term → factor ( ( "-" | "+" ) factor )* ;
    fn term(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.factor()?;

        while let TokenType::Minus | TokenType::Plus = self.peek_ty() {
            let op = self.advance();
            let rhs = self.factor()?;

            expr = Expr::Binary {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Ok(expr)
    }

    // factor → unary ( ( "/" | "*" ) unary )* ;
    fn factor(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.unary()?;

        while let TokenType::Slash | TokenType::Star = self.peek_ty() {
            let op = self.advance();
            let rhs = self.unary()?;

            expr = Expr::Binary {
                lhs: Box::new(expr),
                op,
                rhs: Box::new(rhs),
            };
        }

        Ok(expr)
    }

    // unary → ( "!" | "-" ) unary | primary ;
    fn unary(&mut self) -> Result<Expr, ParseError> {
        if let TokenType::Bang | TokenType::Minus = self.peek_ty() {
            let op = self.advance();
            let rhs = self.unary()?;

            Ok(Expr::Unary {
                op,
                rhs: Box::new(rhs),
            })
        } else {
            self.primary()
        }
    }

    // primary → NUMBER | STRING | "true" | "false" | "nil" | "(" expression ")" ;
    fn primary(&mut self) -> Result<Expr, ParseError> {
        use TokenType::*;

        match self.peek() {
            token if matches!(token.ty, False | True | Nil | Number | String) => {
                let lit = Literal::from(token);
                self.current += 1;
                Ok(Expr::Literal(lit))
            }

            token if matches!(token.ty, LeftParen) => {
                self.current += 1;
                let expr = self.expression()?;

                match self.peek() {
                    token if matches!(token.ty, RightParen) => {
                        self.current += 1;
                        Ok(Expr::Grouping(Box::new(expr)))
                    }
                    token => Err(ParseError::new(token, "Expect ')' after expression.")),
                }
            }

            token => Err(ParseError::new(token, "Expect expression.")),
        }
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
