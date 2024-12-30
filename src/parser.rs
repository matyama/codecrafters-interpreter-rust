use std::fmt::Display;
use std::iter::Peekable;
use std::process::{ExitCode, Termination};

use crate::expr::{Atom, Expr, Operator};
use crate::token::{LexToken, Literal, Token};
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

                while let Ok(LexToken {
                    token: Token::$ty0 $(| Token::$ty)*,
                    ..
                }) = self.peek() {
                    let Ok(op) = self.advance() else {
                        unreachable!("peeked next token");
                    };
                    let mut span = op.span.clone();
                    let op = <Option<Operator>>::from(&op.token)
                        .ok_or_else(|| {
                            ParseError::new(Ok(op), "Expect operator token.")
                        })?;
                    let rhs = self.$rhs()?;
                    span += rhs.span();
                    expr = Expr::binary(op, expr, rhs, span);
                }

                Ok(expr)
            }
        )+
    };

    // models: unary → ( "!" | "-" ) unary | primary ;
    ($($head:ident -> ($ty0:ident $(| $ty:ident)*) $rhs:ident | $primary:ident ;)+) => {
        $(
            fn $head(&mut self) -> Result<Expr, ParseError> {
                if let Ok(LexToken {
                    token: Token::$ty0 $(| Token::$ty)*,
                    ..
                }) = self.peek() {
                    let Ok(op) = self.advance() else {
                        unreachable!("peeked next token");
                    };
                    let mut span = op.span.clone();
                    let op = <Option<Operator>>::from(&op.token)
                        .ok_or_else(|| {
                            ParseError::new(Ok(op), "Expect operator token.")
                        })?;
                    let rhs = self.$rhs()?;
                    span += rhs.span();
                    Ok(Expr::unary(op, rhs, span))
                } else {
                    self.$primary()
                }
            }
        )+
    };

    // models: primary → NUMBER | STRING | "true" | "false" | "nil" | "(" expression ")" ;
    ($head:ident -> $ty0:ident $(| $ty:ident)* | "true" | "false" | "nil" | ( $group:ident ) ;) => {
        fn $head(&mut self) -> Result<Expr, ParseError> {
            use crate::token::Keyword::*;
            match self.peek() {
                Ok(
                    token @ LexToken {
                        token: Token::Literal(
                           Literal::$ty0(..) $(| Literal::$ty(..))*
                        ),
                        ..
                    }
                ) => {
                    let atom = Atom::from(token);
                    let _ = self.advance();
                    Ok(Expr::Atom(atom))
                }

                Ok(token @ LexToken {
                    token: Token::Keyword(True | False | Nil),
                    ..
                }) => {
                    let atom = Atom::from(token);
                    let _ = self.advance();
                    Ok(Expr::Atom(atom))
                }

                Ok(LexToken { token: Token::LeftParen, span, .. }) => {
                    let mut span = span.clone();
                    let _ = self.advance();

                    let expr = self.$group()?;
                    span += expr.span();

                    match self.peek() {
                        Ok(LexToken {
                            token: Token::RightParen,
                            span: ref s,
                            ..
                        }) => {
                            span += s;
                            let _ = self.advance();
                            Ok(Expr::group(expr, span))
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
pub struct Parser<I: Iterator> {
    tokens: Peekable<I>,
    current: Option<I::Item>,
}

impl<'a, I> Parser<I>
where
    I: Iterator<Item = LexToken<'a>>,
{
    #[inline]
    pub fn new(tokens: impl IntoIterator<IntoIter = I>) -> Self {
        Self {
            tokens: tokens.into_iter().peekable(),
            current: None,
        }
    }

    fn peek(&mut self) -> Result<&LexToken<'a>, usize> {
        self.tokens
            .peek()
            .ok_or_else(|| self.current.as_ref().map_or(0, |t| t.span.lineno))
    }

    fn advance(&mut self) -> Result<&LexToken<'a>, usize> {
        let line = self.current.as_ref().map_or(0, |t| t.span.lineno);
        match self.tokens.next() {
            Some(t) => {
                let _ = self.current.insert(t);
                self.current.as_ref().ok_or(line)
            }
            None => Err(line),
        }
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
        primary    -> Num | Str | "true" | "false" | "nil" | ( expression ) ;
    }
}

#[derive(Debug)]
pub struct ParseError;

impl ParseError {
    fn new(token: Result<&LexToken<'_>, usize>, msg: impl Display) -> Self {
        let span = token.map_or_else(Span::Eof, |t| Span::Token(&t.lexeme, t.span.lineno));
        Self.error(span, msg);
        Self
    }
}

impl Report for ParseError {
    fn report(&mut self, line: usize, location: &str, msg: impl Display) {
        eprintln!("[line {line}] Error{location}: {msg}");
    }

    #[inline]
    fn error<T: Display, M: Display>(&mut self, span: Span<T>, msg: M) {
        match span {
            Span::Eof(line) => self.report(line, " at end", msg),
            Span::Token(token, line) => {
                let location = format!(" at '{token}'");
                self.report(line, &location, msg);
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
