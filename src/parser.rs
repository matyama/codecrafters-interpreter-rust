use std::borrow::Cow;
use std::iter::Peekable;

use crate::error::SyntaxError;
use crate::expr::{Atom, Expr, Operator};
use crate::lexer::TokenStream;
use crate::span::Span;
use crate::token::{LexToken, Literal, Token};

macro_rules! rule {

    // models: expression → equality ;
    ($head:ident -> $rule:ident ;) => {
        fn $head(&mut self) -> Result<Expr, SyntaxError> {
            self.$rule()
        }
    };

    // models: equality → comparison ( ( "!=" | "==" ) comparison )* ;
    ($($head:ident -> $lhs:ident (($ty0:ident $(| $ty:ident)*) $rhs:ident)$_:tt ;)+) => {
        $(
            fn $head(&mut self) -> Result<Expr, SyntaxError> {
                let mut expr = self.$lhs()?;

                loop {
                    let Ok(next) = self.peek() else {
                        let Err(error) = self.advance() else {
                            unreachable!("peeked an error");
                        };
                        return Err(error);
                    };

                    let Ok(LexToken {
                        token: Token::$ty0 $(| Token::$ty)*,
                        ..
                    }) = next else {
                        break Ok(expr);
                    };

                    let Ok(op) = self.advance()? else {
                        unreachable!("peeked next token");
                    };

                    let mut span = op.span.clone();

                    let Some(op) = <Option<Operator>>::from(&op.token) else {
                        return Err(SyntaxError {
                            error: Cow::Owned(format!(" at '{}'", op.lexeme)),
                            code: span.snippet(&self.source).to_string(),
                            span,
                            source: "Expect operator token.".into(),
                        });
                    };

                    let rhs = self.$rhs()?;
                    span += rhs.span();
                    expr = Expr::binary(op, expr, rhs, span);
                }
            }
        )+
    };

    // models: unary → ( "!" | "-" ) unary | primary ;
    ($($head:ident -> ($ty0:ident $(| $ty:ident)*) $rhs:ident | $primary:ident ;)+) => {
        $(
            fn $head(&mut self) -> Result<Expr, SyntaxError> {
                let Ok(next) = self.peek() else {
                    let Err(error) = self.advance() else {
                        unreachable!("peeked an error");
                    };
                    return Err(error);
                };

                if let Ok(LexToken {
                    token: Token::$ty0 $(| Token::$ty)*,
                    ..
                }) = next {
                    let Ok(op) = self.advance()? else {
                        unreachable!("peeked next token");
                    };
                    let mut span = op.span.clone();
                    let Some(op) = <Option<Operator>>::from(&op.token) else {
                        return Err(SyntaxError {
                            error: Cow::Owned(format!(" at '{}'", op.lexeme)),
                            code: span.snippet(&self.source).to_string(),
                            span,
                            source: "Expect operator token.".into(),
                        });
                    };
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
        fn $head(&mut self) -> Result<Expr, SyntaxError> {
            use crate::token::Keyword::*;

            let Ok(next) = self.peek() else {
                let Err(error) = self.advance() else {
                    unreachable!("peeked an error");
                };
                return Err(error);
            };

            match next {
                Ok(
                    token @ LexToken {
                        token: Token::Literal(
                           Literal::$ty0(..) $(| Literal::$ty(..))*
                        ),
                        ..
                    }
                ) => {
                    let atom = Atom::from(token);
                    let _ = self.advance()?;
                    Ok(Expr::Atom(atom))
                }

                Ok(token @ LexToken {
                    token: Token::Keyword(True | False | Nil),
                    ..
                }) => {
                    let atom = Atom::from(token);
                    let _ = self.advance()?;
                    Ok(Expr::Atom(atom))
                }

                Ok(LexToken { token: Token::LeftParen, span, .. }) => {
                    let mut span = span.clone();
                    let _ = self.advance()?;

                    let expr = self.$group()?;
                    span += expr.span();

                    let Ok(next) = self.peek() else {
                        let Err(error) = self.advance() else {
                            unreachable!("peeked an error");
                        };
                        return Err(error);
                    };

                    match next {
                        Ok(LexToken {
                            token: Token::RightParen,
                            span: ref s,
                            ..
                        }) => {
                            span += s;
                            let _ = self.advance()?;
                            Ok(Expr::group(expr, span))
                        }

                        Ok(LexToken { lexeme, span, .. }) => {
                            let error = Cow::Owned(format!(" at '{lexeme}'"));
                            let span = span.clone();
                            let code = span.snippet(&self.source).to_string();
                            Err(SyntaxError {
                                error,
                                code,
                                span,
                                source: "Expect ')' after expression.".into(),
                            })
                        },

                        Err(span) => {
                            let code = span.snippet(&self.source).to_string();
                            Err(SyntaxError {
                                error: Cow::Borrowed(" at end"),
                                code,
                                span,
                                source: "Expect ')' after expression.".into(),
                            })
                        }
                    }
                }

                Ok(LexToken { lexeme, span, .. }) => {
                    let error = Cow::Owned(format!(" at '{lexeme}'"));
                    let span = span.clone();
                    let code = span.snippet(&self.source).to_string();
                    Err(SyntaxError {
                        error,
                        code,
                        span,
                        source: "Expect expression.".into(),
                    })
                },

                Err(span) => {
                    let code = span.snippet(&self.source).to_string();
                    Err(SyntaxError {
                        error: Cow::Borrowed(" at end"),
                        code,
                        span,
                        source: "Expect expression.".into(),
                    })
                }
            }
        }
    }

}

/// Recursive descent parser for the Lox language
pub struct Parser<'a> {
    source: &'a str,
    tokens: Peekable<TokenStream<'a>>,
    current: Option<LexToken<'a>>,
}

impl<'a> Parser<'a> {
    // TODO: take the source ref from the tokens
    #[inline]
    pub fn new(source: &'a str, tokens: TokenStream<'a>) -> Self {
        Self {
            source,
            tokens: tokens.peekable(),
            current: None,
        }
    }

    fn peek(&mut self) -> Result<Result<&LexToken<'a>, Span>, &SyntaxError> {
        match self.tokens.peek() {
            Some(Ok(token)) => Ok(Ok(token)),
            Some(Err(error)) => Err(error),
            None => Ok(Err(self
                .current
                .as_ref()
                .map(|t| t.span.clone())
                .unwrap_or_else(Span::empty))),
        }
    }

    fn advance(&mut self) -> Result<Result<&LexToken<'a>, usize>, SyntaxError> {
        let line = self.current.as_ref().map_or(0, |t| t.span.lineno);
        Ok(match self.tokens.next().transpose()? {
            Some(t) => {
                let _ = self.current.insert(t);
                self.current.as_ref().ok_or(line)
            }
            None => Err(line),
        })
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
    pub fn parse(mut self) -> Result<Expr, SyntaxError> {
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
