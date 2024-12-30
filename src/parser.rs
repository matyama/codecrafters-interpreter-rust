use std::borrow::Cow;
use std::iter::Peekable;

use crate::error::SyntaxError;
use crate::expr::{Atom, Expr, Operator};
use crate::lexer::{Lexer, TokenStream};
use crate::span::Span;
use crate::token::{LexToken, Literal, Token};

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
pub fn parse(source: &str) -> Result<Expr, SyntaxError> {
    Parser::new(source).parse()
}

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
                        let loc = ErrLoc::at(&op.lexeme);
                        let msg = "Expect operator token.";
                        return Err(self.error(span, msg, loc));
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
                        let loc = ErrLoc::at(&op.lexeme);
                        let msg = "Expect operator token.";
                        return Err(self.error(span, msg, loc));
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
                            let span = span.clone();
                            let loc = ErrLoc::at(lexeme);
                            let msg = "Expect ')' after expression.";
                            Err(self.error(span, msg, loc))
                        },

                        Err(span) => {
                            let msg = "Expect ')' after expression.";
                            Err(self.error(span, msg, ErrLoc::Eof))
                        },
                    }
                }

                Ok(LexToken { lexeme, span, .. }) => {
                    let span = span.clone();
                    let loc = ErrLoc::at(lexeme);
                    Err(self.error(span, "Expect expression.", loc))
                },

                Err(span) => {
                    Err(self.error(span, "Expect expression.", ErrLoc::Eof))
                },
            }
        }
    }

}

// NOTE: Unfortunately one cannot access the iterator inside Peekable, so
// this has to be instantiated with and hold the input slice. Ideally,
// `Parser::new` would take `tokens: TokenStream<'a>`.
/// Recursive descent parser for the Lox language
pub struct Parser<'a> {
    source: &'a str,
    tokens: Peekable<TokenStream<'a>>,
    current: Option<LexToken<'a>>,
}

impl<'a> Parser<'a> {
    #[inline]
    pub fn new(source: &'a str) -> Self {
        Self {
            source,
            tokens: Lexer::new(source).into_iter().peekable(),
            current: None,
        }
    }

    fn error(&self, span: Span, msg: &str, loc: ErrLoc) -> SyntaxError {
        let code = span.snippet(self.source).to_string();
        SyntaxError {
            span,
            code,
            context: loc.into(),
            source: msg.into(),
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

#[derive(Debug, Default)]
enum ErrLoc {
    At(Cow<'static, str>),
    #[default]
    Eof,
}

impl ErrLoc {
    #[inline]
    fn at(loc: &str) -> Self {
        Self::At(Cow::Owned(format!(" at '{loc}'")))
    }
}

impl From<ErrLoc> for Cow<'static, str> {
    #[inline]
    fn from(loc: ErrLoc) -> Self {
        match loc {
            ErrLoc::At(loc) => loc,
            ErrLoc::Eof => Cow::Borrowed(" at end"),
        }
    }
}
