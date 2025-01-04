use std::borrow::Cow;
use std::iter::Peekable;
use std::str::FromStr;

use crate::error::SyntaxError;
use crate::ir::{AssignTarget, Atom, Block, Decl, Expr, If, Operator, Print, Program, Stmt, Var};
use crate::lexer::{Lexer, TokenStream};
use crate::span::Span;
use crate::token::{Keyword, LexToken, Literal, Token};

impl FromStr for Expr {
    type Err = SyntaxError;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        Parser::new(source).parse_expr()
    }
}

impl FromStr for Program {
    type Err = SyntaxError;

    fn from_str(source: &str) -> Result<Self, Self::Err> {
        Parser::new(source).parse_prog()
    }
}

macro_rules! rule {

    // models: program → declaration* EOF ;
    ($head:ident -> $declaration:ident$_:tt EOF ;) => {
        fn $head(&mut self) -> Result<Program, SyntaxError> {
            let mut declarations = Vec::new();

            loop {
                let Ok(next) = self.peek() else {
                    let Err(error) = self.advance() else {
                        unreachable!("peeked an error");
                    };
                    break Err(error);
                };

                // check EOF
                if next.is_err() {
                    break Ok(Program(declarations));
                }

                match self.$declaration() {
                    Ok(decl) => declarations.push(decl),
                    Err(err) => break Err(err),
                }
            }
        }
    };

    // models simple rule alternatives:
    //  - declaration → var_decl  | statement ;
    //  - statement   → expr_stmt | print_stmt | block ;
    //  - expression  → assignment ;
    ($($head:ident -> $rule0:ident $(| $rule:ident)* ; # $t:ty)+) => {
        $(
            fn $head(&mut self) -> Result<$t, SyntaxError> {
                $(
                    if let Some(res) = self.$rule()?.map(<$t>::from) {
                        return Ok(res);
                    }
                )*
                self.$rule0().map(<$t>::from)
            }
        )+
    };

    // models assignment → IDENTIFIER "=" assignment | equality ;
    ($head:ident -> IDENTIFIER "=" $rval:ident | $lval:ident ;) => {
        fn $head(&mut self) -> Result<Expr, SyntaxError> {
            let expr = self.$lval()?;

            // try to match an assignment operator (=)
            let Ok(next) = self.peek() else {
                let Err(error) = self.advance() else {
                    unreachable!("peeked an error");
                };
                return Err(error);
            };

            if let Ok(LexToken {
                token: Token::Equal,
                ..
            }) = next
            {
                let Ok(Ok(LexToken {
                    lexeme,
                    span: eq_span,
                    ..
                })) = self.advance()
                else {
                    unreachable!("peeked a token");
                };

                // ensure there's a valid assignment target before the operator
                return match AssignTarget::try_from(expr) {
                    Ok(target) => {
                        let lval = Expr::from(target);
                        let rval = self.$rval()?;
                        let span = lval.span() + rval.span();
                        Ok(Expr::binary(Operator::Equal, lval, rval, span))
                    }
                    Err(expr) => {
                        let span = expr.span() + eq_span;
                        let loc = ErrLoc::at(lexeme);
                        Err(self.error(span, "Invalid assignment target.", loc))
                    }
                };
            }

            Ok(expr)
        }
    };

    // models var_decl → "var" IDENTIFIER ( "=" expression )? ";" ;
    ($head:ident -> $_kw:literal $ident:ident ( "=" $init:ident )? ";" ; # $t:ident) => {
        fn $head(&mut self) -> Result<Option<$t>, SyntaxError> {
            let Ok(next) = self.peek() else {
                let Err(error) = self.advance() else {
                    unreachable!("peeked an error");
                };
                return Err(error);
            };

            let Ok(LexToken {
                token: Token::Keyword(Keyword::$t),
                span,
                ..
            }) = next
            else {
                return Ok(None);
            };

            let mut span = span.clone();
            let _ = self.advance()?;

            // mandatory variable identifier
            let (ident, s) = self.$ident()?;
            span += s;

            // optional initializer expression
            let Ok(next) = self.peek() else {
                let Err(error) = self.advance() else {
                    unreachable!("peeked an error");
                };
                return Err(error);
            };

            let expr = match next {
                Ok(LexToken {
                    token: Token::Equal,
                    ..
                }) => {
                    let _ = self.advance()?;

                    // parse expression
                    let expr = self.$init()?;
                    span += expr.span();

                    Some(expr)
                }

                _ => None,
            };

            // parse ;
            span += self.semicolon()?;
            Ok(Some(Var { ident, expr, span }))
        }
    };

    // models block → "{" declaration* "}" ;
    ($head:ident -> "{" $rule:ident* "}" ;) => {
        fn $head(&mut self) -> Result<Option<Block>, SyntaxError> {
            // attempt to match start of a block indicated by '{'
            let Some(mut span) = self.left_brace()? else {
                return Ok(None);
            };

            let mut decls = Vec::new();

            loop {
                let decl = match self.peek() {
                    // stop when '}' is reached
                    Ok(Ok(LexToken {
                        token: Token::RightBrace,
                        ..
                    })) => break,

                    // stop when EOF is reached
                    Ok(Err(_)) => break,

                    // propagate errors
                    Err(_) => {
                        let Err(error) = self.advance() else {
                            unreachable!("peeked an error");
                        };
                        return Err(error);
                    }

                    // otherwise parse a (variable or statement) declaration
                    _ => self.$rule()?,
                };

                decls.push(decl);
            }

            // consume closing '}' or fail if EOF was reached
            span += self.right_brace()?;

            Ok(Some(Block { decls, span }))
        }
    };

    // matches "if" "(" expression ")" statement ( "else" statement )? ;
    ($head:ident -> "if" "(" $cond:ident ")" $then:ident ( "else" $else:ident )? ;) => {
        fn $head(&mut self) -> Result<Option<If>, SyntaxError> {
            let Some(mut span) = self.if_keyword()? else {
                return Ok(None);
            };

            span += self.left_paren()?;

            let cond = self.$cond()?;
            span += cond.span();

            span += self.right_paren()?;

            let then_branch = self.$then().map(Box::new)?;
            span += then_branch.span();

            let else_branch = if self.else_keyword()?.is_some() {
                let else_branch = self.$else().map(Box::new)?;
                span += else_branch.span();
                Some(else_branch)
            } else {
                None
            };

            Ok(Some(If {
                cond,
                then_branch,
                else_branch,
                span,
            }))
        }
    };

    // models expr_stmt → expression ";" ;
    ($($head:ident -> $rule:ident ";" ; # $t:ty)+) => {
        $(
            fn $head(&mut self) -> Result<$t, SyntaxError> {
                let expr = self.$rule()?;
                let span = self.semicolon()?;
                Ok(expr + span)
            }
        )+
    };

    // models print_stmt → "print" expression ";" ;
    ($($head:ident -> $_kw:literal $rule:ident ";" ; # $t:ident)+) => {
        $(
            fn $head(&mut self) -> Result<Option<$t>, SyntaxError> {
                let Ok(next) = self.peek() else {
                    let Err(error) = self.advance() else {
                        unreachable!("peeked an error");
                    };
                    return Err(error);
                };

                let Ok(LexToken {
                    token: Token::Keyword(Keyword::$t),
                    span,
                    ..
                }) = next
                else {
                    return Ok(None);
                };

                let mut span = span.clone();
                let _ = self.advance()?;

                // TODO: generalize to other kinds of statements
                // parse expression
                let expr = self.$rule()?;
                span += expr.span();

                // parse ;
                span += self.semicolon()?;
                Ok(Some($t { expr, span }))
            }
        )+
    };

    // models:
    //  - logic_or  → logic_and ( "or" logic_and )* ;
    //  - logic_and → equality ( "and" equality )* ;
    //  - equality  → comparison ( ( "!=" | "==" ) comparison )* ;
    ($(
        $head:ident ->
        $lhs:ident (($t0:ident$(($k0:ident))? $(| $t:ident$(($k:ident))?)*) $rhs:ident)* ;
    )+) => {
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
                        token: Token::$t0$((Keyword::$k0))? $(| Token::$t$((Keyword::$k))?)*,
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

    // models: primary → NUMBER | STRING | "true" | "false" | "nil" | "(" expression ")" | IDENTIFIER ;
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
    };

    // matches an optional simple token or keyword (e.g., LeftBrace)
    ($($head:ident ? $t:ident$(($kw:ident))? ;)+) => {
        $(
            fn $head(&mut self) -> Result<Option<Span>, SyntaxError> {
                let Ok(next) = self.peek() else {
                    let Err(error) = self.advance() else {
                        unreachable!("peeked an error");
                    };
                    return Err(error);
                };

                let Ok(LexToken {
                    token: Token::$t$((Keyword::$kw))?,
                    span,
                    ..
                }) = next
                else {
                    return Ok(None);
                };

                let span = span.clone();
                let _ = self.advance()?;
                Ok(Some(span))
            }
        )+
    };

    // matches a mandatory simple token or keyword (e.g, Semicolon, RightBrace)
    ($($head:ident ? $t:ident$(($kw:ident))? : $err:expr ;)+) => {
        $(
            fn $head(&mut self) -> Result<Span, SyntaxError> {
                match self.advance()? {
                    Ok(LexToken {
                        token: Token::$t$((Keyword::$kw))?,
                        span,
                        ..
                    }) => Ok(span.clone()),

                    Ok(LexToken { lexeme, span, .. }) => {
                        let span = span.clone();
                        let loc = ErrLoc::at(lexeme);
                        Err(self.error(span, $err, loc))
                    }

                    Err(lineno) => {
                        // FIXME: proper span
                        let mut span = Span::empty();
                        span.lineno = lineno;
                        Err(self.error(span, $err, ErrLoc::Eof))
                    }
                }
            }
        )+
    };
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

    fn identifier(&mut self) -> Result<(String, Span), SyntaxError> {
        match self.advance()? {
            Ok(LexToken {
                token: Token::Literal(Literal::Ident(ident)),
                span,
                ..
            }) => Ok((ident.to_string(), span.clone())),

            Ok(LexToken { lexeme, span, .. }) => {
                let span = span.clone();
                let loc = ErrLoc::at(lexeme);
                let msg = "Expect IDENTIFIER after 'var'.";
                Err(self.error(span, msg, loc))
            }

            Err(lineno) => {
                // FIXME: proper span
                let mut span = Span::empty();
                span.lineno = lineno;
                let msg = "Expect IDENTIFIER after 'var'.";
                Err(self.error(span, msg, ErrLoc::Eof))
            }
        }
    }

    /// Parse a sequence of tokens according to the following grammar:
    /// ```text
    /// program        → declaration* EOF ;
    /// declaration    → var_decl
    ///                | statement ;
    /// var_decl       → "var" IDENTIFIER ( "=" expression )? ";" ;
    /// statement      → expr_stmt
    ///                | if_stmt
    ///                | print_stmt
    ///                | block ;
    /// expr_stmt      → expression ";" ;
    /// if_stmt        → "if" "(" expression ")" statement ( "else" statement )? ;
    /// print_stmt     → "print" expression ";" ;
    /// block          → "{" declaration* "}" ;
    /// expression     → assignment ;
    /// assignment     → IDENTIFIER "=" assignment
    ///                | logic_or ;
    /// logic_or       → logic_and ( "or" logic_and )* ;
    /// logic_and      → equality ( "and" equality )* ;
    /// equality       → comparison ( ( "!=" | "==" ) comparison )* ;
    /// comparison     → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    /// term           → factor ( ( "-" | "+" ) factor )* ;
    /// factor         → unary ( ( "/" | "*" ) unary )* ;
    /// unary          → ( "!" | "-" ) unary
    ///                | primary ;
    /// primary        → NUMBER | STRING | "true" | "false" | "nil"
    ///                | "(" expression ")"
    ///                | IDENTIFIER ;
    /// ```
    #[inline]
    pub fn parse_prog(mut self) -> Result<Program, SyntaxError> {
        self.program()
    }

    /// Parse a sequence of tokens according to the following grammar:
    /// ```text
    /// expression     → assignment ;
    /// assignment     → IDENTIFIER "=" assignment
    ///                | logic_or ;
    /// logic_or       → logic_and ( "or" logic_and )* ;
    /// logic_and      → equality ( "and" equality )* ;
    /// equality       → comparison ( ( "!=" | "==" ) comparison )* ;
    /// comparison     → term ( ( ">" | ">=" | "<" | "<=" ) term )* ;
    /// term           → factor ( ( "-" | "+" ) factor )* ;
    /// factor         → unary ( ( "/" | "*" ) unary )* ;
    /// unary          → ( "!" | "-" ) unary
    ///                | primary ;
    /// primary        → NUMBER | STRING | "true" | "false" | "nil"
    ///                | "(" expression ")"
    ///                | IDENTIFIER ;
    /// ```
    #[inline]
    pub fn parse_expr(mut self) -> Result<Expr, SyntaxError> {
        self.expression()
    }

    rule! {
        program     -> declaration* EOF ;
    }

    rule! {
        declaration -> statement | var_decl ;                     #  Decl
        statement   -> expr_stmt | if_stmt | print_stmt | block ; #  Stmt
        expression  -> assignment ;                               #  Expr
    }

    rule! {
        assignment  -> IDENTIFIER "=" assignment | logic_or ;
    }

    rule! {
        var_decl    -> "var" identifier ( "=" expression )? ";" ; #  Var
    }

    rule! {
        block       -> "{" declaration* "}" ;
    }

    rule! {
        if_stmt     -> "if" "(" expression ")" statement ( "else" statement )? ;
    }

    rule! {
        expr_stmt   -> expression ";" ;                           #  Expr
    }

    rule! {
        print_stmt  -> "print" expression ";" ;                   #  Print
    }

    rule! {
        logic_or    -> logic_and ( (Keyword(Or))  logic_and )* ;
        logic_and   -> equality  ( (Keyword(And)) equality  )* ;
        equality    -> comparison ( (BangEqual | EqualEqual) comparison)* ;
        comparison  -> term ( (Greater | GreaterEqual | Less | LessEqual) term )* ;
        term        -> factor ( (Minus | Plus) factor)* ;
        factor      -> unary ( (Slash | Star ) unary )* ;
    }

    rule! {
        unary       -> (Bang | Minus) unary | primary ;
    }

    rule! {
        primary     -> Num | Str | Ident | "true" | "false" | "nil" | ( expression ) ;
    }

    rule! {
        left_brace    ? LeftBrace ;
        if_keyword    ? Keyword(If) ;
        else_keyword  ? Keyword(Else) ;
    }

    rule! {
        semicolon     ? Semicolon  : "Expect ';' after statement." ;
        left_paren    ? LeftParen  : "Expect '(' after 'if'." ;
        right_paren   ? RightParen : "Expect ')' after if condition." ;
        right_brace   ? RightBrace : "Expect '}' ." ;
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
