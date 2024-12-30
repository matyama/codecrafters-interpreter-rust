use std::borrow::Cow;
use std::fmt::Debug;
use std::iter::Peekable;
use std::str::Chars;

use crate::error::SyntaxError;
use crate::span::Span;
use crate::token::{LexToken, Literal, Token};

use self::matcher::*;

pub type LexResult<T> = Result<T, SyntaxError>;

#[derive(Clone, Copy, Debug)]
pub struct Lexer<'prg>(&'prg str);

impl<'prg> Lexer<'prg> {
    #[inline]
    pub fn new(input: &'prg str) -> Self {
        Self(input)
    }
}

impl<'prg> IntoIterator for Lexer<'prg> {
    type Item = <TokenStream<'prg> as Iterator>::Item;
    type IntoIter = TokenStream<'prg>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        TokenStream {
            prg: self.0,
            pos: 0,
            chars: self.0.chars().peekable(),
            line: 0,
            line_pos: 0,
        }
    }
}

pub struct TokenStream<'prg> {
    /// Raw input program
    prg: &'prg str,
    /// Current position in the input `prg`
    pos: usize,
    /// Character stream from the input `prg`
    chars: Peekable<Chars<'prg>>,
    /// Current line number in the input `prg`
    line: usize,
    /// Offset of the start of current line
    line_pos: usize,
}

impl TokenStream<'_> {
    fn error(
        &self,
        start: usize,
        source: impl Into<Box<dyn std::error::Error + 'static>>,
    ) -> SyntaxError {
        let span = self.span(start, self.pos - start);
        let code = span.snippet(self.prg).to_string();
        SyntaxError {
            span,
            code,
            context: Cow::Borrowed(""),
            source: source.into(),
        }
    }

    #[inline]
    fn span(&self, offset: usize, length: usize) -> Span {
        Span {
            offset,
            length,
            lineno: self.line + 1,
            lineof: self.line_pos,
        }
    }

    /// Advance the character stream while predicate `p` is false.
    ///
    /// Side effects:
    ///  - For each consumed character: increments current position
    ///  - For each character `c` such that `p(c) == false`: calls `visit(self, c)`
    ///
    /// Returns the character `c` for which `p(c) == true`.
    fn visit_until(
        &mut self,
        p: impl Fn(char) -> bool,
        mut visit: impl FnMut(&mut Self, char),
    ) -> Option<char> {
        while let Some(&c) = self.chars.peek() {
            if p(c) {
                return Some(c);
            }
            visit(self, c);
            let _ = self.chars.next();
            self.pos += 1;
        }
        None
    }

    /// Equivalent to [`visit_until`](Self::visit_until) with a dummy visitor.
    #[inline]
    fn advance_until(&mut self, p: impl Fn(char) -> bool) -> Option<char> {
        self.visit_until(p, |_, _| {})
    }

    #[inline]
    fn peek(&self, n: usize) -> Option<char> {
        debug_assert!(n > 0, "zero look-ahead");
        let i = self.pos + n - 1;
        self.prg
            .get(i..i + 1)
            // SAFETY: requested a slice of exactly one character
            .map(|s| unsafe { s.chars().nth(0).unwrap_unchecked() })
    }
}

impl<'prg> Iterator for TokenStream<'prg> {
    type Item = LexResult<LexToken<'prg>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let c = self.chars.next()?;

            let start = self.pos;
            self.pos += 1;

            macro_rules! yield_token {
                ($token:ident) => {{
                    yield_token!(Token::$token);
                }};

                (if $next:literal { $x:ident } else { $y:ident }) => {{
                    yield_token! { if $next { yield_token!($x) } else { $y } }
                }};

                (if $next:literal { $then:stmt } else { $y:ident }) => {{
                    if self.chars.next_if_eq(&$next).is_some() {
                        self.pos += 1;
                        $then
                    } else {
                        yield_token!($y);
                    };
                }};

                ($token:expr) => {{
                    let lexeme = &self.prg[start..self.pos];
                    return Some(Ok(LexToken {
                        lexeme: Cow::Borrowed(lexeme),
                        token: $token,
                        span: self.span(start, lexeme.len()),
                    }));
                }};
            }

            match c {
                // single character tokens

                // basic punctuation symbols
                '.' => yield_token!(Dot),
                ',' => yield_token!(Comma),
                ';' => yield_token!(Semicolon),

                // parenthesis & brackets
                '(' => yield_token!(LeftParen),
                ')' => yield_token!(RightParen),
                '{' => yield_token!(LeftBrace),
                '}' => yield_token!(RightBrace),

                // arithmetic operators
                '+' => yield_token!(Plus),
                '-' => yield_token!(Minus),
                '*' => yield_token!(Star),

                // negation, (in)equality, negation, and relational operators
                '!' => yield_token! { if '=' { BangEqual } else { Bang } },
                '=' => yield_token! { if '=' { EqualEqual } else { Equal } },
                '<' => yield_token! { if '=' { LessEqual } else { Less} },
                '>' => yield_token! { if '=' { GreaterEqual } else { Greater } },

                // slash and comments
                '/' => yield_token! { if '/' { self.advance_until(newline) } else { Slash } },

                // whitespace characters
                c if c.is_whitespace() => {
                    if c == '\n' {
                        self.line += 1;
                        self.line_pos = self.pos;
                    }
                }

                // literal: string
                '"' => {
                    self.visit_until(double_quote, |s, c| {
                        if newline(c) {
                            s.line += 1;
                            s.line_pos = s.pos;
                        }
                    });

                    // closing quote
                    if self.chars.next().is_some() {
                        self.pos += 1;
                    } else {
                        return Some(Err(self.error(start, "Unterminated string.")));
                    };

                    let lexeme = &self.prg[start..self.pos];
                    let text = Cow::Borrowed(lexeme.trim().trim_matches('"'));

                    return Some(Ok(LexToken {
                        lexeme: Cow::Borrowed(lexeme),
                        token: Token::Literal(Literal::Str(text)),
                        span: self.span(start, lexeme.len()),
                    }));
                }

                // literal: number
                c if digit(c) => {
                    let next = self.advance_until(non_digit);

                    if next.is_some_and(dot) && self.peek(2).is_some_and(digit) {
                        // consume the '.'
                        let _ = self.chars.next();
                        self.pos += 1;

                        self.advance_until(non_digit);
                    }

                    let lexeme = &self.prg[start..self.pos];

                    return Some(
                        lexeme
                            .parse()
                            .map(Literal::Num)
                            .map(Token::Literal)
                            .map(|token| LexToken {
                                lexeme: Cow::Borrowed(lexeme),
                                token,
                                span: self.span(start, lexeme.len()),
                            })
                            .map_err(|err| self.error(start, err)),
                    );
                }

                // keyword or identifier
                c if alpha(c) => {
                    self.advance_until(non_alphanumeric);

                    let lexeme = &self.prg[start..self.pos];

                    let token = Cow::Borrowed(lexeme.trim())
                        .try_into()
                        .map_err(Literal::Ident)
                        .map_or_else(Token::Literal, Token::Keyword);

                    return Some(Ok(LexToken {
                        lexeme: Cow::Borrowed(lexeme),
                        token,
                        span: self.span(start, lexeme.len()),
                    }));
                }

                // unexpected chars
                c => return Some(Err(self.error(start, format!("Unexpected character: {c}")))),
            }
        }
    }
}

mod matcher {
    #[inline]
    pub(super) fn double_quote(c: char) -> bool {
        c == '"'
    }

    #[inline]
    pub(super) fn newline(c: char) -> bool {
        c == '\n'
    }

    #[inline]
    pub(super) fn dot(c: char) -> bool {
        c == '.'
    }

    #[inline]
    pub(super) fn digit(c: char) -> bool {
        c.is_ascii_digit()
    }

    #[inline]
    pub(super) fn non_digit(c: char) -> bool {
        !digit(c)
    }

    #[inline]
    pub(super) fn alpha(c: char) -> bool {
        c.is_ascii_alphabetic() || c == '_'
    }

    #[inline]
    pub(super) fn alphanumeric(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_'
    }

    #[inline]
    pub(super) fn non_alphanumeric(c: char) -> bool {
        !alphanumeric(c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! tokenize {
        ($input:expr) => {{
            let mut tokens = Vec::new();
            let mut errors = Vec::new();
            for result in Lexer::new($input) {
                match result {
                    Ok(token) => tokens.push(token),
                    Err(error) => errors.push(error),
                }
            }
            (tokens, errors)
        }};
    }

    #[test]
    fn lexical_errors() {
        let (tokens, errors) = tokenize!("@");
        assert!(tokens.is_empty());
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].source.to_string(), "Unexpected character: @");

        let (actual_tokens, actual_errors) = tokenize!(",.$(#");

        let expected_tokens = vec![
            LexToken {
                lexeme: Cow::Borrowed(","),
                token: Token::Comma,
                span: Span {
                    offset: 0,
                    length: 1,
                    lineno: 1,
                    lineof: 0,
                },
            },
            LexToken {
                lexeme: Cow::Borrowed("."),
                token: Token::Dot,
                span: Span {
                    offset: 1,
                    length: 1,
                    lineno: 1,
                    lineof: 0,
                },
            },
            LexToken {
                lexeme: Cow::Borrowed("("),
                token: Token::LeftParen,
                span: Span {
                    offset: 3,
                    length: 1,
                    lineno: 1,
                    lineof: 0,
                },
            },
        ];

        assert_eq!(expected_tokens, actual_tokens);

        let [err1, err2] = actual_errors.as_slice() else {
            panic!("expected two errors");
        };

        assert_eq!(err1.source.to_string(), "Unexpected character: $");
        assert_eq!(
            err1.span,
            Span {
                offset: 2,
                length: 1,
                lineno: 1,
                lineof: 0,
            }
        );

        assert_eq!(err2.source.to_string(), "Unexpected character: #");
        assert_eq!(
            err2.span,
            Span {
                offset: 4,
                length: 1,
                lineno: 1,
                lineof: 0,
            }
        );
    }
}
