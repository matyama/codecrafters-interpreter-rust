use std::fmt::Display;
use std::ops::{Range, RangeInclusive};
use std::process::{ExitCode, Termination};

use crate::token::{Literal, Token, TokenType, Tokens};
use crate::{Report, Span};
use matcher::*;

macro_rules! add_token {
    ($s:ident; if $lit:literal { $x:ident } else { $y:ident }) => {{
        let ty = if $s.peek_eq($lit) {
            TokenType::$x
        } else {
            TokenType::$y
        };
        $s.add_token(ty, None)
    }};
}

pub struct Scanner {
    source: String,
    tokens: Vec<Token>,
    start: usize,
    current: usize,
    line: usize,
    report: ScanReport,
}

impl Scanner {
    #[inline]
    pub fn new(source: String) -> Self {
        Self {
            source,
            tokens: Vec::new(),
            start: 0,
            current: 0,
            line: 1,
            report: ScanReport::default(),
        }
    }

    // FIXME: this is terribly inefficient
    #[inline]
    fn peek(&self, n: usize) -> Option<char> {
        debug_assert!(n > 0, "zero look-ahead");
        self.source.chars().nth(self.current + n - 1)
    }

    fn peek_eq(&mut self, expected: char) -> bool {
        let Some(c) = self.peek(1) else {
            return false;
        };

        if c != expected {
            return false;
        }

        self.current += 1;

        true
    }

    fn advance(&mut self) -> Option<char> {
        let c = self.peek(1)?;
        self.current += 1;
        Some(c)
    }

    /// Returns source text at `start..current`
    fn text(&self) -> String {
        // FIXME: this is terribly inefficient
        self.source
            .chars()
            .skip(self.start)
            .take(self.current - self.start)
            .collect()
    }

    fn string(&self, span: Range<usize>) -> String {
        // FIXME: this is terribly inefficient
        self.source
            .chars()
            .skip(span.start)
            .take(span.len() - 1)
            .collect()
    }

    fn number(&self, span: RangeInclusive<usize>) -> f64 {
        // FIXME: this is terribly inefficient
        let offset = *span.start();
        let length = span.end() - span.start();

        self.source
            .chars()
            .skip(offset)
            .take(length)
            .collect::<String>()
            .parse()
            .expect("f64")
    }

    fn add_token(&mut self, ty: TokenType, literal: Option<Literal>) {
        self.tokens.push(Token {
            ty,
            lexeme: self.text(),
            literal,
            line: self.line,
        })
    }

    fn advance_until(
        &mut self,
        p: impl Fn(char) -> bool,
        mut visit: impl FnMut(&mut Self, char),
    ) -> Option<char> {
        while let Some(c) = self.peek(1) {
            if p(c) {
                return Some(c);
            }
            visit(self, c);
            self.advance();
        }
        None
    }

    #[inline]
    fn report_error(&mut self, msg: impl Display) {
        self.report.error(Span::Line(self.line), msg);
    }

    pub fn tokenize(mut self) -> Result<Tokens, (Tokens, LexError)> {
        let len = self.source.len();

        while self.current < len {
            self.start = self.current;

            let Some(c) = self.advance() else {
                break;
            };

            match c {
                // single character tokens
                '(' => self.add_token(TokenType::LeftParen, None),
                ')' => self.add_token(TokenType::RightParen, None),
                '{' => self.add_token(TokenType::LeftBrace, None),
                '}' => self.add_token(TokenType::RightBrace, None),
                ',' => self.add_token(TokenType::Comma, None),
                '.' => self.add_token(TokenType::Dot, None),
                '-' => self.add_token(TokenType::Minus, None),
                '+' => self.add_token(TokenType::Plus, None),
                ';' => self.add_token(TokenType::Semicolon, None),
                '*' => self.add_token(TokenType::Star, None),

                // negation, (in)equality, negation, and relational operators
                '!' => add_token! { self; if '=' { BangEqual } else { Bang } },
                '=' => add_token! { self; if '=' { EqualEqual } else { Equal } },
                '<' => add_token! { self; if '=' { LessEqual } else { Less} },
                '>' => add_token! { self; if '=' { GreaterEqual } else { Greater } },

                // slash and comments
                '/' => {
                    if self.peek_eq('/') {
                        self.advance_until(newline, noop);
                    } else {
                        self.add_token(TokenType::Slash, None);
                    }
                }

                // whitespace characters
                '\n' => self.line += 1,
                c if c.is_whitespace() => {}

                // literal: string
                '"' => {
                    let Some(_) = self.advance_until(double_quote, |s, c| {
                        if newline(c) {
                            s.line += 1;
                        }
                    }) else {
                        self.report_error("Unterminated string.");
                        continue;
                    };

                    // closing quote
                    self.advance();

                    // trim quotes
                    let s = self.string((self.start + 1)..self.current);

                    self.add_token(TokenType::String, Some(Literal::Str(s)));
                }

                // literal: number
                c if digit(c) => {
                    let next = self.advance_until(non_digit, noop);

                    if next.is_some_and(dot) && self.peek(2).is_some_and(digit) {
                        // consume the '.'
                        self.advance();

                        self.advance_until(non_digit, noop);
                    }

                    let n = self.number(self.start..=self.current);

                    self.add_token(TokenType::Number, Some(Literal::Num(n)));
                }

                c if alpha(c) => {
                    self.advance_until(non_alphanumeric, noop);
                    let text = self.text();
                    let ty = TokenType::kw_or_ident(text);
                    self.add_token(ty, None);
                }

                // unexpected chars
                c => self.report_error(format!("Unexpected character: {c}")),
            }
        }

        self.tokens.push(Token::eof(self.line));

        if self.report.had_error {
            Err((self.tokens, LexError))
        } else {
            Ok(self.tokens)
        }
    }
}

fn noop(_: &mut Scanner, _: char) {}

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

#[derive(Default)]
struct ScanReport {
    had_error: bool,
}

impl Report for ScanReport {
    fn report(&mut self, line: usize, location: &str, msg: impl Display) {
        eprintln!("[line {line}] Error{location}: {msg}");
        self.had_error = true;
    }

    #[inline]
    fn error(&mut self, span: Span<'_>, msg: impl Display) {
        self.report(span.line(), "", msg)
    }
}

#[derive(Debug)]
pub struct LexError;

impl Termination for LexError {
    #[inline]
    fn report(self) -> ExitCode {
        ExitCode::from(65)
    }
}
