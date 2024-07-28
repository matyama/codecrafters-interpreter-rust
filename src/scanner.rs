use std::fmt::Display;
use std::process::{ExitCode, Termination};

use crate::Report;
use std::ops::Range;

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug)]
pub enum TokenType {
    // Single character tokens
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Minus,
    Plus,
    Semicolon,
    Slash,
    Star,

    // One or two character tokens
    Bang,
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    // Literals
    //Identifier,
    String,
    //Number

    // Keywords
    // TODO

    // End Of File
    EOF,
}

impl Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LeftParen => write!(f, "LEFT_PAREN"),
            Self::RightParen => write!(f, "RIGHT_PAREN"),
            Self::LeftBrace => write!(f, "LEFT_BRACE"),
            Self::RightBrace => write!(f, "RIGHT_BRACE"),
            Self::Comma => write!(f, "COMMA"),
            Self::Dot => write!(f, "DOT"),
            Self::Minus => write!(f, "MINUS"),
            Self::Plus => write!(f, "PLUS"),
            Self::Semicolon => write!(f, "SEMICOLON"),
            Self::Slash => write!(f, "SLASH"),
            Self::Star => write!(f, "STAR"),
            Self::Bang => write!(f, "BANG"),
            Self::BangEqual => write!(f, "BANG_EQUAL"),
            Self::Equal => write!(f, "EQUAL"),
            Self::EqualEqual => write!(f, "EQUAL_EQUAL"),
            Self::Greater => write!(f, "GREATER"),
            Self::GreaterEqual => write!(f, "GREATER_EQUAL"),
            Self::Less => write!(f, "LESS"),
            Self::LessEqual => write!(f, "LESS_EQUAL"),
            Self::String => write!(f, "STRING"),
            Self::EOF => write!(f, "EOF"),
        }
    }
}

#[derive(Debug)]
pub enum Literal {
    Str(String),
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Str(s) => write!(f, "{s}"),
        }
    }
}

#[derive(Debug)]
pub struct Token {
    ty: TokenType,
    lexeme: String,
    literal: Option<Literal>,
    #[allow(dead_code)]
    line: usize,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref literal) = self.literal {
            write!(f, "{} {} {}", self.ty, self.lexeme, literal)
        } else {
            write!(f, "{} {} null", self.ty, self.lexeme)
        }
    }
}

pub type Tokens = Vec<Token>;

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

    #[inline]
    fn peek(&self) -> Option<char> {
        // FIXME: this is terribly inefficient
        self.source.chars().skip(self.current).take(1).next()
    }

    fn peek_eq(&mut self, expected: char) -> bool {
        let Some(c) = self.peek() else {
            return false;
        };

        if c != expected {
            return false;
        }

        self.current += 1;

        true
    }

    fn advance(&mut self) -> Option<char> {
        // FIXME: this is terribly inefficient
        let c = self.peek()?;
        self.current += 1;
        Some(c)
    }

    /// Returns source text at `start..current`
    fn lexeme(&self) -> String {
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

    fn add_token(&mut self, ty: TokenType, literal: Option<Literal>) {
        self.tokens.push(Token {
            ty,
            lexeme: self.lexeme(),
            literal,
            line: self.line,
        })
    }

    fn advance_until(&mut self, target: char, mut visit: impl FnMut(&mut Self, char)) -> bool {
        while let Some(c) = self.peek() {
            if c == target {
                return false;
            }
            visit(self, c);
            self.advance();
        }
        true
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
                        self.advance_until('\n', |_, _| {});
                    } else {
                        self.add_token(TokenType::Slash, None);
                    }
                }

                // whitespace characters
                '\n' => self.line += 1,
                c if c.is_whitespace() => {}

                // literal: string
                '"' => {
                    let eof = self.advance_until('"', |s, c| {
                        if c == '\n' {
                            s.line += 1;
                        }
                    });

                    if eof {
                        self.report.error(self.line, "Unterminated string.");
                        continue;
                    }

                    // closing quote
                    self.advance();

                    // trim quotes
                    let s = self.string((self.start + 1)..self.current);

                    self.add_token(TokenType::String, Some(Literal::Str(s)));
                }

                // unexpected chars
                c => self
                    .report
                    .error(self.line, format!("Unexpected character: {c}")),
            }
        }

        // NOTE: specifically not using `add_non_lit` to trim trailing newline for the lexeme
        self.tokens.push(Token {
            ty: TokenType::EOF,
            lexeme: String::new(),
            literal: None,
            line: self.line,
        });

        if self.report.had_error {
            Err((self.tokens, LexError))
        } else {
            Ok(self.tokens)
        }
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
    fn error(&mut self, line: usize, msg: impl Display) {
        self.report(line, "", msg)
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
