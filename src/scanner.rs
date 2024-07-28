use std::fmt::Display;

#[allow(clippy::upper_case_acronyms)]
#[derive(Debug)]
pub enum TokenType {
    // Single character tokens
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,

    // One or two character tokens
    // TODO

    // Literals
    // TODO

    // Keywords
    // TODO

    // End Of File
    EOF,
}

impl Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenType::LeftParen => write!(f, "LEFT_PAREN"),
            TokenType::RightParen => write!(f, "RIGHT_PAREN"),
            TokenType::LeftBrace => write!(f, "LEFT_BRACE"),
            TokenType::RightBrace => write!(f, "RIGHT_BRACE"),
            TokenType::EOF => write!(f, "EOF"),
        }
    }
}

#[derive(Debug)]
pub enum Literal {}

impl Display for Literal {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
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

    fn advance(&mut self) -> char {
        // FIXME: this is terribly inefficient
        let c = self
            .source
            .chars()
            .skip(self.current)
            .take(1)
            .next()
            .unwrap();
        self.current += 1;
        c
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

    fn add_token(&mut self, ty: TokenType, literal: Option<Literal>) {
        self.tokens.push(Token {
            ty,
            lexeme: self.lexeme(),
            literal,
            line: self.line,
        })
    }

    pub fn tokenize(mut self) -> Result<Vec<Token>, ScanReport> {
        let len = self.source.len();

        while self.current < len {
            self.start = self.current;

            match self.advance() {
                '(' => self.add_token(TokenType::LeftParen, None),
                ')' => self.add_token(TokenType::RightParen, None),
                '{' => self.add_token(TokenType::LeftBrace, None),
                '}' => self.add_token(TokenType::RightBrace, None),
                '\n' => self.line += 1,
                c if c.is_whitespace() => {}
                _ => self.report.error(self.line, "Unexpected character"),
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
            Err(self.report)
        } else {
            Ok(self.tokens)
        }
    }
}

#[derive(Default)]
pub struct ScanReport {
    had_error: bool,
}

trait Report {
    fn report(&mut self, line: usize, location: &str, msg: &str);

    fn error(&mut self, line: usize, msg: &str);
}

impl Report for ScanReport {
    fn report(&mut self, line: usize, location: &str, msg: &str) {
        eprintln!("[line {line}] Error{location}: {msg}");
        self.had_error = true;
    }

    #[inline]
    fn error(&mut self, line: usize, msg: &str) {
        self.report(line, "", msg)
    }
}
