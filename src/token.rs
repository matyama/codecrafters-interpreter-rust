use std::borrow::Cow;
use std::fmt::{Display, Write as _};

use crate::span::Span;

pub const THIS: &str = Keyword::This.name();
pub const SUPER: &str = Keyword::Super.name();

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Keyword {
    And,
    Class,
    Else,
    False,
    Fun,
    For,
    If,
    Nil,
    Or,
    Print,
    Return,
    Super,
    This,
    True,
    Var,
    While,
}

impl Keyword {
    pub const fn name(self) -> &'static str {
        match self {
            Self::And => "and",
            Self::Class => "class",
            Self::Else => "else",
            Self::False => "false",
            Self::Fun => "fun",
            Self::For => "for",
            Self::If => "if",
            Self::Nil => "nil",
            Self::Or => "or",
            Self::Print => "print",
            Self::Return => "return",
            Self::Super => "super",
            Self::This => "this",
            Self::True => "true",
            Self::Var => "var",
            Self::While => "while",
        }
    }
}

impl<'a> TryFrom<&'a str> for Keyword {
    type Error = &'a str;

    fn try_from(ident: &'a str) -> Result<Self, Self::Error> {
        macro_rules! check {
            ($start:literal, $length:literal, $rest:literal => $kw:ident) => {{
                #[allow(deprecated)]
                let start = crate::lexer::unstable::ceil_char_boundary(ident, $start);
                if ident.len() == $start + $length && &ident.as_bytes()[start..] == $rest {
                    Ok(Self::$kw)
                } else {
                    Err(ident)
                }
            }};
        }

        let mut chars = ident.chars();

        match chars.next() {
            Some('a') => check!(1, 2, b"nd" => And),
            Some('c') => check!(1, 4, b"lass" => Class),
            Some('e') => check!(1, 3, b"lse" => Else),
            Some('f') => match chars.next() {
                Some('a') => check!(2, 3, b"lse" => False),
                Some('o') => check!(2, 1, b"r" => For),
                Some('u') => check!(2, 1, b"n" => Fun),
                _ => Err(ident),
            },
            Some('i') => check!(1, 1, b"f" => If),
            Some('n') => check!(1, 2, b"il" => Nil),
            Some('o') => check!(1, 1, b"r" => Or),
            Some('p') => check!(1, 4, b"rint" => Print),
            Some('r') => check!(1, 5, b"eturn" => Return),
            Some('s') => check!(1, 4, b"uper" => Super),
            Some('t') => match chars.next() {
                Some('h') => check!(2, 2, b"is" => This),
                Some('r') => check!(2, 2, b"ue" => True),
                _ => Err(ident),
            },
            Some('v') => check!(1, 2, b"ar" => Var),
            Some('w') => check!(1, 4, b"hile" => While),
            _ => Err(ident),
        }
    }
}

impl<'a> TryFrom<Cow<'a, str>> for Keyword {
    type Error = Cow<'a, str>;

    fn try_from(ident: Cow<'a, str>) -> Result<Self, Self::Error> {
        match ident.as_ref().try_into() {
            Ok(keyword) => Ok(keyword),
            Err(_) => Err(ident),
        }
    }
}

impl AsRef<str> for Keyword {
    #[inline]
    fn as_ref(&self) -> &str {
        self.into()
    }
}

impl From<Keyword> for &'static str {
    #[inline]
    fn from(keyword: Keyword) -> Self {
        keyword.name()
    }
}

impl From<&Keyword> for &'static str {
    #[inline]
    fn from(keyword: &Keyword) -> Self {
        Self::from(*keyword)
    }
}

impl Display for Keyword {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.into())
    }
}

#[repr(transparent)]
struct KeywordTypeFmt(Keyword);

impl Display for KeywordTypeFmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Keyword::And => write!(f, "AND"),
            Keyword::Class => write!(f, "CLASS"),
            Keyword::Else => write!(f, "ELSE"),
            Keyword::False => write!(f, "FALSE"),
            Keyword::Fun => write!(f, "FUN"),
            Keyword::For => write!(f, "FOR"),
            Keyword::If => write!(f, "IF"),
            Keyword::Nil => write!(f, "NIL"),
            Keyword::Or => write!(f, "OR"),
            Keyword::Print => write!(f, "PRINT"),
            Keyword::Return => write!(f, "RETURN"),
            Keyword::Super => write!(f, "SUPER"),
            Keyword::This => write!(f, "THIS"),
            Keyword::True => write!(f, "TRUE"),
            Keyword::Var => write!(f, "VAR"),
            Keyword::While => write!(f, "WHILE"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct LexToken<'prg> {
    /// Raw input slice
    pub lexeme: Cow<'prg, str>,

    /// Token corresponding to the lexeme
    pub token: Token<'prg>,

    /// Span of this token in the input
    pub span: Span,
}

impl Display for LexToken<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let token_type = self.token.type_fmt();

        match self.token {
            Token::Literal(ref literal @ (Literal::Str(_) | Literal::Num(_))) => {
                write!(f, "{} {} {}", token_type, self.lexeme, literal)
            }
            _ => write!(f, "{} {} null", token_type, self.lexeme),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Token<'a> {
    // Single character tokens

    // basic punctuation symbols
    Dot,
    Comma,
    Semicolon,

    // parenthesis & brackets
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,

    // arithmetic operators
    Plus,
    Minus,
    Star,
    Slash,

    // unary operators
    Bang,

    // relational operators
    BangEqual,
    Equal,
    EqualEqual,
    Greater,
    GreaterEqual,
    Less,
    LessEqual,

    /// Literal values (identifiers, strings, numbers)
    Literal(Literal<'a>),

    /// Language keywords
    Keyword(Keyword),
}

impl Token<'_> {
    #[inline]
    fn type_fmt(&self) -> TokenTypeFmt<'_> {
        TokenTypeFmt(self)
    }
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Dot => f.write_char('.'),
            Self::Comma => f.write_char(','),
            Self::Semicolon => f.write_char(';'),
            Self::LeftParen => f.write_char('('),
            Self::RightParen => f.write_char(')'),
            Self::LeftBrace => f.write_char('{'),
            Self::RightBrace => f.write_char('}'),
            Self::Plus => f.write_char('+'),
            Self::Minus => f.write_char('-'),
            Self::Star => f.write_char('*'),
            Self::Slash => f.write_char('/'),
            Self::Bang => f.write_char('!'),
            Self::BangEqual => f.write_str("!="),
            Self::Equal => f.write_char('='),
            Self::EqualEqual => f.write_str("=="),
            Self::Greater => f.write_char('>'),
            Self::GreaterEqual => f.write_str(">="),
            Self::Less => f.write_char('<'),
            Self::LessEqual => f.write_str("<="),
            Self::Literal(literal) => literal.fmt(f),
            Self::Keyword(keyword) => keyword.fmt(f),
        }
    }
}

#[repr(transparent)]
struct TokenTypeFmt<'a>(&'a Token<'a>);

impl Display for TokenTypeFmt<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            Token::Dot => write!(f, "DOT"),
            Token::Comma => write!(f, "COMMA"),
            Token::Semicolon => write!(f, "SEMICOLON"),
            Token::LeftParen => write!(f, "LEFT_PAREN"),
            Token::RightParen => write!(f, "RIGHT_PAREN"),
            Token::LeftBrace => write!(f, "LEFT_BRACE"),
            Token::RightBrace => write!(f, "RIGHT_BRACE"),
            Token::Plus => write!(f, "PLUS"),
            Token::Minus => write!(f, "MINUS"),
            Token::Star => write!(f, "STAR"),
            Token::Slash => write!(f, "SLASH"),
            Token::Bang => write!(f, "BANG"),
            Token::BangEqual => write!(f, "BANG_EQUAL"),
            Token::Equal => write!(f, "EQUAL"),
            Token::EqualEqual => write!(f, "EQUAL_EQUAL"),
            Token::Greater => write!(f, "GREATER"),
            Token::GreaterEqual => write!(f, "GREATER_EQUAL"),
            Token::Less => write!(f, "LESS"),
            Token::LessEqual => write!(f, "LESS_EQUAL"),
            Token::Literal(Literal::Ident(_)) => write!(f, "IDENTIFIER"),
            Token::Literal(Literal::Str(_)) => write!(f, "STRING"),
            Token::Literal(Literal::Num(_)) => write!(f, "NUMBER"),
            Token::Keyword(keyword) => KeywordTypeFmt(*keyword).fmt(f),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum Literal<'a> {
    /// Name (alphabetical) of either a register or label
    Ident(Cow<'a, str>),
    /// String values with lexeme of the form `"some text"`
    Str(Cow<'a, str>),
    /// Integral numeric values
    Num(f64),
}

impl Display for Literal<'_> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Ident(s) => f.write_str(s),
            Self::Str(s) => write!(f, "{s}"),
            Self::Num(n) if n.fract() > 0.0 => write!(f, "{n}"),
            Self::Num(n) => write!(f, "{n:.1}"),
        }
    }
}

/// Dummy End Of File Token
#[allow(clippy::upper_case_acronyms)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EOF;

impl std::fmt::Display for EOF {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "EOF  null")
    }
}
