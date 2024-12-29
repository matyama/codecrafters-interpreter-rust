use std::borrow::Cow;
use std::fmt::Display;

use crate::span::Span;

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

impl<'a> TryFrom<&'a str> for Keyword {
    type Error = &'a str;

    fn try_from(ident: &'a str) -> Result<Self, Self::Error> {
        Ok(match ident {
            "and" => Self::And,
            "class" => Self::Class,
            "else" => Self::Else,
            "false" => Self::False,
            "for" => Self::For,
            "fun" => Self::Fun,
            "if" => Self::If,
            "nil" => Self::Nil,
            "or" => Self::Or,
            "print" => Self::Print,
            "return" => Self::Return,
            "super" => Self::Super,
            "this" => Self::This,
            "true" => Self::True,
            "var" => Self::Var,
            "while" => Self::While,
            ident => return Err(ident),
        })
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

impl Display for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::And => write!(f, "AND"),
            Self::Class => write!(f, "CLASS"),
            Self::Else => write!(f, "ELSE"),
            Self::False => write!(f, "FALSE"),
            Self::Fun => write!(f, "FUN"),
            Self::For => write!(f, "FOR"),
            Self::If => write!(f, "IF"),
            Self::Nil => write!(f, "NIL"),
            Self::Or => write!(f, "OR"),
            Self::Print => write!(f, "PRINT"),
            Self::Return => write!(f, "RETURN"),
            Self::Super => write!(f, "SUPER"),
            Self::This => write!(f, "THIS"),
            Self::True => write!(f, "TRUE"),
            Self::Var => write!(f, "VAR"),
            Self::While => write!(f, "WHILE"),
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
            Token::Keyword(keyword) => write!(f, "{keyword}"),
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
