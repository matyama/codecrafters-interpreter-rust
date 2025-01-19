use std::borrow::Cow;
use std::fmt::{Debug, Display};
use std::process::{ExitCode, Termination};

use crate::span::Span;

#[derive(thiserror::Error)]
#[error("[line {}] Error{context}: {source}", span.lineno())]
pub struct SyntaxError {
    pub span: Span,
    pub code: String,
    pub context: Cow<'static, str>,
    pub source: Box<dyn std::error::Error + 'static>,
}

impl SyntaxError {
    pub fn new<M>(source: &str, span: Span, msg: M, loc: ErrLoc) -> SyntaxError
    where
        M: Into<Box<dyn std::error::Error + 'static>>,
    {
        let code = span.snippet(source).to_string();
        SyntaxError {
            span,
            code,
            context: loc.into(),
            source: msg.into(),
        }
    }
}

impl Debug for SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}] SyntaxError{}: {} ('{}')",
            self.span.loc(),
            self.context,
            self.source,
            self.code,
        )
    }
}

impl Termination for SyntaxError {
    #[inline]
    fn report(self) -> ExitCode {
        ExitCode::from(65)
    }
}

#[derive(thiserror::Error)]
#[error("{source}\n[line {}]", span.lineno())]
pub struct RuntimeError {
    pub span: Span,
    pub source: Box<dyn std::error::Error + 'static>,
}

impl Debug for RuntimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] RuntimeError: {}", self.span.loc(), self.source)
    }
}

impl Termination for RuntimeError {
    #[inline]
    fn report(self) -> ExitCode {
        ExitCode::from(70)
    }
}

pub(crate) trait ThrowRuntimeError {
    fn throw(&self, msg: impl Display) -> RuntimeError;
}

#[derive(Debug, Default)]
pub enum ErrLoc {
    At(Cow<'static, str>),
    #[default]
    Eof,
}

impl ErrLoc {
    #[inline]
    pub fn at(loc: impl AsRef<str>) -> Self {
        Self::At(Cow::Owned(format!(" at '{}'", loc.as_ref())))
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_syntax_error() {
        let error = SyntaxError {
            span: Span::new(25, 1, 1, 25),
            code: r#"var result = (a + b) > 7 && "Success" != "Failure" or x >= 5"#.to_string(),
            context: " at 'IDENTIFIER & null'".into(),
            source: "Unexpected character: &".to_string().into(),
        };

        let expected = "[line 1] Error at 'IDENTIFIER & null': Unexpected character: &";
        assert_eq!(expected.to_string(), error.to_string());
    }

    #[test]
    fn display_runtime_error() {
        let span = Span::new(25, 10, 1, 25);

        let error = span.throw("Operands must be numbers.");

        let expected = "Operands must be numbers.\n[line 1]";
        assert_eq!(expected.to_string(), error.to_string());
    }
}
