use std::borrow::Cow;
use std::fmt::Debug;
use std::process::{ExitCode, Termination};

use crate::span::Span;

#[derive(thiserror::Error)]
#[error("[line {}] Error{error}: {source}", span.lineno)]
pub struct SyntaxError {
    pub error: Cow<'static, str>,
    pub code: String,
    pub span: Span,
    pub source: Box<dyn std::error::Error + 'static>,
}

impl Debug for SyntaxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[{}] SyntaxError{}: {} ('{}')",
            self.span.loc(),
            self.error,
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

// TODO: RuntimeError

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_syntax_error() {
        let error = SyntaxError {
            error: " at 'IDENTIFIER & null'".into(),
            code: r#"var result = (a + b) > 7 && "Success" != "Failure" or x >= 5"#.to_string(),
            span: Span {
                offset: 25,
                length: 1,
                lineno: 1,
                lineof: 25,
            },
            source: "Unexpected character: &".to_string().into(),
        };

        let expected = "[line 1] Error at 'IDENTIFIER & null': Unexpected character: &";
        assert_eq!(expected.to_string(), error.to_string());
    }
}
