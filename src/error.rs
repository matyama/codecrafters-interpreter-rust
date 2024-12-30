use std::borrow::Cow;
use std::fmt::Debug;
use std::process::{ExitCode, Termination};

use crate::span::Span;

#[derive(thiserror::Error)]
#[error("[line {}] Error{context}: {source}", span.lineno)]
pub struct SyntaxError {
    pub span: Span,
    pub code: String,
    pub context: Cow<'static, str>,
    pub source: Box<dyn std::error::Error + 'static>,
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

// TODO: RuntimeError

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn display_syntax_error() {
        let error = SyntaxError {
            span: Span {
                offset: 25,
                length: 1,
                lineno: 1,
                lineof: 25,
            },
            code: r#"var result = (a + b) > 7 && "Success" != "Failure" or x >= 5"#.to_string(),
            context: " at 'IDENTIFIER & null'".into(),
            source: "Unexpected character: &".to_string().into(),
        };

        let expected = "[line 1] Error at 'IDENTIFIER & null': Unexpected character: &";
        assert_eq!(expected.to_string(), error.to_string());
    }
}
