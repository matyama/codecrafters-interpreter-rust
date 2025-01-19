use std::process::{ExitCode, Termination};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    CompileError(#[from] CompileError),
    #[error(transparent)]
    RuntimeError(#[from] RuntimeError),
}

#[derive(Debug, thiserror::Error)]
#[error("[line {line}] CompileError")]
pub struct CompileError {
    pub line: usize,
    // TODO: context fields
}

impl Termination for CompileError {
    #[inline]
    fn report(self) -> ExitCode {
        ExitCode::from(65)
    }
}

// TODO: replace with `crate::error::RuntimeError`
//  - this involves generalizing bytecode Chunk to use Span instead of Line
#[derive(Debug, thiserror::Error)]
#[error("{source}\n[line {line}]")]
pub struct RuntimeError {
    pub line: usize,
    pub source: Box<dyn std::error::Error + 'static>,
}

impl Termination for RuntimeError {
    #[inline]
    fn report(self) -> ExitCode {
        ExitCode::from(70)
    }
}

#[derive(Debug, thiserror::Error)]
#[error("{offset:04} Unknown opcode {opcode}")]
pub(crate) struct UnknownOpCode {
    pub(crate) offset: usize,
    pub(crate) opcode: u8,
}
