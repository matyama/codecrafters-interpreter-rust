use std::fmt::Display;

use crate::bytecode_vm::value::Value;
use crate::bytecode_vm::{Captures, Disassemble, OpCode};

#[derive(Debug, Default)]
pub struct Chunk {
    code: Vec<u8>,
    constants: Vec<Value>,
    lines: Lines,
}

impl Chunk {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    pub fn write(&mut self, byte: u8, line: u32) {
        self.code.push(byte);
        self.lines.push(line);
    }

    pub fn add_constant(&mut self, value: Value) -> u8 {
        // TODO: add support for larger value arrays
        let offset = self.constants.len() as u8;
        self.constants.push(value);
        offset
    }

    #[inline]
    fn instructions(&self) -> impl Iterator<Item = Result<Instruction<'_>, UnknownOpCode>> {
        InstructionIter::new(self)
    }

    fn line(&self, offset: usize) -> LineInfo {
        // TODO: optimization - impl this directly on Lines instead of two index accesses
        let line = self.lines[offset].line();
        if offset > 0 && line == self.lines[offset - 1].line() {
            LineInfo::Cont
        } else {
            LineInfo::Line(line)
        }
    }
}

impl Disassemble for Chunk {
    #[inline]
    fn disassemble<'a>(&'a self, name: &'a str) -> impl std::fmt::Display + Captures<&'a ()> {
        DisplayChunk { chunk: self, name }
    }
}

enum Instruction<'a> {
    Simple(&'a str, &'a Chunk, usize),
    Const(&'a str, &'a Chunk, usize),
}

impl Display for Instruction<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Simple(name, chunk, offset) => {
                let line = chunk.line(*offset);
                writeln!(f, "{offset:04} {line} {name}")
            }
            Self::Const(name, chunk, offset) => {
                let line = chunk.line(*offset);
                let constant = chunk.code[*offset + 1];
                let value = &chunk.constants[constant as usize];
                writeln!(f, "{offset:04} {line} {name:-16} {constant:4} '{value}'")
            }
        }
    }
}

/// Representation of a run of `n` _repeats_ of a _line_ number.
///
/// # Encoding
/// The line is a pair of `(repeats, line)` integers [_run-length encoded_][encoding] into the
/// high and low respective bits of a `u64`.
///
/// [encoding]: https://en.wikipedia.org/wiki/Run-length_encoding
#[derive(Debug)]
#[repr(transparent)]
struct Line(u64);

impl Line {
    #[inline]
    const fn encode(repeats: u32, line: u32) -> u64 {
        ((repeats as u64) << u32::BITS) | line as u64
    }

    #[inline]
    const fn new(line: u32) -> Self {
        Self(Self::encode(1, line))
    }

    #[inline]
    const fn line(&self) -> u32 {
        self.0 as u32
    }

    #[inline]
    const fn repeats(&self) -> u32 {
        (self.0 >> u32::BITS) as u32
    }

    /// Increment the repeat count
    #[inline]
    fn repeat(&mut self) {
        self.0 += 1u64 << u32::BITS;
    }
}

/// Runs of line numbers (including comments).
///
/// Each [`Line`] is a run of [`n`](Line::repeats) `code` bytes with the same source line.
#[derive(Debug, Default)]
#[repr(transparent)]
struct Lines(Vec<Line>);

impl Lines {
    fn push(&mut self, line: u32) {
        match self.0.last_mut() {
            Some(last) if last.line() == line => last.repeat(),
            _ => self.0.push(Line::new(line)),
        }
    }
}

impl std::ops::Index<usize> for Lines {
    type Output = Line;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        let mut i = 0;

        for run in self.0.iter() {
            i += run.repeats() as usize;

            if index < i {
                return run;
            }
        }

        panic!("index out of range: {index}");
    }
}

#[derive(Debug)]
enum LineInfo {
    Line(u32),
    Cont,
}

impl Display for LineInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LineInfo::Line(line) => write!(f, "{line:4}"),
            LineInfo::Cont => write!(f, "{cont:>4}", cont = "|"),
        }
    }
}

#[derive(Debug, thiserror::Error)]
#[error("{0:04} Unknown opcode {1}")]
struct UnknownOpCode(usize, u8);

struct InstructionIter<'a> {
    chunk: &'a Chunk,
    offset: usize,
}

impl<'a> InstructionIter<'a> {
    #[inline]
    fn new(chunk: &'a Chunk) -> Self {
        Self { chunk, offset: 0 }
    }
}

impl<'a> Iterator for InstructionIter<'a> {
    type Item = Result<Instruction<'a>, UnknownOpCode>;

    fn next(&mut self) -> Option<Self::Item> {
        let opcode = self.chunk.code.get(self.offset)?;

        Some(match OpCode::try_from(opcode) {
            Ok(op @ OpCode::Constant) => {
                let meta = op.meta();
                let instr = Instruction::Const(meta.name, self.chunk, self.offset);
                self.offset += meta.len;
                Ok(instr)
            }

            Ok(op @ OpCode::Return) => {
                let meta = op.meta();
                let instr = Instruction::Simple(meta.name, self.chunk, self.offset);
                self.offset += meta.len;
                Ok(instr)
            }

            Err(opcode) => {
                let error = UnknownOpCode(self.offset, opcode);
                self.offset += 1;
                Err(error)
            }
        })
    }
}

pub struct DisplayChunk<'a> {
    chunk: &'a Chunk,
    name: &'a str,
}

impl Display for DisplayChunk<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "== {} ==", self.name)?;

        self.chunk.instructions().try_for_each(|instr| match instr {
            Ok(instr) => instr.fmt(f),
            Err(error) => error.fmt(f),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[should_panic(expected = "index out of range: 0")]
    fn empty_lines() {
        let lines = Lines::default();
        let _ = lines[0];
    }

    #[test]
    #[should_panic(expected = "index out of range: 42")]
    fn line_out_of_range() {
        let lines = Lines::default();
        let _ = lines[42];
    }

    #[test]
    fn lines_encoding() {
        let mut lines = Lines::default();

        lines.push(1);
        lines.push(1);
        lines.push(2);
        lines.push(3);

        assert_eq!(lines[0].line(), 1);
        assert_eq!(lines[0].repeats(), 2);
        assert_eq!(lines[1].line(), 1);
        assert_eq!(lines[1].repeats(), 2);
        assert_eq!(lines[2].line(), 2);
        assert_eq!(lines[2].repeats(), 1);
    }

    macro_rules! disassembly {
        ($s:expr) => {{
            let mut s = String::new();
            for line in $s.lines().filter(|line| !line.trim().is_empty()) {
                s.push_str(line.trim_start());
                s.push('\n');
            }
            s
        }};
    }

    #[test]
    fn disassemble_chunk() {
        let expected = disassembly! {
            "
            == test chunk ==
            0000  123 OP_CONSTANT         0 '1.2'
            0002    | OP_RETURN
            "
        };

        let mut chunk = Chunk::new();

        let constant = chunk.add_constant(Value(1.2));
        chunk.write(OpCode::Constant as u8, 123);
        chunk.write(constant, 123);

        chunk.write(OpCode::Return as u8, 123);

        let actual = chunk.disassemble("test chunk").to_string();

        debug_assert_eq!(expected, actual);
    }
}
