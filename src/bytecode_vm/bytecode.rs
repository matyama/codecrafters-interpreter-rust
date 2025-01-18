use std::fmt::Display;

use super::error::UnknownOpCode;
use super::value::Value;
use super::{Captures, Disassemble, OpCode};

pub(crate) const MAX_SMALL: u32 = u8::MAX as u32;
pub(crate) const MIN_LONG: u32 = MAX_SMALL + 1;
pub(crate) const MAX_LONG: u32 = 16_777_216 - 1; // 2^24 - 1

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

    #[inline]
    pub fn code(&self) -> &[u8] {
        &self.code
    }

    #[inline]
    pub fn constants(&self) -> &[Value] {
        &self.constants
    }

    pub fn write(&mut self, byte: u8, line: u32) {
        self.code.push(byte);
        self.lines.push(line);
    }

    #[inline]
    pub fn write_op(&mut self, op: OpCode, line: u32) {
        self.write(op as u8, line)
    }

    pub fn write_const(&mut self, value: Value, line: u32) {
        let Ok(offset) = u32::try_from(self.constants.len()) else {
            panic!("chunk can store only {MAX_LONG} constants");
        };

        self.constants.push(value);

        match offset {
            ..=MAX_SMALL => {
                let bytes = [OpCode::Constant as u8, offset as u8];
                self.code.extend_from_slice(&bytes);
                self.lines.repeat(2, line);
            }
            MIN_LONG..=MAX_LONG => {
                let mut bytes = offset.to_be_bytes();
                // SAFETY: bytes is a properly initialized (and aligned) array
                unsafe { bytes.as_mut_ptr().write(OpCode::ConstantLong as u8) }
                self.code.extend_from_slice(&bytes);
                self.lines.repeat(4, line);
            }
            _ => unreachable!("u32::MAX > MAX_LONG"),
        }
    }

    /// Read the index into the `constants` array given an instruction `offset`.
    ///
    /// Note that the `offset` points to the first byte of the instruction, that is to the opcode.
    fn read_const(&self, offset: usize) -> u32 {
        match OpCode::try_from(self.code[offset]) {
            Ok(OpCode::Constant) => self.code[offset + 1] as u32,
            Ok(OpCode::ConstantLong) => {
                let bytes = &self.code[offset..offset + 4];
                // SAFETY: the offset range has length of 4, so casting &[u8] to &[u8; 4] is safe
                let bytes = unsafe { &*(bytes as *const [u8] as *const [u8; 4]) };
                u32::from_be_bytes(*bytes) & 0x00ffffff
            }
            opcode => panic!("{opcode:?} is not a constant"),
        }
    }

    pub fn instruction(&self, offset: usize) -> Result<Option<Instruction<'_>>, UnknownOpCode> {
        use OpCode::*;

        let Some(opcode) = self.code.get(offset) else {
            return Ok(None);
        };

        match OpCode::try_from(opcode) {
            Ok(op @ (Constant | ConstantLong)) => {
                Ok(Some(Instruction::Const(op.name(), self, offset)))
            }

            Ok(op @ (Neg | Add | Sub | Mul | Div | Return)) => {
                Ok(Some(Instruction::Simple(op.name(), self, offset)))
            }

            Err(opcode) => Err(UnknownOpCode { offset, opcode }),
        }
    }

    #[inline]
    fn instructions(&self) -> impl Iterator<Item = Result<Instruction<'_>, UnknownOpCode>> {
        InstructionIter::new(self)
    }

    #[inline]
    pub fn line(&self, offset: usize) -> usize {
        self.lines[offset].line() as usize
    }

    fn line_info(&self, offset: usize) -> LineInfo {
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

pub(crate) enum Instruction<'a> {
    Simple(&'a str, &'a Chunk, usize),
    Const(&'a str, &'a Chunk, usize),
}

impl Display for Instruction<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Simple(name, chunk, offset) => {
                let line = chunk.line_info(*offset);
                writeln!(f, "{offset:04} {line} {name}")
            }
            Self::Const(name, chunk, offset) => {
                let line = chunk.line_info(*offset);
                let constant = chunk.read_const(*offset);
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
    const fn new(repeats: u32, line: u32) -> Self {
        Self(((repeats as u64) << u32::BITS) | line as u64)
    }

    #[inline]
    const fn line(&self) -> u32 {
        self.0 as u32
    }

    #[inline]
    const fn repeats(&self) -> u32 {
        (self.0 >> u32::BITS) as u32
    }

    /// Increment the repeat count by `n`
    #[inline]
    fn repeat(&mut self, n: u32) {
        self.0 += (n as u64) << u32::BITS;
    }
}

/// Runs of line numbers (including comments).
///
/// Each [`Line`] is a run of [`n`](Line::repeats) `code` bytes with the same source line.
#[derive(Debug, Default)]
#[repr(transparent)]
struct Lines(Vec<Line>);

impl Lines {
    #[inline]
    fn push(&mut self, line: u32) {
        self.repeat(1, line);
    }

    fn repeat(&mut self, n: u32, line: u32) {
        match self.0.last_mut() {
            Some(last) if last.line() == line => last.repeat(n),
            _ => self.0.push(Line::new(n, line)),
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
        use OpCode::*;

        let opcode = self.chunk.code.get(self.offset)?;

        Some(match OpCode::try_from(opcode) {
            Ok(op @ (Constant | ConstantLong)) => {
                let meta = op.meta();
                let instr = Instruction::Const(meta.name, self.chunk, self.offset);
                self.offset += meta.len;
                Ok(instr)
            }

            Ok(op @ (Neg | Add | Sub | Mul | Div | Return)) => {
                let meta = op.meta();
                let instr = Instruction::Simple(meta.name, self.chunk, self.offset);
                self.offset += meta.len;
                Ok(instr)
            }

            Err(opcode) => {
                let error = UnknownOpCode {
                    offset: self.offset,
                    opcode,
                };
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

        chunk.write_const(Value(1.2), 123);
        chunk.write_op(OpCode::Return, 123);

        let actual = chunk.disassemble("test chunk").to_string();

        debug_assert_eq!(expected, actual);
    }

    #[test]
    fn many_constants() {
        let mut chunk = Chunk::new();

        for i in 0..MIN_LONG {
            chunk.write_const(Value(i as f64), 1);
        }

        chunk.write_const(Value(1_000.0), 2);

        let output = chunk.disassemble("test long chunk").to_string();
        let last = output
            .lines()
            .last()
            .expect("non-empty disassembly")
            .trim_end();

        assert_eq!("0512    2 OP_CONSTANT_LONG  256 '1000'", last);
    }
}
