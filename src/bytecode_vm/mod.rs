#![allow(dead_code)]

mod bytecode;
mod value;

pub trait Captures<U> {}
impl<T: ?Sized, U> Captures<U> for T {}

#[derive(Debug)]
#[repr(u8)]
pub enum OpCode {
    Constant = 0,
    ConstantLong = 1,
    Return = 2,
}

impl OpCode {
    pub(crate) const fn meta(self) -> OpMeta {
        match self {
            Self::Constant => OpMeta {
                name: "OP_CONSTANT",
                len: 2,
            },
            Self::ConstantLong => OpMeta {
                name: "OP_CONSTANT_LONG",
                len: 4,
            },
            Self::Return => OpMeta {
                name: "OP_RETURN",
                len: 1,
            },
        }
    }
}

impl TryFrom<u8> for OpCode {
    type Error = u8;

    fn try_from(opcode: u8) -> Result<Self, Self::Error> {
        match opcode {
            0 => Ok(Self::Constant),
            1 => Ok(Self::ConstantLong),
            2 => Ok(Self::Return),
            b => Err(b),
        }
    }
}

impl TryFrom<&u8> for OpCode {
    type Error = u8;

    #[inline]
    fn try_from(opcode: &u8) -> Result<Self, Self::Error> {
        Self::try_from(*opcode)
    }
}

/// [OpCode] metadata
pub(crate) struct OpMeta {
    /// [OpCode] display name
    name: &'static str,
    /// Instruction length [bytes] including the [OpCode].
    len: usize,
}

pub trait Disassemble {
    fn disassemble<'a>(&'a self, name: &'a str) -> impl std::fmt::Display + Captures<&'a ()>;
}
