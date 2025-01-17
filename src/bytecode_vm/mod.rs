#![allow(dead_code)]

mod bytecode;
mod error;
mod value;
mod vm;

pub trait Captures<U> {}
impl<T: ?Sized, U> Captures<U> for T {}

macro_rules! opcode {
    (
        $ident:ident {
            $(
                $variant:ident = {
                    opcode: $opcode:literal,
                    name: $name:literal,
                    len: $len:literal
                },
            )+
        }
    ) => {
        #[derive(Debug)]
        #[repr(u8)]
        pub enum $ident {
            $($variant = $opcode,)+
        }

        impl $ident {
            /// Returns the display name of this [$ident]
            pub(crate) const fn name(self) -> &'static str {
                match self {
                    $(Self::$variant => $name,)+
                }
            }

            pub(crate) const fn meta(self) -> OpMeta {
                match self {
                    $(Self::$variant => OpMeta { name: $name, len: $len },)+
                }
            }
        }

        impl TryFrom<u8> for $ident {
            type Error = u8;

            fn try_from(opcode: u8) -> Result<Self, Self::Error> {
                match opcode {
                    $($opcode => Ok(Self::$variant),)+
                    b => Err(b),
                }
            }
        }

        impl TryFrom<&u8> for $ident {
            type Error = u8;

            #[inline]
            fn try_from(opcode: &u8) -> Result<Self, Self::Error> {
                Self::try_from(*opcode)
            }
        }
    }
}

opcode! {
    OpCode {
        Constant = { opcode: 0, name: "OP_CONSTANT", len: 2 },
        ConstantLong = { opcode: 1, name: "OP_CONSTANT_LONG", len: 4 },
        Neg = { opcode: 2, name: "OP_NEGATE", len: 2 },
        Add = { opcode: 3, name: "OP_ADD", len: 3 },
        Sub = { opcode: 4, name: "OP_SUBTRACT", len: 3 },
        Mul = { opcode: 5, name: "OP_MULTIPLY", len: 3 },
        Div = { opcode: 6, name: "OP_DIVIDE", len: 3 },
        Return = { opcode: 7, name: "OP_RETURN", len: 1 },
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
