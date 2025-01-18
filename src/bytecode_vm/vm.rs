use std::fmt::Display;
use std::io::Write;
use std::mem;
use std::ops::{Deref, DerefMut};

use super::bytecode::Chunk;
use super::error::{Error, RuntimeError};
use super::value::Value;
use super::OpCode;

const STACK_MAX: usize = 256;

// XXX: consider stack-allocated fixed-size stack
#[derive(Debug)]
#[repr(transparent)]
struct Stack(Vec<Value>);

impl Deref for Stack {
    type Target = Vec<Value>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Stack {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Display for Stack {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("          ")?;
        for slot in self.iter() {
            write!(f, "[ {slot} ]")?;
        }
        writeln!(f)
    }
}

#[derive(Debug)]
pub struct VM<'a, W: Write> {
    stack: Stack,
    writer: &'a mut W,
}

impl<'a, W: Write> VM<'a, W> {
    #[inline]
    pub fn new(writer: &'a mut W) -> Self {
        Self {
            stack: Stack(Vec::with_capacity(STACK_MAX)),
            writer,
        }
    }

    pub fn interpret(&mut self, chunk: &Chunk) -> Result<(), Error> {
        let Some(head) = chunk.code().first() else {
            // chunk has no instructions to interpret
            return Ok(());
        };

        // initialize the Instruction Pointer (IP)
        let mut ip = head as *const u8;

        // convert IP to an instruction offset/index
        let current_offset = |ip| ip as usize - head as *const u8 as usize;

        macro_rules! read_byte {
            () => {{
                // SAFETY: there's no safety story here (FIXME)
                let i = unsafe { ip.read() };
                ip = unsafe { ip.add(1) };
                i
            }};
        }

        macro_rules! read_constant {
            (bytes = 1) => {{
                &chunk.constants()[read_byte!() as usize]
            }};
            (bytes = 3) => {{
                &chunk.constants()
                    [u32::from_be_bytes([0, read_byte!(), read_byte!(), read_byte!()]) as usize]
            }};
        }

        // TODO: values other than f64
        macro_rules! binary_op {
            ($opcode:expr, $op:tt, $offset:expr) => {{
                let Value(rhs) = self.stack.pop().ok_or_else(|| RuntimeError {
                    line: chunk.line($offset),
                    source: format!("{}: no value on stack", $opcode.name()).into(),
                })?;
                let Value(lhs) = self.stack.pop().ok_or_else(|| RuntimeError {
                    line: chunk.line($offset),
                    source: format!("{}: no value on stack", $opcode.name()).into(),
                })?;
                self.stack.push(Value(lhs $op rhs));
            }};
        }

        // main interpretation loop
        loop {
            let offset = current_offset(ip);

            // log instruction (given current IP) and stack
            #[cfg(debug_assertions)]
            {
                let from_io_err = |err: std::io::Error| RuntimeError {
                    line: chunk.line(offset),
                    source: err.into(),
                };

                writeln!(self.writer, "{}", self.stack).map_err(from_io_err)?;

                match chunk.instruction(offset) {
                    Ok(Some(instruction)) => {
                        writeln!(self.writer, "{instruction}").map_err(from_io_err)?;
                    }
                    Ok(None) => {
                        return Err(Error::RuntimeError(RuntimeError {
                            line: chunk.line(offset),
                            source: format!("Offset out of range: {offset}").into(),
                        }));
                    }
                    Err(err) => {
                        return Err(Error::RuntimeError(RuntimeError {
                            line: chunk.line(offset),
                            source: err.into(),
                        }));
                    }
                }
            }

            // read the opcode of the next instruction pointed to by the IP
            let instruction = read_byte!();

            // XXX: this is pretty unsafe, there's no guarantee that IP points to valid opcode
            match unsafe { mem::transmute::<u8, OpCode>(instruction) } {
                // NOTE: temporarily Return pops a value from the top of the stack and prints it
                OpCode::Return => {
                    return if let Some(value) = self.stack.pop() {
                        writeln!(self.writer, "{value}")
                    } else {
                        writeln!(self.writer)
                    }
                    .and_then(|_| self.writer.flush())
                    .map_err(|err| {
                        Error::RuntimeError(RuntimeError {
                            line: chunk.line(offset),
                            source: err.into(),
                        })
                    });
                }

                // TODO: negate the stack value in place
                op @ OpCode::Neg => {
                    let Value(v) = self.stack.pop().ok_or_else(|| RuntimeError {
                        line: chunk.line(offset),
                        source: format!("{}: no value on stack", op.name()).into(),
                    })?;
                    self.stack.push(Value(-v));
                }

                // binary arithmetic operations: pop two values from the stack and push result back
                OpCode::Add => binary_op!(OpCode::Add, +, offset),
                OpCode::Sub => binary_op!(OpCode::Sub, -, offset),
                OpCode::Mul => binary_op!(OpCode::Mul, *, offset),
                OpCode::Div => binary_op!(OpCode::Div, /, offset),

                // load a constant and push it on top of the current stack
                OpCode::Constant => {
                    let constant = read_constant!(bytes = 1);
                    // XXX: really need a cheap clone here
                    self.stack.push(constant.clone());
                }

                OpCode::ConstantLong => {
                    let constant = read_constant!(bytes = 3);
                    // XXX: really need a cheap clone here
                    self.stack.push(constant.clone());
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interpret_chunk() {
        let mut writer = Vec::new();
        let mut vm = VM::new(&mut writer);

        // repr(S-expr): (- (/ (+ 1.2 3.4) 5.6))
        let mut chunk = Chunk::new();
        chunk.write_const(Value(1.2), 123);
        chunk.write_const(Value(3.4), 123);
        chunk.write_op(OpCode::Add, 123);
        chunk.write_const(Value(5.6), 123);
        chunk.write_op(OpCode::Div, 123);
        chunk.write_op(OpCode::Neg, 123);
        chunk.write_op(OpCode::Return, 123);

        vm.interpret(&chunk).expect("chunk interpreted");

        let output = String::from_utf8(writer).expect("UTF-8 output");
        let result = output.lines().last().expect("some value");
        assert_eq!(result, "-0.8214285714285714");
    }

    #[test]
    fn interpret_chunk_const_long() {
        use crate::bytecode_vm::bytecode::MIN_LONG;

        let mut writer = Vec::new();
        let mut vm = VM::new(&mut writer);

        let mut chunk = Chunk::new();
        for _ in 0..MIN_LONG {
            chunk.write_const(Value(1.0), 123);
        }
        chunk.write_const(Value(1_000.0), 123);
        chunk.write_op(OpCode::Neg, 123);
        chunk.write_op(OpCode::Return, 123);

        vm.interpret(&chunk).expect("chunk interpreted");

        let output = String::from_utf8(writer).expect("UTF-8 output");
        let result = output.lines().last().expect("some value");
        assert_eq!(result, "-1000");
    }

    #[test]
    fn missing_operand() {
        let mut writer = Vec::new();
        let mut vm = VM::new(&mut writer);

        let mut chunk = Chunk::new();
        chunk.write_const(Value(1.0), 123);
        chunk.write_op(OpCode::Add, 123);
        chunk.write_op(OpCode::Return, 123);

        let error = vm.interpret(&chunk).expect_err("Add is missing an operand");
        assert_eq!(error.to_string(), "OP_ADD: no value on stack\n[line 123]");
    }
}
