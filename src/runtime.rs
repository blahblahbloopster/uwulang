use std::collections::HashMap;

use crate::{newcompiler::UwUTy, stdlib::NativeFunction};

pub struct VM<'a> {
    types: Vec<UwUTy<'a>>,
    heap: HashMap<u64, UwUIns<'a>>,
    stack: Vec<StackFrame<'a>>
}

struct StackFrame<'a> {
    return_addr: u64,
    values: Vec<(u64, &'a UwUTy<'a>)>
}

enum UwUIns<'a> {
    Arr { item_type: &'a UwUTy<'a>, items: Vec<UwUIns<'a>> },
    Struct { tpe: &'a UwUTy<'a>, data: Vec<u64> }
}

pub enum Cond {
    Always, Never,
    ILe, ILeE, Eq, IGrE, IGr,
    FLe, FLeE,     FGrE, FGr, FNaN, FInf
}

pub enum Instruction<'b> {
    // flow control
    HALT, BRANCH(Cond), CALL,

    // memory
    PUSHFR, POPFR, PUSH(u64), POP,
    ALLOC(&'b UwUTy<'b>),
    ALLOCA(&'b UwUTy<'b>),
    
    /// Gets the nth field from the last object on the stack (does NOT pop)
    GET(u32),
    /// Sets the nth field from the second-to-last object on the stack to the last value, then pops it
    SET(u32),
    GETA, SETA,

    // arithmetic
    IADD, ISUB, IMUL, IDIV, IMOD,
    FADD, FSUB, FMUL, FDIV,

    CMP(Cond),

    NATIVE(&'b NativeFunction<'b>)
}

impl<'a> Instruction<'a> {
    pub fn num_popped(&self) -> i32 {
        match self {
            Instruction::HALT => 0,
            Instruction::BRANCH(_) => 2,
            Instruction::CALL => 0,
            Instruction::PUSHFR => 0,
            Instruction::POPFR => 0,
            Instruction::PUSH(_) => 0,
            Instruction::POP => 1,
            Instruction::ALLOC(_) => 0,
            Instruction::ALLOCA(_) => 1,
            Instruction::GET(_) => 0,
            Instruction::SET(_) => 1,
            Instruction::GETA => 1,
            Instruction::SETA => 2,
            Instruction::IADD => 2,
            Instruction::ISUB => 2,
            Instruction::IMUL => 2,
            Instruction::IDIV => 2,
            Instruction::IMOD => 2,
            Instruction::FADD => 2,
            Instruction::FSUB => 2,
            Instruction::FMUL => 2,
            Instruction::FDIV => 2,
            Instruction::CMP(_) => 2,
            Instruction::NATIVE(v) => v.args.len() as i32
        }
    }

    pub fn num_pushed(&self) -> i32 {
        match self {
            Instruction::HALT => 0,
            Instruction::BRANCH(_) => 0,
            Instruction::CALL => 1,
            Instruction::PUSHFR => 0,
            Instruction::POPFR => 0,
            Instruction::PUSH(_) => 1,
            Instruction::POP => 0,
            Instruction::ALLOC(_) => 1,
            Instruction::ALLOCA(_) => 1,
            Instruction::GET(_) => 1,
            Instruction::SET(_) => 0,
            Instruction::GETA => 1,
            Instruction::SETA => 0,
            Instruction::IADD => 1,
            Instruction::ISUB => 1,
            Instruction::IMUL => 1,
            Instruction::IDIV => 1,
            Instruction::IMOD => 1,
            Instruction::FADD => 1,
            Instruction::FSUB => 1,
            Instruction::FMUL => 1,
            Instruction::FDIV => 1,
            Instruction::CMP(_) => 1,
            Instruction::NATIVE(_) => 1
        }
    }

    pub fn net_stack(&self) -> i32 {
        self.num_pushed() - self.num_popped()
    }
}
