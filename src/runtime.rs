use std::{collections::HashMap, process::exit};

use crate::{newcompiler::UwUTy, stdlib::NativeFunction};

#[derive(Debug, Clone)]
pub enum FieldInfo {
    Primitive,
    Array(Box<FieldInfo>),
    Fields(Vec<FieldInfo>)
}

pub struct VM<'a> {
    types: Vec<FieldInfo>,
    heap: HashMap<u64, UwUIns<'a>>,
    stack: Vec<StackFrame<'a>>,
    program: Vec<Instruction<'a>>,
    program_counter: usize
}

struct StackFrame<'b> {
    return_addr: u64,
    values: Vec<(i64, &'b FieldInfo)>
}

enum UwUIns<'b> {
    Arr { item_type: &'b FieldInfo, items: Vec<FieldInfo> },
    Struct { tpe: &'b FieldInfo, data: Vec<i64> }
}

#[derive(Debug, Clone)]
pub enum Cond {
    Always, Never,
    ILe, ILeE, Eq, IGrE, IGr,
    FLe, FLeE,     FGrE, FGr, FNaN, FInf
}

#[derive(Debug, Clone)]
pub enum Instruction<'b> {
    // flow control
    HALT, BRANCH(Cond, u64), CALL(u64, u32),

    // memory
    PUSHFR, POPFR, PUSH(i64), POP, COPY { from_top: u32, in_frame: u32 }, MOV { from_top: u32, in_frame: u32 },
    ALLOC(FieldInfo),
    ALLOCA(FieldInfo),
    
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

impl<'a> VM<'a> {
    pub fn tick(&mut self) {
        let instruction = &self.program[self.program_counter];
        self.program_counter += 1;

        match instruction {
            Instruction::HALT => exit(0),
            Instruction::BRANCH(_, _) => todo!(),
            Instruction::CALL(_, _) => todo!(),
            Instruction::PUSHFR => todo!(),
            Instruction::POPFR => todo!(),
            Instruction::PUSH(_) => todo!(),
            Instruction::POP => todo!(),
            Instruction::COPY { from_top, in_frame } => todo!(),
            Instruction::MOV { from_top, in_frame } => todo!(),
            Instruction::ALLOC(_) => todo!(),
            Instruction::ALLOCA(_) => todo!(),
            Instruction::GET(_) => todo!(),
            Instruction::SET(_) => todo!(),
            Instruction::GETA => todo!(),
            Instruction::SETA => todo!(),
            Instruction::IADD => todo!(),
            Instruction::ISUB => todo!(),
            Instruction::IMUL => todo!(),
            Instruction::IDIV => todo!(),
            Instruction::IMOD => todo!(),
            Instruction::FADD => todo!(),
            Instruction::FSUB => todo!(),
            Instruction::FMUL => todo!(),
            Instruction::FDIV => todo!(),
            Instruction::CMP(_) => todo!(),
            Instruction::NATIVE(_) => todo!(),
        }
    }

    fn popi(&mut self) -> i64 {
        self.stack.last_mut().unwrap().values.pop().unwrap().0
    }

    fn popf(&mut self) -> f64 {
        unsafe { std::mem::transmute(self.popi()) }
    }

    fn popb(&mut self) -> bool {
        self.popi() != 0
    }

    fn pushi(&mut self, v: i64) {
        self.stack.last_mut().unwrap().values.push((v, &FieldInfo::Primitive))
    }
}
