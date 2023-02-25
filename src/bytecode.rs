// use std::{io::{self, Write}, ops::{Deref, DerefMut}, process::exit};

// use crate::stdlib::{stdlib, runtime_stdlib};

// #[derive(Clone, Copy, Debug, PartialEq)]
// pub enum Primitive {
//     Unit, I64, F64, Bool  // TODO more
// }

// #[derive(Clone, Copy, Debug, PartialEq)]
// pub enum UwUType<'a> {
//     Struct(&'a UwUStruct<'a>),
//     Primitive(Primitive),
//     Array(&'a UwUType<'a>)
// }

// impl<'a> UwUType<'a> {
//     pub fn name(&self) -> String {
//         match self {
//             UwUType::Struct(s) => s.name.clone(),
//             UwUType::Primitive(t) => match t {
//                 Primitive::Unit => "unit",
//                 Primitive::I64 => "i64",
//                 Primitive::F64 => "f64",
//                 Primitive::Bool => "boow",
//             }.to_string(),
//             UwUType::Array(element) => todo!(),
//         }
//     }

//     pub fn primitives() -> Vec<UwUType<'a>> {
//         vec![
//             UwUType::Primitive(Primitive::Unit),
//             UwUType::Primitive(Primitive::I64),
//             UwUType::Primitive(Primitive::F64),
//             UwUType::Primitive(Primitive::Bool)
//         ]
//     }
// }

// trait F64Ify {
//     fn f(&self) -> f64;
// }

// impl F64Ify for i64 {
//     fn f(&self) -> f64 {
//         unsafe { std::mem::transmute(*self) }
//     }
// }

// #[derive(Debug, PartialEq)]
// pub struct Field<'a> {
//     pub tpe: UwUType<'a>,
//     pub name: String
// }

// #[derive(Debug, PartialEq)]
// pub struct UwUStruct<'a> {
//     pub path: Vec<String>,
//     pub name: String,
//     pub fields: Vec<Field<'a>>
// }

// impl<'a> UwUType<'a> {
//     pub fn to_info(&self) -> FieldInfo {
//         match self {
//             UwUType::Struct(v) => {
//                 FieldInfo::Struct { object_fields: v.fields.iter().map(|x| x.tpe.to_info()).collect() }
//             }
//             UwUType::Primitive(_) => FieldInfo::Primitive,
//             UwUType::Array(t) => FieldInfo::Array(Box::new(t.to_info())),
//         }
//     }
// }

// #[derive(Debug, Clone, PartialEq, Eq)]
// pub enum FieldInfo {
//     Struct { object_fields: Vec<FieldInfo> },
//     Array(Box<FieldInfo>),
//     Primitive
// }

// pub struct UwUInstance<'a> {
//     address: u64,
//     refcount: u32,
//     tpe: &'a FieldInfo,
//     data: Vec<u64>
// }

// struct StackItem<'a> {
//     value: i64,
//     tpe: &'a FieldInfo
// }

// impl<'a> Deref for StackItem<'a> {
//     type Target = i64;

//     fn deref(&self) -> &Self::Target {
//         &self.value
//     }
// }

// impl<'a> DerefMut for StackItem<'a> {
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         &mut self.value
//     }
// }

// impl<'a> StackItem<'a> {
//     fn new(value: i64) -> StackItem<'a> {
//         StackItem { value, tpe: &FieldInfo::Primitive }
//     }
// }

// pub struct StackFrame {
//     return_addr: u64,
//     contents: Vec<i64>
// }

// pub struct NativeFunction {
//     pub name: Vec<String>,
//     pub arg_count: u32,
//     pub lambda: fn(vm: &mut VM)
// }

// pub struct VM<'a> {
//     types: Vec<FieldInfo>,
//     pub stack: Vec<StackFrame>,
//     heap: Vec<UwUInstance<'a>>,
//     program: Vec<Instruction<'a>>,
//     program_counter: u64,
//     native: Vec<NativeFunction>
// }

// #[derive(Clone, Copy, Debug)]
// pub enum Comparison {
//     Zero, NonZero, IGr, ILe, IGrE, ILeE, FGr, FLe, FGrE, FLeE, Eq, NEq
// }

// // TODO: modulo, boolean ops, bitshift
// #[derive(Clone, Copy, Debug)]
// pub enum Instruction<'a> {
//     IADD, ISUB, IMUL, IDIV,
//     FADD, FSUB, FMUL, FDIV,
//     CMP(Comparison),

//     BRANCH(Comparison, u64), CALL(u64), RET,

//     READ, WRITE,

//     ALLOC(&'a FieldInfo), SET { tpe: &'a FieldInfo, offset: u32 }, GET { tpe: &'a FieldInfo, offset: u32 },
//     COPY { frame: u32, word: u32 }, PUSHF, POPF, IMMEDIATE(i64), SETS { frame: u32, word: u32 },
//     NATIVE(u64), HALT
// }

// impl<'a> VM<'a> {
//     pub fn new(program: Vec<Instruction<'a>>, types: Vec<FieldInfo>) -> VM<'a> {
//         VM { types, stack: vec![StackFrame { return_addr: 0, contents: vec![] }], heap: vec![], program, program_counter: 0, native: runtime_stdlib() }
//     }

//     pub fn pop(&mut self) -> i64 {
//         self.stack.last_mut().unwrap().contents.pop().unwrap()
//     }

//     fn popf(&mut self) -> f64 {
//         unsafe { std::mem::transmute(self.pop()) }
//     }

//     pub fn push(&mut self, v: i64) {
//         self.stack.last_mut().unwrap().contents.push(v);
//     }

//     fn pushf(&mut self, v: f64) {
//         self.push(unsafe { std::mem::transmute(v) })
//     }

//     fn pushb(&mut self, v: bool) {
//         self.push(if v { 1 } else { 0 })
//     }

//     pub fn tick(&mut self) {
//         let ins = self.program[self.program_counter as usize];
//         self.program_counter += 1;
//         ins.exec(self);
//     }
// }

// impl<'a> Instruction<'a> {
//     fn exec(&self, vm: &mut VM) {
//         match self {
//             Instruction::IADD => { let b = vm.pop(); let a = vm.pop(); vm.push(a + b) }
//             Instruction::ISUB => { let b = vm.pop(); let a = vm.pop(); vm.push(a - b) }
//             Instruction::IMUL => { let b = vm.pop(); let a = vm.pop(); vm.push(a * b) }
//             Instruction::IDIV => { let b = vm.pop(); let a = vm.pop(); vm.push(a / b) }
            
//             Instruction::FADD => { let b = vm.popf(); let a = vm.popf(); vm.pushf(a + b) }
//             Instruction::FSUB => { let b = vm.popf(); let a = vm.popf(); vm.pushf(a - b) }
//             Instruction::FMUL => { let b = vm.popf(); let a = vm.popf(); vm.pushf(a * b) }
//             Instruction::FDIV => { let b = vm.popf(); let a = vm.popf(); vm.pushf(a / b) }

//             Instruction::CMP(t) => { let b = vm.pop(); let a = vm.pop(); vm.pushb(match t {
//                 Comparison::Zero => a == 0,
//                 Comparison::NonZero => a != 0,
//                 Comparison::IGr => a > b,
//                 Comparison::ILe => a < b,
//                 Comparison::IGrE => a >= b,
//                 Comparison::ILeE => a <= b,
//                 Comparison::FGr => a.f() > b.f(),
//                 Comparison::FLe => a.f() < b.f(),
//                 Comparison::FGrE => a.f() >= b.f(),
//                 Comparison::FLeE => a.f() <= b.f(),
//                 Comparison::Eq => a == b,
//                 Comparison::NEq => a != b
//             }) }

//             Instruction::BRANCH(condition, dst) => todo!(),
//             Instruction::CALL(addr) => { vm.stack.push(StackFrame { return_addr: vm.program_counter, contents: Vec::new() }); vm.program_counter = *addr }
//             Instruction::RET => { let frame = vm.stack.pop().unwrap(); let ret = frame.contents.last().unwrap(); vm.program_counter = frame.return_addr; if vm.stack.is_empty() { exit(0) }; vm.push(*ret) }
//             Instruction::READ => todo!(),
//             Instruction::WRITE => { let byte = vm.pop() as u8; let mut stdout = io::stdout(); stdout.write(&[byte]).unwrap(); stdout.flush().unwrap(); }
//             Instruction::ALLOC(t) => todo!(),
//             Instruction::SET { tpe, offset } => todo!(),
//             Instruction::GET { tpe, offset } => todo!(),
//             Instruction::COPY { frame, word } => { let f = vm.stack[vm.stack.len() - *frame as usize - 1].contents[*word as usize]; vm.push(f); }
//             Instruction::PUSHF => { vm.stack.push(StackFrame { return_addr: 0, contents: Vec::new() }) }
//             Instruction::POPF => { vm.stack.pop(); }
//             Instruction::IMMEDIATE(v) => { vm.push(*v); }
//             Instruction::SETS { frame, word } => todo!(),
//             Instruction::NATIVE(idx) => { let l = vm.native[*idx as usize].lambda; l(vm); },
//             Instruction::HALT => exit(0)
//         }
//     }
// }

// pub fn blah() {
//     let program = vec![
//         Instruction::IMMEDIATE('\n' as i64),
//         Instruction::IMMEDIATE('a' as i64),
//         Instruction::IMMEDIATE(2),
//         Instruction::IADD,
//         Instruction::WRITE,
//         Instruction::WRITE
//     ];

//     let mut vm = VM::new(program, vec![]);

//     vm.tick();
//     vm.tick();
//     vm.tick();
//     vm.tick();
//     vm.tick();
//     vm.tick();
// }
