use std::{collections::HashMap, process::exit};

use rand::{thread_rng, RngCore};
use crate::{stdlib::{STDLIB_FUNCS, NativeType, UNIT}, Type, newcompiler::{UwUTy, InstructionBuilder}};

#[derive(Debug, Clone, PartialEq)]
pub enum FieldInfo {
    Primitive,
    Array(Box<FieldInfo>),
    Fields(Vec<FieldInfo>)
}

pub struct VM {
    types: Vec<FieldInfo>,
    pub heap: HashMap<i64, UwUIns>,
    stack: Vec<StackFrame>,
    program: Vec<Instruction>,
    program_counter: usize,
    mark: bool
}

#[derive(Debug, Clone)]
struct StackFrame {
    return_addr: Option<u64>,
    values: Vec<(i64, FieldInfo)>
}

#[derive(Debug)]  // TODO: these can be merged
pub enum UwUIns {
    Arr { mark: bool, item_type: FieldInfo, items: Vec<Option<i64>> },
    Struct { mark: bool, tpe: usize, data: Vec<i64> }
}

#[derive(Debug, Clone, Copy)]
pub enum Cond {
    Always, Never,
    ILe, ILeE, Eq, NEq, IGrE, IGr,
    FLe, FLeE,          FGrE, FGr, FNaN, FInf
}

#[derive(Debug, Clone)]
pub enum Tpe {
    Ref(usize),
    Array(Box<Tpe>),
    Native
}

impl Tpe {
    fn as_field_info(&self, types: &Vec<FieldInfo>) -> FieldInfo {
        match self {
            Tpe::Ref(n) => types[*n].clone(),
            Tpe::Array(v) => FieldInfo::Array(Box::new(v.as_field_info(types))),
            Tpe::Native => FieldInfo::Primitive
        }
    }
}

impl<'a, 'b> UwUTy<'b> {
    pub fn as_tpe(&self, out: &InstructionBuilder<'a, 'b>) -> Tpe {
        match self {
            UwUTy::Struct(_) => Tpe::Ref(out.types.iter().enumerate().find(|x| x.1 == &self.to_info()).unwrap().0),
            UwUTy::Native(_) => Tpe::Native,
            UwUTy::Array(v) => Tpe::Array(Box::new(v.as_tpe(out)))
        }
    }
}

#[derive(Debug, Clone)]
pub enum Instruction {
    // flow control
    HALT, BRANCH(Cond, u64), CALL(u64, u32), RET,

    // memory
    PUSHFR, POPFR, PUSH(i64), POP, COPY { from_top: u32, in_frame: u32 }, MOV { from_top: u32, in_frame: u32 },
    ALLOC(usize),
    ALLOCA(Tpe),
    
    GET(u32),
    SET(u32),
    GETA, SETA,

    // arithmetic
    IADD, ISUB, IMUL, IDIV, IMOD,
    FADD, FSUB, FMUL, FDIV,

    CMP(Cond),

    NATIVE(usize)
}

impl VM {
    pub fn new(program: Vec<Instruction>, types: Vec<FieldInfo>) -> VM {
        VM {
            types,
            heap: HashMap::new(),
            stack: vec![StackFrame { return_addr: None, values: vec![] }],
            program,
            program_counter: 0,
            mark: false
        }
    }

    fn evaluate(&mut self, cond: Cond) -> bool {
        match cond {
            Cond::Always => { return true }
            Cond::Never => { return false }
            Cond::FNaN => { return self.popf().is_nan() }
            Cond::FInf => { return self.popf().is_infinite() }
            _ => {}
        }

        let a = self.popi();
        let b = self.popi();
        let af: f64 = unsafe { std::mem::transmute(a) };
        let bf: f64 = unsafe { std::mem::transmute(b) };

        match cond {
            Cond::Always => panic!(),
            Cond::Never => panic!(),
            Cond::ILe => a < b,
            Cond::ILeE => a <= b,
            Cond::Eq => a == b,
            Cond::NEq => a != b,
            Cond::IGrE => a >= b,
            Cond::IGr => a > b,
            Cond::FLe => af < bf,
            Cond::FLeE => af <= bf,
            Cond::FGrE => af >= bf,
            Cond::FGr => af > bf,
            Cond::FNaN => panic!(),
            Cond::FInf => panic!(),
        }
    }

    pub fn tick(&mut self) {
        let instruction = &self.program[self.program_counter];
        self.program_counter += 1;
        // println!("executing {:?} with stack {:?}", instruction, self.stack);

        match instruction {
            Instruction::HALT => exit(0),
            Instruction::BRANCH(cond, dst) => {
                let d = *dst as usize;
                if self.evaluate(cond.clone()) {
                    self.program_counter = d;
                }
            }
            Instruction::CALL(dst, num_args) => {
                let return_addr = Some(self.program_counter as u64);
                self.program_counter = *dst as usize;
                let mut values = vec![];
                for _ in 0..*num_args {
                    values.push(self.pop())
                };
                self.stack.push(StackFrame { return_addr, values })
            }
            Instruction::RET => {
                let last = self.pop();
                match self.stack.pop() {
                    Some(v) => {
                        // println!("returning to {:?} (stack = {:?})", v.return_addr, self.stack);
                        self.program_counter = v.return_addr.unwrap_or_else(|| exit(0)) as usize;
                        self.push(last)        
                    }
                    None => {
                        exit(0)
                    }
                }
            }
            Instruction::PUSHFR => { self.stack.push(StackFrame { return_addr: None, values: vec![] }); /* println!("pushing frame"); */ }
            Instruction::POPFR => { self.stack.pop(); /* println!("popping frame"); */ 
        }
            Instruction::PUSH(v) => { self.pushi(*v) }
            Instruction::POP => { self.stack.last_mut().unwrap().values.pop(); }
            Instruction::COPY { from_top, in_frame } => { let gotten = &self.stack[self.stack.len() - *from_top as usize - 1].values[*in_frame as usize]; self.push(gotten.clone()) }
            Instruction::MOV { from_top, in_frame } => { let a = *from_top; let b = *in_frame; let l = self.stack.len(); let gotten = self.pop(); self.stack[l - a as usize - 1].values[b as usize] = gotten; }
            Instruction::ALLOC(t) => {
                let n = *t;
                let tpe = self.types[n].clone();
                let addr = thread_rng().next_u64() as i64;
                let mut data = vec![];
                let num = match tpe.clone() {
                    FieldInfo::Fields(v) => v.len(),
                    _ => panic!()
                };
                for _ in 0..num {
                    data.push(self.popi())
                }
                self.heap.insert(addr, UwUIns::Struct { tpe: n, data, mark: false });
                self.push((addr, tpe));
            }
            Instruction::ALLOCA(tpe) => {
                let info = tpe.as_field_info(&self.types);
                let count = self.popi();
                let addr = thread_rng().next_u64() as i64;
                self.heap.insert(addr, UwUIns::Arr { item_type: info.clone(), items: vec![None; count as usize], mark: false });
                self.push((addr, FieldInfo::Array(Box::new(info))))
            }
            Instruction::GET(n) => {
                let num = *n;
                let (addr, tpe) = self.pop();
                let field_tpe = match tpe {
                    FieldInfo::Fields(f) => (&f[num as usize]).clone(),
                    FieldInfo::Array(_) => FieldInfo::Primitive,
                    _ => panic!()
                };
                let fetched = match &self.heap[&addr] {
                    UwUIns::Struct { mark: _, tpe: _, data } => data[num as usize],
                    UwUIns::Arr { mark: _, item_type: _, items } => items.len() as i64,
                    _ => panic!()
                };
                self.push((fetched, field_tpe.clone()))
            }
            Instruction::SET(n) => {
                let num = *n;
                let newv = self.popi();
                let addr = self.popi();
                match &mut self.heap.get_mut(&addr).unwrap() {
                    UwUIns::Struct { mark: _, tpe: _, data } => data[num as usize] = newv,
                    _ => panic!()
                };
            }
            Instruction::GETA => {
                let idx = self.popi();
                let array = self.pop().0;
                let found = &self.heap[&array];
                let (res, tpe) = match found {
                    UwUIns::Arr { mark: _, item_type, items } => (items[idx as usize], item_type),
                    UwUIns::Struct { .. } => panic!()
                };
                self.push((res.unwrap_or(0), tpe.clone()))
            }
            Instruction::SETA => {
                let newval = self.pop();
                let idx = self.popi();
                let array = self.pop().0;
                let found = self.heap.get_mut(&array).unwrap();
                match found {
                    UwUIns::Arr { mark: _, item_type: _, items } => {
                        items[idx as usize] = Some(newval.0)
                    }
                    UwUIns::Struct { .. } => panic!()
                };
            }
            Instruction::IADD => { let b = self.popi(); let a = self.popi(); self.pushi(a + b) }
            Instruction::ISUB => { let b = self.popi(); let a = self.popi(); self.pushi(a - b) }
            Instruction::IMUL => { let b = self.popi(); let a = self.popi(); self.pushi(a * b) }
            Instruction::IDIV => { let b = self.popi(); let a = self.popi(); self.pushi(a / b) }
            Instruction::IMOD => { let b = self.popi(); let a = self.popi(); self.pushi(a % b) }

            Instruction::FADD => { let b = self.popf(); let a = self.popf(); self.pushf(a + b) }
            Instruction::FSUB => { let b = self.popf(); let a = self.popf(); self.pushf(a - b) }
            Instruction::FMUL => { let b = self.popf(); let a = self.popf(); self.pushf(a * b) }
            Instruction::FDIV => { let b = self.popf(); let a = self.popf(); self.pushf(a / b) }
            Instruction::CMP(cond) => {
                let v = self.evaluate(cond.clone());
                self.pushb(v);
            }
            Instruction::NATIVE(f) => (STDLIB_FUNCS[*f].func)(self)
        }

        if self.heap.len() > 1000 {
            self.gc();
        }
    }

    pub fn pop(&mut self) -> (i64, FieldInfo) {
        self.stack.last_mut().unwrap().values.pop().unwrap()
    }

    pub fn popi(&mut self) -> i64 {
        self.pop().0
    }

    fn popf(&mut self) -> f64 {
        unsafe { std::mem::transmute(self.popi()) }
    }

    fn popb(&mut self) -> bool {
        self.popi() != 0
    }

    fn push(&mut self, v: (i64, FieldInfo)) {
        self.stack.last_mut().unwrap().values.push(v)
    }

    pub fn pushi(&mut self, v: i64) {
        self.push((v, FieldInfo::Primitive))
    }

    fn pushf(&mut self, v: f64) {
        self.pushi(unsafe { std::mem::transmute(v) })
    }

    fn pushb(&mut self, v: bool) {
        self.pushi(if v { 1 } else { 0 })
    }

    pub fn gc(&mut self) {
        self.mark = !self.mark;
        for frame in self.stack.clone() {
            for (v, tpe) in &frame.values {
                match tpe {
                    FieldInfo::Primitive => {}
                    _ => {
                        UwUIns::mark(*v, self);
                    }
                }
            }
        }
        self.sweep();
    }

    fn sweep(&mut self) {
        let mut to_remove = vec![];
        for item in &self.heap {
            let mark = match item.1 {
                UwUIns::Arr { mark, item_type, items } => mark,
                UwUIns::Struct { mark, tpe, data } => mark,
            };

            if *mark != self.mark {
                to_remove.push(*item.0);
            }
        }

        // println!("sweeping {} objects ({} remain)", to_remove.len(), self.heap.len() - to_remove.len());
        for item in to_remove {
            self.heap.remove(&item);
        }
    }
}

impl UwUIns {
    fn mark(addr: i64, vm: &mut VM) {
        let slf = &vm.heap[&addr];
        match slf {
            UwUIns::Arr { mark, item_type, items } => {
                match item_type {
                    FieldInfo::Primitive => {}
                    _ => {
                        for i in items {
                            match i {
                                Some(v) => {
                                    UwUIns::mark(*v, unsafe { &mut *(vm as *const VM as *mut VM) });
                                }
                                None => {}
                            }
                        }
                    }
                }
            }
            UwUIns::Struct { mark, tpe, data } => {
                let found = &vm.types[*tpe];
                let fields = match found {
                    FieldInfo::Primitive => panic!(),
                    FieldInfo::Array(_) => panic!(),
                    FieldInfo::Fields(v) => v
                };
                for (idx, item) in fields.iter().enumerate() {
                    match item {
                        FieldInfo::Primitive => { continue }
                        FieldInfo::Array(_) => {}
                        FieldInfo::Fields(_) => {}
                    }
                    let addr = data[idx];
                    UwUIns::mark(addr, unsafe { &mut *(vm as *const VM as *mut VM) });
                }
            }
        }

        let m = vm.mark;
        let s = vm.heap.get_mut(&addr).unwrap();
        match s {
            UwUIns::Arr { mark, item_type, items } => {
                *mark = m;
            }
            UwUIns::Struct { mark, tpe, data } => {
                *mark = m;
            }
        }
    }
}
