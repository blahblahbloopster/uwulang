use core::panic;
use std::{io::Cursor, collections::HashMap};

use byteorder::{WriteBytesExt, LittleEndian, ReadBytesExt};

use crate::runtime::{Instruction, Tpe, Cond, FieldInfo, VM, UwUIns, StackFrame};

fn write_tpe(t: &Tpe, out: &mut Vec<u8>) {
    match t {
        Tpe::Native => out.push(0),
        Tpe::Ref(v) => { out.push(1); out.write_u64::<LittleEndian>(*v as u64).unwrap(); }
        Tpe::Array(inner) => { out.push(2); write_tpe(inner, out) }
    }
}

fn read_tpe(inp: &mut Cursor<Vec<u8>>) -> Tpe {
    let t = inp.read_u8().unwrap();
    match t {
        0 => Tpe::Native,
        1 => Tpe::Ref(inp.read_u64::<LittleEndian>().unwrap() as usize),
        2 => Tpe::Array(Box::new(read_tpe(inp))),
        _ => panic!()
    }
}

fn write_cond(c: &Cond, out: &mut Vec<u8>) {
    out.push(match c {
        Cond::Always => 0,
        Cond::Never => 1,
        Cond::ILe => 2,
        Cond::ILeE => 3,
        Cond::Eq => 4,
        Cond::NEq => 5,
        Cond::IGrE => 6,
        Cond::IGr => 7,
        Cond::FLe => 8,
        Cond::FLeE => 9,
        Cond::FGrE => 10,
        Cond::FGr => 11,
        Cond::FNaN => 12,
        Cond::FInf => 13,
    });
}

fn read_cond(inp: &mut Cursor<Vec<u8>>) -> Cond {
    match inp.read_u8().unwrap() {
        0 => Cond::Always,
        1 => Cond::Never,
        2 => Cond::ILe,
        3 => Cond::ILeE,
        4 => Cond::Eq,
        5 => Cond::NEq,
        6 => Cond::IGrE,
        7 => Cond::IGr,
        8 => Cond::FLe,
        9 => Cond::FLeE,
        10 => Cond::FGrE,
        11 => Cond::FGr,
        12 => Cond::FNaN,
        13 => Cond::FInf,
        _ => panic!()
    }
}

fn serialize(instructions: &Vec<Instruction>, out: &mut Vec<u8>) {
    out.write_u64::<LittleEndian>(instructions.len() as u64).unwrap();
    for ins in instructions {
        match ins {
            Instruction::HALT => out.push(1),
            Instruction::BRANCH(cond, dst) => { out.push(2); write_cond(cond, out); out.write_u64::<LittleEndian>(*dst).unwrap(); }
            Instruction::CALL(dst, args) => { out.push(3); out.write_u64::<LittleEndian>(*dst).unwrap(); out.write_u32::<LittleEndian>(*args).unwrap(); }
            Instruction::RET => out.push(4),
            Instruction::PUSHFR => out.push(5),
            Instruction::POPFR => out.push(6),
            Instruction::PUSH(v) => { out.push(7); out.write_i64::<LittleEndian>(*v).unwrap(); }
            Instruction::POP => out.push(8),
            Instruction::COPY { from_top, in_frame } => { out.push(9); out.write_u32::<LittleEndian>(*from_top).unwrap(); out.write_u32::<LittleEndian>(*in_frame).unwrap(); }
            Instruction::MOV { from_top, in_frame } => { out.push(10); out.write_u32::<LittleEndian>(*from_top).unwrap(); out.write_u32::<LittleEndian>(*in_frame).unwrap(); }
            Instruction::ALLOC(n) => { out.push(11); out.write_u64::<LittleEndian>(*n as u64).unwrap(); }
            Instruction::ALLOCA(n) => { out.push(12); write_tpe(n, out); }
            Instruction::GET(n) => { out.push(13); out.write_u32::<LittleEndian>(*n).unwrap(); }
            Instruction::SET(n) => { out.push(14); out.write_u32::<LittleEndian>(*n).unwrap(); }
            Instruction::GETA => out.push(15),
            Instruction::SETA => out.push(16),
            Instruction::IADD => out.push(17),
            Instruction::ISUB => out.push(18),
            Instruction::IMUL => out.push(19),
            Instruction::IDIV => out.push(20),
            Instruction::IMOD => out.push(21),
            Instruction::FADD => out.push(22),
            Instruction::FSUB => out.push(23),
            Instruction::FMUL => out.push(24),
            Instruction::FDIV => out.push(25),
            Instruction::CMP(n) => { out.push(26); write_cond(n, out); }
            Instruction::NATIVE(n) => { out.push(27); out.write_u64::<LittleEndian>(*n as u64).unwrap(); }
        }
    }
}

fn deserialize(inp: &mut Cursor<Vec<u8>>) -> Vec<Instruction> {
    let mut out = vec![];
    let count = inp.read_u64::<LittleEndian>().unwrap();
    for _ in 0..count {
        let discm = inp.read_u8().unwrap();
        let res = match discm {
            1  => Instruction::HALT,
            2  => Instruction::BRANCH(read_cond(inp), inp.read_u64::<LittleEndian>().unwrap()),
            3  => Instruction::CALL(inp.read_u64::<LittleEndian>().unwrap(), inp.read_u32::<LittleEndian>().unwrap()),
            4  => Instruction::RET,
            5  => Instruction::PUSHFR,
            6  => Instruction::POPFR,
            7  => Instruction::PUSH(inp.read_i64::<LittleEndian>().unwrap()),
            8  => Instruction::POP,
            9  => Instruction::COPY { from_top: inp.read_u32::<LittleEndian>().unwrap(), in_frame: inp.read_u32::<LittleEndian>().unwrap() },
            10 => Instruction::MOV { from_top: inp.read_u32::<LittleEndian>().unwrap(), in_frame: inp.read_u32::<LittleEndian>().unwrap() },
            11 => Instruction::ALLOC(inp.read_u64::<LittleEndian>().unwrap() as usize),
            12 => Instruction::ALLOCA(read_tpe(inp)),
            13 => Instruction::GET(inp.read_u32::<LittleEndian>().unwrap()),
            14 => Instruction::SET(inp.read_u32::<LittleEndian>().unwrap()),
            15 => Instruction::GETA,
            16 => Instruction::SETA,
            17 => Instruction::IADD,
            18 => Instruction::ISUB,
            19 => Instruction::IMUL,
            20 => Instruction::IDIV,
            21 => Instruction::IMOD,
            22 => Instruction::FADD,
            23 => Instruction::FSUB,
            24 => Instruction::FMUL,
            25 => Instruction::FDIV,
            26 => Instruction::CMP(read_cond(inp)),
            27 => Instruction::NATIVE(inp.read_u64::<LittleEndian>().unwrap() as usize),
            _ => panic!()
        };
        out.push(res);
    }

    out
}

fn write_field_info(f: &FieldInfo, out: &mut Vec<u8>) {
    match f {
        FieldInfo::Primitive => out.push(0),
        FieldInfo::Array(inner) => { out.push(1); write_field_info(&*inner, out); }
        FieldInfo::Fields(fields) => { out.push(2); out.write_u32::<LittleEndian>(fields.len() as u32).unwrap(); for item in fields { write_field_info(item, out) } }
    }
}

fn read_field_info(inp: &mut Cursor<Vec<u8>>) -> FieldInfo {
    match inp.read_u8().unwrap() {
        0 => FieldInfo::Primitive,
        1 => FieldInfo::Array(Box::new(read_field_info(inp))),
        2 => {
            let count = inp.read_u32::<LittleEndian>().unwrap();
            let mut f = vec![];
            for _ in 0..count {
                f.push(read_field_info(inp));
            }
            FieldInfo::Fields(f)
        }
        _ => panic!()
    }
}

pub fn save(vm: &VM) {
    let mut out = vec![];
    out.write_u64::<LittleEndian>(vm.types.len() as u64).unwrap();
    for item in &vm.types {
        write_field_info(item, &mut out);
    }
    out.write_u64::<LittleEndian>(vm.heap.len() as u64).unwrap();

    for (a, b) in &vm.heap {
        out.write_i64::<LittleEndian>(*a).unwrap();
        match b {
            UwUIns::Arr { mark, item_type, items } => {
                out.push(1);
                out.write_u8(*mark as u8).unwrap();
                write_field_info(item_type, &mut out);
                out.write_u64::<LittleEndian>(items.len() as u64).unwrap();
                for item in items {
                    match item {
                        Some(v) => { out.push(1); out.write_i64::<LittleEndian>(*v).unwrap(); }
                        None => out.push(0),
                    }
                }
            }
            UwUIns::Struct { mark, tpe, data } => {
                out.push(2);
                out.push(*mark as u8);
                out.write_u64::<LittleEndian>(*tpe as u64).unwrap();
                out.write_u64::<LittleEndian>(data.len() as u64).unwrap();
                for item in data {
                    out.write_i64::<LittleEndian>(*item).unwrap();
                }
            }
        }
    }

    out.write_u32::<LittleEndian>(vm.stack.len() as u32).unwrap();
    for frame in &vm.stack {
        match frame.return_addr {
            None => out.push(0),
            Some(v) => { out.push(1); out.write_u64::<LittleEndian>(v).unwrap(); }
        }
        out.write_u32::<LittleEndian>(frame.values.len() as u32).unwrap();
        for (item, tpe) in &frame.values {
            out.write_i64::<LittleEndian>(*item).unwrap();
            write_field_info(tpe, &mut out);
        }
    }

    serialize(&vm.program, &mut out);
    out.write_u64::<LittleEndian>(vm.program_counter as u64).unwrap();
    out.push(vm.mark as u8);
}

pub fn load(stored: Vec<u8>) -> VM {
    let mut inp = Cursor::new(stored);
    let type_count = inp.read_u64::<LittleEndian>().unwrap();
    let mut types = vec![];
    for _ in 0..type_count {
        types.push(read_field_info(&mut inp));
    }
    let heap_count = inp.read_u64::<LittleEndian>().unwrap();
    let mut heap = HashMap::new();
    for _ in 0..heap_count {
        let addr = inp.read_i64::<LittleEndian>().unwrap();
        let ins = match inp.read_u8().unwrap() {
            1 => {
                let mark = inp.read_u8().unwrap() != 0;
                let item_type = read_field_info(&mut inp);
                let mut items = vec![];
                let count = inp.read_u64::<LittleEndian>().unwrap();
                for _ in 0..count {
                    if inp.read_u8().unwrap() == 0 {
                        items.push(None);
                    } else {
                        items.push(Some(inp.read_i64::<LittleEndian>().unwrap()))
                    }
                }
                UwUIns::Arr { mark, item_type, items }
            }
            2 => {
                let mark = inp.read_u8().unwrap() != 0;
                let tpe = inp.read_u64::<LittleEndian>().unwrap() as usize;
                let data_len = inp.read_u64::<LittleEndian>().unwrap();
                let mut data = vec![];
                for _ in 0..data_len {
                    data.push(inp.read_i64::<LittleEndian>().unwrap());
                }
                UwUIns::Struct { mark, tpe, data }
            }
            _ => panic!()
        };
        heap.insert(addr, ins);
    }

    let stack_len = inp.read_u32::<LittleEndian>().unwrap();
    let mut stack = vec![];
    for _ in 0..stack_len {
        let return_addr = match inp.read_u8().unwrap() {
            0 => None,
            1 => Some(inp.read_u64::<LittleEndian>().unwrap()),
            _ => panic!()
        };
        let mut values = vec![];
        let len = inp.read_u32::<LittleEndian>().unwrap();
        for _ in 0..len {
            values.push((inp.read_i64::<LittleEndian>().unwrap(), read_field_info(&mut inp)));
        }
        stack.push(StackFrame { return_addr, values });
    }

    let program = deserialize(&mut inp);
    let program_counter = inp.read_u64::<LittleEndian>().unwrap() as usize;
    let mark = inp.read_u8().unwrap() != 0;
    VM { types, heap, stack, program, program_counter, mark }
}
