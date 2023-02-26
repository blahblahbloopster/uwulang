// use std::io::{self, Write};

// use crate::bytecode::{UwUType, VM, NativeFunction, Primitive};

// pub struct CompNativeFunction<'a> {
//     pub qualified_name: Vec<String>,
//     pub arg_types: Vec<UwUType<'a>>,
//     pub return_type: UwUType<'a>,
//     pub idx: u64,
//     function: fn(vm: &mut VM)
// }

// impl<'a> CompNativeFunction<'a> {
//     pub fn to_runtime(&self) -> NativeFunction {
//         NativeFunction { name: self.qualified_name.clone(), arg_count: self.arg_types.len() as u32, lambda: self.function  }
//     }

//     fn new(idx: u64, fqn: Vec<&str>, arg_types: Vec<UwUType<'a>>, return_type: UwUType<'a>, function: fn(vm: &mut VM)) -> CompNativeFunction<'a> {
//         CompNativeFunction { qualified_name: fqn.iter().map(|x| x.to_string()).collect(), arg_types, return_type, function, idx }
//     }
// }

// pub fn stdlib<'a>() -> Vec<CompNativeFunction<'a>> {
//     vec![
//         CompNativeFunction::new(0, vec!["io", "wwite"], vec![UwUType::Primitive(Primitive::I64)], UwUType::Primitive(Primitive::Unit), |vm| { io::stdout().write(&[vm.pop() as u8]).expect("failed to write to stdout"); vm.push(0); }),
//         CompNativeFunction::new(1, vec!["io", "fwush"], vec![], UwUType::Primitive(Primitive::Unit), |vm| { io::stdout().flush().unwrap(); vm.push(0); })
//     ]
// }

// pub fn stdlib_types<'a>() -> Vec<UwUType<'a>> {
//     UwUType::primitives()
// }

// pub fn runtime_stdlib() -> Vec<NativeFunction> {
//     stdlib().iter().map(|x| x.to_runtime()).collect()
// }

use std::{fmt::Debug, hash::Hash};

use crate::{newcompiler::{UwUTy, Primitive}, runtime::VM};

pub struct NativeFunction<'b> {
    pub id: u64,
    pub fqn: Vec<String>,
    pub args: Vec<(String, UwUTy<'b>)>,
    pub ret: UwUTy<'b>,
    pub func: fn(&mut VM)
}

impl<'b> Hash for NativeFunction<'b> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
        self.fqn.hash(state);
        self.args.hash(state);
        self.ret.hash(state);
    }
}

impl<'b> PartialEq for NativeFunction<'b> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.fqn == other.fqn && self.args == other.args && self.ret == other.ret
    }
}

impl<'b> Eq for NativeFunction<'b> {}

impl<'b> Debug for NativeFunction<'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeFunction")
            .field("id", &self.id)
            .field("fqn", &self.fqn)
            .field("args", &self.args)
            .field("ret", &self.ret)
        .finish()
    }
}

#[derive(Debug, PartialEq, Hash, Eq)]
pub enum NativeType {
    Primitive(Primitive)
}

pub const UNIT: &'static NativeType = &NativeType::Primitive(Primitive::Unit);
pub const I64: &'static NativeType = &NativeType::Primitive(Primitive::I64);
pub const F64: &'static NativeType = &NativeType::Primitive(Primitive::F64);
pub const BOOL: &'static NativeType = &NativeType::Primitive(Primitive::Bool);

pub const PRIMITIVE_TYPES: [&'static NativeType; 4] = [UNIT, I64, F64, BOOL];
