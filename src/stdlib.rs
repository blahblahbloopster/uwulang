use std::{fmt::Debug, hash::Hash, io::{Write, Read}, fs::File};

use once_cell::sync::Lazy;

use crate::{newcompiler::{UwUTy, Primitive}, runtime::VM, parser::UwUInpFile};

pub struct NativeFunction<'b> {
    pub id: u64,
    pub fqn: Vec<&'b str>,
    pub args: Vec<(&'b str, UwUTy<'b>)>,
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

pub static STDLIB_FUNCS: Lazy<[NativeFunction; 3]> = Lazy::new(|| {[
        NativeFunction { id: 0, fqn: vec!["io", "wwite"], args: vec![("chaw", UwUTy::Native(I64))], ret: UwUTy::Native(UNIT), func: |vm| {
            let value = vm.popi() as u8;
            std::io::stdout().write(&[value]).unwrap();
            vm.pushi(0);
        } },
        NativeFunction { id: 1, fqn: vec!["io", "fwush"], args: vec![], ret: UwUTy::Native(UNIT), func: |vm| {
            std::io::stdout().flush().unwrap();
            vm.pushi(0);
        } },
        NativeFunction { id: 2, fqn: vec!["mem", "gc"], args: vec![], ret: UwUTy::Native(UNIT), func: |vm| {
            vm.gc();
            vm.pushi(0);
        } },
    ]});

fn read_file(mut f: File) -> String {
    let mut buf = String::new();
    f.read_to_string(&mut buf).unwrap();
    buf
}

pub fn stdlib_files<'a>() -> Vec<UwUInpFile> {
    vec![
        UwUInpFile { content: read_file(File::open("src/stdlib/io.uwu").unwrap()) },
        UwUInpFile { content: read_file(File::open("src/stdlib/cowwections.uwu").unwrap()) }
        // UwUFi { fqn: vec!["io".to_string()], content: uwu_parser::file(lexer::tokenize(io_file.as_str(), &UwUInpFile { content: io_file }).unwrap().as_slice()).unwrap().content },
    ]
}

#[derive(Debug, PartialEq, Hash, Eq, Clone)]
pub enum NativeType {
    Primitive(Primitive)
}

impl NativeType {
    pub fn fqn(&self) -> Vec<String> {
        match self {
            NativeType::Primitive(p) => match p {
                Primitive::Unit => vec!["unit".to_string()],
                Primitive::I64 => vec!["i64".to_string()],
                Primitive::F64 => vec!["f64".to_string()],
                Primitive::Bool => vec!["boow".to_string()],
            }
        }
    }
}

pub const UNIT: &'static NativeType = &NativeType::Primitive(Primitive::Unit);
pub const I64: &'static NativeType = &NativeType::Primitive(Primitive::I64);
pub const F64: &'static NativeType = &NativeType::Primitive(Primitive::F64);
pub const BOOL: &'static NativeType = &NativeType::Primitive(Primitive::Bool);

pub const PRIMITIVE_TYPES: [&'static NativeType; 4] = [UNIT, I64, F64, BOOL];
