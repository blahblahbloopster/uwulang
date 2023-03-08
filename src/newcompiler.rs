use std::{collections::HashMap, fmt::Debug};

use rand::{thread_rng, RngCore};

use crate::{stdlib::{NativeType, NativeFunction, PRIMITIVE_TYPES, UNIT, I64, BOOL, F64, STDLIB_FUNCS, stdlib_files}, runtime::{Instruction, FieldInfo, Cond, Tpe}, parser::{Literal, UwUInpFile, uwu_parser, lexer}};
use crate::parser::{Declaration, Expression, Statement, BiOp, Type, Loc};

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct UwUStrc<'b> {
    fqn: Vec<String>,
    fields: Vec<(String, UwUTy<'b>)>
}

impl<'b> UwUStrc<'b> {
    fn pseudo_copy(&self) -> UwUStrc<'b> {
        UwUStrc { fqn: self.fqn.clone(), fields: self.fields.iter().map(|x| (x.0.clone(), x.1.pseudo_copy())).collect() }
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Primitive {
    Unit, I64, F64, Bool
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum UwUTy<'b> {
    Struct(&'b UwUStrc<'b>),
    Native(&'b NativeType),
    Array(Box<UwUTy<'b>>)
}

impl<'b> UwUTy<'b> {
    fn pseudo_copy(&self) -> UwUTy<'b> {
        match self {
            UwUTy::Struct(v) => UwUTy::Struct(v),
            UwUTy::Native(v) => UwUTy::Native(v),
            UwUTy::Array(v) => UwUTy::Array(Box::new(v.pseudo_copy())),
        }
    }
}

#[derive(PartialEq, Hash, Eq)]
struct UnresolvedImport {
    fqn: Vec<String>,
    name: String
}

#[derive(PartialEq, Hash, Eq)]
enum UwUFunc<'a, 'b> {
    Native(&'b NativeFunction<'b>),
    Defined { fqn: Vec<String>, args: Vec<(String, UwUTy<'b>)>, return_type: UwUTy<'b>, data: &'a Vec<Statement<'a>>, receiver: Option<UwUStrc<'b>>, id: u64 }
}

impl<'a, 'b> Debug for UwUFunc<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Native(arg0) => f.debug_tuple("Native").field(arg0).finish(),
            Self::Defined { fqn, args, return_type, data, receiver, id } => f.debug_struct("Defined").field("fqn", fqn).field("args", args).field("return_type", return_type)/*.field("data", data)*/.field("receiver", receiver).field("id", id).finish(),
        }
    }
}

impl<'a, 'b> UwUFunc<'a, 'b> {
    fn fqn(&self) -> Vec<String> {
        match self {
            UwUFunc::Native(v) => v.fqn.iter().map(|x| x.to_string()).collect(),
            UwUFunc::Defined { fqn, args, return_type, data, receiver, id } => fqn.clone(),
        }
    }

    fn pseudo_copy(&self) -> UwUFunc<'a, 'b> {
        match self {
            UwUFunc::Native(v) => UwUFunc::Native(v),
            UwUFunc::Defined { fqn, args, return_type, data, receiver, id } => UwUFunc::Defined { fqn: fqn.clone(), args: args.iter().map(|x| (x.0.clone(), x.1.pseudo_copy())).collect(), return_type: return_type.pseudo_copy(), data, receiver: receiver.clone(), id: *id }
        }
    }

    fn args(&self) -> Vec<(String, UwUTy)> {
        match self {
            UwUFunc::Native(v) => v.args.iter().map(|x| (x.0.to_string(), x.1.pseudo_copy())).collect(),
            UwUFunc::Defined { fqn, args, return_type, data, receiver, id } => args.iter().map(|x| (x.0.clone(), x.1.pseudo_copy())).collect()
        }
    }

    fn return_type(&self) -> UwUTy<'b> {
        match self {
            UwUFunc::Native(v) => v.ret.pseudo_copy(),
            UwUFunc::Defined { fqn, args, return_type, data, receiver, id } => return_type.pseudo_copy()
        }
    }
}

#[derive(Debug)]
enum Importable<'a, 'b> {
    Type(UwUTy<'b>),
    FunctionSet(Vec<UwUFunc<'a, 'b>>)
}

impl<'a, 'b> Importable<'a, 'b> {
    fn as_type(&self) -> Option<UwUTy<'b>> {
        match self {
            Importable::Type(v) => Some(v.pseudo_copy()),
            Importable::FunctionSet(_) => None
        }
    }

    fn as_func(&self, args: &Vec<UwUTy<'b>>) -> Option<UwUFunc<'a, 'b>> {
        match self {
            Importable::Type(_) => None,
            Importable::FunctionSet(v) => {
                for item in v {
                    if item.args().iter().zip(args).all(|((_, a), b)| a == b) {
                        return Some(item.pseudo_copy())
                    }
                }
                None
            }
        }
    }
}

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct UwUFi<'a> {
    pub fqn: Vec<String>,
    pub content: Vec<Declaration<'a>>
}

impl<'b> UwUTy<'b> {
    pub fn to_info(&self) -> FieldInfo {
        match self {
            UwUTy::Struct(s) => FieldInfo::Fields(s.fields.iter().map(|x| x.1.to_info()).collect()),
            UwUTy::Native(_) => FieldInfo::Primitive,
            UwUTy::Array(v) => FieldInfo::Array(Box::new(v.to_info())),
        }
    }
}

macro_rules! unwrap_or_ret {
    ($value:expr, $err:expr) => {
        match $value {
            Some(v) => v,
            None => return Err($err)
        }
    };
}

macro_rules! asrt {
    ($value:expr, $err:expr) => {
        if !$value {
            return Err($err)
        }
    }
}

macro_rules! pnck {
    ($value:expr) => {
        return Err($value)
    };
}

fn resolve<'a, 'b>(mapping: &HashMap<String, Importable<'a, 'b>>, tpe: &'a Type) -> Result<UwUTy<'b>, CompilerError<'a, 'b>> {
    match tpe {
        Type::Simple(t, _) => unwrap_or_ret!(mapping.get(t), CompilerError { tpe: ErrorType::TypeNotFound(tpe.clone()), loc: tpe.loc() }).as_type().ok_or(CompilerError { tpe: ErrorType::TypeNotFound(tpe.clone()), loc: tpe.loc() }),
        Type::Array(t, _) => Ok(UwUTy::Array(Box::new(resolve(mapping, &*t)?)))
    }
}

pub fn compile<'a, 'b, 'c>(files_c: &'a mut Vec<UwUInpFile>, entrypoint: Vec<String>) -> (Vec<FieldInfo>, Vec<Instruction>) {
    for file in stdlib_files() {
        files_c.push(file);
    }
    let files_b = files_c as &'a Vec<UwUInpFile>;

    let mut files_a = vec![];
    for item in files_b {
        if item.content.contains("l") || item.content.contains("L") || item.content.contains("r") || item.content.contains("R") {
            panic!()
        }
        let parsed = uwu_parser::file(lexer::tokenize(&item.content.as_str(), &item).unwrap().as_slice()).unwrap();
        files_a.push(UwUFi { fqn: parsed.package.fqn, content: parsed.content })
    }
    let files = &files_a;

    // let mut structs = vec![];
    let mut structs_s = vec![];
    let mut structs_f = vec![];
    let mut structs_d = vec![];
    let mut functions = vec![];

    // collect all the functions and structs without resolving any times (structs have no fields, functions have no args and return unit)
    for file in files {
        for decl in &file.content {
            match decl {
                Declaration::Function { name, args, return_type, block, loc, receiver } => {
                    let mut recv = None;
                    match receiver {
                        None => {}
                        Some(Type::Simple(v, _)) => {
                            for i in 0..structs_s.len() {
                                let fi = &structs_f[i];
                                let found_struct: &UwUStrc = &structs_s[i];
                                if v == found_struct.fqn.last().unwrap() && fi == &file {
                                    recv = Some(found_struct.clone());
                                }
                            }
                        }
                        _ => panic!()
                    }
                    functions.push((UwUFunc::Defined { fqn: file.fqn.plus(name), args: vec![], return_type: UwUTy::Native(UNIT), data: block, receiver: recv, id: thread_rng().next_u64() }, file, decl));
                }
                Declaration::Struct { name, fields, loc } => {
                    // structs.push((UwUStrc { fqn: file.fqn.plus(name), fields: vec![] }, file, decl));
                    structs_s.push(UwUStrc { fqn: file.fqn.plus(name), fields: vec![] });
                    structs_f.push(file);
                    structs_d.push(decl);
                }
                Declaration::Import { .. } => {}
            }
        }
    }

    // resolve imports
    let mut mapping = HashMap::new();

    for file in files {
        let mut raw_imports = vec![];
        for decl in &file.content {
            match decl {
                Declaration::Import { path, item, loc } => { raw_imports.push(UnresolvedImport { fqn: path.plus(item), name: item.clone() }) }
                _ => {}
            }
        }

        let mut file_mapping = HashMap::new();

        for item in raw_imports {
            let stdlib_type = PRIMITIVE_TYPES.iter().find(|x| x.fqn() == item.fqn).map(|x| Importable::Type(UwUTy::Native(x)));
            let mut matching_funcs: Vec<UwUFunc> = STDLIB_FUNCS.iter().filter(|x| x.fqn == item.fqn).map(|x| UwUFunc::Native(x)).collect();
            // let stdlib_fun = if matching_stdlib_funcs.len() == 0 { None } else { Some(Importable::FunctionSet(matching_stdlib_funcs)) };
            // check if it's a struct
            let found_type = structs_s.iter().find(|x| x.fqn == item.fqn).map(|found| Importable::Type(UwUTy::Struct(&found)));
            // check if it's a function
            matching_funcs.extend(functions.iter().filter(|x| x.0.fqn() == item.fqn).map(|found| found.0.pseudo_copy()));
            let found_function = if matching_funcs.len() == 0 { None } else { Some(Importable::FunctionSet(matching_funcs)) };
            
            // require that exactly one of these possibilities actually matches
            let all = vec![stdlib_type, found_type, found_function];
            // println!("{:?}", all);
            let found = all.single(|x| x.is_some()).expect("unable to resolve import").unwrap();

            match &found {
                Importable::Type(s) => {
                    for (f, _, _) in &functions {
                        match f {
                            UwUFunc::Native(_) => {}
                            UwUFunc::Defined { fqn, args, return_type, data, receiver, id } => {
                                match receiver {
                                    Some(v) => {
                                        if &UwUTy::Struct(v) == s {
                                            let existing = file_mapping.get_mut(fqn.last().unwrap());
                                            match existing {
                                                Some(Importable::FunctionSet(v)) => { v.push(f.pseudo_copy()); continue; },
                                                _ => {
                                                    file_mapping.insert(fqn.last().unwrap().clone(), Importable::FunctionSet(vec![f.pseudo_copy()]));
                                                }
                                            }
                                        }
                                    }
                                    None => {}
                                }
                            }
                        }
                    }
                }
                Importable::FunctionSet(s) => {
                    let existing = file_mapping.get_mut(&item.name);
                    match existing {
                        Some(Importable::FunctionSet(v)) => { v.extend(s.iter().map(|x| x.pseudo_copy())); continue; },
                        _ => {}
                    }
                }
            }
            file_mapping.insert(item.name, found);
        }

        for item in PRIMITIVE_TYPES {
            file_mapping.insert(item.fqn().last().unwrap().to_string(), Importable::Type(UwUTy::Native(item)));
        }

        for i in 0..structs_s.len() {
            let strct = &structs_s[i];
            let fi = &structs_f[i];

            if fi == &file {
                file_mapping.insert(strct.fqn.last().unwrap().clone(), Importable::Type(UwUTy::Struct(strct)));
            }
        }

        for (func, fi, _) in &functions {
            if fi == &file {
                let name = func.fqn().last().unwrap().clone();
                let found = file_mapping.get_mut(&name);
                match found {
                    Some(Importable::FunctionSet(v)) => {
                        v.push(func.pseudo_copy());
                    }
                    _ => {
                        file_mapping.insert(name, Importable::FunctionSet(vec![func.pseudo_copy()]));
                    }
                };
            }
        }


        // println!("mapping for file {:?}: {:?}", file.fqn, file_mapping);
        mapping.insert(file, file_mapping);
    }

            // Resolve function arg+return types
            for (func, file, decl) in &functions {
                let (args, rtype, data) = match decl {
                    Declaration::Function { name, args, return_type, block, loc, receiver } => (args.clone(), return_type.clone(), block),
                    _ => panic!()
                };
    
                let resolved_ret_type = resolve(&mapping[file], &rtype.unwrap_or(Type::Simple("unit".to_string(), decl.loc().clone() /* FIXME */))).expect("cannot use a function as a type");
                let resolved_args = args.iter().map(|arg| {
                    (arg.name.0.clone(), resolve(&&mapping[file], &arg.tpe).unwrap())
                }).collect();
                let (receiver, id) = match func {
                    UwUFunc::Native(_) => panic!(),
                    UwUFunc::Defined { fqn, args, return_type, data, receiver, id } => (match receiver { Some(v) => Some(v.pseudo_copy()), None => None }, *id)
                }.clone();
                let new = &mut UwUFunc::Defined { fqn: func.fqn(), args: resolved_args, return_type: resolved_ret_type, data, receiver, id };
                std::mem::swap(new, unsafe { &mut *(func as *const UwUFunc as *mut UwUFunc) });
            }
    
            for (func, fi, _) in &functions {
                let (func_id, func_args, func_return_type, func_receiver) = match func {
                    UwUFunc::Native(_) => continue,
                    UwUFunc::Defined { fqn, args, return_type, data, receiver, id } => (*id, args, return_type, receiver),
                };
                for (_, f_mapping) in &mut mapping {
                    for (_, v) in f_mapping {
                        let found: &mut Importable = v;  // compiler gets angy without this
                        match found {
                            Importable::Type(_) => {}
                            Importable::FunctionSet(s) => {
                                for item in s {
                                    match item {
                                        UwUFunc::Native(_) => {}
                                        UwUFunc::Defined { fqn, args, return_type, data, receiver, id } => {
                                            if *id == func_id {
                                                std::mem::swap(&mut func_args.iter().map(|x| (x.0.clone(), x.1.pseudo_copy())).collect(), args);
                                                std::mem::swap(&mut func_return_type.pseudo_copy(), return_type);
                                                std::mem::swap(&mut match func_receiver { Some(v) => Some(v.pseudo_copy()), None => None }, receiver);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
    // Resolve struct types
    for idx in 0..structs_s.len() {
        let strct = &structs_s[idx];
        let file = &structs_f[idx];
        let decl = &structs_d[idx];
        let fields = match decl {
            Declaration::Struct { name, fields, loc } => fields,
            _ => panic!()
        };
        let resolved_fields = fields.iter().map(|pair| {
            let (name, loc) = pair.name.clone();
            let type_name = &pair.tpe;

            let resolved_type = resolve(&mapping[file], type_name).expect("cannot use a function as a type");  // TODO: error checking instead of just panic if not found

            (name, resolved_type)
        }).collect();

        // This is slightly horrible, but necessary
        unsafe { (*(strct as *const UwUStrc as *mut UwUStrc)).fields = resolved_fields }
    }

    // println!("mapping: {:?}", mapping);

    // do the actual compiling
    let entryp = functions.iter().find(|x| x.0.fqn() == entrypoint).expect("entrypoint not found");

    let mut out = InstructionBuilder { out: vec![], calls_to_update: vec![], stack: vec![], starts: HashMap::new(), type_m: HashMap::new(), types: vec![] };
    compile_function(&entryp.0, &mapping[&entryp.1], &mut out);

    for (func, file, _) in &functions {
        if func == &entryp.0 {
            continue;
        }
        // println!("compiling function {:?}", func);
        compile_function(func, &mapping[file], &mut out);
    }

    for (func, idx) in out.calls_to_update {
        // println!("fixing call to {:?}", func);
        let found = out.starts[&func];
        out.out[idx] = Instruction::CALL(found as u64, func.args().len() as u32 + match func {
            UwUFunc::Native(v) => 0,
            UwUFunc::Defined { fqn, args, return_type, data, receiver, id } => if receiver.is_some() { 1 } else { 0 },
        });
    }

    (out.types, out.out)
}

fn compile_expr<'a, 'b, 'c>(expr: &'a Expression, import_mapping: &HashMap<String, Importable<'a, 'b>>, out: &mut InstructionBuilder<'a, 'b>) -> Result<(), CompilerError<'a, 'b>> {
    match expr {
        Expression::Literal(v, _) => {
            let tpe = match v {
                Literal::Int(n) => { out.push(Instruction::PUSH(*n)); UwUTy::Native(I64) }
                Literal::Float(n) => { out.push(Instruction::PUSH(n.as_int())); UwUTy::Native(F64) }
                Literal::Bool(b) => { out.push(Instruction::PUSH(b.as_int())); UwUTy::Native(BOOL) }
                Literal::String(s) => {
                    let in_frame = out.current().values.len() as u32;
                    let chars = s.chars().collect::<Vec<_>>();
                    out.push(Instruction::PUSH(chars.len() as i64));
                    out.push(Instruction::ALLOCA(Tpe::Native));
                    for (i, c) in chars.iter().enumerate() {
                        out.push(Instruction::COPY { from_top: 0, in_frame });
                        out.push(Instruction::PUSH(i as i64));
                        out.push(Instruction::PUSH(*c as i64));
                        out.push(Instruction::SETA);
                    };
                    UwUTy::Array(Box::new(UwUTy::Native(&I64)))
                }
            };
            out.current().values.push((None, tpe));
        }
        Expression::BiOperation(l, op, r, loc) => {
            compile_expr(&*l, import_mapping, out)?;
            let l_type = out.last_tpe().pseudo_copy();
            compile_expr(&*r, import_mapping, out)?;
            let r_type = out.last_tpe().pseudo_copy();

            if l_type != r_type {
                panic!("left and right terms must have the same type (left = {:?}, right = {:?})", l_type, r_type);  // FIXME
            }

            let matrix = match op {
                // i64, f64, bool, custom
                BiOp::Plus => [Some((Instruction::IADD, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), Some((Instruction::FADD, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), None, None],
                BiOp::Minus => [Some((Instruction::ISUB, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), Some((Instruction::FSUB, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), None, None],
                BiOp::Times => [Some((Instruction::IMUL, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), Some((Instruction::FMUL, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), None, None],
                BiOp::Divide => [Some((Instruction::IDIV, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), Some((Instruction::FDIV, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), None, None],
                BiOp::Mod => [Some((Instruction::IMOD, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), None, None, None],
                BiOp::DoubleEquals => [Some((Instruction::CMP(Cond::Eq), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::Eq), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::Eq), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None],  // TODO
                BiOp::NotEquals => [Some((Instruction::CMP(Cond::NEq), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::NEq), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::NEq), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None],  // TODO
                BiOp::GreaterThan => [Some((Instruction::CMP(Cond::IGr), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::FGr), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None, None],
                BiOp::GreatherThanEquals => [Some((Instruction::CMP(Cond::IGrE), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::FGrE), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None, None],
                BiOp::LessThan => [Some((Instruction::CMP(Cond::ILe), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::FLe), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None, None],
                BiOp::LessThanEquals => [Some((Instruction::CMP(Cond::ILeE), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::FLeE), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None, None],
            };

            let gotten = &matrix[match l_type {
                UwUTy::Native(&NativeType::Primitive(Primitive::I64)) => 0,
                UwUTy::Native(&NativeType::Primitive(Primitive::F64)) => 1,
                UwUTy::Native(&NativeType::Primitive(Primitive::Bool)) => 2,
                UwUTy::Native(&NativeType::Primitive(Primitive::Unit)) => pnck!(CompilerError { tpe: ErrorType::UnsupportedOperation("cannot perform operations on unit type"), loc: *loc }),
                UwUTy::Struct(_) => 3,
                UwUTy::Array(_) => pnck!(CompilerError { tpe: ErrorType::UnsupportedOperation("no operations are supported on arrays"), loc: *loc }),
            }];

            let ins_res = match gotten {
                Some(v) => {
                    v
                }
                None => panic!("I don't get paid enough for this shit, you're on your own"),
            };
            out.push(ins_res.0.clone());
            out.current().values.pop();
            out.current().values.pop();
            out.current().values.push((None, ins_res.1.pseudo_copy()))
        }
        Expression::FunctionInvocation { name, args, loc } => {
            let mut types = vec![];
            for expr in args {
                compile_expr(expr, import_mapping, out)?;  // NOTE: this could be backwards
                types.push(out.last_tpe());
            }
            let resolved = import_mapping[name].as_func(&types).expect("function not found");
            for _ in 0..args.len() {
                out.current().values.pop();
            }
            out.current().values.push((None, resolved.return_type()));
            match &resolved {
                UwUFunc::Native(v) => {
                    out.push(Instruction::NATIVE(v.id as usize));
                }
                UwUFunc::Defined { .. } => {
                    out.calls_to_update.push((resolved, out.out.len()));
                    out.push(Instruction::CALL(u64::MAX, args.len() as u32));
                }
            }
        }
        Expression::Instantiation { name, args, loc } => {
            let resolved = import_mapping[name].as_type().expect("can't instantiate a function");
            match resolved {
                UwUTy::Struct(v) => {
                    assert!(v.fields.len() == args.len(), "wrong number of args");
                    for (field, expr) in v.fields.iter().zip(args).rev() {
                        compile_expr(expr, import_mapping, out)?;  // NOTE: this could be backwards
                        assert!(out.current().values.last().unwrap().1 == field.1);
                    }
                    for _ in 0..v.fields.len() {
                        out.current().values.pop();
                    }
                    let found = out.type_m.get(&resolved);
                    let num = match found {
                        Some(v) => *v,
                        None => {
                            let n = out.types.len();
                            out.types.push(resolved.to_info());
                            out.type_m.insert(resolved.pseudo_copy(), n);
                            n
                        }
                    };
                    out.push(Instruction::ALLOC(num));
                    out.current().values.push((None, resolved));
                }
                UwUTy::Native(_) => panic!("can't instantiate a native type"),
                UwUTy::Array(_) => panic!("can't instantiate an array"),
            }
        }
        Expression::VarAccess(name, loc) => {
            let mut found = None;
            for (fridx, frame) in out.stack.iter().rev().enumerate() {
                for (idx, item) in frame.values.iter().enumerate().rev() {
                    if match &item.0 {
                        Some(v) => v == name,
                        None => false
                    } {
                        found = Some((fridx as u32, idx as u32, item.1.pseudo_copy()));
                    }
                }
            }

            let f = found.expect("couldn't find variable");
            out.push(Instruction::COPY { from_top: f.0, in_frame: f.1 });
            out.current().values.push((None, f.2));
        }
        Expression::PropertyAccess(value, name, loc) => {
            compile_expr(&*value, import_mapping, out)?;
            let tpe = out.last_tpe();
            let (idx, field_tpe) = match tpe {
                UwUTy::Struct(s) => {
                    let (idx, (_, field_tpe)) = s.fields.iter().enumerate().find(|x| &x.1.0 == name).expect("field not found");
                    (idx, field_tpe)
                }
                UwUTy::Native(_) => panic!("cannot access field of native type"),
                UwUTy::Array(_) => {
                    assert!(name == "size" || name == "wength", "field not found");
                    (0, &UwUTy::Native(I64))
                }
            };
            out.current().values.pop();
            out.current().values.push((None, field_tpe.pseudo_copy()));
            out.push(Instruction::GET(idx as u32));
        }
        Expression::ArrayCreation { typename, degree, num, loc } => {
            let inner = import_mapping[typename].as_type().expect("type not found");
            let mut tpe = inner.pseudo_copy();
            for _ in 0..*degree {
                tpe = UwUTy::Array(Box::new(tpe));
            }

            compile_expr(&*num, import_mapping, out)?;
            assert!(out.last_tpe() == UwUTy::Native(I64), "array lengths must be integers");
            out.push(Instruction::ALLOCA(inner.as_tpe(out)));
            out.current().values.pop();
            out.current().values.push((None, tpe));
        }
        Expression::ArrayAccess { arr, idx, loc } => {
            compile_expr(arr, import_mapping, out)?;
            let item_type = match out.last_tpe() {
                UwUTy::Array(v) => v.pseudo_copy(),
                _ => panic!("cannot index non-array type")
            };
            compile_expr(&*idx, import_mapping, out)?;
            let idx_type = out.last_tpe();
            assert!(idx_type == UwUTy::Native(I64), "arrays must be indexed with integers");
            out.push(Instruction::GETA);
            out.current().values.pop();
            out.current().values.pop();
            out.current().values.push((None, item_type));
        },
        Expression::MethodInvocation { left, name, args, loc: _ } => {
            compile_expr(left, import_mapping, out)?;
            let left_type = match out.current().values.last().unwrap().1 {
                UwUTy::Struct(v) => v.fqn.clone(),
                UwUTy::Native(_) => panic!(),
                UwUTy::Array(_) => panic!(),
            };

            // println!("file mapping: {:?}", import_mapping);

            let mut types = vec![];
            for expr in args {
                compile_expr(expr, import_mapping, out)?;  // NOTE: this could be backwards
                types.push(out.last_tpe());
            }

            let resolved = import_mapping[name].as_func(&types).expect("function not found");
            match &resolved {
                UwUFunc::Native(_) => panic!("can't call a method on a native type"),
                UwUFunc::Defined { fqn: _, args: _, return_type: _, data: _, receiver, id: _ } => {
                    // println!("rec: {:?} found: {:?}", receiver, left_type);
                    assert!(receiver.clone().unwrap().fqn == left_type)
                }
            }
            
            for _ in 0..args.len() {
                out.current().values.pop();
            }
            out.current().values.pop();
            out.current().values.push((None, resolved.return_type()));
            match &resolved {
                UwUFunc::Native(v) => {
                    out.push(Instruction::NATIVE(v.id as usize));
                }
                UwUFunc::Defined { .. } => {
                    out.calls_to_update.push((resolved, out.out.len()));
                    out.push(Instruction::CALL(u64::MAX, args.len() as u32 + 1));
                }
            }
        }
    }

    Ok(())
}

fn compile_block<'a, 'b, 'c>(block: &'a Vec<Statement<'a>>, import_mapping: &HashMap<String, Importable<'a, 'b>>, out: &mut InstructionBuilder<'a, 'b>) -> Result<(), CompilerError<'a, 'b>> {
    for item in block {
        match item {
            Statement::VariableDeclaration { mutable, name, value, loc } => {
                compile_expr(value, import_mapping, out)?;
                out.current().values.last_mut().unwrap().0 = Some(name.clone());
            }
            Statement::Assignment(name, value, loc) => {
                let mut found = None;
                for (fridx, frame) in out.stack.iter().rev().enumerate() {
                    for (idx, item) in frame.values.iter().enumerate().rev() {
                        if match &item.0 {
                            Some(v) => v == name,
                            None => false
                        } {
                            found = Some((fridx as u32, idx as u32, item.1.pseudo_copy()));
                        }
                    }
                }
                let dst = unwrap_or_ret!(found, CompilerError { loc: *loc, tpe: ErrorType::VariableNotFound(name.clone()) });
                compile_expr(value, import_mapping, out)?;
                asrt!(out.current().values.last().unwrap().1 == dst.2, CompilerError { loc: value.loc(), tpe: ErrorType::TypeMismatch { expected: dst.2, found: out.last_tpe() } });
                out.push(Instruction::MOV { from_top: dst.0, in_frame: dst.1 });
                out.current().values.pop();
            }
            Statement::PropertySet(left, name, right, loc) => {
                compile_expr(left, import_mapping, out)?;
                let tpe = out.last_tpe();
                let (idx, field_tpe) = match tpe {
                    UwUTy::Struct(s) => {
                        let (idx, (_, field_tpe)) = unwrap_or_ret!(s.fields.iter().enumerate().find(|x| &x.1.0 == name), CompilerError { tpe: ErrorType::FieldNotFound { tpe, name: name.clone() }, loc: *loc });
                        (idx, field_tpe.pseudo_copy())
                    }
                    UwUTy::Native(_) => pnck!(CompilerError { tpe: ErrorType::UnsupportedOperation("cannot set field of native type"), loc: *loc }),
                    UwUTy::Array(_) => pnck!(CompilerError { tpe: ErrorType::UnsupportedOperation("cannot set field of array"), loc: *loc }),
                };

                compile_expr(right, import_mapping, out)?;
                asrt!(field_tpe == out.last_tpe(), CompilerError { tpe: ErrorType::TypeMismatch { expected: field_tpe, found: out.last_tpe() }, loc: right.loc() });
                out.push(Instruction::SET(idx as u32));
                out.current().values.pop();
                out.current().values.pop();
            }
            Statement::Expression(e, loc) => compile_expr(e, import_mapping, out)?,
            Statement::If { condition, block, loc } => {
                compile_expr(condition, import_mapping, out)?;
                asrt!(out.last_tpe() == UwUTy::Native(BOOL), CompilerError { tpe: ErrorType::TypeMismatch { expected: UwUTy::Native(BOOL), found: out.last_tpe() }, loc: condition.loc() });
                out.current().values.pop();
                out.push(Instruction::PUSH(0));
                out.push(Instruction::HALT);
                let idx = out.out.len();
                out.stack.push(CompileStackFrame { values: vec![] });
                out.push(Instruction::PUSHFR);
                compile_block(block, import_mapping, out)?;
                out.push(Instruction::POPFR);
                out.stack.pop();
                out.out[idx - 1] = Instruction::BRANCH(Cond::Eq, out.out.len() as u64);
            }
            Statement::While { condition, block, loc } => {
                let start = out.out.len();
                out.stack.push(CompileStackFrame { values: vec![] });
                out.push(Instruction::PUSHFR);

                compile_expr(condition, import_mapping, out)?;
                asrt!(out.last_tpe() == UwUTy::Native(BOOL), CompilerError { tpe: ErrorType::TypeMismatch { expected: UwUTy::Native(BOOL), found: out.last_tpe() }, loc: condition.loc() });

                out.push(Instruction::PUSH(0));
                let idx = out.out.len();
                out.push(Instruction::BRANCH(Cond::Eq, u64::MAX));
                out.current().values.pop();

                compile_block(block, import_mapping, out)?;

                out.push(Instruction::POPFR);
                out.push(Instruction::BRANCH(Cond::Always, start as u64));
                out.stack.pop();
                out.out[idx] = Instruction::BRANCH(Cond::Eq, out.out.len() as u64);
                out.push(Instruction::POPFR);
            }
            Statement::Break(loc) => todo!(),
            Statement::Return(_, loc) => todo!(),
            Statement::ArraySet { arr, indexes, value, loc } => {
                compile_expr(arr, import_mapping, out)?;
                let item_type = match out.last_tpe() {
                    UwUTy::Array(v) => v.pseudo_copy(),
                    _ => pnck!(CompilerError { tpe: ErrorType::UnsupportedOperation("cannot index non-array type"), loc: arr.loc() })
                };
                let idx = &indexes[0];
                asrt!(indexes.len() == 1, CompilerError { tpe: ErrorType::Unimplemented("multidimensional arrays are not yet supported"), loc: *loc });
                compile_expr(idx, import_mapping, out)?;
                let idx_type = out.last_tpe();
                asrt!(idx_type == UwUTy::Native(I64), CompilerError { tpe: ErrorType::TypeMismatch { expected: UwUTy::Native(I64), found: idx_type.pseudo_copy() }, loc: idx.loc() });
                compile_expr(value, import_mapping, out)?;
                asrt!(out.last_tpe() == item_type, CompilerError { tpe: ErrorType::TypeMismatch { expected: item_type, found: out.last_tpe() }, loc: value.loc() });
                out.push(Instruction::SETA);
                out.current().values.pop();
                out.current().values.pop();
                out.current().values.pop();
            }
        }
    }

    Ok(())
}

fn compile_function<'a, 'b, 'c>(func: &UwUFunc<'a, 'b>, import_mapping: &HashMap<String, Importable<'a, 'b>>, out: &mut InstructionBuilder<'a, 'b>) {
    out.starts.insert(func.pseudo_copy(), out.out.len());
    out.stack.clear();
    out.stack.push(CompileStackFrame { values: vec![] });
    let (_, args, _, data, receiver) =  match func {
        UwUFunc::Native(_) => panic!(),
        UwUFunc::Defined { fqn, args, return_type, data, receiver, id: _ } => (fqn, args, return_type, *data, receiver)
    };
    match receiver {
        Some(v) => {
            let found = match &import_mapping[v.fqn.last().unwrap()] {
                Importable::Type(v) => v.pseudo_copy(),
                Importable::FunctionSet(_) => panic!(),
            };
            out.current().values.push((Some("sewf".to_string()), found));    
        }
        None => {}
    }
    for item in args {
        out.current().values.push((Some(item.0.clone()), item.1.pseudo_copy()))
    }

    compile_block(data, import_mapping, out).unwrap();

    out.push(Instruction::PUSH(0));
    out.push(Instruction::RET);
}

pub struct InstructionBuilder<'a, 'b> {
    out: Vec<Instruction>,
    calls_to_update: Vec<(UwUFunc<'a, 'b>, usize)>,
    stack: Vec<CompileStackFrame<'b>>,
    starts: HashMap<UwUFunc<'a, 'b>, usize>,
    type_m: HashMap<UwUTy<'b>, usize>,
    pub types: Vec<FieldInfo>
}

#[derive(Debug)]
struct CompileStackFrame<'b> {
    values: Vec<(Option<String>, UwUTy<'b>)>
}

impl<'a, 'b> InstructionBuilder<'a, 'b> {
    fn current(&mut self) -> &mut CompileStackFrame<'b> {
        self.stack.last_mut().unwrap()
    }

    fn push(&mut self, ins: Instruction) {
        self.out.push(ins)
    }

    fn last_tpe(&self) -> UwUTy<'b> {
        self.stack.last().unwrap().values.last().unwrap().1.pseudo_copy()
    }
}

trait Append<T> {
    fn plus(&self, v: T) -> Self;
}

impl<T> Append<T> for Vec<T> where T : Clone {
    fn plus(&self, v: T) -> Self {
        let mut out = self.clone();
        out.push(v);
        out
    }
}

impl<T> Append<&T> for Vec<T> where T : Clone {
    fn plus(&self, v: &T) -> Self {
        self.plus(v.clone())
    }
}

impl Append<&str> for Vec<String> {
    fn plus(&self, v: &str) -> Self {
        self.plus(v.to_string())
    }
}

trait Single<T> {
    fn single(self, predicate: fn(&T) -> bool) -> Option<T>;
}

impl<T> Single<T> for Vec<T> {
    fn single(self, predicate: fn(&T) -> bool) -> Option<T> {
        let mut found = None;

        for item in self {
            if predicate(&item) {
                if found.is_some() {
                    return None;
                }
                found = Some(item);
            }
        }

        return found;
    }
}

trait Intify {
    fn as_int(self) -> i64;
}

impl Intify for f64 {
    fn as_int(self) -> i64 {
        unsafe { std::mem::transmute(self) }
    }
}

impl Intify for bool {
    fn as_int(self) -> i64 {
        if self { 1 } else { 0 }
    }
}

pub struct CompilerError<'a, 'b> {
    pub tpe: ErrorType<'a, 'b>,
    pub loc: Loc<'a>
}

impl<'a, 'b> Debug for CompilerError<'a, 'b> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{:?}: {:?}", self.loc, self.tpe)
    }
}

#[derive(Debug)]
pub enum ErrorType<'a, 'b> {
    VariableNotFound(String),
    TypeMismatch { expected: UwUTy<'b>, found: UwUTy<'b> },
    FieldNotFound { tpe: UwUTy<'b>, name: String },
    UnsupportedOperation(&'static str),
    TypeNotFound(Type<'a>),
    Unimplemented(&'static str)
}
