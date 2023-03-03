/*

 1. Resolve types
  1. Go through all files
  2. Instantiate all structs with no fields
  3. Instantiate all functions with no args and unit return type
  4. Resolve struct types and function types

*/

use std::{collections::HashMap, slice::Iter};

use crate::{Declaration, ParsedFile, NameTypePair, stdlib::{NativeType, NativeFunction, PRIMITIVE_TYPES, UNIT, I64, BOOL, F64, STDLIB_FUNCS}, runtime::{Instruction, FieldInfo, Cond, Tpe}, Expression, Statement, BiOp, Type};

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct UwUStrc<'b> {
    fqn: Vec<String>,
    fields: Vec<(String, UwUTy<'b>)>
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

#[derive(PartialEq, Hash, Eq, Debug)]
enum UwUFunc<'a, 'b> {
    Native(&'b NativeFunction<'b>),
    Defined { fqn: Vec<String>, args: Vec<(String, UwUTy<'b>)>, return_type: UwUTy<'b>, data: &'a Vec<Statement<'a>> }
}

impl<'a, 'b> UwUFunc<'a, 'b> {
    fn fqn(&self) -> Vec<String> {
        match self {
            UwUFunc::Native(v) => v.fqn.iter().map(|x| x.to_string()).collect(),
            UwUFunc::Defined { fqn, args, return_type, data } => fqn.clone(),
        }
    }

    fn pseudo_copy(&self) -> UwUFunc<'a, 'b> {
        match self {
            UwUFunc::Native(v) => UwUFunc::Native(v),
            UwUFunc::Defined { fqn, args, return_type, data } => UwUFunc::Defined { fqn: fqn.clone(), args: args.iter().map(|x| (x.0.clone(), x.1.pseudo_copy())).collect(), return_type: return_type.pseudo_copy(), data }
        }
    }

    fn args(&self) -> Vec<(String, UwUTy)> {
        match self {
            UwUFunc::Native(v) => v.args.iter().map(|x| (x.0.to_string(), x.1.pseudo_copy())).collect(),
            UwUFunc::Defined { fqn, args, return_type, data } => args.iter().map(|x| (x.0.clone(), x.1.pseudo_copy())).collect()
        }
    }

    fn return_type(&self) -> UwUTy<'b> {
        match self {
            UwUFunc::Native(v) => v.ret.pseudo_copy(),
            UwUFunc::Defined { fqn, args, return_type, data } => return_type.pseudo_copy()
        }
    }
}

#[derive(Debug)]
enum Importable<'a, 'b> {
    Type(UwUTy<'b>),
    Function(UwUFunc<'a, 'b>)
}

impl<'a, 'b> Importable<'a, 'b> {
    fn as_type(&self) -> Option<UwUTy<'b>> {
        match self {
            Importable::Type(v) => Some(v.pseudo_copy()),
            Importable::Function(_) => None
        }
    }

    fn as_func(&self) -> Option<UwUFunc<'a, 'b>> {
        match self {
            Importable::Type(_) => None,
            Importable::Function(v) => Some(v.pseudo_copy())
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

fn resolve<'a, 'b>(mapping: &HashMap<String, Importable<'a, 'b>>, tpe: &Type) -> Option<UwUTy<'b>> {
    match tpe {
        Type::Simple(t) => mapping[t].as_type(),
        Type::Array(t) => Some(UwUTy::Array(Box::new(resolve(mapping, &*t)?)))
    }
}

pub fn compile<'a, 'b, 'c>(files: &'a Vec<UwUFi<'a>>, entrypoint: Vec<String>) -> (Vec<FieldInfo>, Vec<Instruction>) {
    // let mut structs = vec![];
    let mut structs_s = vec![];
    let mut structs_f = vec![];
    let mut structs_d = vec![];
    let mut functions = vec![];

    // collect all the functions and structs without resolving any times (structs have no fields, functions have no args and return unit)
    for file in files {
        for decl in &file.content {
            match decl {
                Declaration::Function { name, args, return_type, block } => {
                    functions.push((UwUFunc::Defined { fqn: file.fqn.plus(name), args: vec![], return_type: UwUTy::Native(UNIT), data: block }, file, decl));
                }
                Declaration::Struct { name, fields } => {
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
                Declaration::Import { path, item } => { raw_imports.push(UnresolvedImport { fqn: path.plus(item), name: item.clone() }) }
                _ => {}
            }
        }

        let mut file_mapping = HashMap::new();

        for item in raw_imports {
            let stdlib_type = PRIMITIVE_TYPES.iter().find(|x| x.fqn() == item.fqn).map(|x| Importable::Type(UwUTy::Native(x)));
            let stdlib_fun = STDLIB_FUNCS.iter().find(|x| x.fqn == item.fqn).map(|x| Importable::Function(UwUFunc::Native(x)));
            // check if it's a struct
            let found_type = structs_s.iter().find(|x| x.fqn == item.fqn).map(|found| Importable::Type(UwUTy::Struct(&found)));
            // check if it's a function
            let found_function = functions.iter().find(|x| x.0.fqn() == item.fqn).map(|found| Importable::Function(found.0.pseudo_copy()));
            
            // require that exactly one of these possibilities actually matches
            let all = vec![stdlib_type, stdlib_fun, found_type, found_function];
            let found = all.single(|x| x.is_some()).expect("unable to resolve import").unwrap();

            file_mapping.insert(item.name, found);
        }

        for item in PRIMITIVE_TYPES {
            file_mapping.insert(item.fqn().last().unwrap().to_string(), Importable::Type(UwUTy::Native(item)));
        }

        for (func, fi, _) in &functions {
            if fi == &file {
                file_mapping.insert(func.fqn().last().unwrap().clone(), Importable::Function(func.pseudo_copy()));
            }
        }

        for i in 0..structs_s.len() {
            let strct = &structs_s[i];
            let fi = &structs_f[i];

            if fi == &file {
                file_mapping.insert(strct.fqn.last().unwrap().clone(), Importable::Type(UwUTy::Struct(strct)));
            }
        }

        mapping.insert(file, file_mapping);
    }

    // println!("mapping: {:?}", mapping);

    // Resolve struct types
    for idx in 0..structs_s.len() {
        let strct = &structs_s[idx];
        let file = &structs_f[idx];
        let decl = &structs_d[idx];
        let fields = match decl {
            Declaration::Struct { name, fields } => fields,
            _ => panic!()
        };
        let resolved_fields = fields.iter().map(|pair| {
            let name = pair.name.clone();
            let type_name = &pair.tpe;

            let resolved_type = resolve(&mapping[file], type_name).expect("cannot use a function as a type");  // TODO: error checking instead of just panic if not found

            (name, resolved_type)
        }).collect();

        // This is slightly horrible, but necessary
        unsafe { (*(strct as *const UwUStrc as *mut UwUStrc)).fields = resolved_fields }
    }

    // Resolve function arg+return types
    for (func, file, decl) in &functions {
        let (args, rtype, data) = match decl {
            Declaration::Function { name, args, return_type, block } => (args.clone(), return_type.clone(), block),
            _ => panic!()
        };

        let resolved_ret_type = resolve(&mapping[file], &rtype.unwrap_or(Type::Simple("unit".to_string()))).expect("cannot use a function as a type");
        let resolved_args = args.iter().map(|arg| {
            (arg.name.clone(), resolve(&mapping[file], &arg.tpe).expect("cannot use a function as a type"))
        }).collect();
        let new = &mut UwUFunc::Defined { fqn: func.fqn(), args: resolved_args, return_type: resolved_ret_type, data };
        std::mem::swap(new, unsafe { &mut *(func as *const UwUFunc as *mut UwUFunc) });
    }

    // do the actual compiling
    let entryp = functions.iter().find(|x| x.0.fqn() == entrypoint).expect("entrypoint not found");

    let mut out = InstructionBuilder { out: vec![], calls_to_update: vec![], stack: vec![], starts: HashMap::new(), type_m: HashMap::new(), types: vec![] };
    compile_function(&entryp.0, &mapping[entryp.1], &mut out);

    for (func, file, _) in &functions {
        if func == &entryp.0 {
            continue;
        }
        compile_function(func, &mapping[file], &mut out);
    }

    for (func, idx) in out.calls_to_update {
        let found = out.starts[&func];
        out.out[idx] = Instruction::CALL(found as u64, func.args().len() as u32);
    }

    (out.types, out.out)
}

fn compile_expr<'a, 'b, 'c>(expr: &Expression, import_mapping: &HashMap<String, Importable<'a, 'b>>, out: &mut InstructionBuilder<'a, 'b>) {
    match expr {
        Expression::Literal(v) => {
            let tpe = match v {
                crate::Literal::Int(n) => { out.push(Instruction::PUSH(*n)); UwUTy::Native(I64) }
                crate::Literal::Float(n) => { out.push(Instruction::PUSH(n.as_int())); UwUTy::Native(F64) }
                crate::Literal::Bool(b) => { out.push(Instruction::PUSH(b.as_int())); UwUTy::Native(BOOL) }
                crate::Literal::String(s) => {
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
        Expression::Parenthesis(v) => compile_expr(v, import_mapping, out),
        Expression::BiOperation(l, op, r) => {
            compile_expr(&*l, import_mapping, out);
            let l_type = &out.current().values.last().unwrap().1.pseudo_copy();
            compile_expr(&*r, import_mapping, out);
            let r_type = &out.current().values.last().unwrap().1.pseudo_copy();

            if l_type != r_type {
                panic!("left and right terms must have the same type (left = {:?}, right = {:?})", l_type, r_type);
            }

            let matrix = match op {
                // i64, f64, bool, custom
                BiOp::Plus => [Some((Instruction::IADD, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), Some((Instruction::FADD, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), None, None],
                BiOp::Minus => [Some((Instruction::ISUB, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), Some((Instruction::FSUB, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), None, None],
                BiOp::Times => [Some((Instruction::IMUL, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), Some((Instruction::FMUL, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), None, None],
                BiOp::Divide => [Some((Instruction::IDIV, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), Some((Instruction::FDIV, UwUTy::Native(&NativeType::Primitive(Primitive::I64)))), None, None],
                BiOp::DoubleEquals => [Some((Instruction::CMP(Cond::Eq), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::Eq), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::Eq), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None],  // TODO
                BiOp::GreaterThan => [Some((Instruction::CMP(Cond::IGr), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::FGr), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None, None],
                BiOp::GreatherThanEquals => [Some((Instruction::CMP(Cond::IGrE), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::FGrE), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None, None],
                BiOp::LessThan => [Some((Instruction::CMP(Cond::ILe), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::FLe), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None, None],
                BiOp::LessThanEquals => [Some((Instruction::CMP(Cond::ILeE), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), Some((Instruction::CMP(Cond::FLeE), UwUTy::Native(&NativeType::Primitive(Primitive::Bool)))), None, None],
            };

            let gotten = &matrix[match l_type {
                UwUTy::Native(&NativeType::Primitive(Primitive::I64)) => 0,
                UwUTy::Native(&NativeType::Primitive(Primitive::F64)) => 1,
                UwUTy::Native(&NativeType::Primitive(Primitive::Bool)) => 2,
                UwUTy::Native(&NativeType::Primitive(Primitive::Unit)) => panic!("cannot perform operations on unit type"),
                UwUTy::Struct(_) => 3,
                UwUTy::Array(_) => panic!("no operations are supported on arrays"),
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
        Expression::FunctionInvocation { name, args } => {
            let resolved = import_mapping[name].as_func().expect("can't call a type (use new)");
            let exp_args = resolved.args();
            let num_args = exp_args.len();

            assert!(num_args == args.len(), "wrong number of args");
            for (arg, expr) in exp_args.iter().zip(args) {
                compile_expr(expr, import_mapping, out);  // NOTE: this could be backwards
                assert!(out.current().values.last().unwrap().1 == arg.1, "incorrect argument type (expected {:?}, found {:?})", arg.1, out.current().values.last().unwrap().1);
            }
            for _ in 0..exp_args.len() {
                out.current().values.pop();
            }
            out.current().values.push((None, resolved.return_type()));
            match &resolved {
                UwUFunc::Native(v) => {
                    out.push(Instruction::NATIVE(v.id as usize));
                }
                UwUFunc::Defined { .. } => {
                    out.calls_to_update.push((resolved, out.out.len()));
                    out.push(Instruction::CALL(u64::MAX, num_args as u32));
                }
            }
        }
        Expression::Instantiation { name, args } => {
            let resolved = import_mapping[name].as_type().expect("can't instantiate a function");
            match resolved {
                UwUTy::Struct(v) => {
                    assert!(v.fields.len() == args.len(), "wrong number of args");
                    for (field, expr) in v.fields.iter().zip(args).rev() {
                        compile_expr(expr, import_mapping, out);  // NOTE: this could be backwards
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
        Expression::VarAccess(name) => {
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
        Expression::PropertyAccess(value, name) => {
            compile_expr(&*value, import_mapping, out);
            let tpe = out.current().values.last().unwrap().1.pseudo_copy();
            let (idx, field_tpe) = match tpe {
                UwUTy::Struct(s) => {
                    let (idx, (_, field_tpe)) = s.fields.iter().enumerate().find(|x| &x.1.0 == name).expect("field not found");
                    (idx, field_tpe)
                }
                UwUTy::Native(_) => panic!("cannot access field of native type"),
                UwUTy::Array(_) => {
                    assert!(name == "size" || name == "wength", "field not found");
                    out.push(Instruction::GET(0));
                    (0, &UwUTy::Native(I64))
                }
            };
            out.current().values.pop();
            out.current().values.push((None, field_tpe.pseudo_copy()));
            out.push(Instruction::GET(idx as u32));
        }
        Expression::ArrayCreation { typename, degree, num } => {
            let inner = import_mapping[typename].as_type().expect("type not found");
            let mut tpe = inner.pseudo_copy();
            for _ in 0..*degree {
                tpe = UwUTy::Array(Box::new(tpe));
            }

            compile_expr(&*num, import_mapping, out);
            assert!(&out.current().values.last().unwrap().1 == &UwUTy::Native(I64), "array lengths must be integers");
            out.push(Instruction::ALLOCA(inner.as_tpe(out)));
            out.current().values.pop();
            out.current().values.push((None, tpe));
        }
        Expression::ArrayAccess { arr, idx } => {
            compile_expr(arr, import_mapping, out);
            let item_type = match &out.current().values.last().unwrap().1 {
                UwUTy::Array(v) => v.pseudo_copy(),
                _ => panic!("cannot index non-array type")
            };
            compile_expr(&*idx, import_mapping, out);
            let idx_type = &out.current().values.last().unwrap().1;
            assert!(idx_type == &UwUTy::Native(I64), "arrays must be indexed with integers");
            out.push(Instruction::GETA);
            out.current().values.pop();
            out.current().values.pop();
            out.current().values.push((None, item_type));
        }
    }
}

fn compile_block<'a, 'b, 'c>(block: &Vec<Statement<'a>>, import_mapping: &HashMap<String, Importable<'a, 'b>>, out: &mut InstructionBuilder<'a, 'b>) {
    for item in block {
        match item {
            Statement::VariableDeclaration { mutable, name, value } => {
                compile_expr(value, import_mapping, out);
                out.current().values.last_mut().unwrap().0 = Some(name.clone());
            }
            Statement::Assignment(name, value) => {
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
                let dst = found.expect("couldn't find variable");
                compile_expr(value, import_mapping, out);
                assert!(out.current().values.last().unwrap().1 == dst.2, "variable type mismatch");
                out.push(Instruction::MOV { from_top: dst.0, in_frame: dst.1 });
                out.current().values.pop();
            }
            Statement::PropertySet(left, name, right) => {
                compile_expr(left, import_mapping, out);
                let tpe = out.current().values.last().unwrap().1.pseudo_copy();
                let (idx, field_tpe) = match tpe {
                    UwUTy::Struct(s) => {
                        let (idx, (_, field_tpe)) = s.fields.iter().enumerate().find(|x| &x.1.0 == name).expect("field not found");
                        (idx, field_tpe.pseudo_copy())
                    }
                    UwUTy::Native(_) => panic!("cannot set property '{}' of native type", name),
                    UwUTy::Array(_) => panic!("cannot set field '{}' of array", name),
                };

                compile_expr(right, import_mapping, out);
                assert!(&field_tpe == &out.current().values.last().unwrap().1, "field type mismatch");
                out.push(Instruction::SET(idx as u32));
                out.current().values.pop();
                out.current().values.pop();
            }
            Statement::Expression(e) => compile_expr(e, import_mapping, out),
            Statement::If { condition, block } => {
                compile_expr(condition, import_mapping, out);
                assert!(&out.current().values.last().unwrap().1 == &UwUTy::Native(BOOL), "if condition must be a boolean");
                out.current().values.pop();
                out.push(Instruction::PUSH(0));
                out.push(Instruction::HALT);
                let idx = out.out.len();
                out.stack.push(CompileStackFrame { values: vec![] });
                out.push(Instruction::PUSHFR);
                compile_block(block, import_mapping, out);
                out.push(Instruction::POPFR);
                out.stack.pop();
                out.out[idx - 1] = Instruction::BRANCH(Cond::Eq, out.out.len() as u64);
            }
            Statement::While { condition, block } => {
                let start = out.out.len();
                out.stack.push(CompileStackFrame { values: vec![] });
                out.push(Instruction::PUSHFR);

                compile_expr(condition, import_mapping, out);
                assert!(&out.current().values.last().unwrap().1 == &UwUTy::Native(BOOL), "while condition must be a boolean");

                out.push(Instruction::PUSH(0));
                let idx = out.out.len();
                out.push(Instruction::BRANCH(Cond::Eq, u64::MAX));
                out.current().values.pop();

                compile_block(block, import_mapping, out);

                out.push(Instruction::POPFR);
                out.push(Instruction::BRANCH(Cond::Always, start as u64));
                out.stack.pop();
                out.out[idx] = Instruction::BRANCH(Cond::NEq, out.out.len() as u64);
                out.push(Instruction::POPFR);
            }
            Statement::Break => todo!(),
            Statement::Return(_) => todo!(),
            Statement::ArraySet { arr, indexes, value } => {
                compile_expr(arr, import_mapping, out);
                let item_type = match &out.current().values.last().unwrap().1 {
                    UwUTy::Array(v) => v.pseudo_copy(),
                    _ => panic!("cannot index non-array type")
                };
                let idx = &indexes[0];
                assert!(indexes.len() == 1, "multidimensional arrays are not yet supported");
                compile_expr(idx, import_mapping, out);
                let idx_type = &out.current().values.last().unwrap().1;
                assert!(idx_type == &UwUTy::Native(I64), "arrays must be indexed with integers");
                compile_expr(value, import_mapping, out);
                assert!((&out.current().values.last().unwrap().1).pseudo_copy() == item_type, "incorrect type for item");
                out.push(Instruction::SETA);
                out.current().values.pop();
                out.current().values.pop();
                out.current().values.pop();
            }
        }
    }
}

fn compile_function<'a, 'b, 'c>(func: &UwUFunc<'a, 'b>, import_mapping: &HashMap<String, Importable<'a, 'b>>, out: &mut InstructionBuilder<'a, 'b>) {
    out.starts.insert(func.pseudo_copy(), out.out.len());
    out.stack.clear();
    out.stack.push(CompileStackFrame { values: vec![] });
    let (fqn, args, return_type, data) =  match func {
        UwUFunc::Native(_) => panic!(),
        UwUFunc::Defined { fqn, args, return_type, data } => (fqn, args, return_type, *data)
    };
    for item in args {
        out.current().values.push((Some(item.0.clone()), item.1.pseudo_copy()))
    }

    compile_block(data, import_mapping, out);

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
