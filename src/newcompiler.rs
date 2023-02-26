/*

 1. Resolve types
  1. Go through all files
  2. Instantiate all structs with no fields
  3. Instantiate all functions with no args and unit return type
  4. Resolve struct types and function types

*/

use std::{collections::HashMap, slice::Iter};

use crate::{Declaration, ParsedFile, NameTypePair, stdlib::{NativeType, NativeFunction, PRIMITIVE_TYPES, UNIT, I64, BOOL, F64}, runtime::{Instruction, FieldInfo}, Expression, Statement};

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
struct UwUStrc<'b> {
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

#[derive(PartialEq, Hash, Eq)]
enum UwUFunc<'a, 'b> {
    Native(&'b NativeFunction<'b>),
    Defined { fqn: Vec<String>, args: Vec<(String, UwUTy<'b>)>, return_type: UwUTy<'b>, data: &'a Vec<Statement<'a>> }
}

impl<'a, 'b> UwUFunc<'a, 'b> {
    fn fqn(&self) -> Vec<String> {
        match self {
            UwUFunc::Native(v) => v.fqn.clone(),
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
            UwUFunc::Native(v) => v.args.iter().map(|x| (x.0.clone(), x.1.pseudo_copy())).collect(),
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

#[derive(PartialEq, Eq, Hash)]
struct UwUFi<'a> {
    fqn: Vec<String>,
    content: Vec<Declaration<'a>>
}

impl<'b> UwUTy<'b> {
    fn to_info(&self) -> FieldInfo {
        match self {
            UwUTy::Struct(s) => FieldInfo::Fields(s.fields.iter().map(|x| x.1.to_info()).collect()),
            UwUTy::Native(_) => FieldInfo::Primitive,
            UwUTy::Array(v) => FieldInfo::Array(Box::new(v.to_info())),
        }
    }
}

fn compile<'a, 'b, 'c>(files: &'a Vec<UwUFi<'a>>, entrypoint: Vec<String>) -> (Vec<FieldInfo>, Vec<Instruction<'c>>) {
    // let mut out = ResolvedTypesFileData { mapping: HashMap::new(), structs: vec![], functions: vec![], files };
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
            let stdlib_type = None;  // TODO: stdlib types here!
            let stdlib_fun = None;  // TODO: stdlib functions here!
            // check if it's a struct
            let found_type = structs_s.iter().find(|x| x.fqn == item.fqn).map(|found| Importable::Type(UwUTy::Struct(&found)));
            // check if it's a function
            let found_function = functions.iter().find(|x| x.0.fqn() == item.fqn).map(|found| Importable::Function(found.0.pseudo_copy()));
            
            // require that exactly one of these possibilities actually matches
            let all = vec![stdlib_type, stdlib_fun, found_type, found_function];
            let found = all.single(|x| x.is_some()).expect("unable to resolve import").unwrap();

            file_mapping.insert(item.name, found);
        }

        mapping.insert(file, file_mapping);
    }

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

            let resolved_type = mapping[file][type_name].as_type().expect("cannot use a function as a type");  // TODO: error checking instead of just panic if not found

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

        let resolved_ret_type = mapping[file][&rtype.unwrap_or("unit".to_string())].as_type().expect("cannot use a function as a type");
        let resolved_args = args.iter().map(|arg| {
            (arg.name.clone(), mapping[file][&arg.tpe].as_type().expect("cannot use a function as a type"))
        }).collect();
        let new = &mut UwUFunc::Defined { fqn: func.fqn(), args: resolved_args, return_type: resolved_ret_type, data };
        std::mem::swap(new, unsafe { &mut *(func as *const UwUFunc as *mut UwUFunc) });
    }

    // do the actual compiling
    let entryp = functions.iter().find(|x| x.1.fqn == entrypoint).expect("entrypoint not found");

    let mut out = InstructionBuilder { out: vec![], calls_to_update: vec![], stack: vec![], starts: HashMap::new(), types: HashMap::new() };
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

    // let mut out_structs = vec![];
    // for (strct, _, _) in structs_s {
    //     out_structs.push(strct);
    // };

    let mut info = vec![];
    for item in &structs_s {
        info.push(UwUTy::Struct(item).to_info())
    }

    (info, out.out)
}

fn compile_expr<'a, 'b, 'c>(expr: &Expression, import_mapping: &HashMap<String, Importable<'a, 'b>>, out: &mut InstructionBuilder<'a, 'b, 'c>) {
    match expr {
        Expression::Literal(v) => {
            let tpe = match v {
                crate::Literal::Int(n) => { out.push(Instruction::PUSH(*n)); UwUTy::Native(I64) }
                crate::Literal::Float(n) => { out.push(Instruction::PUSH(n.as_int())); UwUTy::Native(F64) }
                crate::Literal::Bool(b) => { out.push(Instruction::PUSH(b.as_int())); UwUTy::Native(BOOL) }
                crate::Literal::String(s) => todo!(),
            };
            out.current().values.push((None, tpe));
        }
        Expression::Parenthesis(v) => compile_expr(v, import_mapping, out),
        Expression::BiOperation(l, op, r) => todo!(),
        Expression::FunctionInvocation { name, args } => {
            let resolved = import_mapping[name].as_func().expect("can't call a type (use new)");
            let exp_args = resolved.args();
            let num_args = exp_args.len();

            assert!(num_args == args.len(), "wrong number of args");
            for (arg, expr) in exp_args.iter().zip(args) {
                compile_expr(expr, import_mapping, out);  // NOTE: this could be backwards
                assert!(out.current().values.last().unwrap().1 == arg.1);
            }
            for _ in 0..exp_args.len() {
                out.current().values.pop();
            }
            out.current().values.push((None, resolved.return_type()));
            out.calls_to_update.push((resolved, out.out.len()));
            out.push(Instruction::CALL(u64::MAX, num_args as u32));
        }
        Expression::Instantiation { name, args } => {
            let resolved = import_mapping[name].as_type().expect("can't instantiate a function");
            match resolved {
                UwUTy::Struct(v) => {
                    assert!(v.fields.len() == args.len(), "wrong number of args");
                    for (field, expr) in v.fields.iter().zip(args) {
                        compile_expr(expr, import_mapping, out);  // NOTE: this could be backwards
                        assert!(out.current().values.last().unwrap().1 == field.1);
                    }
                    for _ in 0..v.fields.len() {
                        out.current().values.pop();
                    }
                    out.push(Instruction::ALLOC(resolved.to_info()));
                    out.current().values.push((None, resolved))
                }
                UwUTy::Native(_) => panic!("can't instantiate a native type"),
                UwUTy::Array(_) => todo!(),
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
    }
}

fn compile_function<'a, 'b, 'c>(func: &UwUFunc<'a, 'b>, import_mapping: &HashMap<String, Importable<'a, 'b>>, out: &mut InstructionBuilder<'a, 'b, 'c>) {
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
    for item in data {
        match item {
            Statement::VariableDeclaration { mutable, name, value } => todo!(),
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
                out.push(Instruction::COPY { from_top: dst.0, in_frame: dst.1 });
            }
            Statement::Expression(e) => compile_expr(e, import_mapping, out),
            Statement::If { condition, block } => todo!(),
            Statement::While { condition, block } => todo!(),
            Statement::Break => todo!(),
            Statement::Return(_) => todo!(),
        }
    }
}

struct InstructionBuilder<'a, 'b, 'c> {
    out: Vec<Instruction<'c>>,
    calls_to_update: Vec<(UwUFunc<'a, 'b>, usize)>,
    stack: Vec<CompileStackFrame<'b>>,
    starts: HashMap<UwUFunc<'a, 'b>, usize>,
    types: HashMap<UwUTy<'b>, FieldInfo>
}

struct CompileStackFrame<'b> {
    values: Vec<(Option<String>, UwUTy<'b>)>
}

impl<'a, 'b, 'c> InstructionBuilder<'a, 'b, 'c> {
    fn current(&mut self) -> &mut CompileStackFrame<'b> {
        self.stack.last_mut().unwrap()
    }

    fn push(&mut self, ins: Instruction<'c>) {
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
