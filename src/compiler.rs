// use std::collections::HashMap;

// use crate::{uwu_parser, lexer, Declaration, bytecode::{UwUStruct, Field, UwUType, Instruction, Primitive, Comparison, FieldInfo}, Statement, Expression, BiOp, stdlib::{CompNativeFunction, stdlib, stdlib_types}};

// #[derive(Hash, PartialEq, Eq, Clone)]
// pub struct UwUFile {
//     pub content: String,
//     pub path: Vec<String>,
//     pub name: String
// }

// struct UnresolvedField {
//     name: String,
//     tpe: String
// }

// struct UnresolvedStruct {
//     path: Vec<String>,
//     name: String,
//     fields: Vec<UnresolvedField>
// }

// #[derive(Debug, PartialEq, Eq, Hash)]
// struct FunctionData {
//     name: String,
//     args: Vec<String>,
//     return_type: String,
//     native: Option<u64>
// }

// #[derive(Debug)]
// enum ResolvedImport<'a> {
//     Type(UwUType<'a>),
//     Function(FunctionData)
// }

// impl<'a> ResolvedImport<'a> {
//     fn as_type(&self) -> &UwUType<'a> {
//         match self {
//             Self::Type(v) => v,
//             _ => panic!()
//         }
//     }

//     fn name(&self) -> String {
//         match self {
//             ResolvedImport::Type(v) => v.name(),
//             ResolvedImport::Function(d) => d.name.clone(),
//         }
//     }
// }

// impl<'a> UwUType<'a> {
//     fn as_field_info(&self) -> FieldInfo {
//         match self {
//             // TODO: cache to avoid infinite loop
//             UwUType::Struct(v) => FieldInfo::Struct { object_fields: v.fields.iter().map(|x| x.tpe.as_field_info()).collect() },
//             UwUType::Primitive(p) => FieldInfo::Primitive,
//             UwUType::Array(_) => todo!(),
//         }
//         // FieldInfo::Struct { object_fields: self.fields.iter().map(|x|) }
//     }
// }

// pub fn compile<'a>(files: Vec<UwUFile>, entrypoint: (Vec<String>, String)) -> (Vec<Instruction<'a>>, Vec<FieldInfo>) {  // entrypoint takes the form path.to.file::functionname
//     let parsed = files.iter().map(|x| (x, uwu_parser::file(lexer::tokenize(&x.content).unwrap().as_slice()).unwrap())).collect::<Vec<_>>();
//     // let mut finished_structs = vec![];
//     let mut structs = vec![];
//     let mut resolved_by_file = HashMap::new();
//     for (file, declarations) in &parsed {
//         let mut imports = vec![];
//         for decl in declarations {
//             match decl {
//                 Declaration::Import { path, item } => {
//                     imports.push((path, item))
//                 }
//                 _ => {}
//             }
//         }

//         resolved_by_file.insert(*file, (declarations, imports.clone()));

//         for decl in declarations {
//             match decl {
//                 Declaration::Struct { name, fields } => {
//                     let finished = UwUStruct { path: file.path.clone(), name: name.clone(), fields: vec![] };
//                     // finished_structs.push(finished);
//                     structs.push((finished, fields, imports.clone(), declarations));
//                 }
//                 _ => {}
//             }
//         }
//     }

//     let mut resolved = vec![];
//     for (strc, _, imports, file) in &structs {
//         let mut resolved_imports = stdlib().iter().map(|x| ResolvedImport::Function(FunctionData { name: x.qualified_name.last().unwrap().clone(), args: x.arg_types.iter().map(|x| x.name()).collect(), return_type: x.return_type.name(), native: Some(x.idx) })).collect::<Vec<_>>();
//         resolved_imports.extend(UwUType::primitives().iter().map(|x| ResolvedImport::Type(x.clone())));

//         for i in imports {
//             let mut found = None;
//             for s in structs.as_slice() {
//                 if &s.0.name == i.1 && &s.0.path == i.0 {
//                     found = Some(ResolvedImport::Type(UwUType::Struct(&s.0)));
//                 }
//             }
//             resolved_imports.push(found.expect("failed to resolve import"))
//         }

//         for s in &structs {
//             if s.0.path == strc.path {
//                 resolved_imports.push(ResolvedImport::Type(UwUType::Struct(&s.0)));
//             }
//         }

//         for s in *file {
//             match s {
//                 Declaration::Function { name, args, return_type, block } => {
//                     resolved_imports.push(ResolvedImport::Function(FunctionData { name: name.clone(), args: args.iter().map(|x| x.tpe.clone()).collect(), return_type: return_type.clone().unwrap_or("unit".to_string()), native: None }))
//                 }
//                 _ => {}
//             }
//         }

//         resolved_imports.extend(stdlib_types().iter().map(|x| ResolvedImport::Type(*x)));

//         resolved.push(resolved_imports);
//     }

//     let mut resolved_by_file_2 = HashMap::new();
//     for (file, (decls, item)) in resolved_by_file {
//         let mut resolved_imports = stdlib().iter().map(|x| ResolvedImport::Function(FunctionData { name: x.qualified_name.last().unwrap().clone(), args: x.arg_types.iter().map(|x| x.name()).collect(), return_type: x.return_type.name(), native: Some(x.idx) })).collect::<Vec<_>>();
//         resolved_imports.extend(UwUType::primitives().iter().map(|x| ResolvedImport::Type(x.clone())));

//         for i in item {
//             let mut found = None;
//             for s in structs.as_slice() {
//                 if &s.0.name == i.1 && &s.0.path == i.0 {
//                     found = Some(ResolvedImport::Type(UwUType::Struct(&s.0)));
//                 }
//             }
//             resolved_imports.push(found.expect("failed to resolve import"))
//         }

//         for s in &structs {
//             if s.0.path == file.path {
//                 resolved_imports.push(ResolvedImport::Type(UwUType::Struct(&s.0)));
//             }
//         }

//         for s in decls {
//             match s {
//                 Declaration::Function { name, args, return_type, block } => {
//                     // println!("function {}", name);
//                     resolved_imports.push(ResolvedImport::Function(FunctionData { name: name.clone(), args: args.iter().map(|x| x.tpe.clone()).collect(), return_type: return_type.clone().unwrap_or("unit".to_string()), native: None }))
//                 }
//                 _ => {}
//             }
//         }

//         resolved_imports.extend(stdlib_types().iter().map(|x| ResolvedImport::Type(*x)));

//         resolved_by_file_2.insert(file, resolved_imports);
//     }

//     let mut finalized_structs = vec![];

//     for i in 0..structs.len() {
//         let strct = &structs[i];
//         let res = &resolved[i];
//         let fields = strct.1.iter().map(|x| {
//             Field { tpe: *res.iter().find(|y| y.name() == x.name).unwrap().as_type(), name: x.name.clone() }
//         }).collect::<Vec<_>>();

//         // let fields = vec![];

//         finalized_structs.push(UwUStruct { path: strct.0.path.clone(), name: strct.0.name.clone(), fields })
//     }

//     // for i in 0..structs.len() {
//     //     let strct = &mut finalized_structs[i];

//     //     let old_strct = &structs[i];
//     //     let res = &resolved[i];
//     //     let fields = old_strct.1.iter().map(|x| {
//     //         (res.iter().enumerate().find(|y| y.1.name() == x.name).unwrap().0, x.name.clone())
//     //     }).map(|x| Field { tpe: UwUType::Struct(&finalized_structs[x.0]), name: x.1 }).collect::<Vec<_>>();
//     //     strct.fields = fields;
//     // }

//     println!("structs: {:?}", finalized_structs);

//     let mut instructions = vec![];

//     let mut to_compile = vec![];
//     let mut entryp = None;
//     for (file, decl, idx) in parsed.iter().enumerate().map(|x| x.1.1.iter().map(move |y| (x.1.0, y, x.0))).flatten() {
//         match decl {
//             Declaration::Function { name, args, return_type, block } => {
//                 let imports = &resolved_by_file_2[file];
//                 let items = (decl, imports);
//                 to_compile.push(items);
//                 let mut full_file_path = file.path.clone();
//                 full_file_path.push(file.name.clone());
//                 if name == &entrypoint.1 && entrypoint.0 == full_file_path {
//                     entryp = Some(items);
//                 }
//             }
//             _ => {}
//         }
//     }

//     let mut function_starts = HashMap::new();
//     let e = entryp.expect("main function not found");
//     let mut jumps_to_resolve = vec![];
//     jumps_to_resolve.extend(compile_function(e.0, &mut instructions, e.1));
//     // instructions.push(Instruction::HALT);
//     for (item, imports) in to_compile {
//         if item == e.0 {
//             continue;
//         }
//         function_starts.insert(match item {
//             Declaration::Function { name, args, return_type, block } => FunctionData { name: name.clone(), args: args.iter().map(|x| x.tpe.clone()).collect(), return_type: return_type.clone().unwrap_or("unit".to_string()), native: None },
//             _ => panic!()
//         }, instructions.len() as u64);

//         jumps_to_resolve.extend(compile_function(item, &mut instructions, imports));
//     }

//     for item in jumps_to_resolve {
//         println!("resolving jump to {:?} at {}", item.function, item.to_update);
//         let found = function_starts[item.function];
//         let existing = instructions[item.to_update];
//         match existing {
//             Instruction::CALL(_) => {
//                 instructions[item.to_update] = Instruction::CALL(found);
//             }
//             _ => panic!()
//         }
//     };

//     let finfo = finalized_structs.iter().map(|x| UwUType::Struct(x).as_field_info()).collect();

//     (instructions, finfo)
// }

// struct CompileStackFrame<'a> {
//     allow_outer_vars: bool,
//     data: Vec<(Option<String>, UwUType<'a>)>
// }

// struct FunctionCompileData<'a> {
//     stack: Vec<CompileStackFrame<'a>>,
//     // imports: &'a Vec<ResolvedImport<'a>>
// }

// impl<'a> FunctionCompileData<'a> {
//     fn cur(&self) -> &CompileStackFrame<'a> {
//         self.stack.last().unwrap()
//     }

//     fn cur_mut(&mut self) -> &mut CompileStackFrame<'a> {
//         self.stack.last_mut().unwrap()
//     }
// }

// #[derive(Clone, Copy)]
// struct ResolveableJump<'a> {
//     function: &'a FunctionData,
//     to_update: usize
// }

// fn compile_expr<'a>(expression: &Expression, data: &mut FunctionCompileData<'a>, out: &mut Vec<Instruction>, imports: &'a Vec<ResolvedImport>) -> (UwUType<'a>, Vec<ResolveableJump<'a>>) {
//     let return_type = match expression {
//         Expression::Literal(v) => match v {
//             crate::Literal::Int(v) => { out.push(Instruction::IMMEDIATE(*v)); (UwUType::Primitive(Primitive::I64), vec![]) }
//             crate::Literal::Float(v) => { out.push(Instruction::IMMEDIATE(unsafe { std::mem::transmute(*v) })); (UwUType::Primitive(Primitive::F64), vec![]) }
//             crate::Literal::Bool(v) => { out.push(Instruction::IMMEDIATE(if *v { 1 } else { 0 })); (UwUType::Primitive(Primitive::Bool), vec![]) }
//             crate::Literal::String(_) => todo!(),
//         },
//         Expression::Parenthesis(e) => compile_expr(e, data, out, imports),
//         Expression::BiOperation(left, op, right) => {
//             let lft = compile_expr(left, data, out, imports);
//             let rgt = compile_expr(right, data, out, imports);
//             if lft.0 != rgt.0 {
//                 panic!("left and right terms must have the same type");
//             }

//             let ins_res = match op {
//                 // i64, f64, bool, custom
//                 BiOp::Plus => [Some((Instruction::IADD, UwUType::Primitive(Primitive::I64))), Some((Instruction::FADD, UwUType::Primitive(Primitive::I64))), None, None],
//                 BiOp::Minus => [Some((Instruction::ISUB, UwUType::Primitive(Primitive::I64))), Some((Instruction::FSUB, UwUType::Primitive(Primitive::I64))), None, None],
//                 BiOp::Times => [Some((Instruction::IMUL, UwUType::Primitive(Primitive::I64))), Some((Instruction::FMUL, UwUType::Primitive(Primitive::I64))), None, None],
//                 BiOp::Divide => [Some((Instruction::IDIV, UwUType::Primitive(Primitive::I64))), Some((Instruction::FDIV, UwUType::Primitive(Primitive::I64))), None, None],
//                 BiOp::DoubleEquals => [Some((Instruction::CMP(Comparison::Eq), UwUType::Primitive(Primitive::Bool))), Some((Instruction::CMP(Comparison::Eq), UwUType::Primitive(Primitive::Bool))), Some((Instruction::CMP(Comparison::Eq), UwUType::Primitive(Primitive::Bool))), None],  // TODO
//                 BiOp::GreaterThan => [Some((Instruction::CMP(Comparison::IGr), UwUType::Primitive(Primitive::Bool))), Some((Instruction::CMP(Comparison::FGr), UwUType::Primitive(Primitive::Bool))), None, None],
//                 BiOp::GreatherThanEquals => [Some((Instruction::CMP(Comparison::IGrE), UwUType::Primitive(Primitive::Bool))), Some((Instruction::CMP(Comparison::FGrE), UwUType::Primitive(Primitive::Bool))), None, None],
//                 BiOp::LessThan => [Some((Instruction::CMP(Comparison::ILe), UwUType::Primitive(Primitive::Bool))), Some((Instruction::CMP(Comparison::FLe), UwUType::Primitive(Primitive::Bool))), None, None],
//                 BiOp::LessThanEquals => [Some((Instruction::CMP(Comparison::ILeE), UwUType::Primitive(Primitive::Bool))), Some((Instruction::CMP(Comparison::FLeE), UwUType::Primitive(Primitive::Bool))), None, None],
//             }[match lft.0 {
//                 UwUType::Primitive(Primitive::I64) => 0,
//                 UwUType::Primitive(Primitive::F64) => 1,
//                 UwUType::Primitive(Primitive::Bool) => 2,
//                 UwUType::Primitive(Primitive::Unit) => panic!("cannot perform operations on unit type"),
//                 UwUType::Struct(_) => 3,
//                 UwUType::Array(_) => panic!("no operations are supported on arrays"),
//             }];

//             match ins_res {
//                 Some((ins, res)) => {
//                     out.push(ins);
//                     data.stack.last_mut().unwrap().data.pop();
//                     data.stack.last_mut().unwrap().data.pop();
//                     let mut all = lft.1.clone();
//                     all.extend(rgt.1);
//                     (res, all)
//                 }
//                 None => panic!("unsupported operation")
//             }
//         }
//         Expression::FunctionInvocation { name, args } => {
//             let resolved = imports.iter().find(|x| &x.name() == name).expect("function not found");
//             let func = match resolved {
//                 ResolvedImport::Type(_) => panic!("cannot invoke '{}'", name),
//                 ResolvedImport::Function(v) => v,
//             };
            
//             // println!("imports: {:?}", imports);
//             // println!("return type: {}", func.return_type);
//             let return_type = imports.iter().find(|x| x.name() == func.return_type).unwrap().as_type();

//             let mut resolveable_jumps = vec![];
//             let mut addrs_to_copy = vec![];
//             let mut idx = 0;
//             let expected_idx = data.cur().data.len() + args.len();
//             for a in args {
//                 let (arg_type, jumps) = compile_expr(a, data, out, imports);
//                 addrs_to_copy.push((data.cur().data.len() - 1, arg_type));
//                 let exp = &func.args[idx];
//                 assert!(&arg_type.name() == exp, "invalid type for function argument (expected {}, got {})", exp, arg_type.name());
//                 resolveable_jumps.extend(jumps);
//                 idx += 1;
//             }

//             if expected_idx == data.cur().data.len() {
//                 for _ in 0..args.len() {
//                     data.cur_mut().data.pop();
//                 }
//             } else {
//                 for (item, tpe) in addrs_to_copy {
//                     out.push(Instruction::COPY { frame: 0, word: item as u32 });
//                 }
//             }

//             match func.native {
//                 Some(v) => {
//                     out.push(Instruction::NATIVE(v))
//                 }
//                 None => {
//                     resolveable_jumps.push(ResolveableJump { function: func, to_update: out.len() });
//                     out.push(Instruction::CALL(0));        
//                 }
//             }

//             (*return_type, resolveable_jumps)
//         }
//         Expression::Instantiation { name, args } => todo!(),
//         Expression::VarAccess(n) => {
//             let mut found = None;

//             'outer: for (frame_idx, frame) in data.stack.iter().rev().enumerate() {
//                 for (word_idx, item) in frame.data.iter().enumerate().rev() {
//                     match &item.0 {
//                         Some(name) => {
//                             if name == n {
//                                 found = Some((item, frame_idx as u32, word_idx as u32));
//                                 break 'outer;
//                             }
//                         }
//                         None => {}
//                     }
//                 }
//                 if !frame.allow_outer_vars {
//                     break;
//                 }
//             }

//             match found {
//                 Some((v, frame, word)) => {
//                     out.push(Instruction::COPY { frame, word });
//                     (v.1, vec![])
//                 }
//                 None => panic!("variable '{}' not found", n)
//             }
//         }
//     };
//     data.stack.last_mut().unwrap().data.push((None, return_type.0));
//     return_type
// }

// fn compile_block<'a>(block: &Vec<Statement>, data: &mut FunctionCompileData<'a>, out: &mut Vec<Instruction>, imports: &'a Vec<ResolvedImport>) -> Vec<ResolveableJump<'a>> {
//     /*
//     1. for each line...
//         1. if it's a var declaration, evaluate expr, infer type, and find spot on stack
//         2. if it's assignment, decrement refcount (if applicable) and set
//         3. if it's an expression, evaluate and keep track of stack space
//         4. if it's an if or while statement, create a new stack block and do stuff there (keep track of innermost loop exit addr)
//         5. if it's a break, jump to innermost loop exit addr
//         6. if it's return, jump back and figure out how to persist last stack value
//     */
//     let mut resolveable = vec![];

//     for item in block {
//         match item {
//             Statement::VariableDeclaration { mutable, name, value } => {
//                 let tpe = compile_expr(value, data, out, imports);
//                 data.stack.last_mut().unwrap().data.pop();
//                 // TODO: store mutability
//                 data.stack.last_mut().unwrap().data.push((Some(name.clone()), tpe.0));
//                 resolveable.extend(tpe.1)
//             }
//             Statement::Assignment(_, _) => {
//                 todo!()
//             },
//             Statement::Expression(e) => { resolveable.extend(compile_expr(e, data, out, imports).1); }
//             Statement::If { condition, block } => {
//                 let cond = compile_expr(condition, data, out, imports);
//                 resolveable.extend(cond.1);
//                 assert!(cond.0 == UwUType::Primitive(Primitive::Bool), "condition must return a boolean");
//                 let jump_ins_idx = out.len();
//                 out.push(Instruction::BRANCH(Comparison::Zero, 0));
//                 data.stack.last_mut().unwrap().data.pop();
//                 data.stack.push(CompileStackFrame { allow_outer_vars: true, data: vec![] });
//                 compile_block(block, data, out, imports);
//                 data.stack.pop();
//                 out[jump_ins_idx] = Instruction::BRANCH(Comparison::Zero, out.len() as u64);  // probable off-by-one
//             }
//             Statement::While { condition, block } => todo!(),
//             Statement::Break => todo!(),
//             Statement::Return(out) => todo!(),
//         }
//     };

//     resolveable
// }

// fn compile_function<'a>(func: &Declaration, out: &mut Vec<Instruction>, imports: &'a Vec<ResolvedImport>) -> Vec<ResolveableJump<'a>> {
//     match func {
//         Declaration::Function { name, args, return_type, block } => {
//             let mut data = FunctionCompileData { stack: vec![CompileStackFrame { allow_outer_vars: false, data: vec![] }] };
//             let res = compile_block(block, &mut data, out, imports);

//             out.push(Instruction::RET);

//             res
//         }
//         _ => panic!()
//     }
// }
