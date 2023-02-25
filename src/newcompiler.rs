/*

 1. Resolve types
  1. Go through all files
  2. Instantiate all structs with no fields
  3. Resolve struct types
  4. Resolve function arg and return types

*/

use std::collections::HashMap;

use crate::{Declaration, ParsedFile, NameTypePair, stdlib::{NativeType, NativeFunction, PRIMITIVE_TYPES}};

#[derive(Clone, Debug, PartialEq, Hash)]
struct UwUStrc<'b> {
    fqn: Vec<String>,
    fields: Vec<(String, UwUTy<'b>)>
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Primitive {
    Unit, I64, F64, Bool
}

#[derive(Clone, Debug, PartialEq, Hash)]
pub enum UwUTy<'b> {
    Struct(&'b UwUStrc<'b>),
    Native(&'b NativeType),
    Array(Box<UwUTy<'b>>)
}

struct IntermediateStruct<'a, 'b> {
    fqn: Vec<String>,
    fields: Vec<(String, Importable<'a, 'b>)>
}

#[derive(PartialEq, Hash, Eq)]
enum NativeObj<'b> {
    PrimitiveType(Primitive),
    Function(&'b NativeFunction<'b>)
}

#[derive(PartialEq, Hash, Eq)]
enum Importable<'a, 'b> {
    Defined(&'a Declaration<'a>),
    Native(&'b NativeObj<'b>)
}

#[derive(PartialEq, Hash, Eq)]
struct DeclData<'a, 'b> {
    original: Importable<'a, 'b>,
    fqn: Vec<String>
}

#[derive(PartialEq, Hash, Eq)]
struct Imp<'a, 'b> {
    fqn: Vec<String>,
    resolved: Option<(String, &'a DeclData<'a, 'b>)>,
    name: String
}

#[derive(PartialEq, Hash, Eq)]
struct FileData<'a, 'b> {
    decls: Vec<DeclData<'a, 'b>>,
    imports: Vec<Imp<'a, 'b>>,
    fqn: Vec<String>
}

fn collect_resolve<'a, 'b>(files: &'a Vec<ParsedFile<'a>>) -> Vec<FileData<'a, 'b>> {
    let mut declared = vec![];
    for f in files {
        let mut in_file = vec![];
        let mut imports = vec![];
        for declaration in &f.content {
            match declaration {
                Declaration::Function { name, args, return_type, block } => {
                    in_file.push(DeclData { original: Importable::Defined(&declaration), fqn: f.package.fqn.plus(name) })
                }
                Declaration::Struct { name, fields } => {
                    in_file.push(DeclData { original: Importable::Defined(&declaration), fqn: f.package.fqn.plus(name) })
                }
                Declaration::Import { path, item } => {
                    imports.push(Imp { fqn: path.plus(item.clone()), resolved: None, name: item.clone() })
                }
            }
        }

        declared.push(FileData { decls: in_file, imports, fqn: f.package.fqn.clone() });
        // declared_data.push(in_file);
        // declared_imports.push(imports);
    }

    // the set of all importable items, including non-imported-by-default stdlib types
    let importable = declared.iter().map(|x| &x.decls).flatten().collect::<Vec<_>>();  // TODO: add stdlib stuff here


    // resolve all imports
    for decl in &declared {
        for imp in &decl.imports {
            let found = importable.iter().find(|x| x.fqn == imp.fqn).expect("failed to resolve import");
            unsafe {
                // this is fine
                let ptr = imp as *const Imp as *mut Imp;
                (*ptr).resolved = Some((imp.name.clone(), found));
            }
        }
    }

    declared
}

struct TypeResolveInfo<'a, 'b> {
    imports: &'a Vec<Imp<'a, 'b>>,
    structs: &'b HashMap<&'a Declaration<'a>, (&'a FileData<'a, 'b>, UwUStrc<'b>)>
}

fn resolve_type<'a, 'b>(type_name: String, info: &TypeResolveInfo<'a, 'b>) -> UwUTy<'b> {
    let resolved = &info.imports.iter().find(|imp| imp.name == type_name).expect("type not found").resolved;
    let res = match resolved {
        Some(v) => v,
        None => panic!(),
    };

    match res.1.original {
        Importable::Defined(v) => UwUTy::Struct(&info.structs[v].1),
        Importable::Native(v) => UwUTy::Native(match v {
            NativeObj::PrimitiveType(p) => PRIMITIVE_TYPES[p.clone() as usize],
            NativeObj::Function(_) => panic!(),
        })
    }
}

fn generate_structs<'a, 'b>(files: &'a Vec<FileData<'a, 'b>>) -> (Vec<UwUStrc<'b>>, HashMap<&'a FileData<'a, 'b>, TypeResolveInfo<'a, 'b>>) {
    let mut structs = HashMap::new();
    let mut data = HashMap::new();

    for file in files {
        for decl in &file.decls {
            match decl.original {
                Importable::Defined(v) => {
                    match v {
                        Declaration::Struct { name, fields } => {
                            structs.insert(v, (file, UwUStrc {
                                fqn: file.fqn.plus(name),
                                fields: vec![]
                            }));
                        }
                        _ => {}
                    }
                }
                Importable::Native(_) => panic!("unreachable state, native object cannot be defined in a file")
            }
        }
    }

    for file in files {
        data.insert(file, TypeResolveInfo { imports: &file.imports, structs: &structs });
    }

    for (decl, (file, strct)) in &structs {
        match decl {
            Declaration::Struct { name, fields } => {
                let resolved_fields = fields.iter().map(|pair| {
                    // let resolved = &file.imports.iter().find(|imp| imp.name == pair.tpe).expect("type not found").resolved;
                    // let res = match resolved {
                    //     Some(v) => v,
                    //     None => panic!(),
                    // };

                    // let field_type = match res.1.original {
                    //     Importable::Defined(v) => UwUTy::Struct(&structs[v].1),
                    //     Importable::Native(v) => UwUTy::Native(match v {
                    //         NativeObj::PrimitiveType(p) => PRIMITIVE_TYPES[p.clone() as usize],
                    //         NativeObj::Function(_) => panic!(),
                    //     })
                    // };
                    let res_info = &data[file];
                    let field_type = resolve_type(pair.name.clone(), res_info);

                    (pair.name.clone(), field_type)
                }).collect::<Vec<_>>();

                // nothing horrible is going on here
                unsafe { (*(strct as *const UwUStrc as *mut UwUStrc)).fields = resolved_fields };
            }
            _ => {}
        }
    }

    let strcts = structs.values().map(|x| x.1).collect();
    
    (strcts, data)
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
