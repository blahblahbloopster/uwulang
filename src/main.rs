use std::{fs::File, io::Read, hash::Hash, ops::Range, fmt::Debug};

use newcompiler::{compile, UwUFi};

use crate::{runtime::VM, parser::{UwUInpFile, uwu_parser, lexer}};

// use compiler::{compile, UwUFile};

// use crate::bytecode::VM;
mod bytecode;
mod compiler;
mod stdlib;
mod newcompiler;
mod runtime;
mod serialization;
mod parser;

fn main() {
    let mut inp = String::new();
    File::open("example.uwu").unwrap().read_to_string(&mut inp).unwrap();

    // let (program, types) = compile(vec![UwUFile { content: inp, path: vec![], name: "main".to_string() }], (vec!["main".to_string()], "main".to_string()));
    // println!("program: {:?}", program);
    // println!();
    // println!();
    // let mut vm = VM::new(program, types);

    // loop {
    //     vm.tick();
    // }

    let inp_file = UwUInpFile { content: inp };

    let files = vec![UwUFi { fqn: vec!["main".to_string()], content: uwu_parser::file(lexer::tokenize(inp_file.content.as_str(), &inp_file).unwrap().as_slice()).unwrap().content }];

    // println!("files: {:?}", files);

    let (types, program) = compile(&files, vec!["main".to_string(), "main".to_string()]);

    // println!("types: {:?}", types);
    // println!("program:\n{:?}", program);
    println!("{} instructions", program.len());

    let mut vm = VM::new(program, types);
    loop {
        vm.tick();
    }
}
