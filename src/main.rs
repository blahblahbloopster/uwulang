use std::{fs::{File, self}, io::Read, path::Path};

use newcompiler::compile;

use crate::{runtime::VM, parser::UwUInpFile};

mod stdlib;
mod newcompiler;
mod runtime;
mod serialization;
mod parser;

fn main() {
    let files = fs::read_dir("uwu").expect("uwu directory not found, is your working directory wrong?");
    let mut inp_files = vec![];
    for item in files {
        let mut inp = String::new();
        File::open(item.unwrap().path()).unwrap().read_to_string(&mut inp).unwrap();
    
        inp_files.push(UwUInpFile { content: inp });
    }

    let (types, program) = compile(&mut inp_files, vec!["main".to_string(), "main".to_string()]);

    // println!("types: {:?}", types);
    // println!("program:\n{:?}", program);
    println!("{} instructions", program.len());

    let mut vm = VM::new(program, types);
    loop {
        vm.tick();
    }
}
