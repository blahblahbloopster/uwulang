use std::{fs::File, io::Read, hash::Hash};

// use compiler::{compile, UwUFile};

// use crate::bytecode::VM;
mod bytecode;
mod compiler;
mod stdlib;
mod newcompiler;
mod runtime;

// TOKENS
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Keyword {
    Fun, Struct, Return, If, While, Break, Import, New, Let, Var, Package
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Literal<'a> {
    Int(i64), Float(f64), Bool(bool), String(&'a str)
}

impl<'a> Hash for Literal<'a> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Literal::Int(v) => v.hash(state),
            Literal::Float(v) => unsafe { std::mem::transmute::<_, u64>(v) }.hash(state),
            Literal::Bool(v) => v.hash(state),
            Literal::String(v) => v.hash(state),
        }
    }
}

impl<'a> Eq for Literal<'a> {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Symbol {
    Dot, Plus, Minus, Times, Divide, Equals, OpenBrace, CloseBrace, OpenParen, CloseParen, Semicolon, Colon, Comma, GreaterThan, LessThan
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Token<'a> {
    Keyword(Keyword),
    Literal(Literal<'a>),
    Symbol(Symbol),
    Identifier(&'a str)
}

// AST
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum BiOp {
    Plus, Minus, Times, Divide, DoubleEquals, GreaterThan, GreatherThanEquals, LessThan, LessThanEquals
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Expression<'a> {
    Literal(Literal<'a>),
    Parenthesis(Box<Expression<'a>>),
    BiOperation(Box<Expression<'a>>, BiOp, Box<Expression<'a>>),
    FunctionInvocation { name: String, args: Vec<Expression<'a>> },
    Instantiation { name: String, args: Vec<Expression<'a>> },
    VarAccess(String)
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Statement<'a> {
    VariableDeclaration { mutable: bool, name: String, value: Expression<'a> },
    Assignment(String, Expression<'a>),
    Expression(Expression<'a>),
    If { condition: Expression<'a>, block: Vec<Statement<'a>> },
    While { condition: Expression<'a>, block: Vec<Statement<'a>> },
    Break,
    Return(Option<Expression<'a>>)
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct NameTypePair {
    name: String,
    tpe: String
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Declaration<'a> {
    Import { path: Vec<String>, item: String },
    Function { name: String, args: Vec<NameTypePair>, return_type: Option<String>, block: Vec<Statement<'a>> },
    Struct { name: String, fields: Vec<NameTypePair> }
}

peg::parser!{
    grammar lexer() for str {
        rule _ = [' ' | '\n']*

        // LITERALS
        rule string_literal() -> Literal<'input>
        = "\"" chars:$([^ '"']+) "\"" { Literal::String(chars) }

        rule numbers() -> &'input str
        = chars:$(['0'..='9']+) { chars }

        rule decimal() -> &'input str
        = numbers() / $(numbers() "." numbers())

        rule scientific() -> &'input str
        = decimal() / $(decimal() "e" decimal())

        rule int() -> Literal<'input>
        = v:numbers() { Literal::Int(v.parse().unwrap()) }

        rule float() -> Literal<'input>
        = v:scientific() { Literal::Float(v.parse().unwrap()) }

        rule true_l() -> Literal<'input>
        = "twue" { Literal::Bool(true) }

        rule false_l() -> Literal<'input>
        = "fawse" { Literal::Bool(false) }

        rule bool() -> Literal<'input>
        = true_l() / false_l()

        rule literal() -> Literal<'input>
        = string_literal() / int() / float() / bool()

        rule lit() -> Token<'input>
        = l:literal() { Token::Literal(l) }


        // KEYWORDS
        rule fun() -> Keyword
        = "fuwn" { Keyword::Fun }

        rule struct_k() -> Keyword
        = "stwuct" { Keyword::Struct }

        rule return_k() -> Keyword
        = "wetuwn" { Keyword::Return }

        rule if_k() -> Keyword
        = "if" { Keyword::If }

        rule while_k() -> Keyword
        = "whiwe" { Keyword::While }

        rule break_k() -> Keyword
        = "bweak" { Keyword::Break }

        rule import() -> Keyword
        = "impowt" { Keyword::Import }

        rule new() -> Keyword
        = "new" { Keyword::New }

        rule let_k() -> Keyword
        = "wet" { Keyword::Let }

        rule var() -> Keyword
        = "vaw" { Keyword::Var }

        rule package() -> Keyword
        = "package" { Keyword::Package }

        rule keyword() -> Keyword
        = fun() / struct_k() / return_k() / if_k() / while_k() / break_k() / import() / new() / let_k() / var() / package()

        rule keyw() -> Token<'input>
        = k:keyword() { Token::Keyword(k) }

        // SYMBOLS
        // Dot, Plus, Minus, Times, Divide, Equals, OpenBrace, CloseBrace, 
        // OpenParen, CloseParen, Semicolon, Colon, Comma, GreaterThan, LessThan
        rule dot() -> Symbol = "." { Symbol::Dot }
        rule plus() -> Symbol = "+" { Symbol::Plus }
        rule minus() -> Symbol = "-" { Symbol::Minus }
        rule times() -> Symbol = "*" { Symbol::Times }
        rule divide() -> Symbol = "/" { Symbol::Divide }
        rule equals() -> Symbol = "=" { Symbol::Equals }
        rule openbrace() -> Symbol = "{" { Symbol::OpenBrace }
        rule closebrace() -> Symbol = "}" { Symbol::CloseBrace }
        rule openparen() -> Symbol = "(" { Symbol::OpenParen }
        rule closeparen() -> Symbol = ")" { Symbol::CloseParen }
        rule semicolon() -> Symbol = ";" { Symbol::Semicolon }
        rule colon() -> Symbol = ":" { Symbol::Colon }
        rule comma() -> Symbol = "," { Symbol::Comma }
        rule greaterthan() -> Symbol = ">" { Symbol::GreaterThan }
        rule lessthan() -> Symbol = "<" { Symbol::LessThan }

        rule symbol() -> Symbol
        = dot() / plus() / minus() / times() / divide() / equals() / openbrace() / closebrace() / openparen() / closeparen() / semicolon() / colon() / comma() / greaterthan() / lessthan()

        rule sym() -> Token<'input>
        = s:symbol() { Token::Symbol(s) }

        // IDENTIFIERS
        rule identifier() -> Token<'input>
        = v:$(['a'..='z' | 'A'..='Z'] (['a'..='z' | 'A'..='Z' | '_' | '0'..='9'])*) { Token::Identifier(v) }

        // TOKENS
        rule token() -> Token<'input>
        = lit() / keyw() / sym() / identifier()

        rule tok() -> Token<'input>
        = _ t:token() _ { t }
    
        pub rule tokenize() -> Vec<Token<'input>>
        = tok()+
    }
}

pub struct PackageDecl {
    pub fqn: Vec<String>
}

pub struct ParsedFile<'a> {
    pub package: PackageDecl,
    pub content: Vec<Declaration<'a>>
}

peg::parser!{
    grammar uwu_parser<'a>() for [Token<'a>] {
        rule package_decl() -> PackageDecl
        = [Token::Keyword(Keyword::Package)] name:([Token::Identifier(_)] ** [Token::Symbol(Symbol::Dot)]) { PackageDecl { fqn: name.iter().map(|x| match x { Token::Identifier(v) => v.to_string(), _ => panic!() }).collect() } }

        rule name_type_pair() -> NameTypePair
        = [Token::Identifier(name)] [Token::Identifier(tpe)] { NameTypePair { name: name.to_string(), tpe: tpe.to_string() } }

        rule braceblock() -> Vec<Statement<'a>>
        = [Token::Symbol(Symbol::OpenBrace)] statements:statement()* [Token::Symbol(Symbol::CloseBrace)] { statements }


        rule import() -> Declaration<'a>
        = [Token::Keyword(Keyword::Import)] paths:([Token::Identifier(_)] ** [Token::Symbol(Symbol::Dot)]) [Token::Symbol(Symbol::Colon)][Token::Symbol(Symbol::Colon)] [Token::Identifier(name)] { Declaration::Import { path: paths.iter().map(|x| match x { Token::Identifier(v) => v.to_string(), _ => panic!() }).collect(), item: name.to_string() } }

        rule function_ret() -> Declaration<'a>
        = [Token::Keyword(Keyword::Fun)] [Token::Identifier(name)] [Token::Symbol(Symbol::OpenParen)] args:(name_type_pair() ** [Token::Symbol(Symbol::Comma)]) [Token::Symbol(Symbol::CloseParen)] [Token::Symbol(Symbol::Colon)] [Token::Identifier(return_type)] block:braceblock() { Declaration::Function { name: name.to_string(), args, return_type: Some(return_type.to_string()), block } }

        rule function_no_ret() -> Declaration<'a>
        = [Token::Keyword(Keyword::Fun)] [Token::Identifier(name)] [Token::Symbol(Symbol::OpenParen)] args:(name_type_pair() ** [Token::Symbol(Symbol::Comma)]) [Token::Symbol(Symbol::CloseParen)] block:braceblock() { Declaration::Function { name: name.to_string(), args, return_type: None, block } }

        rule function() -> Declaration<'a>
        = function_ret() / function_no_ret()

        rule strct() -> Declaration<'a>
        = [Token::Keyword(Keyword::Struct)] [Token::Identifier(name)] [Token::Symbol(Symbol::OpenBrace)] fields:(name_type_pair() ** [Token::Symbol(Symbol::Comma)]) [Token::Symbol(Symbol::CloseBrace)] { Declaration::Struct { name: name.to_string(), fields } }

        rule declaration() -> Declaration<'a>
        = import() / function() / strct()


        rule parens() -> Expression<'a>
        = [Token::Symbol(Symbol::OpenParen)] e:expr() [Token::Symbol(Symbol::CloseParen)] { e }

        // TODO incorporate
        rule operation() -> Expression<'a>
        = precedence! {
            x:(@) [Token::Symbol(Symbol::GreaterThan)] y:@ { Expression::BiOperation(Box::new(x), BiOp::GreaterThan, Box::new(y)) }
            x:(@) [Token::Symbol(Symbol::GreaterThan)] [Token::Symbol(Symbol::Equals)] y:@ { Expression::BiOperation(Box::new(x), BiOp::GreatherThanEquals, Box::new(y)) }
            x:(@) [Token::Symbol(Symbol::LessThan)] y:@ { Expression::BiOperation(Box::new(x), BiOp::LessThan, Box::new(y)) }
            x:(@) [Token::Symbol(Symbol::LessThan)] [Token::Symbol(Symbol::Equals)] y:@ { Expression::BiOperation(Box::new(x), BiOp::LessThanEquals, Box::new(y)) }
            x:(@) [Token::Symbol(Symbol::Equals)] [Token::Symbol(Symbol::Equals)] y:@ { Expression::BiOperation(Box::new(x), BiOp::DoubleEquals, Box::new(y)) }
            --
            x:(@) [Token::Symbol(Symbol::Plus)] y:@ { Expression::BiOperation(Box::new(x), BiOp::Plus, Box::new(y)) }
            x:(@) [Token::Symbol(Symbol::Minus)] y:@ { Expression::BiOperation(Box::new(x), BiOp::Minus, Box::new(y)) }
            --
            x:(@) [Token::Symbol(Symbol::Times)] y:@ { Expression::BiOperation(Box::new(x), BiOp::Times, Box::new(y)) }
            x:(@) [Token::Symbol(Symbol::Divide)] y:@ { Expression::BiOperation(Box::new(x), BiOp::Divide, Box::new(y)) }
            --
            [Token::Symbol(Symbol::OpenParen)] v:operation() [Token::Symbol(Symbol::CloseParen)] { v }
            v:expr() { v }
        }

        rule function_inv() -> Expression<'a>
        = [Token::Identifier(name)] [Token::Symbol(Symbol::OpenParen)] args:(expr() ** [Token::Symbol(Symbol::Comma)]) [Token::Symbol(Symbol::CloseParen)] { Expression::FunctionInvocation { name: name.to_string(), args } }

        rule instantiation() -> Expression<'a>
        = [Token::Keyword(Keyword::New)] [Token::Identifier(name)] [Token::Symbol(Symbol::OpenParen)] args:(expr() ** [Token::Symbol(Symbol::Comma)]) [Token::Symbol(Symbol::CloseParen)] { Expression::Instantiation { name: name.to_string(), args } }

        rule var_access() -> Expression<'a>
        = [Token::Identifier(name)] { Expression::VarAccess(name.to_string()) }

        rule literal() -> Expression<'a>
        = [Token::Literal(v)] { Expression::Literal(v) }

        rule expr() -> Expression<'a>
        = parens() / instantiation() / function_inv() / var_access() / literal()

        rule var_declaration_let() -> Statement<'a>
        = [Token::Keyword(Keyword::Let)] [Token::Identifier(name)] [Token::Symbol(Symbol::Equals)] value:expr() [Token::Symbol(Symbol::Semicolon)] { Statement::VariableDeclaration { mutable: false, name: name.to_string(), value } }

        rule var_declaration_var() -> Statement<'a>
        = [Token::Keyword(Keyword::Var)] [Token::Identifier(name)] [Token::Symbol(Symbol::Equals)] value:expr() [Token::Symbol(Symbol::Semicolon)] { Statement::VariableDeclaration { mutable: true, name: name.to_string(), value } }

        rule var_declaration() -> Statement<'a>
        = var_declaration_let() / var_declaration_var()

        rule assignment() -> Statement<'a>
        = [Token::Identifier(name)] [Token::Symbol(Symbol::Equals)] value:expr() [Token::Symbol(Symbol::Semicolon)] { Statement::Assignment(name.to_string(), value) }

        rule expression_statement() -> Statement<'a>
        = e:expr() [Token::Symbol(Symbol::Semicolon)] { Statement::Expression(e) }

        rule if_statement() -> Statement<'a>
        = [Token::Keyword(Keyword::If)] condition:expr() block:braceblock() { Statement::If { condition, block } }

        rule while_loop() -> Statement<'a>
        = [Token::Keyword(Keyword::While)] condition:expr() block:braceblock() { Statement::While { condition, block } }

        rule break_statement() -> Statement<'a>
        = [Token::Keyword(Keyword::Break)] [Token::Symbol(Symbol::Semicolon)] { Statement::Break }

        rule return_statement() -> Statement<'a>
        = [Token::Keyword(Keyword::Return)] e:expr()? [Token::Symbol(Symbol::Semicolon)] { Statement::Return(e) }

        rule statement() -> Statement<'a>
        = var_declaration() / assignment() / expression_statement() / if_statement() / while_loop() / break_statement() / return_statement()

        rule decls() -> Vec<Declaration<'a>>
        = declaration()+

        pub rule file() -> ParsedFile<'a>
        = package:package_decl() content:decls() { ParsedFile { package, content } }
    }
}

fn main() {
    // let mut inp = String::new();
    // File::open("example.uwu").unwrap().read_to_string(&mut inp).unwrap();

    // let (program, types) = compile(vec![UwUFile { content: inp, path: vec![], name: "main".to_string() }], (vec!["main".to_string()], "main".to_string()));
    // println!("program: {:?}", program);
    // println!();
    // println!();
    // let mut vm = VM::new(program, types);

    // loop {
    //     vm.tick();
    // }
}
