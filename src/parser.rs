use std::fmt::Debug;
use std::hash::Hash;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Loc<'a> {
    file: &'a UwUInpFile,
    left: usize, right: usize
}

impl<'a> Loc<'a> {
    pub fn new(file: &'a UwUInpFile, left: usize, right: usize) -> Loc<'a> {
        Loc { file, left, right }
    }

    pub fn to(&self, other: &Loc<'a>) -> Loc<'a> {
        Loc { file: self.file, left: self.left, right: other.right }
    }
}

// TOKENS
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Keyword {
    Fun, Struct, Return, If, While, Break, Import, New, Let, Var, Package
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Literal<'a> {
    Int(i64), Float(f64), Bool(bool), String(&'a str)
}

#[derive(Debug, Clone, PartialEq, Hash, Eq)]
pub enum Type<'a> {
    Simple(String, Loc<'a>),
    Array(Box<Type<'a>>, Loc<'a>)
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
    Dot, Plus, Minus, Times, Divide, Equals, Percent, Bang,
    OpenBrace, CloseBrace, OpenParen, CloseParen, OpenBracket, CloseBracket,
    Semicolon, Colon, Comma, GreaterThan, LessThan
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Token<'a> {
    Keyword(Keyword, Loc<'a>),
    Literal(Literal<'a>, Loc<'a>),
    Symbol(Symbol, Loc<'a>),
    Identifier(&'a str, Loc<'a>)
}

// AST
#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum BiOp {
    Plus, Minus, Times, Divide, Mod, DoubleEquals, NotEquals, GreaterThan, GreatherThanEquals, LessThan, LessThanEquals
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Expression<'a> {
    Literal(Literal<'a>, Loc<'a>),
    Parenthesis(Box<Expression<'a>>, Loc<'a>),
    BiOperation(Box<Expression<'a>>, BiOp, Box<Expression<'a>>, Loc<'a>),
    FunctionInvocation { name: String, args: Vec<Expression<'a>>, loc: Loc<'a> },
    Instantiation { name: String, args: Vec<Expression<'a>>, loc: Loc<'a> },
    VarAccess(String, Loc<'a>),
    PropertyAccess(Box<Expression<'a>>, String, Loc<'a>),
    ArrayCreation { typename: String, degree: usize, num: Box<Expression<'a>>, loc: Loc<'a> },
    ArrayAccess { arr: Box<Expression<'a>>, idx: Box<Expression<'a>>, loc: Loc<'a> },
    MethodInvocation { left: Box<Expression<'a>>, name: String, args: Vec<Expression<'a>>, loc: Loc<'a> }
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Statement<'a> {
    VariableDeclaration { mutable: bool, name: String, value: Expression<'a>, loc: Loc<'a> },
    Assignment(String, Expression<'a>, Loc<'a>),
    PropertySet(Expression<'a>, String, Expression<'a>, Loc<'a>),
    ArraySet { arr: Expression<'a>, indexes: Vec<Expression<'a>>, value: Expression<'a>, loc: Loc<'a> },
    Expression(Expression<'a>, Loc<'a>),
    If { condition: Expression<'a>, block: Vec<Statement<'a>>, loc: Loc<'a> },
    While { condition: Expression<'a>, block: Vec<Statement<'a>>, loc: Loc<'a> },
    Break(Loc<'a>),
    Return(Option<Expression<'a>>, Loc<'a>)
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub struct NameTypePair<'a> {
    pub name: (String, Loc<'a>),
    pub tpe: Type<'a>,
}

#[derive(Clone, Debug, PartialEq, Hash, Eq)]
pub enum Declaration<'a> {
    Import { path: Vec<String>, item: String, loc: Loc<'a> },
    Function { name: String, args: Vec<NameTypePair<'a>>, return_type: Option<Type<'a>>, block: Vec<Statement<'a>>, loc: Loc<'a>, receiver: Option<Type<'a>> },
    Struct { name: String, fields: Vec<NameTypePair<'a>>, loc: Loc<'a> }
}

impl<'a> Declaration<'a> {
    pub fn loc(&self) -> Loc<'a> {
        *match self {
            Declaration::Import { path, item, loc } => loc,
            Declaration::Function { name, args, return_type, block, loc, receiver } => loc,
            Declaration::Struct { name, fields, loc } => loc,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct UwUInpFile {
    pub content: String,
    pub fqn: Vec<String>
}

impl Debug for UwUInpFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("UwUInpFile").finish()
    }
}

peg::parser!{
    pub grammar lexer(file: &'input UwUInpFile) for str {
        rule ___ = [' ' | '\n']*
        rule __ = "//" [^'\n']*
        rule _ = ___ __? ___

        // LITERALS
        rule string_literal() -> Literal<'input>
        = "\"" chars:$([^ '"']*) "\"" { Literal::String(chars) }

        rule char_literal() -> Literal<'input>
        = "'" c:[^ '\''] "'" { Literal::Int(c as i64) }

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
        = string_literal() / int() / float() / bool() / char_literal()

        rule lit() -> Token<'input>
        = le:position!() l:literal() ri:position!() { Token::Literal(l, Loc::new(file, le, ri)) }


        // SYMBOLS
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
        rule openbracket() -> Symbol = "[" { Symbol::OpenBracket }
        rule closebracket() -> Symbol = "]" { Symbol::CloseBracket }
        rule semicolon() -> Symbol = ";" { Symbol::Semicolon }
        rule colon() -> Symbol = ":" { Symbol::Colon }
        rule comma() -> Symbol = "," { Symbol::Comma }
        rule greaterthan() -> Symbol = ">" { Symbol::GreaterThan }
        rule lessthan() -> Symbol = "<" { Symbol::LessThan }
        rule percent() -> Symbol = "%" { Symbol::Percent }
        rule bang() -> Symbol = "!" { Symbol::Bang }

        rule symbol() -> Symbol
        = dot() / plus() / minus() / times() / divide() / equals() / openbrace() / closebrace() / openparen() / closeparen() / openbracket() / closebracket() / semicolon() / colon() / comma() / greaterthan() / lessthan() / percent() / bang()

        rule sym() -> Token<'input>
        = le:position!() s:symbol() ri:position!() { Token::Symbol(s, Loc::new(file, le, ri)) }

        // IDENTIFIERS
        rule identifier() -> Token<'input>
        = le:position!() v:$(['a'..='z' | 'A'..='Z'] (['a'..='z' | 'A'..='Z' | '_' | '0'..='9'])*) ri:position!() {
            match v {
                "fuwn" => Token::Keyword(Keyword::Fun, Loc::new(file, le, ri)),
                "stwuct" => Token::Keyword(Keyword::Struct, Loc::new(file, le, ri)),
                "wetuwn" => Token::Keyword(Keyword::Return, Loc::new(file, le, ri)),
                "if" => Token::Keyword(Keyword::If, Loc::new(file, le, ri)),
                "whiwe" => Token::Keyword(Keyword::While, Loc::new(file, le, ri)),
                "bweak" => Token::Keyword(Keyword::Break, Loc::new(file, le, ri)),
                "impowt" => Token::Keyword(Keyword::Import, Loc::new(file, le, ri)),
                "new" => Token::Keyword(Keyword::New, Loc::new(file, le, ri)),
                "wet" => Token::Keyword(Keyword::Let, Loc::new(file, le, ri)),
                "vaw" => Token::Keyword(Keyword::Var, Loc::new(file, le, ri)),
                "package" => Token::Keyword(Keyword::Package, Loc::new(file, le, ri)),
                _ => Token::Identifier(v, Loc::new(file, le, ri))
            }
        }

        // TOKENS
        rule token() -> Token<'input>
        = lit() / sym() / identifier()

        rule tok() -> Token<'input>
        = _ t:token() _ { t }
    
        pub rule tokenize() -> Vec<Token<'input>>
        = tok()+
    }
}

pub struct PackageDecl<'a> {
    pub fqn: Vec<String>,
    pub loc: Loc<'a>
}

pub struct ParsedFile<'a> {
    pub package: PackageDecl<'a>,
    pub content: Vec<Declaration<'a>>
}

impl<'a> Expression<'a> {
    pub fn loc(&self) -> Loc<'a> {
        *match self {
            Expression::Literal(_, l) => l,
            Expression::Parenthesis(_, l) => l,
            Expression::BiOperation(_, _, _, l) => l,
            Expression::FunctionInvocation { name, args, loc } => loc,
            Expression::Instantiation { name, args, loc } => loc,
            Expression::VarAccess(_, l) => l,
            Expression::PropertyAccess(_, _, l) => l,
            Expression::ArrayCreation { typename, degree, num, loc } => loc,
            Expression::ArrayAccess { arr, idx, loc } => loc,
            Expression::MethodInvocation { left, name, args, loc } => loc
        }
    }
}

peg::parser!{
    pub grammar uwu_parser<'a>() for [Token<'a>] {
        rule package_decl() -> PackageDecl<'a>
        = [Token::Keyword(Keyword::Package, left)] name:([Token::Identifier(_, _)] ** [Token::Symbol(Symbol::Dot, _)]) [Token::Symbol(Symbol::Semicolon, right)] { PackageDecl { fqn: name.iter().map(|x| match x { Token::Identifier(v, _) => v.to_string(), _ => panic!() }).collect(), loc: left.to(&right) } }

        rule tpe() -> Type<'a>
        = precedence!{
            x:(@) [Token::Symbol(Symbol::OpenBracket, left)] [Token::Symbol(Symbol::CloseBracket, right)] { Type::Array(Box::new(x), left.to(&right)) }
            --
            x:[Token::Identifier(name, t)] { Type::Simple(name.to_string(), t) }
        }

        rule name_type_pair() -> NameTypePair<'a>
        = [Token::Identifier(name, left)] [Token::Symbol(Symbol::Colon, _)] t:tpe() { NameTypePair { name: (name.to_string(), left), tpe: t } }

        rule braceblock() -> (Vec<Statement<'a>>, Loc<'a>)
        = [Token::Symbol(Symbol::OpenBrace, left)] statements:statement()* [Token::Symbol(Symbol::CloseBrace, right)] { (statements, left.to(&right)) }

        rule import() -> Vec<Declaration<'a>>
        = [Token::Keyword(Keyword::Import, left)] paths:([Token::Identifier(_, _)] ** [Token::Symbol(Symbol::Dot, _)]) [Token::Symbol(Symbol::Colon, _)][Token::Symbol(Symbol::Colon, _)] [Token::Identifier(name, _)] [Token::Symbol(Symbol::Semicolon, right)] { vec![Declaration::Import { path: paths.iter().map(|x| match x { Token::Identifier(v, _) => v.to_string(), _ => panic!() }).collect(), item: name.to_string(), loc: left.to(&right) }] }

        rule ret_none() -> Option<Type<'a>>
        = { None }

        rule ret_some() -> Option<Type<'a>>
        = [Token::Symbol(Symbol::Colon, _)] t:tpe() { Some(t) }

        rule ret() -> Option<Type<'a>>
        = ret_some() / ret_none()

        // rule receiver_none() -> Option<Type<'a>>
        // = { None }

        // rule receiver_some() -> Option<Type<'a>>
        // = t:tpe() [Token::Symbol(Symbol::Dot, _)] { Some(t) }

        // rule receiver() -> Option<Type<'a>>
        // = receiver_some() / receiver_none()

        rule function() -> Vec<Declaration<'a>>
        = [Token::Keyword(Keyword::Fun, left)] [Token::Identifier(name, _)] [Token::Symbol(Symbol::OpenParen, _)] args:(name_type_pair() ** [Token::Symbol(Symbol::Comma, _)]) [Token::Symbol(Symbol::CloseParen, _)] return_type: ret() block:braceblock() right:position!() { vec![Declaration::Function { name: name.to_string(), args, return_type, block: block.0, loc: left.to(&Loc { file: left.file, left: left.left, right }), receiver: None }] }

        rule method(n: String) -> Declaration<'a>
        = [Token::Keyword(Keyword::Fun, left)] [Token::Identifier(name, _)] [Token::Symbol(Symbol::OpenParen, _)] args:(name_type_pair() ** [Token::Symbol(Symbol::Comma, _)]) [Token::Symbol(Symbol::CloseParen, _)] return_type: ret() block:braceblock() right:position!() { Declaration::Function { name: name.to_string(), args, return_type, block: block.0, loc: left.to(&Loc { file: left.file, left: left.left, right }), receiver: Some(Type::Simple(n, left)) } }

        rule strct() -> Vec<Declaration<'a>>
        = [Token::Keyword(Keyword::Struct, left)] [Token::Identifier(name, _)] [Token::Symbol(Symbol::OpenBrace, _)] fields:(name_type_pair() ** [Token::Symbol(Symbol::Comma, _)]) methods:(method(name.to_string())*) [Token::Symbol(Symbol::CloseBrace, right)] {
            let mut m = methods;
            m.insert(0, Declaration::Struct { name: name.to_string(), fields, loc: left.to(&right) });
            m
        }

        rule declaration() -> Vec<Declaration<'a>>
        = import() / function() / strct()


        rule parens() -> Expression<'a>
        = [Token::Symbol(Symbol::OpenParen, _)] e:expr() [Token::Symbol(Symbol::CloseParen, _)] { e }

        rule function_inv() -> Expression<'a>
        = [Token::Identifier(name, left)] [Token::Symbol(Symbol::OpenParen, _)] args:(expr() ** [Token::Symbol(Symbol::Comma, _)]) [Token::Symbol(Symbol::CloseParen, right)] { Expression::FunctionInvocation { name: name.to_string(), args, loc: Loc::new(left.file, left.left, right.right) } }

        rule instantiation() -> Expression<'a>
        = [Token::Keyword(Keyword::New, left)] [Token::Identifier(name, _)] [Token::Symbol(Symbol::OpenParen, _)] args:(expr() ** [Token::Symbol(Symbol::Comma, _)]) [Token::Symbol(Symbol::CloseParen, right)] { Expression::Instantiation { name: name.to_string(), args, loc: Loc::new(left.file, left.left, right.right) } }

        rule var_access() -> Expression<'a>
        = [Token::Identifier(name, loc)] { Expression::VarAccess(name.to_string(), loc) }

        rule literal() -> Expression<'a>
        = [Token::Literal(v, loc)] { Expression::Literal(v, loc) }

        rule expr() -> Expression<'a>
        = precedence! {
            x:(@) [Token::Symbol(Symbol::GreaterThan, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::GreaterThan, Box::new(y.clone()), x.loc().to(&y.loc())) }
            x:(@) [Token::Symbol(Symbol::GreaterThan, _)] [Token::Symbol(Symbol::Equals, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::GreatherThanEquals, Box::new(y.clone()), x.loc().to(&y.loc())) }
            x:(@) [Token::Symbol(Symbol::LessThan, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::LessThan, Box::new(y.clone()), x.loc().to(&y.loc())) }
            x:(@) [Token::Symbol(Symbol::LessThan, _)] [Token::Symbol(Symbol::Equals, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::LessThanEquals, Box::new(y.clone()), x.loc().to(&y.loc())) }
            x:(@) [Token::Symbol(Symbol::Equals, _)] [Token::Symbol(Symbol::Equals, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::DoubleEquals, Box::new(y.clone()), x.loc().to(&y.loc())) }
            x:(@) [Token::Symbol(Symbol::Bang, _)] [Token::Symbol(Symbol::Equals, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::NotEquals, Box::new(y.clone()), x.loc().to(&y.loc())) }
            --
            x:(@) [Token::Symbol(Symbol::Plus, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::Plus, Box::new(y.clone()), x.loc().to(&y.loc())) }
            x:(@) [Token::Symbol(Symbol::Minus, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::Minus, Box::new(y.clone()), x.loc().to(&y.loc())) }
            --
            x:(@) [Token::Symbol(Symbol::Times, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::Times, Box::new(y.clone()), x.loc().to(&y.loc())) }
            x:(@) [Token::Symbol(Symbol::Divide, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::Divide, Box::new(y.clone()), x.loc().to(&y.loc())) }
            x:(@) [Token::Symbol(Symbol::Percent, _)] y:@ { Expression::BiOperation(Box::new(x.clone()), BiOp::Mod, Box::new(y.clone()), x.loc().to(&y.loc())) }
            --
            x:(@) [Token::Symbol(Symbol::Dot, _)] [Token::Identifier(name, left)] [Token::Symbol(Symbol::OpenParen, _)] args:(expr() ** [Token::Symbol(Symbol::Comma, _)]) [Token::Symbol(Symbol::CloseParen, right)] { let loc = x.loc().to(&right); Expression::MethodInvocation { left: Box::new(x), name: name.to_string(), args, loc } }
            x:(@) [Token::Symbol(Symbol::Dot, _)] [Token::Identifier(name, right)] { Expression::PropertyAccess(Box::new(x.clone()), name.to_string(), Loc::new(x.loc().file, x.loc().left, right.right)) }
            [Token::Literal(v, loc)] { Expression::Literal(v, loc) }
            [Token::Keyword(Keyword::New, left)] [Token::Identifier(name, _)] [Token::Symbol(Symbol::OpenBracket, _)] len:expr() [Token::Symbol(Symbol::CloseBracket, right)] { Expression::ArrayCreation { typename: name.to_string(), degree: 1, num: Box::new(len), loc: Loc::new(left.file, left.left, right.right) } }
            [Token::Keyword(Keyword::New, left)] [Token::Identifier(name, _)] [Token::Symbol(Symbol::OpenParen, _)] args:(expr() ** [Token::Symbol(Symbol::Comma, _)]) [Token::Symbol(Symbol::CloseParen, right)] { Expression::Instantiation { name: name.to_string(), args, loc: Loc::new(left.file, left.left, right.right) } }
            [Token::Identifier(name, left)] [Token::Symbol(Symbol::OpenParen, _)] args:(expr() ** [Token::Symbol(Symbol::Comma, _)]) [Token::Symbol(Symbol::CloseParen, right)] { Expression::FunctionInvocation { name: name.to_string(), args, loc: Loc::new(left.file, left.left, right.right) } }
            [Token::Identifier(name, loc)] { Expression::VarAccess(name.to_string(), loc) }
            x:(@) [Token::Symbol(Symbol::OpenBracket, _)] idx:expr() [Token::Symbol(Symbol::CloseBracket, right)] { Expression::ArrayAccess { arr: Box::new(x.clone()), idx: Box::new(idx), loc: Loc::new(x.loc().file, x.loc().left, right.right) } }
            [Token::Symbol(Symbol::OpenParen, _)] v:expr() [Token::Symbol(Symbol::CloseParen, _)] { v }
        }

        rule var_declaration_let() -> Statement<'a>
        = [Token::Keyword(Keyword::Let, left)] [Token::Identifier(name, _)] [Token::Symbol(Symbol::Equals, _)] value:expr() [Token::Symbol(Symbol::Semicolon, right)] { Statement::VariableDeclaration { mutable: false, name: name.to_string(), value, loc: Loc::new(left.file, left.left, right.right) } }

        rule var_declaration_var() -> Statement<'a>
        = [Token::Keyword(Keyword::Var, left)] [Token::Identifier(name, _)] [Token::Symbol(Symbol::Equals, _)] value:expr() [Token::Symbol(Symbol::Semicolon, right)] { Statement::VariableDeclaration { mutable: true, name: name.to_string(), value, loc: Loc::new(left.file, left.left, right.right) } }

        rule var_declaration() -> Statement<'a>
        = var_declaration_let() / var_declaration_var()

        rule assignment() -> Statement<'a>
        = [Token::Identifier(name, left)] [Token::Symbol(Symbol::Equals, _)] value:expr() [Token::Symbol(Symbol::Semicolon, right)] { Statement::Assignment(name.to_string(), value, Loc::new(left.file, left.left, right.right)) }

        rule array_set() -> Statement<'a>
        = left:expr() [Token::Symbol(Symbol::Equals, _)] right:expr() [Token::Symbol(Symbol::Semicolon, r)] {
            match left.clone() {
                Expression::ArrayAccess { arr, idx, loc } => Statement::ArraySet { arr: *arr, indexes: vec![*idx], value: right, loc: Loc::new(left.loc().file, left.loc().left, r.right) },
                Expression::PropertyAccess(expr, prop, l) => { Statement::PropertySet(*expr, prop, right.clone(), left.loc().to(&right.loc())) },
                _ => panic!("must be an array or propety access")
            }
        }

        rule expression_statement() -> Statement<'a>
        = e:expr() [Token::Symbol(Symbol::Semicolon, right)] { Statement::Expression(e.clone(), Loc::new(e.loc().file, e.loc().left, right.right)) }

        rule if_statement() -> Statement<'a>
        = [Token::Keyword(Keyword::If, left)] condition:expr() block:braceblock() { Statement::If { condition, block: block.0, loc: left.to(&block.1) } }

        rule while_loop() -> Statement<'a>
        = [Token::Keyword(Keyword::While, left)] condition:expr() block:braceblock() { Statement::While { condition, block: block.0, loc: left.to(&block.1) } }

        rule break_statement() -> Statement<'a>
        = [Token::Keyword(Keyword::Break, left)] [Token::Symbol(Symbol::Semicolon, right)] { Statement::Break(left.to(&right)) }

        rule return_statement() -> Statement<'a>
        = [Token::Keyword(Keyword::Return, left)] e:expr()? [Token::Symbol(Symbol::Semicolon, right)] { Statement::Return(e, left.to(&right)) }

        rule statement() -> Statement<'a>
        = assignment() / array_set() / var_declaration() / expression_statement() / if_statement() / while_loop() / break_statement() / return_statement()

        rule decls() -> Vec<Declaration<'a>>
        = d:declaration()* { 
            let mut out = vec![];
            for item in d {
                for v in item {
                    out.push(v);
                }
            }
            out
        }

        pub rule file() -> ParsedFile<'a>
        = package:package_decl() content:decls() { ParsedFile { package, content } }
    }
}
