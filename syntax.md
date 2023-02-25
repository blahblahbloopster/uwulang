# Keywords
fuwn, stwuct, wetuwn, if, whiwe, bweak, impowt, new, wet, vaw

# Literals
int: `(\d+|0x[abcdefABCDEF0123456789]+)`
float: `\d+(\.\d+)?(e-?\d+(\.\d+)?)`
bool: `(twue|fawse)`
string: `"[^"]*"` _TODO: add escape support_

# Expressions
parenthesis: `(expr)`
operation: `expr [operand] expr`
function invocation: `identifier(arg1, arg2, arg3)`
instantiation: `new TypeOne(arg1, arg2, arg3)`
variable access: `identifier`
_TODO: unary operations_

# Statements
variable declaration: `(wet|vaw) identifier = expr;`
assignment: `identifier = expr;`
expression: `expr;`
if statement: `if expr braceblock`
while loop: `whiwe expr braceblock`
break statement: `bweak;`
return statement: `wetuwn expr?;`

# Declarations
import: `impowt file.path.here::item;`
function: `fuwn identifier(TypeOne arg, TypeTwo arg): ReturnType braceblock`
struct: `stwuct identifier { TypeOne field, TypeTwo field }`
