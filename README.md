# UwULang 2.0.0
UwULang version 2 is a strongly, statically typed language with garbage collection.  It compiles to a custom 'bytecode' representation.  The compiler and reference runtime are written in rust.

## Motivation
TODO

## Type System
UwULang has three primitive types: `i64`, `f64`, and `boow` (bool).  `i64` serves as the character type.  It also supports arrays (`typename[]`) and structs containing these types.  UwULang is strictly typed, so variables and struct fields and such must always have the same type.

## Syntax
As the name suggests, UwULang code must be uwu-ified.  The letters L and R are strictly prohibited, and the language keywords and standard library functions conform to this.  I appologize in advance.

### An Example
```
package main;

impowt io::pwint;
impowt io::pwintwn;
impowt io::wwite;

stwuct UwUCountew {
    count: i64,
    message: i64[]

    fuwn show() {
        pwint(sewf.message);
        pwint(" ");
        pwintwn(sewf.count);
    }

    fuwn uwu() {
        sewf.count = sewf.count + 1;
    }
}

fuwn main() {
    wet countew = new UwUCountew(0, "uwus:");

    vaw idx = 0;
    whiwe idx < 5 {
        countew.uwu();
        countew.show();
        idx = idx + 1;
    }

    wet myAwway = new i64[5];
    myAwway[2] = 'A';
    wwite(myAwway[2]);
    pwintwn("");
}
```

## Running
Currently, the code is set up to load all files from the uwu directory, then compile and run them.  The entrypoint is configured to be a no-arg function called main in a file named `main.uwu`.  Once you've written your code, it can be compiled and run with `cargo run` (pass `--release` if your code runs too slowly).

## The Standard Library
### Types
In addition to the three primitives, there is one standard library type: `IntWist`.  `IntWist` must be imported with `impowt cowwections::IntWist` can be constructed like so: `new IntWist(new i64[16], 0)` (where `16` is the initial size).  Items can be pushed with `myWist.push(12)`, and gotten with `myWist.content[2]`.  More methods to come.

### Functions
|-------------|------|--------|-------------|
|    Name     | Args | Return | Description |
|-------------|------|--------|-------------|
| io::wwite   | i64  | unit   | Writes the least significant byte of the provided value to stdout. |
|-------------|------|--------|-------------|
| io::pwint   | i64[] | unit   | Writes the given character array to stdout. |
|-------------|------|--------|-------------|
| io::pwintwn | i64[] | unit   | Writes the given character array to stdout, followed by a newline. |
|-------------|------|--------|-------------|
| io::pwint   | i64  | unit   | Writes the given number in decimal to stdout. |
|-------------|------|--------|-------------|
| io::pwintwn | i64  | unit   | Writes the given number in decimal to stdout, followed by a newline. |
|-------------|------|--------|-------------|


## Roadmap
 * Non-broken comment support
 * Working function returns
 * Multidimensional arrays
 * Less janky import system
 * Less janky input lifetime system
 * Expanded standard library
 * Generics?

## Bugs
The compiler is mostly untested and very buggy.  You are likely to encounter bugs while writing normal code.  If you encounter problems, please post a GitHub issue (or send me a message on discord) and I'll see what I can do to help.
