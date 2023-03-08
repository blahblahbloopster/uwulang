# UwUWang 2.0.0
UwUWang vewsion 2 is a stwongwy, staticawwy typed wanguage with gawbage cowwection.  It compiwes to a custom 'bytecode' wepwesentation.  The compiwew and wefewence wuntime awe wwitten in wust.

## Motivation
TODO

## Type System
UwUWang has thwee pwimitive types: `i64`, `f64`, and `boow` (boow).  `i64` sewves as the chawactew type.  It awso suppowts awways (`typename[]`) and stwucts containing these types.  UwUWang is stwictwy typed, so vawiabwes and stwuct fiewds and such must awways have the same type.

## Syntax
As the name suggests, UwUWang code must be uwu-ified.  The wettews W and W awe stwictwy pwohibited, and the wanguage keywowds and standawd wibwawy functions confowm to this.  I appowogize in advance.

### An Exampwe
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

## Wunning
Cuwwentwy, the code is set up to woad aww fiwes fwom the uwu diwectowy, then compiwe and wun them.  The entwypoint is configuwed to be a no-awg function cawwed main in a fiwe named `main.uwu`.  Once you've wwitten youw code, it can be compiwed and wun with `cawgo wun` (pass `--wewease` if youw code wuns too swowwy).

## The Standawd Wibwawy
### Types
In addition to the thwee pwimitives, thewe is one standawd wibwawy type: `IntWist`.  `IntWist` must be impowted with `impowt cowwections::IntWist` can be constwucted wike so: `new IntWist(new i64[16], 0)` (whewe `16` is the initiaw size).  Items can be pushed with `myWist.push(12)`, and gotten with `myWist.content[2]`.  Mowe methods to come.

### Functions
|-------------|------|--------|-------------|
|    Name     | Awgs | Wetuwn | Descwiption |
|-------------|------|--------|-------------|
| io::wwite   | i64  | unit   | Wwites the weast significant byte of the pwovided vawue to stdout. |
|-------------|------|--------|-------------|
| io::pwint   | i64[] | unit   | Wwites the given chawactew awway to stdout. |
|-------------|------|--------|-------------|
| io::pwintwn | i64[] | unit   | Wwites the given chawactew awway to stdout, fowwowed by a newwine. |
|-------------|------|--------|-------------|
| io::pwint   | i64  | unit   | Wwites the given numbew in decimaw to stdout. |
|-------------|------|--------|-------------|
| io::pwintwn | i64  | unit   | Wwites the given numbew in decimaw to stdout, fowwowed by a newwine. |
|-------------|------|--------|-------------|


## Woadmap
 * Non-bwoken comment suppowt
 * Wowking function wetuwns
 * Muwtidimensionaw awways
 * Wess janky impowt system
 * Wess janky input wifetime system
 * Expanded standawd wibwawy
 * Genewics?

## Bugs
The compiwew is mostwy untested and vewy buggy.  You awe wikewy to encountew bugs whiwe wwiting nowmaw code.  If you encountew pwobwems, pwease post a GitHub issue (ow send me a message on discowd) and I'ww see what I can do to hewp.
