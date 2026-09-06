<!-- docs/src/language.md -->

# Language Guide

This guide covers Wax syntax and semantics. For the detailed mapping to WebAssembly instructions, see [Correspondence](correspondence.md).

## Module Name

A whole `.wax` file is a module. To give the module a name, place a
`#![module = "..."]` inner attribute at the top of the file:

```wax,check
#![module = "my_module"]

fn f() -> i32 {
    1;
}
```

Unlike the `#[...]` outer attributes that decorate a following field (such as
`#[export = "name"]`), `#![...]` is an *inner* attribute: it applies to the
enclosing module. A module may carry at most one name.

(This maps to the WebAssembly module name stored in the `name` custom section,
the `$name` in a WAT `(module $name …)`; see
[Module Fields](correspondence.md#module-name).)

## Features

A module can declare the optional proposals it uses (the `-X`/`--feature` set,
such as `custom-descriptors` or `compact-import-section`) with a
`#![feature = "..."]` inner attribute at the top of the file, one feature per
attribute:

```wax,check
#![feature = "custom-descriptors"]

rec {
    type obj = descriptor obj_desc { x: i32 };
    type obj_desc = describes obj { };
}
```

The file is then self-describing: it compiles, validates, and round-trips
without every consumer passing `-X`, and the editor needs no configuration.
The value is a feature name exactly as `-X` spells it; an unknown name is an
error listing the known features. Repeating an attribute is allowed
(declaring a feature is idempotent).

The attribute states a fact ("this module uses X"), while an explicit
`-X x=off` states a policy; neither silently overrides the other:

- The file declares X and the command line is silent: X is enabled.
- The file is silent and the command line passes `-X x`: X is enabled.
- Both declare and enable X: X is enabled.
- The file declares X but the command line passes `-X x=off`: this is an
  error, reported once at the attribute.

(This maps to a module-level `(@feature "...")` annotation in WAT, and to a
`+name` entry of the conventional `target_features` custom section in the
binary; see
[Module Fields](correspondence.md#feature-declarations).
Decompiling a binary restores the attribute from that section and from the
gated encodings the module actually uses, so even a binary from a producer
that wrote no section decompiles to a self-describing module.)

## Comments

Wax supports C-style comments:

```wax,check
// Single-line comment

/* Multi-line
   comment */
```

## Trailing Commas

A trailing comma is allowed after the last element of any comma-separated
list: function parameters, call arguments, struct fields, result types, and
so on:

```wax,check
type point = { x: i32, y: i32, };

fn add(a: i32, b: i32,) -> i32 {
    a + b;
}
```

## Literals

### Integers

```wax
42          // Decimal
0x2A        // Hexadecimal
```

A numeric literal is **flexible**: it has no fixed type of its own but takes a
concrete one from its context: a type annotation, the operation it feeds, or a
function's result type.

```wax,check
let x: i64 = 42;        // takes i64 from the annotation
```

Which concrete types a literal can take depends on its magnitude:

| Literal | Can become | Defaults to |
|---------|-----------|-------------|
| fits in 32 bits (≤ `0xFFFF_FFFF`) | `i32`, `i64`, `f32`, `f64` | `i32` |
| larger, fits in 64 bits | `i64`, `f32`, `f64` (never `i32`) | `i64` |
| larger than 64 bits | `f32`, `f64` only | `f64` |
| a floating-point literal | `f32`, `f64` | `f64` |

The *defaults* apply only when nothing constrains the literal:

```wax,check
let a = 42;             // unconstrained -> i32
let b = 5_000_000_000;  // too big for i32 -> i64
let c = 3.14;           // float literal -> f64
```

Wax performs **no implicit conversions** between numeric types. A numeric
expression must be coherent: an operator's operands must share one type, so
mixing an `i32` with an `i64`, or an integer with a float, does not type-check.
A flexible literal is never converted; it simply takes the type that keeps its
expression coherent. An operation that accepts only integers (a bitwise op, a
shift, `ctz`, …) holds the flexible literals feeding it to the integer family,
so they can only be `i32` or `i64`, never a float.

Changing a value's type takes an explicit [`as` cast](#type-conversions), which
emits the conversion: an out-of-range constant `as i32` wraps to its low 32
bits, and an integer `as f64` converts.

### Floating Point

```wax
3.14        // Decimal
1.0e10      // Scientific notation
0x1.5p10    // Hexadecimal float
inf         // Infinity
nan         // Not a number
```

A floating-point literal is `f32` or `f64`, defaulting to `f64` when
unconstrained (see the table above).

### Characters

A character literal is a single character in single quotes. It evaluates to that
character's Unicode code point as an `i32`: it is simply a readable spelling of
an `i32.const`:

```wax
'A';            // 65
'\n';           // 10
'\x41';         // 65, a byte written as two hex digits
'\u{1F600}';    // 128512, a Unicode code point
```

The recognised escapes are `\t`, `\n`, `\r`, `\'`, `\"`, `\\`, `\xNN` (exactly
two hex digits, one byte), and `\u{...}` (a Unicode code point in hex). For
text, see [Strings](#strings).

A character literal round-trips through WAT, where it is written with a
`(@char …)` annotation. A Wasm binary keeps only the underlying `i32.const`,
though, so decompiling from Wasm yields the plain integer code point.

## Variables

### Local Variables

Declare local variables with `let`. Each variable gets a type, either from an
explicit annotation or from an initializer:

```wax,check
fn example() -> i32 {
    let x: i32;        // annotated, no initializer
    let y = 20;        // type inferred from the initializer (i32)
    x = 10;
    x + y;
}
```

Unlike Rust, a local is freely mutable: there is no `let mut`, and no
immutable-local form. (`mut` exists in Wax, but it marks
[struct fields](#structs) and array element types, not bindings; the
immutable module-level form is [`const`](#global-variables).)

A local declared without an initializer starts at its type's zero value (`0`,
`0.0`, or `null`). When the type is omitted, it is taken from the initializer;
an otherwise-unconstrained integer literal then defaults to `i32` and a float to
`f64`. An annotation and an initializer can be combined, and must agree:

```wax,check
let count: i64 = 0;
```

A `let` can bind several names at once from an initializer that produces
multiple values, a call to a [multi-result function](#functions),
for instance. The names are written as a parenthesised list and each takes the
corresponding value, left to right. As with a single binding, each name may be
annotated or left to be inferred, and `_` discards its value:

```wax
let (q, r) = divmod(17, 5);     // q and r inferred from the results
let (n: i64, _) = stats();      // n annotated, the second result dropped
```

### Assignment

Use `=` for assignment (like `local.set`):

```wax
x = 42;
```

Use `:=` for assignment that also returns the value (like `local.tee`):

```wax
y = (x := 42) + 1;  // x is set to 42, y is set to 43
```

`:=` works on local variables only: WebAssembly has no `global.tee`, so applying
it to a global is an error.

A compound assignment combines a binary operator with `=`: `x op= e` is
shorthand for `x = x op e`, where the left-hand side is a local or global
variable.

```wax
counter += 1;       // counter = counter + 1
mask &= 0xff;        // mask = mask & 0xff
total /s= n;         // total = total /s n
```

Every value-producing arithmetic and bitwise operator has a compound form:
`+=`, `-=`, `*=`, `/=`, `/s=`, `/u=`, `%s=`, `%u=`, `&=`, `|=`, `^=`, `<<=`,
`>>s=`, and `>>u=`. As for the corresponding binary operators, the signed and
unsigned variants apply to integers, while the sign-agnostic `/=` is float
division. Comparisons have no compound form.

### Discarding a value

Assigning to `_` evaluates an expression and throws its result away, the
equivalent of WebAssembly's `drop`. Nothing is bound, so no name comes into
scope:

```wax
_ = f();            // call f for its side effects, ignore its result
```

An optional type annotation, `_: t = e`, pins the type of the discarded value.
This is hardly ever needed, since the value is thrown away anyway:

```wax
_: i64 = 1 << 40;   // discard the result, but keep it i64
```

### Global Variables

Globals are declared at module level. `const` is immutable; `let` is mutable:

```wax,check
const PI: f64 = 3.14159;        // immutable global
let counter: i32 = 0;           // mutable global
```

As with locals, an initialized global may omit its type and take it from the
initializer (an unconstrained integer literal defaults to `i32`):

```wax,check
const answer = 42;              // i32
```

A global's initializer must be a constant expression (a literal, another
global, or a simple reference-building expression).

A `let` global that nothing ever assigns is reported by the
[`unnecessary-mut`](cli.md#warnings) warning, since it could be a `const`.
Exported globals are exempt: the host may assign those.

### Names and Scope

Functions, globals, memories, and tables share one module-level namespace: a
name must be distinct across all four: you cannot, say, declare both a memory
and a global named `buf`. Types, tags, and data/element segments each have their
own namespace, so those names may overlap with the above and with one another.

A local variable is scoped to its function and takes precedence over module-level
names. A bare name resolves to a local before a global or function, and the
name-based module forms (`mem.load(..)`, `tab[i]`, `seg.drop()`) likewise defer
to a same-named local. So a local that reuses a memory, table, or segment name
shadows it; rename the local if you still need to reach the module entity.

## Expressions

Wax is a readable layer over WebAssembly, and it keeps WebAssembly's execution
model: the **operand stack**. A function or block body is a sequence of
statements, each ended with `;`. Evaluating a statement may push values onto the
stack and pop values off it, and whatever remains on the stack when the body
ends is its result, which must match the declared result type. A
value-returning function therefore ends with a statement that leaves that value:

```wax,check
fn double(x: i32) -> i32 {
    x * 2;
}
```

Most expressions produce a value. This same stack model underlies
[blocks](#blocks), [holes](#holes), and functions or blocks with more than one
result.

### Arithmetic

```wax
x + y       // Add
x - y       // Subtract
x * y       // Multiply
x / y       // Divide (float)
x /s y      // Divide signed (integer)
x /u y      // Divide unsigned (integer)
x %s y      // Remainder signed
x %u y      // Remainder unsigned
```

### Bitwise

```wax
x & y       // And
x | y       // Or
x ^ y       // Xor
x << y      // Shift left
x >>s y     // Shift right signed
x >>u y     // Shift right unsigned
```

### Comparison

```wax
x == y      // Equal
x != y      // Not equal
x < y       // Less than (float)
x <s y      // Less than signed (integer)
x <u y      // Less than unsigned (integer)
x <= y      // Less or equal (float)
x <=s y     // Less or equal signed
x <=u y     // Less or equal unsigned
// Similarly: >, >=, >s, >u, >=s, >=u
```

On reference operands (any subtype of `&eq`), `==` and `!=` are reference
identity, not a numeric comparison.

### Unary Operations

```wax
-x          // Negate
+x          // Positive (no-op for integers)
!x          // Logical not / is_null for references
```

Unlike Rust, `!` on an integer is *logical* not, not bitwise complement: it
yields `1` for `0` and `0` for any non-zero value (Wasm's `eqz`), so `!5` is
`0`, not `-6`. For a bitwise complement, write `x ^ -1`.

### Operator Precedence

Operators are listed below from highest precedence (binds tightest) to lowest.
The ordering follows **Rust's** for every operator the two share (Wax adds
`? :`, which Rust lacks, just above assignment; it has no short-circuit `&&`/`||`:
`&`/`|` are bitwise). Two mixes are worth committing to memory:

- `&`, `^`, `|` bind **tighter** than the comparison operators, so `a & b == c`
  parses as `(a & b) == c`. Rust agrees; C is the opposite: there it means
  `a & (b == c)`.
- The shifts bind **looser** than `+`/`-`, so `1 << nbits - 1` parses as
  `1 << (nbits - 1)`, not `(1 << nbits) - 1`. (Same in Rust and C.)

| Precedence | Operators | Associativity |
|------------|-----------|---------------|
| highest | `.field` &nbsp; `f(…)` &nbsp; `[…]` (field, call, index) | left |
|  | `-x` &nbsp; `+x` &nbsp; `!x` (unary) | n/a |
|  | `as` &nbsp; `is` (cast, test) | left |
|  | `*` &nbsp; `/` &nbsp; `/s` &nbsp; `/u` &nbsp; `%s` &nbsp; `%u` | left |
|  | `+` &nbsp; `-` | left |
|  | `<<` &nbsp; `>>s` &nbsp; `>>u` | left |
|  | `&` | left |
|  | `^` | left |
|  | <code>&#124;</code> | left |
|  | `==` &nbsp; `!=` &nbsp; `<` &nbsp; `>` &nbsp; `<=` &nbsp; `>=` (and `s`/`u` forms) | none |
|  | `? :` | right |
| lowest | `=` &nbsp; `:=` &nbsp; `+=` … (assignment) | right |

Because the two cross-class mixes above are easy to misread, the
[`precedence` lint](cli.md) (in the `correctness` group, on by default) flags a
shift mixed with arithmetic, or a comparison mixed with a bitwise operator, when
it is written without disambiguating parentheses.

### Method-Style Operations

Some operations use method syntax. These are calls, so they take parentheses
even when they have no argument:

```wax
x.abs()       // Absolute value
x.sqrt()      // Square root
x.floor()     // Floor
x.ceil()      // Ceiling
x.trunc()     // Truncate
x.nearest()   // Round to nearest
x.clz()       // Count leading zeros
x.ctz()       // Count trailing zeros
x.popcnt()    // Population count
x.extend8_s()   // Sign-extend the low 8 bits
x.extend16_s()  // Sign-extend the low 16 bits
```

Two-argument operations pass the second operand as the argument:

```wax
x.min(y)
x.max(y)
x.copysign(y)
x.rotl(y)      // Rotate left
x.rotr(y)      // Rotate right
```

### Qualified Intrinsics

Most built-in operations are written as methods on a receiver (`x.clz()`,
`a.add_i32x4(b)` above). The few that have no natural receiver are written
instead as a **qualified path**, `type::member(args)`, a built-in free
function namespaced by the WebAssembly type it belongs to. These names are
built in, not user functions, and because the `::` form is distinct from an
ordinary name it can never clash with your own functions, globals, or locals.

Two families use this syntax today.

**`v128::`: SIMD free functions.** The vector constants (one argument per
lane) and `bitselect`, which have no receiver:

```wax
v128::i32x4(1, 2, 3, 4)         // a v128 constant (also a constant expression)
v128::f32x4(1.5, 2.5, 3.5, 4.5)
v128::bitselect(a, b, mask)           // per-bit select
```

**`i64::`: wide arithmetic.** 128-bit integer operations, taking and returning
their operands as `(low, high)` pairs of `i64`, so each returns two results
(bind them with a multi-value `let`):

```wax
i64::add128(a_lo, a_hi, b_lo, b_hi)   // 128-bit add, returns (lo, hi)
i64::sub128(a_lo, a_hi, b_lo, b_hi)   // 128-bit subtract
i64::mul_wide_s(a, b)                 // signed 64×64 → 128-bit product
i64::mul_wide_u(a, b)                 // unsigned 64×64 → 128-bit product
```

### Type Conversions

Use `as` for type conversions:

```wax
x as i32        // Wrap i64 to i32
x as i64_s      // Sign-extend i32 to i64
x as i64_u      // Zero-extend i32 to i64
x as f32        // Demote f64 to f32
x as f64        // Promote f32 to f64
x as i32_s      // Truncate float to signed int
x as f32_s      // Convert signed int to float
x.to_bits()     // Reinterpret float as int
x.from_bits()   // Reinterpret int as float
```

### Conditional Expression

```wax
cond ? val_true : val_false
```

This maps directly to Wasm's `select` instruction.

> **⚠ Warning: both branches are always evaluated.** Unlike the `?:` (or
> `if`/`else` expression) of most languages, this operator is *not* lazy: it
> compiles to a `select`, which computes *both* `val_true` and `val_false`
> before choosing between them. So `cond ? 1 /s x : 0` still divides by `x`
> even when `cond` is false (trapping if `x` is `0`), and `cond ? f() : g()`
> calls *both* `f` and `g`. When a branch may trap or has a side effect, use an
> [`if` expression](#if-expressions) instead: it evaluates only the chosen
> branch. The
> [`eager-select` lint](cli.md) (in the `correctness` group, on by default)
> flags a trapping or effectful operation in a `?:` branch.

## Control Flow

Statements are separated by `;`. The final `;` of a block is optional: a
block's last statement may omit it. Unlike Rust, writing that trailing `;` does
not discard the statement's value — the value stays on the stack and becomes the
block's or function's result either way (a trailing `;` is just an empty
statement, which contributes nothing). The formatter always writes the canonical
trailing `;`. The block-shaped statements below
(`do`, `if`, `while`, `loop`, `dispatch`, `match`, and `try`) are the
exception: their closing `}` ends the statement, so no `;` is needed. A bare
`;` is an empty statement (it does nothing), so a redundant one is harmless
anywhere and dropped on formatting, most usefully after a block, where the
reflex of ending every line with `;` would otherwise be an error. The same
holds outside function bodies: a stray `;` is an empty element wherever items
are listed: among module fields, the declarations of an `import` block, and
the arms of a `dispatch`, `match`, or `catch`.

### Blocks

A block groups a sequence of statements, written with `do`.

```wax
do {
    let x: i32;
    x = compute();
    use(x);
}
```

By default a block is **void**: it produces no value, so, like a function with
no result type, its body must leave the operand stack empty.

To make a block produce a value, give it a result type after `do`. The body
must leave a value of that type on the stack, and that becomes the block's
value:

```wax
answer = do i32 {
    42;
};
```

This is a stack discipline, not a "last expression" rule: the body must leave
*exactly* the values the block's type describes: no more, no less. A void
block that leaves a value, or a `do i32` block that leaves two, is an error.

The result type may be **omitted** and inferred: from the value the body leaves
(including a value branched to the block's own label), or from the surrounding
context such as a function's result type, a typed binding, or a call argument.
It is needed only where neither determines it, for instance when two branches
produce values with no common supertype. So the block above can drop its `i32`:

```wax
answer = do {
    42;
};
```

`loop`, `try`, and `try_table` infer their result type the same way. Converting
WebAssembly to Wax drops the annotation wherever it is redundant, and re-reading
that Wax recovers the type by the same inference.

A block type may also take parameters off the enclosing stack, using the full
`(params) -> results` form:

```wax
do (i32) -> i32 {
    // the i32 operand below the block is available here
}
```

Parameters only work when the block stands on its own as a statement, where
those values come from the operand stack. A block used *inside* an expression
has no enclosing stack to draw from, so it cannot take parameters. To combine a
parameterized block's result with other operands, keep the block at statement
level and pick up its result with a [hole](#holes):

```wax
x;                        // leaves an i32 on the stack
do (i32) -> i32 { … }     // a statement: consumes that i32, leaves an i32
_ + 1;                    // the hole plugs in the block's result
```

Blocks can be labelled and used as branch targets; see
[Labels and Branches](#labels-and-branches).

### If Expressions

`if` tests a condition (any `i32`, where non-zero means true) and runs the
matching branch. Like a block it is **void** by default (the branches leave no
value), and the `else` is optional:

```wax
if condition {
    then_branch;
}
```

To make `if` produce a value, give it a result type with `=> <type>`. Both
branches must then leave a value of that type, so the `else` becomes required:

```wax
if condition => i32 {
    1;
} else {
    0;
}
```

Like a block's result type, the `=> <type>` may be **omitted** and inferred:
from the branches (here both produce `i32`) or from the surrounding context. The
`else` stays required, since a value-producing `if` needs both branches:

```wax
x = if condition {
    1;
} else {
    0;
};
```

### Loops

A `loop` runs its body once and then falls through to whatever follows: it does
*not* repeat on its own. What makes it a loop is its label: branching to a
loop's label jumps back to the **start** of its body. So a loop iterates by
branching to itself, and stops once control reaches the end of the body without
branching back.

```wax
'next: loop {
    total = total + i;
    i = i + 1;
    br_if 'next i <s n;   // jump back to the start while i < n
}
```

This is the opposite of a `do` block, whose label branches *past* the block (see
[Labels and Branches](#labels-and-branches)). To leave a loop early, branch to
an enclosing block's label.

Loops nest, and a branch may target any enclosing label:

```wax
'outer: loop {
    'inner: loop {
        br 'outer;   // jump back to the start of the outer loop
    }
}
```

### While Loops

A `while` is readable sugar over the `loop`-and-back-branch idiom above; it
tests *before* each iteration:

```wax
while i <s n {
    total = total + i;
    i = i + 1;
}
```

which is exactly:

```wax
'next: loop {
    if i <s n {
        total = total + i;
        i = i + 1;
        br 'next;
    }
}
```

It is void, and the test must be an `i32`. It may carry a label
(`'l: while …`), which names the loop, so a `br 'l` from inside the body is a
*continue*: it jumps back to re-test. Decompiling recovers a `while` from this
shape, so a loop written this way survives a round trip through WAT or Wasm.

A `while` may carry a *continue-expression* after the condition,
`while cond : (step) { … }`, a statement run at the end of every iteration,
including on a `continue`. It keeps the loop's step next to its header instead of
at the bottom of the body, and, unlike a step written as the last statement,
it still runs when the body branches to the loop label:

```wax
'l: while i <s n : (i += 1) {
    if skip(i) { br 'l; }   // continue: runs `i += 1`, then re-tests
    total += i;
}
```

The step must be parenthesised (a bare statement would be ambiguous with the
loop body). Without a `continue` this is equivalent to writing the step as the
last statement of the body, and decompiling recovers it: a loop whose last
statement updates a variable its condition reads (the induction variable) is
rendered as `while … : (step) { … }`, so index-and-stride loops read like `for`
loops.

A *trailing*-test loop, where the body always runs at least once, has no
leading-`while` form. Write it directly as a `loop` with a back-`br_if`:

```wax
'next: loop {
    total = total - 1;
    br_if 'next total >s 0;
}
```

### Labels and Branches

Labels start with `'` and prefix a block, loop, `if`, or `try`. A branch targets
a label; **where** it lands depends on the labelled construct: branching to a
block, `if`, or `try` jumps *past* it (an exit), while branching to a `loop`
jumps to its *start* (an iteration, see [Loops](#loops)).

```wax
'done: do {
    if condition {
        br 'done;   // jump past the block (exits it)
    }
    // ...
}
```

Branch instructions:

```wax
br 'label;                          // unconditional branch
br_if 'label cond;                  // branch if cond (an i32) is non-zero
br_table ['a, 'b, else 'default] i;   // branch to the i-th label, else 'default
```

The labels in a `br_table` are separated by commas, and the mandatory final
`else` gives the fallback for an out-of-range index. A branch also carries any values its target
expects: a `do i32` target receives an `i32`, and so on.

Four more branch instructions test a reference and branch on the result, passing
the refined reference to the target. They appear mainly in Wax decompiled from
WebAssembly; hand-written code usually reaches for [`match`](#match), a
[null check](#null-check), or a [cast or test](#type-testing-and-casting)
instead.

```wax
br_on_null 'l val;          // branch if val is null; else continue with val non-null
br_on_non_null 'l val;      // branch (passing val) if val is non-null; else continue
br_on_cast 'l &t val;       // branch (passing val as &t) if val is a &t; else continue
br_on_cast_fail 'l &t val;  // branch if val is not a &t; else continue with val as &t
```

### Branch Hints

A conditional branch can be annotated `#[likely]` or `#[unlikely]` to tell the
engine which way it usually goes (the
[branch-hinting proposal](https://github.com/WebAssembly/branch-hinting)). The
attribute prefixes the branch:

```wax
#[likely] if cond {
    // the common case
} else {
    // the rare case
}

'next: loop {
    #[unlikely] br_if 'next done;   // rarely taken
}
```

Any conditional branch accepts a hint: `if`, `br_if`, `br_on_null`,
`br_on_non_null`, `br_on_cast`, and `br_on_cast_fail`. The hint is purely
advisory (it does not change behaviour) and is preserved across every conversion
to and from WebAssembly, so no compiler flag is needed. See
[Instructions → Branch Hints](correspondence.md#branch-hints) for
the WebAssembly encoding.

### Compilation Hints

The [compilation-hints proposal](https://github.com/WebAssembly/compilation-hints)
extends the same mechanism to profile data an engine can use to decide what to
optimize. Two attributes carry it, and they prefix an expression rather than only a
branch:

```wax
#[freq = 16] 'l: loop {          // runs about 16 times per call
    #[never_opt] slow_path();    // never worth optimizing
}

#[targets(draw_rect: 0.73, draw_circle: 0.21)]
shape.draw();                    // the indirect call's likely callees
```

- `#[freq = n]` is how often the instruction runs per call of its function.
  `#[never_opt]` and `#[always_opt]` are the two reserved values. It is meaningful
  on a call or a control instruction.
- `#[targets(f: 0.73, …)]` lists the likely callees of an *indirect* call, each with
  how often it is taken as a fraction of 1. The fractions must total at most 1; a
  shortfall says other, unlisted callees take the remainder. Naming a function here
  is not a *use* of it, so one reachable only through a target list is still
  reported by the `unused-field` lint.

A hint attribute takes the **whole** expression that follows it. That makes the
extent unambiguous, at the price of rejecting a placement where a reader could not
tell what was meant:

```wax
#[freq = 4] f(x);            // fine: the hint is on the call
let y = #[freq = 4] f(x);    // fine: the initialiser is delimited
(#[freq = 4] f(x)) + 1       // fine: parentheses say which operand
#[freq = 4] f(x) + 1         // error: the hint lands on the `+`
```

This is the rule Rust's experimental `stmt_expr_attributes` uses. Several hints may
stack on one instruction, and a hint on a block statement needs no trailing `;`, as
a plain block statement does not.

The proposal's third section is per-*function*, so it is an ordinary field
attribute rather than an expression prefix:

```wax
#[priority = 1] #[run_once]
fn init() { /* compiled early, never optimized */ }

#[priority = 5] #[optimization = 10]
fn hot(x: i32) -> i32 { x }
```

`#[priority = n]` says how soon to compile the function relative to the others, and
is what makes the entry exist at all. The optimization priority is optional:
`#[optimization = n]`, or `#[run_once]` for the reserved value saying the function
is expected to run once, so optimizing it is wasted work. A function states at most
one of those two, and neither without `#[priority]`. It needs a body to attach to,
so it is allowed on a defined function, not an imported one.

Like branch hints, these are advisory and preserved across every conversion, so no
compiler flag is needed. See
[Instructions → Branch Hints](correspondence.md#branch-hints) for the
WebAssembly encoding.

### Dispatch

A `dispatch` is a multi-way branch, the readable form of a `br_table` jump
table. A bracket maps an index to a case label (with an `else` default for an
out-of-range index), and each arm gives that case's body:

```wax,check
fn classify(x: i32) -> i32 {
    dispatch x ['zero, 'one, 'two, else 'big] {
        'big:  { return 99; }
        'two:  { return 30; }
        'one:  { return 20; }
        'zero: { return 10; }
    }
}
```

The bracket is exactly the underlying `br_table`: index `0` jumps to the label
named first, `1` to the second, and so on, and an out-of-range index jumps to
the `else` label. A label may be listed more than once (several indices sharing
a case), and every listed label (and `else`) must name an arm. The index must be
an `i32`, and the labels are 0-ary branch targets. Case (arm) labels must be
distinct.

`dispatch` lowers to one nested block per case, with the `br_table` in the
innermost block and each case body just after its block. As in a C `switch`,
cases **fall through**: reaching a case runs its body and then falls into the
*next* arm listed, unless it branches away first. So the arms are written in
fall-through order, which is the reverse of the bracket's index order: the
last arm is the one index `0` reaches. The example above gives each case its
own result via `return`; to break out instead, branch to an enclosing label:

```wax
let r: i32;
'done: do {
    dispatch x ['zero, 'one, else 'two] {
        'two:  { r = 30; }
        'one:  { r = 20; br 'done; }
        'zero: { r = 10; br 'done; }
    }
}
```

This is the shape compilers emit for a dense switch, so decompiling WAT/Wasm to
Wax recovers `dispatch` from it (and a Wax `dispatch` round-trips through the
binary).

### Match

A `match` is a multi-way *type* test, the readable form of the nested type-test
ladder that hand-written GC code uses to take apart a value of some general
reference type. Each arm tests the scrutinee against a reference type, optionally
binding the narrowed value, and runs its body when the test succeeds:

```wax
fn classify(v: &?eq) -> i32 {
    match v {
        p: &point => { return p.x + p.y; }   // v is a &point, bound to p
        a: &bytes => { return a.length(); }  // else if v is a &bytes
        null      => { return -1; }           // else if v is null
        _         => { return 0; }            // otherwise (the default)
    }
}
```

A `x: &T` arm binds the narrowed value to `x` for its body; drop the `x:` to
test without binding. A `null` arm matches a null reference, and the required
`_` arm (as with a `dispatch`'s `else`) is the default. The scrutinee must be a
reference type; it is evaluated once.

`match` lowers to a nested ladder of blocks, one per arm plus an outer *escape*
block. The scrutinee is threaded through a `br_on_cast` (or `br_on_null` for a
`null` arm) chain in the innermost block; each test, on success, branches *out*
to its arm's block carrying the narrowed value, and the arm body follows that
block. As with `dispatch`, an arm's body must leave the `match` (here each
`return`s); to continue past it, branch to an enclosing label. When no test
matches, the chain falls through to a `br` past all the arm bodies, and the
default follows the escape block as trailing code, so reaching it falls through
to whatever comes after, including the rest of the enclosing block:

```wax
let r: i32;
'done: do {
    match v {
        p: &point => { r = p.x; br 'done; }
        a: &bytes => { r = a.length(); br 'done; }
        _ => { r = 0; }   // also reached by a non-point, non-bytes v
    }
}
```

This is the shape hand-written GC code uses, so decompiling WAT/Wasm to Wax
recovers `match` from such a ladder, even a single type test that branches out
and then falls through to a default (and a Wax `match` round-trips through the
binary).

### Return

```wax
return value;
```

### Tail Calls

Use `become` for tail calls (guaranteed not to grow the stack):

```wax,check
fn factorial_helper(n: i32, acc: i32) -> i32 {
    if n <=s 1 => i32 {
        acc;
    } else {
        become factorial_helper(n - 1, n * acc);
    }
}
```

`become` also accepts an intrinsic operation (for example `become mem.grow(n)`);
since there is no tail-call instruction for intrinsics, this is equivalent to
`return mem.grow(n)`: the intrinsic's result must match the function's result
type.

### Unreachable and Nop

`unreachable` marks code that should never run: it traps if reached. `nop` does
nothing. Neither is an expression, so neither can be bound to a name or written
as an operand. Because `unreachable` diverges, the code after it is dead and the
stack polymorphic there, so `unreachable` can satisfy any block result type,
fill any [hole](#holes) `_`, and supply any block parameter.

```wax
if x <s 0 {
    unreachable;            // this branch cannot happen
}
nop;                        // no operation
```

## Functions

### Definition

```wax
fn name(param1: type1, param2: type2) -> return_type {
    body;
}
```

Functions without a return type return nothing:

```wax,check
fn log_value(x: i32) {
    // side effects only
}
```

A function may return several values, written as a parenthesized list; the body
leaves them all on the stack, in order:

```wax,check
fn divmod(a: i32, b: i32) -> (i32, i32) {
    a /s b;
    a %s b;
}
```

### Start Function

A function marked with the `#[start]` attribute runs automatically when the
module is instantiated. It must take no parameters and return nothing, and a
module may have at most one:

```wax,check
#[start]
fn init() {
    // initialization code
}
```

Like `#[export]`, `#[start]` can carry an `if <condition>` guard, so a function
is the start only in some configurations (at most one start per configuration):

```wax,check
#[start, if(debug)]
fn init() {
    // only run under `-D debug=true`
}
```

(This maps to the WebAssembly `start` field; see
[Module Fields](correspondence.md#start-attribute).)

### Function Types

Function types use `fn`:

```wax,check
type binary_op = fn(i32, i32) -> i32;
```

An unnamed parameter is written as just its type:

```wax,check
type callback = fn(i32) -> i32;
```

### Calls

```wax
result = my_function(arg1, arg2);
```

### Indirect Calls

Writing a function's name without calling it is a reference to that function (a
`&func` value). This is how you get one: to store in a global or a
[table](#tables-and-element-segments), or to pass as an argument.

```wax
const handler: &callback = inc;   // a reference to `inc`, not a call
```

Call through such a reference by casting it to the expected function type:

```wax
(func_ref as &?callback)(arg)
```

## Imports and Exports

A module talks to its host through imports and exports.

**Export** a definition under a name with `#[export = "name"]`. It applies to
functions, globals, memories, tables, and tags, and a field may carry several.
The bare `#[export]` (no name) exports the field under its own Wax name:

```wax,check
#[export]
fn add(x: i32, y: i32) -> i32 { x + y; }

#[export = "PI"]
const PI: f64 = 3.14159;
```

**Import** fields from a host module with an `import "module" { … }` block. Each
entry has no body: a function is declared with just its signature, a global
with its type. It is imported under its own Wax name unless a name-only
`#[import = "name"]` overrides that:

```wax,check
import "env" {
    fn log(x: i32);
    #[import = "base_value"]
    const base: i32;
}

#[export = "run"]
fn run() { log(base); }
```

A lone import can be written on one line, `import "module" <declaration>;`:

```wax,check
import "env" fn trace(x: i32);
```

An imported field is re-exported by adding `#[export]` to its declaration.

An `#[export]` can carry an `if <condition>` guard, making just that export
[conditional](#conditional-compilation) independently of the field's own
reachability. This is how a definition can be exported under an extra name only
in some configurations:

```wax,check
#[export]
#[export = "add_alias", if(not(bootstrap))]
fn add(x: i32, y: i32) -> i32 { x + y; }
```

Here `add` is always exported under its own name, and also as `add_alias`
except when `bootstrap` holds. `#[export]` and [`#[start]`](#start-function) are
the only attributes that accept a guard.

## References

### Reference Types

A reference type is written `&type` (non-nullable) or `&?type` (nullable):

```wax
&type           // Non-nullable reference
&?type          // Nullable reference
```

`type` is either a declared type (a struct, array, [function](#function-types),
or [continuation](#stack-switching)) or one of WebAssembly's **abstract heap
types**. These form five disjoint subtype hierarchies; a reference to a type
accepts any reference to a type below it in the same tree (a `&any` accepts an
`&eq`, an `&i31`, a declared struct, and so on):

```
any     (internal / GC references)
└─ eq   (comparable with ==)
   ├─ i31
   ├─ struct
   │  └─ declared struct types
   └─ array
      └─ declared array types

func    (function references)
└─ declared function types

extern  (host references)

exn     (exceptions)

cont    (continuations)
└─ declared continuation types
```

Each hierarchy also has a **bottom** type, a subtype of everything in its tree
and inhabited only by `null`: `none` under `any`, `nofunc` under `func`,
`noextern` under `extern`, `noexn` under `exn`, and `nocont` under `cont`. So
`&any`, `&?extern`, and `&eq` are all valid reference types; see
[Types → Heap Types](correspondence.md#heap-types) for how each maps to
WebAssembly.

### Null

```wax
null            // Null reference (requires type context)
```

### Null Check

```wax
!ref            // True if ref is null
ref!            // Assert non-null (trap if null)
```

### Type Testing and Casting

```wax
val is &type    // Test if val is of type (returns i32)
val as &type    // Cast val to type (trap on failure)
```

Structs and arrays are WebAssembly GC heap types: a value of such a type is
always held through a reference (`&point`, `&bytes`, …), not inline.

### i31

An `i31` reference packs a 31-bit signed integer directly into a reference, with
no heap allocation. Box an `i32` with `as &i31`, and read it back with a signed
or unsigned cast:

```wax
x as &i31       // box an i32 (its low 31 bits) into a reference
r as i32_s      // read an &i31 back, sign-extended
r as i32_u      //   or zero-extended
```

`&i31` is a subtype of `&eq` and `&any`, so it can stand in wherever one of those
is expected.

## Structs

### Definition

A struct is a named record. Mark a field `mut` to allow assignment after
creation; a plain field is set only at creation time. A value of `type point`
is held as `&point`.

```wax,check
type point = { x: i32, y: i32 };
type mutable_point = { x: mut i32, y: mut i32 };
```

A field may also hold a packed storage type, `i8` or `i16`, stored in one or two
bytes rather than a full `i32`. Reading one back needs an explicit cast,
described under [Field Access](#field-access).

### Creation

`{T| …}` allocates a new struct of type `T` and yields a `&T`. Give every field
a value, or use `..` to default them all (each field type must have a zero/null
default):

```wax
{point| x: 10, y: 20}       // all fields given
{point| ..}                 // every field defaulted
```

The type name may be omitted in two cases. The first is when an expected type
supplies it: a `let`/`const` annotation, the surrounding struct or array type
(when the literal is a field value or an element), the parameter type of a
function being called (when it is an argument), or the result type of a function
or block. So `let p: &point = {x: 10, y: 20};` is equivalent to writing
`{point| …}`. Such an expectation also reaches into both
branches of a conditional `?:`, so a branch may omit the name (or default it
with `{..}`): `let p: &point = cond ? {x: 0, y: 0} : {..};`. The second is when
the **field set** names the type unambiguously: if exactly one struct type in
the module has that exact set of field names, it is inferred even with no
expected type:

```wax
fn origin() -> &eq {
    {x: 0, y: 0};               // inferred as &point from its fields
}
```

Field inference takes precedence over the expected type, so when the fields name
a subtype of the expected type, that subtype is used. The type must still be
given when the field set is ambiguous (several types share it) or absent (a
`{..}` default with no fields).

A field written as a bare name is **punned** to the like-named local or global:
`{x}` is shorthand for `{x: x}`. Punned and explicit fields mix freely, in any
order:

```wax
fn make(x: i32, y: i32) -> &point {
    {x, y: y + 1};              // same as {x: x, y: y + 1}
}
```

### Field Access

```wax
p.x                         // read a field
p.x = 42;                   // write a field (only if it is `mut`)
```

A packed (`i8`/`i16`) field is read as its raw bits, so accessing one needs an
explicit `as i32_s` (sign-extend) or `as i32_u` (zero-extend) cast; there is no
implicit widening. Storing to a packed field needs no cast, as the value is
truncated to the field width.

## Arrays

### Definition

```wax,check
type bytes = [i8];
type mutable_ints = [mut i32];
```

### Creation

```wax
[bytes| 0; 100]             // New array: 100 elements, all 0
[bytes| ..; 100]            // New array: 100 elements, default value
[bytes| 1, 2, 3, 4]         // New array with specific values
[bytes| seg @ 0; 100]       // New array from a segment (offset, count)
```

The last form builds the array from a named passive segment, copying `count`
elements starting at `offset`. For a numeric array, `seg` is a
[data segment](#data-segments) and this is `array.new_data`; for a reference
array it is an [element segment](#tables-and-element-segments) and the same
syntax is `array.new_elem`.

As with structs, the type name may be omitted when an expected type supplies it,
e.g. `let xs: &bytes = [0; 100];`.

### Element Access

```wax
arr[i]                      // Get element
arr[i] = val;               // Set element (if mutable)
arr.length()                // Array length
```

Bulk operations are method calls on the array:

```wax
arr.fill(idx, val, count)             // fill count elements from idx with val
arr.copy(idx, src, src_idx, count)    // copy from another array src
arr.init(seg, idx, src_idx, count)    // fill from a passive data/element segment
```

An element may be a packed storage type (`i8` or `i16`), like `bytes` above.
As with a [packed struct field](#field-access), reading one needs an explicit
`as i32_s`/`as i32_u` cast, while storing needs none.

## Recursive and Subtyped Types

Struct and array types can refer to one another, form subtype hierarchies, and
be left open for extension: the WebAssembly GC type features.

### Recursive Groups

Types that reference each other are declared together in a `rec { … }` group, so
each name is in scope for the others:

```wax,check
rec {
    type expr = { op: i32, args: &?args };
    type args = [mut &expr];
}
```

### Subtyping

`type sub : super` declares `sub` as a subtype of `super`: it repeats the
supertype's fields in order and may add more, and a `&sub` is accepted wherever
a `&super` is expected. Types are *final* by default; a type must be declared
`open` to be extended.

```wax,check
type shape = open { kind: i32 };
type circle : shape = { kind: i32, radius: f64 };

fn kind_of(s: &shape) -> i32 { s.kind; }   // also accepts a &circle
```

Since the inherited fields must be repeated verbatim, a leading `..` stands in
for them: it copies the supertype's field names and types, and the fields after
it are the subtype's additions. So `circle` above can be written to highlight
just its delta:

```wax,check
type shape = open { kind: i32 };
type circle : shape = { .., radius: f64 };
```

`..` must come first and appear once, and only where there is a supertype to
inherit from. An inherited field that is *renamed* or whose type is *refined*
(a covariant subtype) is no longer a verbatim copy, so it must be written out
explicitly rather than covered by `..`.

## Exact References and Descriptors

The [custom-descriptors proposal](https://github.com/WebAssembly/custom-descriptors)
adds two related features, enabled together with `-X custom-descriptors` (off by
default).

### Exact references

An **exact** reference points to values of exactly one concrete type, with no
subtypes. The exactness marker `!` goes between the `&`/`&?` sigil and the type
name, next to the nullability `?`:

```wax
&!point         // a non-null reference to exactly point
&?!point        // nullable, exactly point
```

Only a concrete (declared) type can be exact; `&!any` and other abstract heap
types are rejected. An exact reference is a subtype of the plain one, so an
`&!point` is accepted where an `&point` is expected, but exactness is invariant
across distinct concrete types. The `as` and `is` operators reach an exact type
explicitly:

```wax
x as &!point    // cast to an exact reference
x is &!point    // test for an exact type
```

Because `!` comes before the type name, it never clashes with the postfix
[non-null assertion](#null-check) `!`: `x as &!point` casts to an exact
reference, whereas `(x as &point)!` asserts the cast result is non-null.

A struct or array construction already yields an exact reference, since the new
object has exactly the allocated type, so a literal can go where an `&!point` is
expected without a cast. A module-defined function is likewise always exact; only
an **imported** function needs the marker to be treated as exact, written on the
declaration as `fn g: !ft;` (named type) or `fn h!(x: i32) -> i64;` (inline
signature). A plainly imported function is not exact, so a reference to it must
be cast to reach an exact type.

### Descriptors

A struct can carry a runtime *descriptor*: a second struct linked to it, handy
for modelling a runtime type or a vtable. The described type names its
descriptor with a `descriptor` clause, and the descriptor names what it
describes with a `describes` clause. The two are declared together in a `rec`
group:

```wax,check
rec {
    type obj = descriptor obj_desc { x: i32 };
    type obj_desc = describes obj { info: i32 };
}

#[export = "make"]
fn make(d: &!obj_desc) -> &obj {
    {descriptor(d)| x: 42};      // construct, supplying the descriptor
}

#[export = "describe"]
fn describe(o: &obj) -> &obj_desc {
    o.descriptor;                // read the descriptor back
}
```

Construction takes the descriptor as an **exact** reference (`&!obj_desc`).
Reading `.descriptor` gives an `&obj_desc`, or the exact `&!obj_desc` when the
value's own type is exact. A descriptor-based cast checks that a reference's
descriptor is a given one: `o as descriptor(d)`, or `as ?descriptor(d)` to allow
null. The [`br_on_cast` and `br_on_cast_fail`](#labels-and-branches) branches
accept the same `descriptor(d)` operand in place of a type
(`br_on_cast 'l descriptor(d) val`, with an optional `?` for the nullable form),
branching on that descriptor check. The reciprocity, finality and rec-group
rules the two types must satisfy are listed under
[Types → Custom Descriptors](correspondence.md#custom-descriptors).

## Strings

A string literal builds a new array and lowers to an `array.new_fixed`. The
element type must be `i8` or `i16`, and it decides the encoding:

- an `i8` array holds the raw bytes of the (UTF-8) text, one element per byte;
- an `i16` array holds the UTF-16 code units of the text, so it must be a valid
  Unicode string (a code point outside the basic plane becomes a surrogate pair,
  hence two elements).

By default its type is `[mut i8]`:

```wax
"hello";                    // a new [mut i8] holding the 5 bytes
```

As with [array](#arrays) and [struct](#structs) literals, a different array type
can be selected: either by prefixing the string with the type name and `#`, or
by an expected type from the context:

```wax
type chars = [i8];
type wide = [i16];

chars # "hi";               // a &chars, one i8 per UTF-8 byte
wide # "café";              // a &wide, one i16 per UTF-16 code unit
let s: &chars = "yo";       // type taken from the annotation
```

String literals recognise the same escapes as [character literals](#characters):
`\t`, `\n`, `\r`, `\'`, `\"`, `\\`, `\xNN` (two hex digits, one byte), and
`\u{...}` (a Unicode code point, encoded as its UTF-8 bytes):

```wax
"tab\tend";
"smile \u{1F600}";
```

A string also supplies the bytes of a [data segment](#data-segments).

A string literal round-trips faithfully through WAT, where it is written with a
`(@string …)` annotation. Through Wasm it is best-effort: the binary keeps only
the `array.new_fixed`, which is recovered as a string literal only when its
elements, decoded by the array's element type (UTF-8 for `i8`, UTF-16 for
`i16`), form a *reasonable* string: valid text with no control characters other
than tab, newline, and carriage return. Anything else (arbitrary binary data)
decompiles as an ordinary [array literal](#arrays) instead.

## SIMD (v128)

The 128-bit vector type is `v128`. Its operations are written as method
intrinsics with the lane shape baked into the name: the Wax name is the
WebAssembly mnemonic with the leading shape moved to the end, so `i32x4.add`
becomes `add_i32x4` and `f32x4.splat` becomes `splat_f32x4`. Signed/unsigned
variants keep their `_s`/`_u` suffix, and constant lane immediates (lane and
shuffle indices) come first in the argument list.

```wax,check
fn scale(v: v128, k: i32) -> v128 {
    v.add_i32x4(k.splat_i32x4());     // i32x4.add of v and (i32x4.splat k)
}

fn lane0(v: v128) -> i32 {
    v.extract_lane_i32x4(0);          // extract lane 0
}
```

Constants are `v128::` free functions, one argument per lane:

```wax,check
const ones: v128 = v128::i32x4(1, 1, 1, 1);
```

Memory accesses are methods on a [memory](#memories), named like the scalar
accesses with the access shape in the name (a widening load keeps its
`_s`/`_u` suffix, as the value ops do); the full-width pair takes the family
letter, `loadv128`/`storev128` (like `loadf32`/`storef32`):

```wax,check
memory buf: i32 [1];

fn sum2(p: i32) -> v128 {
    let v = buf.loadv128(p);                // v128.load
    let w = buf.load32x2_s(p, offset: 16);  // v128.load32x2_s
    buf.storev128(p, v);                    // v128.store
    v.add_i64x2(w);
}
```

See [Instructions › SIMD](correspondence.md#simd-vector-instructions) for the full
mnemonic mapping (`extract_lane`/`replace_lane`/`shuffle`, comparisons, shifts,
and the whole-vector `*_v128` operations).

## Memories

### Declaration

```wax,check
memory mem0: i32 [1, 1000];     // address type i32, min 1 page, max 1000
memory mem1: i64 [2];           // min 2 pages, no maximum
memory mem2: i32;               // size derived from data segments
```

A memory may declare a custom page size with a `pagesize` clause after its
limits. The page size is a byte count and must be `1` or `65536` (the default);
limits are then counted in pages of that size:

```wax,check
memory small: i32 [4096] pagesize 1;      // 4096 pages of 1 byte
memory mem3: i32 [1, 1000] pagesize 65536; // the default page size, explicit
```

A memory may be declared `shared` (the threads proposal), for use with atomic
accesses across threads. A shared memory must specify a maximum size:

```wax,check
memory pool: i32 [1, 16] shared;
```

### Atomics

Atomic memory operations are methods on a memory, following the same naming
convention as the plain [loads and stores](#load-and-store): the access width
is in the method name, the `i32`/`i64` value type comes from the operand and
result types, and a narrow load returns raw bits, resolved by an `as iN_u`
cast:

```wax,check
memory mem: i32 [1, 2] shared;

fn atomics(p: i32, v: i32, w: i64) -> i32 {
    _ = mem.atomic_load32(p);              // i32.atomic.load
    _ = mem.atomic_load8(p) as i32_u;      // i32.atomic.load8_u (zero-extend)
    _ = mem.atomic_load32(p) as i64_u;     // i64.atomic.load32_u
    mem.atomic_store16(p, v);              // i32.atomic.store16 (v is i32)
    mem.atomic_store16(p, w);              // i64.atomic.store16 (w is i64)
    _ = mem.atomic_rmw_add32(p, v);        // read-modify-write: the old value
    _ = mem.atomic_rmw_add16(p, w);        // i64.atomic.rmw16.add_u
    _ = mem.atomic_rmw_cmpxchg32(p, v, v); // compare-and-exchange
    _ = mem.atomic_wait32(p, v, w);        // wait: expected value and timeout
    mem.atomic_notify(p, 1);               // wake waiters: how many woke
}
```

A narrow atomic load zero-extends: there is no sign-extending form, so
`as iN_s` is rejected on it (use `as iN_u`, then `.extend8_s()`/`.extend16_s()`
if you need the sign; `atomic_load32(p) as i64_s` compiles as the plain
`i32.atomic.load` followed by `i64.extend_i32_s`). An atomic access must use
its natural alignment, the access width from the name. `atomic.fence`, which
has no memory operand, is written as the
[`atomic::fence()`](#qualified-intrinsics) intrinsic.

### Data Segments

```wax
memory mem1: i64 {
    data _ @ [0x1000] = "hello world";   // active, anonymous
    data greeting @ [0x2000] = "hi";     // active, named
}

data seg = "raw\x00bytes";               // top-level passive segment
data init @ mem0 [0] = "hello";          // top-level active segment
```

A segment's contents may concatenate (with `++`) string literals and **numeric
runs** — a bracketed list `[type: values]` whose element type is stated once
and whose values are packed little-endian — instead of hand-escaping every
byte:

```wax
data table = "hdr" ++ [f32: 0.2, 0.3, 0.4] ++ [i16: -1, -2] ++ [i8: 1, 2, 3, 4];
```

The scalar element types are `i8`, `i16`, `i32`, `i64`, `f32`, and `f64`; values
(including `nan`/`inf`) are ordinary literals. A `v128` run holds lane groups
written `shape(lanes)`:

```wax
data vectors = [v128: i32x4(1, 2, 3, 4), f64x2(1.0, 2.0)];
```

### Load and Store

```wax
mem0.load32(p)              // i32 load
mem0.load64(p)              // i64 load
mem0.load8(p) as i32_u      // narrow load, zero-extended
mem0.load16(p) as i32_s     // narrow load, sign-extended
mem0.load32(p) as i64_s     // load then widen to i64

mem0.store32(p, v);         // store (width by method, type by value)
mem0.store16(p, v);
mem0.store32(p, v, offset: 16, align: 1);
```

The optional `offset` and `align` of the access are labelled arguments
(constant integers), written after the operands in either order.

A `load8` or `load16` returns raw bits, so it needs an explicit `as i32_s`/`as i32_u`
(or `as i64_s`/`as i64_u`) cast to extend to the value type, as the lines above
show; `load32`/`load64` and the stores need none.

## Tables and Element Segments

A table holds references and is indexed like an array. Element segments declare lists of references, optionally initializing a table.

```wax
table funcs: &?func [1, 10];          // table of function references
elem init: &?func @ funcs[0] = [f];   // active: initialize funcs at offset 0
elem pool: &?func = [f, g, h];        // passive segment

funcs[i]                              // table.get
funcs[i] = g;                         // table.set
(funcs[i] as &cmp)(x, y)              // indirect call (call_indirect)
```

The table-management instructions are method calls on the table (and `drop` on
an element segment):

```wax
funcs.size()                          // current size
funcs.grow(init, n)                   // grow by n, filling with init; returns the old size
funcs.fill(dst, val, n)               // set n slots from dst to val
funcs.copy(dst, src, n)               // copy n slots within the table
funcs.init(pool, dst, src, n)         // copy n refs from element segment pool
pool.drop();                          // drop a passive element segment
```

A passive element segment initializes a GC array of references with the same `[t| seg @ off; count]` form used for data segments; a reference element type selects the element segment:

```wax
[handlers| pool @ 0; 3]               // array.new_elem
```

## Exceptions

### Tags

A tag declares an exception, optionally carrying a payload. The parameter list
is required; write `()` for no payload:

```wax,check
tag stop();                 // no payload
tag overflow(i32);          // carries an i32
tag pair(i32, f64);         // carries several values
```

A tag may also declare a **result type**, written like a function signature.
This is used by [stack switching](#stack-switching): resuming a suspended
continuation hands this value back to the `suspend` expression.

```wax,check
tag yield(i32) -> i32;      // carries an i32; resumes with an i32
```

### Throw

`throw` raises a tag together with its payload:

```wax
throw overflow(42);
```

### Try / Catch

A `try` runs its body and routes a matching thrown tag to a catch arm,
compiling to WebAssembly's standard `try_table` plus a block ladder. Like a
block it may carry a result type (`try i32 { … }`). An arm enters with the
caught tag's payload on the operand stack, picked up with [holes](#holes) `_`;
a `tag & => { … }` arm also delivers the exception reference (`&exn`) above
the payload, and a bare `_ => { … }` (or `_ & => { … }`) matches any
exception, grammar-enforced last. Leave the catch-all out to let unmatched
exceptions propagate.

Like `dispatch` and `match`, the arms are honest trailing code in clause
order:

- the body's normal completion **escapes past all arms**, supplying the try's
  value (one implicit branch);
- an arm's completion **falls into the next arm** — its completion stack must
  match that arm's entry (payload, plus `&exn` for a `&` arm) — and the last
  arm's completion supplies the try's value;
- diverging arms (`throw`, `return`, `become`, a `br` out) are exempt, as
  usual.

An early arm that produces the result escapes explicitly through a label on
the try: the label is the join, so branching to it exits the try carrying the
value, block-like. (In expression position no label can prefix the try, so
such an arm must diverge, or the code restructures.)

```wax
fn lookup(k: i32) -> i32 {
    't: try i32 {
        find(k);                     // may throw `overflow` or `timeout`
    } catch {
        overflow => { br 't _; }     // `_` is the thrown i32 payload
        timeout & => { _ = _; br 't (0 - 1); }  // drop the &exn, escape
        _ => { 0; }                  // catch-all supplies the value
    }
}
```

The fall-through makes the *normalize, then handle* idiom direct — the first
arm's completion **is** the next arm's payload, with no re-throw:

```wax
let res: &eq = try &eq {
    apply(f);
} catch {
    javascript_exception => { wrap_exception(_); }  // normalize; falls through
    ocaml_exception => { _; }                       // handle either
};
```

### Branching handlers (try_table)

The low-level spelling branches to a label instead of running an inline arm,
mapping one-to-one to a raw `try_table`:

```wax
try { might_throw(); } catch [overflow -> 'h]    // on `overflow`, branch to 'h
try { might_throw(); } catch [overflow & -> 'h]  // also deliver the exnref
try { might_throw(); } catch [_ -> 'h]           // catch any exception
```

The target label receives the payload (and, with `&`, the exception reference,
of type `&exn`, or `&?exn` for the nullable form), so the labelled block's type
must match what it is handed. Braced arms are the same clauses with the
target blocks written inline.

### Legacy exceptions (try_legacy)

`try_legacy` compiles to the deprecated `try`/`catch` instructions, kept for
targets that still use the legacy exception proposal. Its arms have the old
semantics — each arm independently produces the try's result (no fall-through,
no `&` forms):

```wax
try_legacy i32 { find(k); } catch { overflow => { _; } _ => { 0; } }
```

## Stack Switching

*Stack switching* (the WebAssembly typed-continuations proposal) lets a
computation suspend itself, yield control to a scheduler, and later be resumed.
A **continuation type** wraps a function type with `cont`:

```wax,check
type task = fn(i32) -> i32;
type k = cont task;
```

A [tag with a result type](#tags) is the suspend/resume channel: `suspend`
passes the tag's payload out and evaluates to its result once resumed.

```wax,check
tag yield(i32) -> i32;

fn worker(x: i32) -> i32 {
    suspend yield(x);          // yield `x`; the result is what resumes it
}
```

A continuation is created with the `T::new` constructor of its declared type
(the `T::` namespace constructs a `&T`, extending the `v128::`/`i64::`
qualified-intrinsic pattern), and driven with the `resume`, `resume_throw` and
`resume_throw_ref` methods on the continuation reference. `T::bind` binds
leading arguments away, yielding a `&T`; its source type, like the type
immediate of the resume methods, is inferred from the continuation operand's
static type — the call_ref model, so the receiver must have a *declared*
continuation type.

Continuations carry no runtime type information, so `as` with a continuation
target is a *compile-time ascription*, not a cast: it is accepted exactly when
it is a provable no-op — the operand's type is already a subtype of the target
(`(c as &k0).resume(x)` resumes through the supertype signature, selecting the
`resume $k0` immediate), a `null` literal with a nullable target, or dead code
the ascription pins — and it compiles to no instruction. A `&cont` can never
be *narrowed*: an abstract reference cannot be resumed, and no cast can fix it,
so give the value its precise type where it is introduced (a parameter, local
or block-result annotation). `is` and `br_on_cast` reject continuation targets
outright (they are inherently runtime tests).

```wax
type unit_task = fn() -> i32;
type k0 = cont unit_task;

fn spawn() -> &k { k::new(worker); }        // wrap `worker` (a task)
fn prime(c: &k) -> &k0 { k0::bind(7, c); }  // bind the argument
fn go(c: &k0) -> i32 { c.resume(); }        // run until it suspends
```

Handlers routing a suspended tag to a label are a postfix `on` clause on the
call, a bracket of `tag -> 'label` or `tag -> switch` arms (the same shape and
placement as `try { … } catch [t -> 'l]`), omitted when empty:

```wax
c.resume(x) on [yield -> 'on_yield]
```

The abstract continuation heap types are written `&cont` and `&nocont` (with
`&?cont` for the nullable form).

`c.switch(args, tag: t)` hands control straight to another continuation `c`
instead of suspending back to a handler, passing `args` and the current
continuation; the enabling tag is the required labelled `tag:` immediate, and
the `resume` that drives things enables it with a `t -> switch` arm in its
handler list.

The receiver of these methods compiles *last*: operands compile in the
instruction's stack order, which for continuations — as for `call_ref` — puts
the receiver after the arguments.

## Holes

A hole (`_`) is a placeholder for a value that an **earlier statement in the
same sequence** has left on WebAssembly's implicit operand stack. It is the
surface syntax for that stack flow: rather than naming an intermediate value,
you leave a hole where it should be plugged in.

```wax,check
fn example() -> i32 {
    1; 2; _ + _;    // Equivalent to: let a = 1; let b = 2; a + b
}
```

Here the statements `1` and `2` each push a value; the two holes in `_ + _`
consume them.

**How many, and in what order.** The number of holes in an expression is the
number of stack values it pulls in. They are filled **left-to-right with the
stack values in the order those values were produced**: the earliest value
fills the leftmost hole. Order therefore matters for non-commutative
operators:

```wax,check
fn diff() -> i32 {
    10; 20; _ - _;    // 10 - 20, not 20 - 10
}
```

A single hole is common when combining one stacked value with an explicit
operand:

```wax,check
fn add_one(x: i32) -> i32 {
    x; _ + 1;
}
```

**Holes must come first.** Within an expression, every hole must precede (in
evaluation order) any explicit value-producing operand. Once a non-hole operand
appears, no further holes may follow it. Explicit operands *after* all the holes
are fine:

```wax,check
fn ok() -> i32 {
    1; 2; _ + _ + 3;    // OK: the literal 3 comes after both holes
}
```

but an explicit operand wedged *before* an unfilled hole is rejected:

```wax
fn bad() -> i32 {
    2; 3; _ + 3 + _;    // Error: This expression occurs before a hole '_'.
}
```

This restriction keeps holes unambiguous: they always refer to values already on
the stack, never to operands appearing later in the expression.

**Not every position accepts a hole.** The scrutinee of a
[`match`](#match), the index of a [`dispatch`](#dispatch), and the condition of a
[`while`](#while-loops) cannot be a hole. Each of these desugars to a
nested block structure, and a hole inside a block draws only from that block's
own stack, not from the values pending in the enclosing sequence, so there is
nothing there for it to pick up:

```wax
fn bad(x: &any) {
    x; match _ { … }    // Error: A hole '_' cannot be used as a 'match' scrutinee.
}
```

When decompiling Wasm or WAT back to Wax, the compiler introduces holes wherever
an instruction takes an operand from the stack instead of from a nested
sub-expression, so this same mechanism round-trips stack-style code.

## Conditional Compilation

Top-level items can be guarded by conditions, using a Rust-like attribute syntax. `#[if(<condition>)] { ... }` keeps the braced items only when `<condition>` holds; an optional `#[else] { ... }` provides an alternative. The braces are required:

```wax,check
#[if(ocaml_version >= (5, 1, 0))]
{
    const caml_marshal_header_size: i32 = 16;
}
#[else]
{
    const caml_marshal_header_size: i32 = 20;
}
```

A condition is one of:

- a **boolean variable**, e.g. `debug`;
- a **comparison** `variable op literal`, where `op` is `=`, `!=`, `<`, `<=`, `>` or `>=`, and the literal is either a **version** tuple `(major, minor, patch)` or a **string** `"..."`:

  ```text
  feature = "gc"
  ocaml_version >= (5, 1, 0)
  ```

- a **combination** built with `all(...)` (conjunction), `any(...)` (disjunction) or `not(...)` (negation), nested arbitrarily:

  ```text
  all(debug, not(target = "wasm32"))
  ```

A branch groups any number of items, so several can be guarded at once:

```wax,check
#[if(debug)]
{
    const debug_enabled: i32 = 1;
    fn debug_log(msg: i32) {
        // ...
    }
}
```

The same `#[if(...)] { ... }` / `#[else] { ... }` form also guards **statements** inside a function body:

```wax,check
fn size() -> i32 {
    #[if(debug)]
    {
        return 16;
    }
    #[else]
    {
        return 20;
    }
}
```

These two are the only levels at which conditional compilation applies: whole module items and whole statements. A condition cannot guard part of an expression. The one finer-grained case is the `if <condition>` guard on an [`#[export]`](#imports-and-exports) or [`#[start]`](#start-function), which makes a single export (or the start) conditional without wrapping its definition in an `#[if]` block; its condition is simplified against any enclosing `#[if]` and resolved by `-D` just like a block condition.

A statement-level branch cannot introduce a local with `let`, since the two branches are mutually exclusive and a binding made in one would not be in scope after the conditional. Declare the local before the conditional and assign to it inside each branch instead:

```wax,check
fn size() -> i32 {
    let s: i32;
    #[if(debug)]
    {
        s = 16;
    }
    #[else]
    {
        s = 20;
    }
    return s;
}
```

The conditions are **not evaluated** by the compiler; they are preserved for a downstream preprocessor. The `#[if]` and `#[else]` branches are **mutually exclusive** (they never coexist), so, for instance, the same name may be defined in both.

Variables can be given values on the command line with [`-D`/`--define`](cli.md), which specializes the conditionals: a condition that becomes fully determined causes its conditional to be removed (the surviving branch is spliced in), and one that still mentions unset variables is kept with its condition simplified. For example, `wax -D debug=true` turns `#[if(all(debug, target = "wasi"))]` into `#[if(target = "wasi")]`, and `wax -D debug=false` removes that conditional altogether.

When type checking is enabled (`--validate`), every reachable combination of conditions is checked independently. Because branches are mutually exclusive, a name defined in both the `#[if]` and `#[else]` branch is accepted. An error that occurs only under some conditions is reported together with the assumption that makes it reachable:

```
Error: This instruction has type float but is expected to have type i32.
 ──➤  example.wax:4:16
Hint: reachable when not debug
```


<!-- docs/src/features.md -->

# Feature Support

Wax works across all three formats (Wax, WAT, Wasm) and targets recent
WebAssembly proposals, several of them **on by default**, that most toolchains
still gate. This page summarises what the toolchain accepts and produces.

## On by default

Wax fully supports the **WebAssembly 3.0** standard: garbage collection
(WasmGC), exception handling (`try_table`), tail calls, multiple memories,
64-bit memory (memory64), reference types, bulk memory, and SIMD (including
relaxed SIMD).

On top of that, it enables these further proposals by default:

| Proposal | In Wax |
|----------|--------|
| Stack switching (typed continuations) | `cont`, `suspend`, `resume`, … |
| Threads / atomics | shared memory, atomic loads/stores/RMW, `atomic::fence()` |
| Wide arithmetic | 128-bit integer ops (e.g. `i64::add128`) |
| Branch hinting | `#[likely]` / `#[unlikely]` |
| [Compilation hints](https://github.com/WebAssembly/compilation-hints) | `#[freq = n]` / `#[never_opt]` / `#[always_opt]`, `#[targets(f: 0.73)]`, `#[priority = n]` / `#[optimization = n]` / `#[run_once]` |
| Custom page sizes | `pagesize` |
| [Extended name section](https://github.com/WebAssembly/extended-name-section) | `$`-identifiers for types, tables, memories, globals, data/element segments, fields, and labels survive the binary round-trip |
| [WAT numeric values](https://github.com/WebAssembly/wat-numeric-values) | typed numeric runs in [data segments](language.md#data-segments) (`data d = [i16: -1, 2] ++ [f32: 0.5, nan] ++ [v128: i32x4(1,2,3,4)];`); runs survive the wax↔wat round-trip |

## Enabled with `-X`

Off by default; turn one on with `-X NAME` (see the [CLI reference](cli.md)):

| Feature | What it adds |
|---------|--------------|
| `custom-descriptors` | exact reference types, descriptor structs, and the descriptor instructions (`descriptor` / `describes`) |
| `compact-import-section` | writes same-module imports under one module name in the binary import section. From a text input it lowers a `import "m" { … }` block / `(import "m" (item …) …)` group to a compact entry (a shared-type group when the items' types match, else one type per item; a one-item block flattens; separate imports are never merged). From a binary input it coalesces runs of consecutive same-module plain imports. Groups written explicitly (in WAT, or already present in a binary) round-trip regardless of the flag |

## Not supported

| Feature | Notes |
|---------|-------|
| Legacy `delegate` / `rethrow` | rejected on input. The rest of legacy exception handling (`try`/`catch`/`catch_all`) *is* supported: it has dedicated Wax syntax (`try { … } catch { … }`) and round-trips through the legacy binary opcodes |
| Component Model | |

### A deliberate relaxation

A tag may carry a **result type**: `tag yield(i32) -> i32`. The MVP requires
tags to have empty results; the stack-switching proposal lifts that (a suspended
tag resumes with a value), so Wax permits it on purpose. See
[Stack Switching](language.md#stack-switching).
