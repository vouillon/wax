# Wax and WebAssembly correspondence

How each WebAssembly construct is written in Wax, assembled from the
correspondence chapter of the documentation: types, instructions, module
fields, and round-tripping guarantees.


<!-- docs/src/correspondence/intro.md -->

# Introduction

This guide documents the correspondence between WebAssembly (Wasm) and Wax constructs. It is intended for developers who are familiar with Wasm and want to understand how Wax maps to it.

## High-level differences

Wax is an expression-oriented language, whereas Wasm is stack-oriented. However, Wax constructs map very closely to Wasm instructions, often one-to-one or with simple desugaring. Decompiling a module and recompiling it reproduces the original; see [Round-Tripping](correspondence.md) for what is preserved exactly and the few inert divergences.

Key differences:
- **Expressions vs Stack**: Wax uses variables (`let`) and nested expressions instead of explicit stack manipulation (`local.get`/`set`, `drop`).
- **Control Flow**: Wax uses structured control flow (`if`, `loop`, `do`, `try`) that resembles high-level languages but maps directly to Wasm structured control instructions.
- **Types**: Wax types define a direct mapping to Wasm types, with a slightly more concise syntax.
- **Modules**: Wax modules group imports under an `import "module" { … }` block and mark exports with an `#[export]` attribute on the field itself, rather than using separate import/export definitions.

## Extensions to WAT

Wax understands a few non-standard annotations in WAT. They reuse the standard `(@name …)` annotation syntax, but Wax gives them a meaning a stock WAT tool would not, so WAT that uses them round-trips only through Wax:

- **Literals**: `(@char "c")` and `(@string $t "…")` are character and string literals. `(@char …)` stands in for the `i32.const` of a code point; `(@string …)` for the `array.new_fixed` that builds an `i8` or `i16` array. They round-trip through WAT, but a Wasm binary keeps only the underlying instructions. See [Literals](correspondence.md#literals). Use [`--desugar`](cli.md#options) to expand them into plain wasm.
- **Conditional compilation**: `(@if <cond> (@then …) (@else …))` guards a module field by a condition that a downstream preprocessor resolves. It is the WAT counterpart of Wax's `#[if]`. See [Conditional Annotations](correspondence.md#conditional-annotations). Resolve conditions with [`-D`](cli.md#options); an unresolved `(@if …)` makes `--desugar` fail.


<!-- docs/src/correspondence/types.md -->

# Types

Wax types map directly to WebAssembly types.

## Value Types

| Wasm | Wax | Notes |
|------|-----|-------|
| `i32` | `i32` | 32-bit integer |
| `i64` | `i64` | 64-bit integer |
| `f32` | `f32` | 32-bit float |
| `f64` | `f64` | 64-bit float |
| `v128` | `v128` | 128-bit vector |
| `(ref null <ht>)` | `&?<ht>` | Nullable reference to heap type `<ht>` |
| `(ref <ht>)` | `&<ht>` | Non-nullable reference to heap type `<ht>` |
| `(ref (exact <t>))` | `&!<t>` | Reference to *exactly* concrete type `<t>` |
| `(ref null (exact <t>))` | `&?!<t>` | Nullable reference to exactly `<t>` |

Exact references (`&!<t>` / `&?!<t>`, gated on `-X custom-descriptors`) are
explained in the [language guide](language.md#exact-references).

## Storage Types

Storage types are used in fields of structs and arrays to define packed data.

| Wasm | Wax | Notes |
|------|-----|-------|
| `i8` | `i8` | 8-bit integer (packed) |
| `i16` | `i16` | 16-bit integer (packed) |

Any [value type](#value-types) is also a valid storage type; `i8` and `i16` are
the additional packed types available only in struct and array fields.


## Heap Types

| Wasm | Wax |
|------|-----|
| `func` | `func` |
| `extern` | `extern` |
| `any` | `any` |
| `eq` | `eq` |
| `struct` | `struct` |
| `array` | `array` |
| `i31` | `i31` |
| `exn` | `exn` |
| `cont` | `cont` |
| `noextern` | `noextern` |
| `nofunc` | `nofunc` |
| `noexn` | `noexn` |
| `nocont` | `nocont` |
| `none` | `none` |
| `<typeidx>` | `<identifier>` |

## Composite Types

### Structs
```wax,check
type point = { x: i32, y: i32 };
type mutable_point = { x: mut i32, y: mut i32 };
```
Maps to Wasm `(type $point (struct (field i32) (field i32)))`.

### Arrays
```wax,check
type bytes = [i8];
type mutable_bytes = [mut i8];
```
Maps to Wasm `(type $bytes (array i8))`.

### Functions
```wax,check
type binop = fn(i32, i32) -> i32;
```
Maps to Wasm `(type $binop (func (param i32 i32) (result i32)))`.
### Continuations
A continuation type (from the [stack-switching proposal](https://github.com/WebAssembly/stack-switching)) wraps a function type:
```wax,check
type ft = fn(i32) -> i32;
type k = cont ft;
```
Maps to Wasm `(type $k (cont $ft))`. See [Stack Switching Instructions](correspondence.md#stack-switching-instructions) for the operations on continuations.

`cont` and `nocont` are reserved heap types (like `func`/`struct`), so the abstract continuation references `&cont`, `&?cont` and `&nocont` are available directly in addition to references to declared continuation types (`&k`, `&?k`). Because these names are reserved, a WebAssembly type literally named `$cont` is renamed (e.g. to `cont_2`) when decompiling to Wax.

### Recursive Types

Wax allows defining recursive reference types using `rec { ... }`.

```wax,check
rec {
    type tree = { value: i32, children: &forest };
    type forest = [&?tree];
}
```

### Supertypes and Finality

Types are final by default. To make a type open (extensible), use the `open` keyword.
To specify a supertype, use `: supertype` before the assignment.

```wax,check
type point = { x: i32, y: i32 };                  // final by default
type open_point = open { x: i32 };                // non-final: extensible
type sub_point : open_point = { x: i32, y: i32 }; // extends open_point
```

A subtype repeats its supertype's fields in order; a leading `..` abbreviates
that repeated prefix (`type sub_point : open_point = { .., y: i32 };`). There is
no Wasm counterpart (every Wasm struct lists all its fields), so `..` is
expanded on the way to Wasm. Decompiling reverses it: when a subtype's leading
fields exactly match (name and type) its supertype's, they are collapsed back to
`..`. A renamed or covariantly-refined inherited field does not match, so it is
kept explicit.

### Custom Descriptors

The [custom-descriptors proposal](https://github.com/WebAssembly/custom-descriptors)
lets a struct carry a *descriptor*: a second struct associated with it (used, for
instance, to model a runtime type or vtable). The described type names its
descriptor with a `descriptor <name>` clause, and the descriptor names what it
describes with a `describes <name>` clause. Both clauses sit between the `open`
marker and the struct body:

```wax,check
rec {
  type obj = descriptor obj_desc { x: i32 };
  type obj_desc = describes obj { };
}
```

Maps to Wasm:

```wat,check
(rec
  (type $obj (descriptor $obj_desc) (struct (field $x i32)))
  (type $obj_desc (describes $obj) (struct)))
```

The two types must satisfy several well-formedness rules, all checked during
validation:

- both must be **structs**, declared in the **same `rec` group**;
- the clauses must be **reciprocal**: if `obj` names `obj_desc` as its
  descriptor, then `obj_desc` must describe `obj`;
- a described type must be declared **before** its descriptor;
- the two must **agree on finality**: both `open`, or neither. An open type with
  a final descriptor could never be extended, since a subtype of it would need a
  descriptor extending a final type, and a final type with an open descriptor
  leaves that descriptor with no possible subtypes either;
- in a subtype hierarchy, a type has a descriptor exactly when its declared
  supertype does (with a descriptor that is itself a subtype), and a described
  type is inherited covariantly.


<!-- docs/src/correspondence/instructions.md -->

# Instructions

Wax instructions are expression-oriented.

## Literals

A [character literal](language.md#characters) is an `i32` constant (its
Unicode code point); a [string literal](language.md#strings) builds an `i8`
or `i16` array with `array.new_fixed`. An `i8` array holds the raw UTF-8 bytes;
an `i16` array holds the UTF-16 code units (so the string must be valid Unicode).

| Wasm | Wax |
|------|-----|
| `i32.const <code point>` | `'c'` |
| `array.new_fixed $t` (constant elements) | `"..."` or `t # "..."` |

In WAT both forms are written with annotations (`(@char …)` and `(@string …)`),
so they round-trip faithfully through WAT. A Wasm binary keeps only the
underlying `i32.const` / `array.new_fixed`: a character decompiles to a plain
integer, and an `array.new_fixed` is recovered as a string only when its
elements, decoded by the array's element type (UTF-8 for `i8`, UTF-16 for
`i16`), form a reasonable string (valid text, no control characters other
than tab/newline/carriage return); otherwise it stays an
[array literal](#aggregate-instructions).

## Numeric Instructions

Binary and unary operations use standard mathematical operators. Signedness is often explicit in the operator.

| Wasm | Wax |
|------|-----|
| `i32.add` / `i64.add` | `+` |
| `i32.sub` / `i64.sub` | `-` |
| `i32.mul` / `i64.mul` | `*` |
| `i32.div_s` / `i64.div_s` | `/s` |
| `i32.div_u` / `i64.div_u` | `/u` |
| `i32.rem_s` / `i64.rem_s` | `%s` |
| `i32.rem_u` / `i64.rem_u` | `%u` |
| `i32.and` / `i64.and` | `&` |
| `i32.or` / `i64.or` | `\|` |
| `i32.xor` / `i64.xor` | `^` |
| `i32.shl` / `i64.shl` | `<<` |
| `i32.shr_s` / `i64.shr_s` | `>>s` |
| `i32.shr_u` / `i64.shr_u` | `>>u` |
| `i32.eqz` / `i64.eqz` | `!x` (logical not) |

### Floating Point Operations

| Wasm | Wax |
|---|---|
| `f32.add` / `f64.add` | `+` |
| `f32.sub` / `f64.sub` | `-` |
| `f32.mul` / `f64.mul` | `*` |
| `f32.div` / `f64.div` | `/` |
| `f32.abs` ... `f64.sqrt` | `val.abs()`, `val.ceil()`, `val.floor()`, `val.trunc()`, `val.nearest()`, `val.sqrt()` |
| `f32.min` ... `f64.copysign` | `v1.min(v2)`, `v1.max(v2)`, `v1.copysign(v2)` |

### Advanced Integer Operations

| Wasm | Wax |
|---|---|
| `i32.clz` ... `i64.popcnt` | `val.clz()`, `val.ctz()`, `val.popcnt()` |
| `i32.extend8_s` ... `i64.extend16_s` | `val.extend8_s()`, `val.extend16_s()` |
| `i32.rotl` ... `i64.rotr` | `v1.rotl(v2)`, `v1.rotr(v2)` |

### Wide Arithmetic

These 128-bit operations take and return their operands as `(low, high)` pairs
of `i64` values, so each is written as a call returning two results (typically
bound with a multi-value `let`).

| Wasm | Wax |
|---|---|
| `i64.add128` | `i64::add128(a_lo, a_hi, b_lo, b_hi)` |
| `i64.sub128` | `i64::sub128(a_lo, a_hi, b_lo, b_hi)` |
| `i64.mul_wide_s` | `i64::mul_wide_s(a, b)` |
| `i64.mul_wide_u` | `i64::mul_wide_u(a, b)` |



### Conversions

| Wasm | Wax |
|---|---|
| `i32.wrap_i64` | `val as i32` |
| `i64.extend_i32_s` | `val as i64_s` |
| `i64.extend_i32_u` | `val as i64_u` |
| `i32.trunc_f32_s` | `val as i32_s` |
| `f32.convert_i32_s` | `val as f32_s` |
| `f32.demote_f64` | `val as f32` |
| `f64.promote_f32` | `val as f64` |
| `i32.reinterpret_f32` | `val.to_bits()` |
| `f32.reinterpret_i32` | `val.from_bits()` |

## Comparison

| Wasm | Wax |
|------|-----|
| `eq` | `==` |
| `ne` | `!=` |
| `lt_s` / `lt` | `<s` / `<` |
| `lt_u` | `<u` |
| `le_s` / `le` | `<=s` / `<=` |
| `le_u` | `<=u` |
| `gt_s` / `gt` | `>s` / `>` |
| `gt_u` | `>u` |
| `ge_s` / `ge` | `>=s` / `>=` |
| `ge_u` | `>=u` |

On reference operands (any subtype of `&eq`), `==` and `!=` are reference
equality: `a == b` is `ref.eq`, and `a != b` is `ref.eq` followed by `i32.eqz`
(there is no `ref.ne` instruction).

## Variable Instructions

| Wasm | Wax |
|------|-----|
| `local.get $x` | `x` |
| `local.set $x` | `x = val` |
| `local.tee $x` | `x := val` |
| `global.get $g` | `g` |
| `global.set $g` | `g = val` |
| `(local $x t)` | `let x : t` |

When an expression leaves several values on the stack (typically a call to a
[multi-result function](language.md#variables)) and a run of `local.set`
instructions immediately stores them into locals, the two collapse into a single
multi-binding `let`. A `drop` of one of the results becomes a `_` binding:

```
(call $divmod ...)      let (q, r) = divmod(...);
(local.set $r)
(local.set $q)
```

The number of stores folded is exactly the producer's result arity, so a
`local.set` that consumes a value already on the stack below the call is left as
its own assignment.

A [compound assignment](language.md#assignment) `x op= val` is shorthand for
`x = x op val`; it lowers to a `local.get`/`global.get` of `x`, the operand, the
binary operator, and a `local.set`/`global.set` back into `x`. The reverse
direction recognises exactly this shape (a `set` of `x` whose value is a binary
operator with `x` as its *left* operand) and reconstructs the compound form
(`x = x + 1` becomes `x += 1`). A comparison, or `x` in the right operand
(`x = 1 - x`), is left as an ordinary assignment.

## Control Instructions

| Wasm | Wax |
|------|-----|
| `block` | `do { ... }` or `{ ... }` |
| `loop` | `loop { ... }` |
| `loop` + leading back-`br` idiom | `while cond { ... }` |
| `loop { if c { block 'l {...}; step; br } }` | `'l: while c : (step) { ... }` (continue-expression) |
| `loop` + trailing back-`br_if` idiom | `loop { ... br_if 'l cond; }` (kept as a plain loop) |
| `if ... else ...` | `if cond { ... } else { ... }` |
| `br $l` | `br 'l` |
| `br_if $l` | `br_if 'l cond` |
| `br_table $l* $ld` | `br_table ['l1, 'l2, else 'ld] val` |
| `br_on_null $l` | `br_on_null 'l val` |
| `br_on_non_null $l` | `br_on_non_null 'l val` |
| `br_on_cast $l $t1 $t2` | `br_on_cast 'l t2 val` |
| `br_on_cast_fail $l $t1 $t2` | `br_on_cast_fail 'l t2 val` |
| `br_on_cast_desc_eq $l $t1 $t2` | `br_on_cast 'l [?]descriptor(d) val` |
| `br_on_cast_desc_eq_fail $l $t1 $t2` | `br_on_cast_fail 'l [?]descriptor(d) val` |
| `return` | `return val` |
| `call $f` | `f(args)` |
| `call_ref $t` | `(val as &?t)(args)` |
| `return_call $f` | `become f(args)` |
| `return_call_ref $t` | `become (val as &?t)(args)` |
| `unreachable` | `unreachable` |
| `nop` | `nop` |
| `select` | `cond ? v1 : v2` |
| `drop` | `_ = val` |

A `drop` becomes an assignment to `_`, an anonymous binding that evaluates its
value and discards it (see [Discarding a value](language.md#discarding-a-value)).
When the dropped value is a bare numeric expression whose width the Wax syntax
would not otherwise carry, the conversion pins it with a type annotation,
`_: t = val`, so re-reading the Wax does not re-default the value to `i32`/`f64`
and silently change its width. The annotation is emitted only where it is
load-bearing; a value already anchored by a typed sub-expression (a local, a
call) needs none.

The rows above are the raw instructions. Two common *shapes* built from them are
recovered as higher-level constructs on the way back to Wax: a `br_table` in the
conventional dense void-switch shape becomes a [`dispatch`](#dispatch-and-match),
and a `br_on_cast`/`br_on_null` ladder becomes a [`match`](#dispatch-and-match)
(both below).

### Block Labels and Types

Blocks, loops, and ifs can be labeled and typed.
Labels are identifiers starting with `'` followed by a colon.

```wax
'my_block: do { ... }
'my_loop: loop { ... }
```

Block types (signatures) can be specified using `(param) -> result` syntax or a single value type.
If no type is specified, the `do` keyword is optional.

```wax
do (i32) -> i32 { ... }
do i32 { ... }
{ ... }                  ;; equivalent to do { ... }
if cond => (i32) -> i32 { ... } else { ... }
```

A single result type can be **inferred**, so converting from WebAssembly drops
it wherever it is redundant: a `do i32 { ... }` becomes `do { ... }`, an
`if cond => i32 { ... }` loses its `=> i32`, and likewise for `loop`, `try`, and
`try_table`. The type is recovered when reading the Wax back, from the values
reaching the block's exit or from the surrounding context (see
[Type inference](language.md#blocks)). Parameterized and multi-result block
types are always kept.

### Branch Hints

The [branch-hinting proposal](https://github.com/WebAssembly/branch-hinting)
annotates a conditional branch as likely or unlikely taken. Wax writes the hint
as an attribute on the branch and preserves it on every round-trip (it is stored
in the `metadata.code.branch_hint` custom section; no feature flag is needed):

```wax
#[likely] if cond { ... } else { ... }
#[unlikely] br_if 'l cond
```

Any conditional branch may be hinted: `if`, `br_if`, `br_on_null`,
`br_on_non_null`, `br_on_cast`, and `br_on_cast_fail`. In WAT the same hint is
the `(@metadata.code.branch_hint "\00"|"\01")` annotation preceding the branch
(`"\01"` = likely, `"\00"` = unlikely).

The [compilation-hints proposal](https://github.com/WebAssembly/compilation-hints)
adds two more sections of the same family, addressed the same way — by the
instruction's byte offset from the start of the function body — and likewise
preserved with no feature flag:

| Wax | WAT | Section |
|-----|-----|---------|
| `#[freq = n]` | `(@metadata.code.instr_freq (freq n))` | `metadata.code.instr_freq` |
| `#[never_opt]` | `(@metadata.code.instr_freq (never_opt))` | " |
| `#[always_opt]` | `(@metadata.code.instr_freq (always_opt))` | " |
| `#[targets(f: 0.73)]` | `(@metadata.code.call_targets (target $f 0.73))` | `metadata.code.call_targets` |
| `#[priority = n]` | `(@metadata.code.compilation_priority (priority n))` | `metadata.code.compilation_priority` |
| `#[optimization = n]` | `… (optimization n)` | " |
| `#[run_once]` | `… (run_once)` | " |

`instr_freq` is one byte: an offset base-2 logarithm of the executions-per-call
ratio, `max 1 (min 64 (floor (log2 r) + 32))`, so `32` means once. `0` is
`never_opt` and `127` is `always_opt`. A byte outside `{0, 127} ∪ [1, 64]` — only
reachable from a hand-written binary — stands for no ratio, so WAT prints it in the
raw-byte form `(@metadata.code.instr_freq "\NN")`, which Wax has no spelling for.
Both text forms are accepted on input, per the proposal.

`call_targets` holds LEB128 `(function index, percentage)` pairs. Both text surfaces
write the frequency as a fraction of 1 and store the whole percent, so the round-trip
is exact. Only the structured `(target …)` form can *name* a target; the raw-byte
form's indices are numeric.

`compilation_priority` is the one section of the family that addresses a *function*
rather than an instruction, so its entries are keyed at offset `0`. Its payload is a
compilation priority, optionally followed by an optimization priority; `127` is the
"runs once" value that prints as `(run_once)`. (The proposal's prose gives 127; its
own worked example renders the value as 31. We follow the prose, and a binary
carrying 31 round-trips as the plain number it is.) A trailing byte beyond what is
required is read past and ignored, per the proposal's forward-compatibility rule.

Each section is emitted before the code section, since its offsets are only known
once the bodies are encoded. A hint belongs to the operation itself, never to a
folded group around it: the opcode is emitted after the folded operands, so that is
where the offset is taken and where a decoder puts the hint back.

### Dispatch and Match

Two Wax control constructs have no instruction of their own: they are readable
spellings of a lower-level *shape*, so they lower to that shape and are
*recovered* from it on decompilation (both round-trip through the binary). See
the language guide for the surface syntax: [`dispatch`](language.md#dispatch)
and [`match`](language.md#match).

`dispatch` is a jump table. It lowers to one nested block per case with a
`br_table` in the innermost block and the case bodies (which fall through) after
their blocks; a `br_table` matching that dense void-switch shape decompiles back
to `dispatch`:

```
(block $big (block $b (block $a           dispatch x ['zero, 'one, else 'big] {
  (br_table $a $b $big (local.get $x)))     'big:  { … }
  … 'one body …) … 'big body …)             'one:  { … }
                                            'zero: { … } }
```

`match` is a multi-way type test. It lowers to a ladder of blocks threading the
scrutinee through `br_on_cast` (and `br_on_null` for a `null` arm), each branch
delivering the narrowed value out to its arm; such a ladder decompiles back to
`match`:

```
(block $default (block $arm_1                match v {
  (block $arm (result (ref $point))            p: &point => { … }
    (br_on_null $arm_1                          null      => { … }
      (br_on_cast $arm eqref (ref $point) …)))  _         => { … } }
  … arm body …) … default …)
```

## Reference Instructions

| Wasm | Wax |
|------|-----|
| `ref.null` | `null` |
| `ref.func $f` | `f` |
| `ref.is_null` | `!val` |
| `ref.as_non_null` | `val!` |
| `ref.i31` | `val as &i31` |
| `i31.get_s` | `val as i32_s` |
| `i31.get_u` | `val as i32_u` |
| `ref.cast` | `val as &type` |
| `ref.test` | `val is &type` |
| `ref.cast (ref (exact $t))` | `val as &!t` |
| `ref.test (ref (exact $t))` | `val is &!t` |
| `ref.cast_desc_eq $t` | `val as descriptor(d)` |
| `ref.cast_desc_eq (ref null …) $t` | `val as ?descriptor(d)` |
| (no instruction) | `val as &k` (`k` a continuation type: a compile-time ascription) |

There is no `ref.cast` (or `ref.test`/`br_on_cast`) to a continuation type: `as` with a continuation target is a compile-time ascription, accepted only when the operand's static type is already a subtype of the target (or the operand is a `null` literal / stack-polymorphic), and it emits nothing — its use is pinning the type immediate of a [`resume` through a supertype signature](#stack-switching-instructions).

A bare function name used as a value, `f` rather than the call `f(args)`, is `ref.func $f`: it produces a reference to the function. This works in a global initializer and anywhere a `&func` reference is expected (for example the callee of an [indirect call](language.md#indirect-calls)).

These casts can also chain through a forced intermediate, written as a single `as`:

- **`&ref as i32_s`/`as i32_u`** on a reference that is not already `&i31` (e.g. an `&any` or `&eq`) inserts a `ref.cast (ref i31)` before the `i31.get`, so it covers both `i31.get_s` and `ref.cast (ref i31)` + `i31.get_s`.
- **`&ref as i64_s`/`as i64_u`** widens that further: the `i31.get` (with the `ref.cast` above as needed) is followed by `i64.extend_i32_s`/`_u`.
- **`i64 as &i31`** wraps to `i32` (`i32.wrap_i64`) before `ref.i31`.
- **`extern_val as &T`** for an `any`-hierarchy `T` (e.g. a struct type) inserts `any.convert_extern` before the `ref.cast (ref T)`; likewise an `any`-hierarchy value `as &extern` uses `extern.convert_any`.
- **`i32_val as &extern`** boxes the `i32` with `ref.i31` before `extern.convert_any`.

## Aggregate Instructions

A struct or array literal takes an optional type prefix (`{t| … }` for a
struct, `[t| … ]` for an array), but it is omitted whenever the literal's type
can be inferred from context (an assignment, a return, a call argument), which
is the common case shown below. Write the prefix only when the type is
ambiguous. The `{descriptor(d)| … }` forms are different: `descriptor(d)`
supplies the runtime descriptor and is part of the construction, not a prefix
that can be dropped.

| Wasm | Wax |
|------|-----|
| `struct.new $t` | `{ field: val, ... }` |
| `struct.new_default $t` | `{ .. }` |
| `struct.new_desc $t` | `{descriptor(d)\| field: val, ... }` |
| `struct.new_default_desc $t` | `{descriptor(d)\| .. }` |
| `struct.get $t $f` | `val.field` |
| `struct.set $t $f` | `val.field = new_val` |
| `ref.get_desc $t` | `val.descriptor` |
| `array.new $t` | `[ val; len ]` |
| `array.new_default $t` | `[ ..; len ]` |
| `array.new_fixed $t` | `[ val, ... ]` |
| `array.new_data $t $d` | `[ d @ offset; count ]` |
| `array.new_elem $t $e` | `[ e @ offset; count ]` |
| `array.init_data $t $d` | `arr.init(d, dest, src, count)` |
| `array.init_elem $t $e` | `arr.init(e, dest, src, count)` |
| `array.fill $t` | `arr.fill(idx, val, count)` |
| `array.copy $t1 $t2` | `arr.copy(idx, src_arr, src_idx, count)` |
| `array.get $t` | `arr[idx]` |
| `array.get_s $t` | `arr[idx] as i32_s` |
| `array.get_u $t` | `arr[idx] as i32_u` |
| `array.set $t` | `arr[idx] = val` |
| `array.len` | `arr.length()` |

A packed (`i8`/`i16`) struct field or array element read sign- or zero-extends to `i32` via the `as i32_s`/`as i32_u` cast, as shown above (`struct.get_s`/`_u`, `array.get_s`/`_u`). Widening straight to `i64` (`val.field as i64_s` or `arr[idx] as i64_u`) emits the packed read followed by `i64.extend_i32_s`/`_u`.

## SIMD (Vector) Instructions

`v128` vector operations are written as method intrinsics with the lane shape baked into the name. The Wax name is the WebAssembly mnemonic with the leading shape moved to the end: `i32x4.add` becomes `add_i32x4`, `f32x4.sqrt` becomes `sqrt_f32x4`, and the whole-vector `v128.and` becomes `and_v128`. Signed/unsigned variants keep the `_s`/`_u` (`min_s_i8x16`, `extract_lane_u_i8x16`). The constant lane immediates of the value-receiver operations (lane indices, shuffle indices) come first in the argument list, before any remaining stack operands; the lane index of a memory lane access is instead the labelled `lane:` argument (see the loads and stores below).

Lanewise unary and binary operations (the receiver is the first operand):

| Wasm | Wax |
|------|-----|
| `i32x4.add` | `a.add_i32x4(b)` |
| `f32x4.mul` | `a.mul_f32x4(b)` |
| `i8x16.min_s` / `i8x16.min_u` | `a.min_s_i8x16(b)` / `a.min_u_i8x16(b)` |
| `i16x8.lt_u` | `a.lt_u_i16x8(b)` |
| `i32x4.neg` | `v.neg_i32x4()` |
| `f64x2.sqrt` | `v.sqrt_f64x2()` |
| `i8x16.narrow_i16x8_s` | `a.narrow_i16x8_s_i8x16(b)` |
| `f32x4.convert_i32x4_s` | `v.convert_i32x4_s_f32x4()` |

Whole-vector bitwise operations, bit selection (a free function):

| Wasm | Wax |
|------|-----|
| `v128.and` / `or` / `xor` / `andnot` | `a.and_v128(b)`, `a.or_v128(b)`, `a.xor_v128(b)`, `a.andnot_v128(b)` |
| `v128.not` | `v.not_v128()` |
| `v128.bitselect` | `v128::bitselect(a, b, mask)` |

Splat, lane access, and shuffle:

| Wasm | Wax |
|------|-----|
| `i32x4.splat` | `x.splat_i32x4()` |
| `i32x4.extract_lane` | `v.extract_lane_i32x4(lane)` |
| `i8x16.extract_lane_u` | `v.extract_lane_u_i8x16(lane)` |
| `i32x4.replace_lane` | `v.replace_lane_i32x4(lane, x)` |
| `i8x16.shuffle` | `a.shuffle_i8x16(l0, ..., l15, b)` |

Shifts, tests, and bitmask:

| Wasm | Wax |
|------|-----|
| `i16x8.shl` | `v.shl_i16x8(n)` |
| `i32x4.shr_s` / `i32x4.shr_u` | `v.shr_s_i32x4(n)` / `v.shr_u_i32x4(n)` |
| `v128.any_true` | `v.any_true_v128()` |
| `i32x4.all_true` | `v.all_true_i32x4()` |
| `i8x16.bitmask` | `v.bitmask_i8x16()` |

Constants are `v128::` free functions (one argument per lane: 16, 8, 4, or 2). `v128.const` is a constant expression, so it may initialise a global:

| Wasm | Wax |
|------|-----|
| `v128.const i32x4 1 2 3 4` | `v128::i32x4(1, 2, 3, 4)` |
| `v128.const f32x4 1.5 2.5 3.5 4.5` | `v128::f32x4(1.5, 2.5, 3.5, 4.5)` |
| `v128.const i8x16 0 1 ... 15` | `v128::i8x16(0, 1, ..., 15)` |

Memory loads and stores are methods on a [memory](correspondence.md#memories), like the scalar [memory accesses](#memory-access) (the optional labelled `offset:`/`align:` arguments work the same way): the `v128.` mnemonic prefix is dropped and the access shape stays in the name, `_s`/`_u` included; the full-width pair takes the family letter, `loadv128`/`storev128` (extending the `loadf32` convention). The lane index of a lane access is the labelled `lane:` argument, mandatory and in any order with `offset:`/`align:`:

| Wasm | Wax |
|------|-----|
| `v128.load` | `m.loadv128(p)` |
| `v128.store` | `m.storev128(p, v)` |
| `v128.load8x8_s` (and `16x4`/`32x2`, `_s`/`_u`) | `m.load8x8_s(p)` |
| `v128.load32_zero` (and `64_zero`) | `m.load32_zero(p)` |
| `v128.load8_splat` (and `16`/`32`/`64`) | `m.load8_splat(p)` |
| `v128.load8_lane` (and `16`/`32`/`64`) | `m.load8_lane(p, v, lane: l)` |
| `v128.store8_lane` (and `16`/`32`/`64`) | `m.store8_lane(p, v, lane: l)` |

Relaxed-SIMD operations follow the same scheme:

| Wasm | Wax |
|------|-----|
| `f32x4.relaxed_madd` | `a.relaxed_madd_f32x4(b, c)` |
| `i8x16.relaxed_swizzle` | `a.relaxed_swizzle_i8x16(b)` |

No intrinsic can clash with a module entity name: the free-function intrinsics are written as `v128::`/`i64::` qualified paths and every other is a method on a receiver, so a function may freely be named e.g. `v128_bitselect` without any renaming.

## Memory Access

Loads and stores are method calls on a [memory](correspondence.md#memories). The method name carries the access width; the value's signedness (for narrow loads) and its `i32`/`i64` type are expressed with the surrounding `as iN_s`/`as iN_u` cast, mirroring packed array access.

| Wasm | Wax |
|------|-----|
| `i32.load` | `m.load32(p)` |
| `i64.load` | `m.load64(p)` |
| `f32.load` / `f64.load` | `m.loadf32(p)` / `m.loadf64(p)` |
| `i32.load8_s` | `m.load8(p) as i32_s` |
| `i32.load16_u` | `m.load16(p) as i32_u` |
| `i64.load32_s` | `m.load32(p) as i64_s` |
| `i64.load8_s` | `m.load8(p) as i64_s` |
| `i64.load16_u` | `m.load16(p) as i64_u` |
| `i32.store` (`v: i32`) or `i64.store32` (`v: i64`) | `m.store32(p, v)` |
| `i32.store16` or `i64.store16` (by `v`'s type) | `m.store16(p, v)` |
| `i64.store` / `f64.store` | `m.store64(p, v)` / `m.storef64(p, v)` |

A bare narrow load (`m.load8(p)` with no cast) defaults to unsigned `i32`, like `array.get_u`. The store value's `i32`/`i64` type is inferred from the operand.

The `offset` and `align` of the access (both constant integers) are optional labelled arguments, written after the operands in either order:

```wax
m.load32(p);                        // i32.load
m.load32(p, offset: 16);            // i32.load offset=16
m.load32(p, offset: 16, align: 1);  // i32.load offset=16 align=1
m.load32(p, align: 1);              // i32.load align=1
```

The alignment defaults to the access's natural alignment and is only printed when it differs; the offset defaults to `0` and is only printed when non-zero.

The remaining memory operations are also methods on the memory (a data segment is named directly, not as a value):

| Wasm | Wax |
|------|-----|
| `memory.size` | `m.size()` |
| `memory.grow` | `m.grow(n)` |
| `memory.fill` | `m.fill(dest, val, len)` |
| `memory.copy` (within `m`) | `m.copy(dest, src, len)` |
| `memory.copy m m2` (copy from `m2` into `m`) | `m.copy(m2, dest, src, len)` |
| `memory.init seg` | `m.init(seg, dest, src, len)` |
| `data.drop seg` | `seg.drop()` |

### Atomics

Atomic accesses (the threads proposal) are methods on a memory, following the scalar-access naming convention: the access width is in the method name (`atomic_load16`, `atomic_rmw_add8`), the `i32`/`i64` value type comes from the operand and result types, and a narrow load is resolved by an `as iN_u` cast. The narrow accesses are the zero-extending `_u` forms, the only kind that exists, so no suffix or cast signedness choice arises (`as iN_s` on a narrow atomic load is rejected; `atomic_load32(p) as i64_s` has no fused form and compiles as `i32.atomic.load` then `i64.extend_i32_s`). They take the same labelled `offset:` argument as the other accesses; an `align:` argument is accepted but must be exactly the natural alignment (the access width from the name), which is also the default. `atomic.fence` has no memory operand and is the [`atomic::fence()`](language.md#qualified-intrinsics) intrinsic.

| Wasm | Wax |
|---|---|
| `i32.atomic.load` | `m.atomic_load32(p)` |
| `i64.atomic.load` | `m.atomic_load64(p)` |
| `i32.atomic.load8_u` | `m.atomic_load8(p) as i32_u` |
| `i64.atomic.load32_u` | `m.atomic_load32(p) as i64_u` |
| `i32.atomic.store` (`v: i32`) or `i64.atomic.store32` (`v: i64`) | `m.atomic_store32(p, v)` |
| `i64.atomic.store8` (`v: i64`) | `m.atomic_store8(p, v)` |
| `i32.atomic.rmw.add` (`v: i32`) | `m.atomic_rmw_add32(p, v)` |
| `i64.atomic.rmw16.add_u` (`v: i64`) | `m.atomic_rmw_add16(p, v)` |
| `i32.atomic.rmw.cmpxchg` | `m.atomic_rmw_cmpxchg32(p, expected, replacement)` |
| `memory.atomic.notify` | `m.atomic_notify(p, count)` |
| `memory.atomic.wait32` | `m.atomic_wait32(p, expected, timeout)` |
| `atomic.fence` | `atomic::fence()` |

## Table Access

A [table](correspondence.md#tables) is indexed like an array, and an indirect call is written as a call through a table slot cast to the callee's function type.

| Wasm | Wax |
|------|-----|
| `table.get $t` | `t[i]` |
| `table.set $t` | `t[i] = v` |
| `call_indirect $t (type $ft)` | `(t[i] as &?ft)(args)` |
| `call_indirect $t (result i32)` | `(t[i] as &?fn() -> i32)(args)` |
| `return_call_indirect $t (type $ft)` | `return (t[i] as &?ft)(args)` |

`call_indirect` is reconstructed from this pattern on conversion to WAT/Wasm, so it round-trips. The cast target names the callee's function type, a defined type (`ft`) or an inline one written `fn(params) -> results` (used when the WAT type is anonymous), and matches the table's element type: for a `funcref` table (the usual case) it is the nullable `&?ft`, as shown. When the element type is already a non-null `&ft`, the cast may be omitted (`t[i](args)`).

The other table operations are methods on the table (an element segment is named directly):

| Wasm | Wax |
|------|-----|
| `table.size` | `t.size()` |
| `table.grow` | `t.grow(val, n)` |
| `table.fill` | `t.fill(dest, val, len)` |
| `table.copy` (within `t`) | `t.copy(dest, src, len)` |
| `table.copy t t2` (copy from `t2` into `t`) | `t.copy(t2, dest, src, len)` |
| `table.init seg` | `t.init(seg, dest, src, len)` |
| `elem.drop seg` | `seg.drop()` |

A GC array can also be filled from a segment with `arr.init(seg, dest, src, len)` (`array.init_data`/`array.init_elem`, selected by the array's element type), the segment-from-array counterpart of [`array.new_data`/`array.new_elem`](#aggregate-instructions).

## Exception Instructions

| Wasm | Wax |
|------|-----|
| `throw $tag` | `throw tag()` (no payload), `throw tag(x)` (one), `throw tag(x, y)` (several) |
| `throw_ref` | `throw_ref` |
| `try_table ... catch $tag $l ...` | `try { ... } catch [ tag -> 'l, ... ]` |
| `try_table ... catch_ref $tag $l ...` | `try { ... } catch [ tag & -> 'l, ... ]` |
| `try_table ... catch_all $l ...` | `try { ... } catch [ _ -> 'l, ... ]` |
| `try_table ... catch_all_ref $l ...` | `try { ... } catch [ _ & -> 'l, ... ]` |
| `try_table` + block ladder | `try { ... } catch { tag => { ... } tag & => { ... } _ => { ... } }` |
| `try ... catch $tag ...` | `try_legacy { ... } catch { tag => { ... } ... }` |
| `try ... catch_all ...` | `try_legacy { ... } catch { _ => { ... } }` |

Both `try` forms compile to WebAssembly's `try_table` instruction (the current standard): the bracket form is the raw instruction (each clause branches to a label), and the braced structured form adds one block per arm around it — each catch clause branches to its arm's block, the arm bodies are the trailing code between the block ends (so an arm's completion falls into the next arm), and the body's completion escapes past all arms with a single branch carrying the try's value. The decompiler recovers the structured form from exactly that ladder shape (a label on the try is the join block), falling back to the bracket form for any other use of `try_table`. `try_legacy` compiles to the older `try`/`catch` instructions (deprecated but still supported for compatibility), and legacy-instruction modules decompile to it.

## Stack Switching Instructions

These correspond to the WebAssembly [stack-switching proposal](https://github.com/WebAssembly/stack-switching). A continuation type is declared with `type k = cont ft;` (see [Types](correspondence.md)); `<k>` and `<tag>` below are the names of a continuation type and a tag respectively.

The resume family and `switch` are methods on the continuation reference `c`; `cont.new` and `cont.bind` are the `T::new` / `T::bind` constructors of the declared continuation type (the `T::` namespace constructs a `&T`). The type immediates are not written: the `$k` of `resume`/`resume_throw`/`resume_throw_ref`/`switch`, and the *source* type of `bind`, are inferred from the static type of the continuation expression, exactly as `call_ref`'s type immediate comes from the callee's — so the receiver must have a *declared* continuation type (an abstract `&cont` is rejected; a cast can never narrow a continuation, so give the value its precise type where it is introduced). An identity/upcast ascription `(c as &k0).resume(x)` selects the supertype's immediate (`resume $k0`) and emits no instruction; decompilation inserts exactly this ascription when an instruction's type immediate is a strict supertype of its continuation operand's own type, so the immediate survives the round trip.

| Wasm | Wax |
|------|-----|
| `cont.new $k` | `k::new(func)` |
| `cont.bind $k1 $k2` | `k2::bind(args, cont)` |
| `suspend $tag` | `suspend tag(args)` |
| `resume $k` | `c.resume(args)` |
| `resume $k (on $tag $l) ...` | `c.resume(args) on [tag -> 'l, ...]` |
| `resume $k (on $tag switch) ...` | `c.resume(args) on [tag -> switch, ...]` |
| `resume_throw $k $tag ...` | `c.resume_throw(tag(payload)) on [...]` |
| `resume_throw_ref $k ...` | `c.resume_throw_ref(exn) on [...]` |
| `switch $k $tag` | `c.switch(args, tag: tag)` |

Operands compile in WebAssembly stack order: for continuations — as for `call_ref` — that puts the receiver *last*, so `c.resume(x)` evaluates `x` before `c` even though `c` is written first (this diverges from receiver-first methods like `arr.fill`, whose instruction takes the receiver first on the stack). The handler list of a postfix `on [...]` clause mirrors the `try ... catch [...]` syntax — a keyword-led handler bracket after the guarded operation: `tag -> 'l` is an `(on $tag $l)` clause and `tag -> switch` an `(on $tag switch)` clause; the clause is omitted when empty. `resume_throw` raises its tag applied to the payload, `tag(payload)`, exactly as `throw tag(payload)` spells it, and `switch`'s enabling tag is the required labelled `tag:` immediate.

Tags used with `suspend`/`resume` may have result types (unlike exception tags); see [Tags](correspondence.md#tags). When a function reference is passed to `T::new` for a continuation whose function type belongs to a recursion group, declare the function with an explicit type (`fn f: ft (...) { ... }`) so its type matches the continuation's.


<!-- docs/src/correspondence/module_fields.md -->

# Module Fields

Wax modules are defined by a sequence of top-level fields: types, functions, globals, memories, tables, and tags.

## Module Name

A `#![module = "..."]` inner attribute at the top of the file names the module.
It maps to the WebAssembly module name, the symbolic name stored in the module
subsection of the `name` custom section, written `$name` in WAT:

```wax,check
#![module = "my_module"]
```

corresponds to the WAT

```wat
(module $my_module …)
```

A module may carry at most one name, and it must not appear inside a conditional
(`#[if]`/`#[else]`): the name applies in every configuration. See also
[Module Name](language.md#module-name) in the language guide.

## Feature Declarations

A `#![feature = "..."]` inner attribute declares an optional proposal the
module uses (see [Features](language.md#features) in the language guide).
It maps to a module-level `(@feature "...")` annotation in WAT:

```wax,check
#![feature = "custom-descriptors"]
```

corresponds to the WAT

```wat
(@feature "custom-descriptors")
```

Both are read on input and emitted on output, so the declaration survives a
Wax/WAT round-trip. In the binary format, each declared feature becomes a
`+name` entry of the conventional `target_features` custom section
([tool-conventions](https://github.com/WebAssembly/tool-conventions/blob/main/Linking.md#target-features-section)):

```text
(@custom "target_features" "\01+\12custom-descriptors")
```

Other producers' entries in that section (standard names like `+simd128`, or
`-` entries) are preserved verbatim through a binary round-trip but do not
become attributes. Decompiling a binary restores the declarations from the
union of the section's recognised `+` entries and the gated encodings the
module actually uses (a descriptor type, an exact reference, a compact import
section, ...), so even a binary whose producer wrote no section decompiles to
a module that recompiles standalone.

## Types

Types are defined using `type` for single definitions or `rec { ... }` for mutually recursive types.

### Simple Types

```wax,check
type point = { x: i32, y: i32 };
type bytes = [i8];
type callback = fn(i32) -> i32;
```

### Recursive Types

Use `rec` when types reference each other:

```wax,check
rec {
    type list = { head: i32, tail: &?node };
    type node = { rest: &list };
}
```

### Supertypes and Finality

Types are final (non-extensible) by default. Use `open` to allow subtypes:

```wax,check
type shape = open { x: i32, y: i32 };
type circle : shape = { x: i32, y: i32, radius: i32 };
```

Maps to:

```wat,check
(type $shape (sub (struct (field $x i32) (field $y i32))))
(type $circle (sub $shape (struct (field $x i32) (field $y i32) (field $radius i32))))
```

## Functions

### Definition

```wax
fn name(param: type, ...) -> return_type {
    body
}
```

Functions without a return type:

```wax,check
fn log_value(x: i32) {
    // no return
}
```

### Function Signatures (Declarations)

Declare a function signature without a body (used with imports):

```wax
fn external_function(x: i32) -> i32;
```

An imported function can be marked [exact](language.md#exact-references) so
that referencing it yields an exact reference: `fn g: !ft;` for a named type, or
`fn h!(x: i32) -> i64;` for an inline signature. This maps to the WAT
`(func (exact <type>))` import descriptor.

### Block Type Annotation

Functions can have a block type on the body:

```wax
fn example() -> i32 'label: {
    // body can use 'label
}
```

## Globals

### Immutable Globals

```wax,check
const PI: f64 = 3.14159;
const MAX_SIZE: i32 = 1024;
```

### Mutable Globals

```wax,check
let counter: i32 = 0;
let state: &?any = null;
```

### Imported Globals

```wax,check
import "env" {
    const base: i32;
    let counter: i32;
}
```

## Memories

A memory is declared with `memory`, followed by its address type (`i32` or `i64`) and, optionally, its limits as `[min]` or `[min, max]` (in pages of 64 KiB):

```wax,check
memory mem0: i32 [1, 1000];
memory mem1: i64 [2];
memory mem2: i32;
```

Maps to:

```wat
(memory $mem0 i32 1 1000)
(memory $mem1 i64 2)
(memory $mem2 i32 ...)
```

When the limits are omitted, the minimum size is derived from the extent of the memory's data segments (using their literal offsets).

A custom page size is written with a `pagesize` clause after the limits, mapping to the WAT `(pagesize N)` form. The page size must be `1` or `65536` (the default), and the limits are counted in pages of that size:

```wax,check
memory small: i32 [4096] pagesize 1;
```

```wat,check
(memory $small 4096 (pagesize 1))
```

A `shared` clause (the threads proposal) marks the memory shared; it must have a maximum size:

```wax,check
memory pool: i32 [1, 16] shared;
```

```wat,check
(memory $pool 1 16 shared)
```

Loads and stores use method-call syntax on the memory, with the value's width in the method name and its signedness expressed by the surrounding [`as iN_s`/`as iN_u` cast](correspondence.md#memory-access), the same convention as packed array access:

```wax
let x: i32 = mem0.load32(p);
let b: i32 = mem0.load8(p) as i32_u;
mem0.store16(p, v);
mem0.store32(p, v, offset: 16, align: 1);
```

See [Memory Access](correspondence.md#memory-access) for the full instruction mapping.

### Data Segments

A memory declaration may carry active data segments in a block, placed at a constant offset:

```wax,check
memory mem1: i64 {
    data _ @ [0x1000] = "hello world";
    data greeting @ [0x2000] = "hi";
}
```

Top-level `data` defines a passive segment, or an active segment for a named memory:

```wax
data seg = "raw\x00bytes";
data init @ mem0 [0] = "hello";
```

Data bytes are ordinary [string literals](language.md#strings); escapes such as `\x41` and `\x00` (two hex digits) decode to raw bytes.

A segment's contents may also concatenate (with `++`) strings and **typed numeric runs** — `[type: values]`, whose element type is stated once and whose values are packed little-endian. This is the WebAssembly *numeric values* text-format extension, and it round-trips through WAT:

```wax
data pixels = "hdr" ++ [f32: 0.2, 0.3, 0.4] ++ [i16: -1, -2, -3] ++ [i8: 1, 2, 3, 4];
```

The scalar element types are `i8`, `i16`, `i32`, `i64`, `f32`, and `f64`; the values (including `nan`/`inf`) are ordinary literals. A `v128` run holds lane groups written `shape(lanes)`, e.g. `[v128: i32x4(1, 2, 3, 4), f64x2(1.0, 2.0)]`. The bytes are the same as if the values were written out as an escaped string.

## Tables

A table is declared with `table`, followed by its element [reference type](correspondence.md) and, optionally, its limits as `[min]` or `[min, max]`:

```wax,check
table funcs: &?func [1, 10];
table objs: &?any [0];
```

Maps to:

```wat,check
(table $funcs 1 10 funcref)
(table $objs 0 anyref)
```

A table element is read and written with index syntax, like an array: `tab[i]` is `table.get` and `tab[i] = v` is `table.set`:

```wax
let f: &?func = funcs[i];
funcs[i] = g;
```

There is no dedicated `call_indirect` syntax: it is written as a call through a table slot, narrowing the slot to the callee's [function type](#functions) with a cast. WAT `call_indirect` round-trips through this form:

```wax
type cmp = fn(i32, i32) -> i32;

(funcs[i] as &cmp)(x, y)        // call_indirect $funcs (type $cmp)
```

The other table-management instructions have method syntax too: `t.size()`,
`t.grow(init, n)`, `t.fill(dst, val, n)`, `t.copy(dst, src, n)`,
`t.init(seg, dst, src, n)`, and `seg.drop()` on an element segment (see
[Instructions](correspondence.md)).

### Element Segments

An element segment is declared with `elem`, its element reference type, and a bracketed list of constant element expressions. A bare `elem` is passive; `@ table[offset]` makes it an active segment that initializes a table:

```wax
elem dispatch: &?func = [handler_a, handler_b, handler_c];   // passive
elem init: &?func @ funcs[0] = [handler_a, handler_b];       // active
elem nums: &?i31 = [1 as &i31, 2 as &i31];                   // expression form
```

A passive element segment can initialize a GC array with [`array.new_elem`](correspondence.md#aggregate-instructions), written with the same `[t| seg @ off; count]` syntax as `array.new_data`; which one applies is determined by the array's element type (a reference element selects the element segment):

```wax
type handlers = [&?func];

let hs: &handlers = [handlers| dispatch @ 0; 3];
```

## Tags

Tags define exception types for structured exception handling.

### Definition

```wax,check
type string = [mut i8];

tag my_error(code: i32);
tag empty_error();
tag multi_arg(a: i32, b: &string);
```

Maps to:

```wat
(tag $my_error (param i32))
(tag $empty_error)
(tag $multi_arg (param i32) (param (ref $string)))
```

A tag may also declare a result type, in which case it is used as a suspension tag for [stack switching](correspondence.md#stack-switching-instructions) rather than for exceptions:

```wax,check
tag yield(value: i32) -> i32;
```

### Imported Tags

```wax,check
import "env" tag js_error(&?extern);
```

## Attributes

Attributes modify module fields. They use the syntax `#[name = value]`, or `#[name]` when no value is needed, and appear before the field they modify.

### Export Attribute

Export a field with a given name:

```wax,check
#[export = "add"]
fn add(x: i32, y: i32) -> i32 { x + y; }

#[export = "PI"]
const PI: f64 = 3.14159;

#[export = "my_error"]
tag my_error(code: i32);
```

The name is optional: a bare `#[export]` exports the field under its own Wax name.

```wax,check
#[export]
fn add(x: i32, y: i32) -> i32 { x + y; }
```

Multiple exports can share the same function:

```wax,check
#[export = "add"]
#[export = "plus"]
fn add(x: i32, y: i32) -> i32 { x + y; }
```

### Start Attribute

Mark a function to run at module instantiation. It takes no value and the
function must have no parameters and no results (it maps to the Wasm `start`
field):

```wax,check
#[start]
fn init() {
    // initialization code
}
```

An imported function can also be the start function, running host-provided
initialization at instantiation:

```wax,check
import "env" #[start] fn init();
```

## Imports

Import fields from a host module with an `import "module" { … }` block; a lone
import can use the one-line `import "module" <declaration>;` form. Each entry is
imported under its own Wax name, unless a name-only `#[import = "name"]`
overrides that.

```wax,check
import "env" {
    fn log(msg: i32);
    const memory_base: i32;
    #[import = "js_error"]
    tag error(code: i32);
}

import "env" fn trace(msg: i32);
```

### Combined Import and Export

A field can be both imported and re-exported by adding `#[export]` to it:

```wax,check
import "env" #[export = "value"] const value: i32;
```

## Conditional Annotations

Both formats can guard module fields by a condition that a downstream preprocessor evaluates. Wax uses `#[if(...)] { ... }` / `#[else] { ... }`, with the braces required around each branch; WAT uses the annotation form `(@if <cond> (@then ...) (@else ...))`.

```wax,check
#[if(ocaml_version >= (5, 1, 0))]
{
    const size: i32 = 16;
}
#[else]
{
    const size: i32 = 20;
}
```

```wat
(@if (>= $ocaml_version (5 1 0))
  (@then (global $size i32 (i32.const 16)))
  (@else (global $size i32 (i32.const 20))))
```

The conditions are equivalent; note the surface differences: Wax variables are bare (`ocaml_version`) while WAT variables are `$`-prefixed; Wax versions are tuples `(5, 1, 0)` while WAT writes them `(5 1 0)`; Wax combines conditions with `all`/`any`/`not`, WAT with `and`/`or`/`not`.

The conditions are preserved, not evaluated. Type checking (`--validate`) explores each reachable combination independently (see the [Language Guide](language.md#conditional-compilation)). The two forms convert to each other, so a conditional written in Wax survives a round-trip through WAT and back.

## Module Structure

A typical Wax module follows this structure:

```wax,check
// 1. Type definitions
type point = { x: i32, y: i32 };
type callback = fn(i32) -> i32;

// 2. Imported globals and functions
import "env" {
    fn log(value: i32);
    const base: i32;
}

// 3. Tags
tag my_error(code: i32);

// 4. Module globals
const FACTOR: i32 = 100;
let counter: i32 = 0;

// 5. Internal functions
fn helper(x: i32) -> i32 {
    x * FACTOR;
}

// 6. Exported functions
#[export = "compute"]
fn compute(x: i32) -> i32 {
    counter = counter + 1;
    log(counter);
    helper(x + base);
}
```

This order is conventional but not required; Wax allows fields in any order.


<!-- docs/src/correspondence/round_trip.md -->

# Round-Tripping

Decompiling a Wasm module to Wax and recompiling it (`wasm → wax → wasm`)
reproduces the instruction stream opcode-for-opcode, dead code included. The
type section is preserved as well: structurally identical types stay distinct
and keep their order and numbering. The rest of this page lists the places where
the round trip diverges. Every divergence is semantically inert: the recompiled
module behaves identically, it just is not byte-for-byte identical.

## Divergences

1. **Locals and names.** Local order and numbering are not preserved; every use
   is rewritten consistently. The `name` section is rewritten.

2. **`eq` then `eqz` fuses to `ne`.** A `t.eq` followed by `i32.eqz` decompiles
   to `a != b`, which recompiles as a single `t.ne`. (`--faithful` keeps the
   pair.)

3. **Flat cast-dispatch chains are canonicalised.** A flat run of
   `br_on_cast_fail` blocks is recovered as a `match`, which re-lowers to the
   nested `br_on_cast` ladder rather than the flat chain. The ladder shape
   itself round-trips byte-for-byte. (`--faithful` keeps the flat chain.)

4. **Redundant `ref.cast` erased (best-effort).** A `ref.cast` decompiles to an
   `as` ascription, which is dropped when the operand's inferred type is already
   a subtype of the target (an identity cast or an upcast), so it recompiles to
   no instruction. A genuine downcast is kept and re-emits `ref.cast`. The
   decompiler also inserts scaffolding casts of its own (a member-access
   receiver, a `call_ref` callee) to nullable reference types, and these are
   indistinguishable from a redundant source cast to a nullable type, so cast
   keeping is best-effort. A few load-bearing ascriptions (a width pin, a
   bottom-reference type name, a continuation type immediate) are never dropped.

5. **A typed `select` may lose its immediate.** The value type is always
   preserved through the arms, but the explicit `(result t)` immediate form is
   not guaranteed to be reproduced.

6. **Shared spellings.** A few distinct opcode streams share a single Wax
   spelling, so the recompiler picks one canonical encoding for both:

   - **`i64.extend32_s`** is spelled `(x as i32) as i64_s`, the same
     wrap-then-sign-extend pair a hand-written `i32.wrap_i64; i64.extend_i32_s`
     produces, and both recompile to `i64.extend32_s`.
   - **A 32-bit load widened to `i64`.** `i32.load; i64.extend_i32_u` and the
     fused `i64.load32_u` are both `m.load32(x) as i64_u` and recompile to
     `i64.load32_u`. The atomic analogue behaves the same:
     `i32.atomic.load; i64.extend_i32_u` and `i64.atomic.load32_u` are both
     `m.atomic_load32(x) as i64_u`. (The 8- and 16-bit narrow loads carry an
     inner `as i32_s`, so the pair and the fused load stay distinct; only the
     zero-extending `_u` load32 fuses.)
   - **The call family.** `call` and `call_indirect` desugar through `call_ref`
     (via a `ref.func` or a table access) and are recovered by pattern; a shape
     that cannot re-fuse recompiles to the desugared `call_ref` form.
   - **Float negation of a literal.** `f32.neg`/`f64.neg` of a constant folds
     into the negated literal (Wax spells a negative float literal `-X`), so
     both `const -X` and `const X; neg` recompile the same way.
   - **Empty `else`.** An `if` with an empty `else` branch decompiles to a
     branchless `if`, which recompiles without the `else`.

7. **Types may become more precise.** A declared type wider than the value it
   holds tightens to the value's precise type across a round trip: the
   decompiler infers each binding's type from its content and drops the wider
   annotation, and the recompiler re-infers the precise type. The module still
   validates (the precise type is a subtype of the original) and behaves
   identically. This affects a `local` or a `const` global declared at a
   supertype but only ever assigned a narrower value, a block result type
   declared wider than its body when no consumer pins the wider type, and a
   `br_on_cast`'s source-type immediate re-inferred from its operand.

## Faithful round-tripping

The `--faithful` flag (wax output only) preserves the reachable instruction
structure the reshaping recoveries would otherwise change. It keeps the
`eq; eqz` pair rather than fusing to `t.ne` (divergence 2), keeps a flat
`br_on_cast_fail` chain rather than recovering the `br_on_cast` ladder
(divergence 3), and keeps a redundant non-null `ref.cast` as an `as` ascription
(divergence 4). The other divergences are inert normalisations it does not gate.

## How this is checked

These guarantees are enforced by a differential fuzzing harness that compares
per-opcode histograms across a round trip, over both a curated corpus and a
`wasm-smith` campaign.
