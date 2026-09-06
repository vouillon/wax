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
explained in the [language guide](../language.md#exact-references).

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
Maps to Wasm `(type $k (cont $ft))`. See [Stack Switching Instructions](instructions.md#stack-switching-instructions) for the operations on continuations.

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
