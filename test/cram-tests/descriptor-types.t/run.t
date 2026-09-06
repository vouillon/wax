A custom descriptor (the custom-descriptors proposal) attaches a descriptor
struct to another struct. Wax spells the two clauses as [descriptor <name>] (on
the described type) and [describes <name>] (on the descriptor), between the
[open] marker and the struct body. They must pair up within a single [rec] group.

  $ wax --validate -X custom-descriptors desc.wax -f wat
  (rec
    (type $obj (descriptor $obj_desc) (struct (field $x i32)))
    (type $obj_desc (describes $obj) (struct))
  )

The clauses survive a binary round-trip.

  $ wax -X custom-descriptors desc.wax -f wasm -o desc.wasm
  $ wax -X custom-descriptors desc.wasm -f wax
  #![feature = "custom-descriptors"]
  rec {
      type obj = descriptor obj_desc { x: i32 };
      type obj_desc = describes obj { };
  }

A descriptor and its described type must refer to each other.

  $ wax check -X custom-descriptors not-reciprocal.wax
  Error: The descriptor of this type does not describe it back.
   ──➤  not-reciprocal.wax:2:3
  1 │ rec {
  2 │   type a = descriptor b { };
    ·   ^^^^^^^^^^^^^^^^^^^^^^^^^^
  3 │   type b = { };
  4 │ }
  [128]


Both types in a descriptor pair must be structs.

  $ wax check -X custom-descriptors not-struct.wax
  Error: A descriptor type must be a struct type.
   ──➤  not-struct.wax:2:3
  1 │ rec {
  2 │   type a = descriptor b fn();
    ·   ^^^^^^^^^^^^^^^^^^^^^^^^^^^
  3 │   type b = describes a { };
  4 │ }
  [128]


If a supertype has a descriptor, its subtype must have one too.

  $ wax check -X custom-descriptors sub-missing-descriptor.wax
  Error: This type is not a valid subtype of 'a'.
   ──➤  sub-missing-descriptor.wax:4:11
  2 │   type a = open descriptor a_desc { };
  3 │   type a_desc = open describes a { };
  4 │   type b: a = open { };
    ·           ^
  5 │ }
  6 │ 
  [128]


Conversely, a subtype may not add a descriptor its supertype lacks: descriptor
presence must match along the declared subtype chain.

  $ wax check -X custom-descriptors sub-added-descriptor.wax
  Error: This type is not a valid subtype of 'a'.
   ──➤  sub-added-descriptor.wax:3:11
  1 │ rec {
  2 │   type a = open { };
  3 │   type b: a = open descriptor b_desc { };
    ·           ^
  4 │   type b_desc = open describes b { };
  5 │ }
  [128]
  $ wax check -X custom-descriptors sub-added-descriptor.wat
  Error: This type is not a valid subtype of its declared supertype.
   ──➤  sub-added-descriptor.wat:4:5
  2 │   (rec
  3 │     (type $a (sub (struct)))
  4 │     (type $b (sub $a (descriptor $b_desc) (struct)))
    ·     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  5 │     (type $b_desc (sub (describes $b) (struct)))))
  6 │ 
  [128]


A type and its descriptor must also agree on finality. An open type with a final
descriptor could never be extended, since a subtype of it would need a
descriptor extending a final type; a final type with an open descriptor leaves
that descriptor with no possible subtypes either.

  $ wax check -X custom-descriptors finality-mismatch.wax
  Error: A type and its descriptor must both be 'open', or neither.
   ──➤  finality-mismatch.wax:2:3
  1 │ rec {
  2 │   type a = open descriptor b { };
    ·   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  3 │   type b = describes a { };
  4 │ }
  [128]
  $ wax check -X custom-descriptors finality-mismatch.wat
  Error: A type and its descriptor must both be 'final', or neither.
   ──➤  finality-mismatch.wat:3:5
  1 │ (module
  2 │   (rec
  3 │     (type $a (sub final (descriptor $b) (struct)))
    ·     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  4 │     (type $b (sub (describes $a) (struct))))
  5 │   (global (export "g") (ref null $a) (ref.null $a)))
  [128]
