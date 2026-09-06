The (@if) x dead-code corner (ATIF-DEADCODE.md, backing-scan grid ScondEq/
ScondNe cells). A conditional annotation is validated by SPLICING each branch
into the enclosing frame (per configuration), so a branch can consume an
enclosing dead residual — which lets a residual of the WRONG hierarchy (or a
numeric) sit where a dead reference op's hole would reconnect to it, a shape
plain wasm can never build (its validator types the residual into the consumer
and rejects). The tree the lowering reads instead types each branch as an
isolated void block: `From_wasm`'s backing scan models THAT rule (an annotation
claims nothing), and a backing the reader's pin could not ascribe gets the
claim-free BOTTOM pin (`_ as &?none` and kin), which the typer gives no pending
value — it grounds the hole without capturing the residual a branch consumes.

A funcref residual under the annotation backs the `ref.is_null` hole bare (any
reference recovers `ref.is_null`); the extern residual deeper is what the
spliced else-configuration's `!_` reads. This used to crash the decompile
(typing.ml's expected-side assertion, via the `&?any` pin capturing the
funcref):

  $ cat > isnull.wat <<'WAT'
  > (module (elem declare func $f) (func $f (result i64) (i64.const 1))
  >   (func
  >     return
  >     extern.convert_any
  >     ref.func $f
  >     (@if $dbg (@then drop) (@else drop))
  >     ref.is_null
  >     drop
  >     unreachable))
  > WAT
  $ wax -i wat -f wax isnull.wat -o isnull.wax && cat isnull.wax
  fn f() -> i64 {
      1;
  }
  fn f_2() {
      return;
      _ as &any as &extern;
      f;
      #[if(dbg)]
      {
          _ = _;
      }
      #[else]
      {
          _ = _;
      }
      _ = !_;
      unreachable;
  }
  $ wax isnull.wax -f wat
  (func $f (result i64) (i64.const 1))
  (func $f_2
    (return)
    (extern.convert_any)
    (ref.func $f)
    (@if $dbg (@then (drop)) (@else (drop)))
    (drop (ref.is_null))
    (unreachable)
  )
  (elem declare func $f)

An extern residual the branches consume, under `ref.eq`: extern is no
`eq`-subtype, so a bare `_ == _` capturing it would not type-check and an
`(_ as &?eq)` pin capturing it would cross hierarchies. Both holes take the
claim-free bottom pin, which must lower to NOTHING (not the general ref-to-ref
`ref.cast`):

  $ cat > refeq.wat <<'WAT'
  > (module
  >   (func
  >     return
  >     extern.convert_any
  >     (@if $dbg (@then drop) (@else drop))
  >     ref.eq
  >     drop
  >     unreachable))
  > WAT
  $ wax -i wat -f wax refeq.wat -o refeq.wax && cat refeq.wax
  fn f() {
      return;
      _ as &any as &extern;
      #[if(dbg)]
      {
          _ = _;
      }
      #[else]
      {
          _ = _;
      }
      _ = _ as &?none == _ as &?none;
      unreachable;
  }
  $ wax refeq.wax -f wat
  (func $f
    (return)
    (extern.convert_any)
    (@if $dbg (@then (drop)) (@else (drop)))
    (drop (ref.eq))
    (unreachable)
  )

A width-tagged NUMERIC residual the branches consume, under `ref.is_null`: the
positional capture would be the `i64.add` value (claiming is type-blind), which
neither a bare `!_` (re-defaults to `i32.eqz`) nor the `&?any` pin (fails to
type) survives — the scan's `` `Value`` verdict routes it to the bottom pin
too. This used to crash the wax->wat direction (`to_wasm`'s cast lowering, on
the poisoned i64-to-reference cast):

  $ cat > num.wat <<'WAT'
  > (module
  >   (func
  >     return
  >     i64.add
  >     (@if $dbg (@then drop) (@else drop))
  >     ref.is_null
  >     drop
  >     unreachable))
  > WAT
  $ wax -i wat -f wax num.wat -o num.wax && cat num.wax
  fn f() {
      return;
      (_ + _) as i64;
      #[if(dbg)]
      {
          _ = _;
      }
      #[else]
      {
          _ = _;
      }
      _ = !(_ as &?none);
      unreachable;
  }
  $ wax num.wax -f wat
  (func $f
    (return)
    (i64.add)
    (@if $dbg (@then (drop)) (@else (drop)))
    (drop (ref.is_null))
    (unreachable)
  )

The cross-hierarchy converts aim their wrong-hierarchy pin at the SOURCE
hierarchy's bottom, so the convert lowers over it exactly as the source did —
a top-of-hierarchy pin would capture the extern residual and lower to the very
`any.convert_extern` it should not add:

  $ cat > cvt.wat <<'WAT'
  > (module
  >   (func
  >     return
  >     ref.func $f
  >     (@if $dbg (@then drop) (@else drop))
  >     any.convert_extern
  >     drop
  >     unreachable)
  >   (elem declare func $f) (func $f))
  > WAT
  $ wax -i wat -f wax cvt.wat -o cvt.wax && cat cvt.wax
  fn f() {
      return;
      f_2;
      #[if(dbg)]
      {
          _ = _;
      }
      #[else]
      {
          _ = _;
      }
      _ = _ as &noextern as &any;
      unreachable;
  }
  fn f_2() {}
  $ wax cvt.wax -f wat
  (func $f
    (return)
    (ref.func $f_2)
    (@if $dbg (@then (drop)) (@else (drop)))
    (drop (any.convert_extern))
    (unreachable)
  )
  (func $f_2)
  (elem declare func $f_2)

A member-access RECEIVER pin capturing across the annotation (the grid's
`Vmulti.ScondEq.S2` cells): the struct.set receiver hole's positional capture
is the call residual's FIRST result (its sibling value hole eats the second),
a non-reference the `&?s` pin cannot absorb — and the lowering reads the
struct type off the receiver, so the poisoned capture crashed it. The pin
nests the claim-free bottom inside the type pin, which still names the type:

  $ cat > recv.wat <<'WAT'
  > (module
  >   (type $s (struct (field (mut i64))))
  >   (func $f2 (result i64 i64) (i64.const 1) (i64.const 2))
  >   (func
  >     return
  >     call $f2
  >     (@if $dbg (@then drop) (@else drop))
  >     struct.set $s 0
  >     ref.is_null
  >     drop
  >     unreachable))
  > WAT
  $ wax -i wat -f wax recv.wat -o recv.wax && grep -A1 'if(dbg)' -m1 recv.wax >/dev/null && sed -n '/}$/,$p' recv.wax | grep -E 'as &|!'
      (_ as &?none as &?s).f = _;
      _ = !(_ as &?none);
  $ wax recv.wax -f wat | grep -cE 'struct.set \$s|ref.is_null|ref.cast'
  2

A width-tagged numeric residual whose positional capture belongs to an
interposed `if` CONDITION hole (`Rnum.ScondEq.Bif`): the condition claims the
`i64.add` value in the tree the lowering reads, and the reconciliation's
repair then re-grounds that shared cell at i64. This used to rewrite one of
the typer's SHARED base-type cells (the flexible operand had been union-merged
into the expected `i32` cell by `subtype`), retyping every `!` result in the
module and failing the decompile; `subtype` now settles a flexible value by
setting its own cell:

  $ cat > numif.wat <<'WAT'
  > (module
  >   (func
  >     return
  >     i64.add
  >     (@if $dbg (@then drop) (@else drop))
  >     if end
  >     ref.is_null
  >     drop
  >     unreachable))
  > WAT
  $ wax -i wat -f wax numif.wat -o numif.wax && wax numif.wax -f wat
  (func $f
    (return)
    (i64.add)
    (@if $dbg (@then (drop)) (@else (drop)))
    (if (then))
    (drop (ref.is_null))
    (unreachable)
  )
