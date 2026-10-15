# Declared conventions: code a program makes, under a contract it states

Kayak's request (2026-10-14, `TODO.md` §97): kayak is writing FX-26's
native code generators in KFX, which may use only what FX-26 has, and
FX-26 has no way to place machine code a program made and run it. This
note designs that, and the contract the code must keep, so that the same
machine code runs on fixpt's machines and on kayak's runtime.

The user's direction (2026-10-14): not leaf code only, and the contract
*declared*: a convention is a description that means something, not a
version number, even if, at first, the declarations an implementation
accepts are a fixed set.

## What a program does

1. **Make a code bloblet** in the heap's code area (`docs/object-model.md`,
   "A collected code area"): so many fields, traced, and a suffix of so many
   bytes, both zero.
2. **Fill it**: its fields with any values, its suffix with the machine code,
   by the suffix writes bloblets already have.
3. **Seal it**: the suffix frozen (the header's bit 13, past which a suffix
   write already fails), the instruction cache flushed for it, and the
   bloblet marked as code that may run.
4. **Make a procedure of it**, at a convention and a type the program
   states. This is the step that is trusted: nothing checks that machine
   code keeps a type, or a convention, so it carries an effect of its own,
   `(io native)`, and every use of the power shows in effects.
5. **Ask first** whether this machine runs native code at all, and fall back
   to interpretation where it does not.

The procedure made is a first-class FX-26 procedure, a native closure of
the code bloblet over nothing: every machine calls native closures
already (the cellular ones through the Rust machine, `TODO.md` §93), so a
call of it needs nothing new. Its code bloblet is one of the code area's,
collected as fixpt's own are: never moved, mark-swept, its fields traced
and updated in place, alive while the closure, or a frame running it, is.

## The forms

Syntax, as the bloblet forms are (`docs/fx26.md`, "Bloblets"), since a
code bloblet is a bloblet, and its type says its fields':

| form                         | type                       | effect         |
| ---------------------------- | -------------------------- | -------------- |
| `(make-code-bloblet bytes e …)` | `(bloblet (fields T …) R)` | `(alloc R)` |
| `(code-seal! b)`             | `unit`                     | `(write R)`    |
| `(native-procedure T b)`     | `T`, a `subr` type         | `(io native)`  |
| `(native-code?)`             | `bool`                     | pure           |
| `(define-convention C clause …)` | at top level: binds `C` | none          |

- `make-code-bloblet` is `make-bloblet` in the code area. Its suffix is
  written by `bloblet-set-byte!`, or four bytes at a time through a
  `(blobref B u32)` (`blobref-set!`). Its fields stay mutable, before the
  seal and after (the collector updates them in place already); its code,
  once sealed, never changes.
- `code-seal!` freezes the suffix and flushes it from the instruction
  cache. Nothing else freezes a code bloblet's suffix, so a frozen one is
  sealed.
- `native-procedure` checks, at run time, that `b` is a sealed code
  bloblet (else a failure, not a crash), and makes a native closure of it
  over nothing; `T`'s convention must be one that names a supported
  declaration (`native`, or a name `define-convention` bound to it); left
  out, it is `native`. A program whose own convention is `cellular` gets
  the closure through the checker's conversion, as any native closure.
- `native-code?` is false on a machine that cannot run native code, where
  `native-procedure` fails; a program asks first, and interprets instead.
- `(io native)` is a new member of the `io` family, so a program that
  makes procedures of code says so in its effects, and a caller's
  `(io native)` shows it.

## A convention, declared

A convention is a set of *clauses*, each binding a *role* to where it is,
or to the protocol it follows. The roles, and what each clause's head
means, are defined by this note and, once settled, by `docs/fx26.md`; the
parameters are data. Two declarations whose normal forms are equal are the
same convention. Nothing in a declaration is a version: a change to the
convention is a change to some clause, and says what changed.

```scheme
(define-convention native
  (target arm64)
  (registers
    (arguments x1 x2 x3 x4 x5 x6 x7 x8)
    (count x9)                       ; arguments given, for a variadic callee
    (result x0)
    (closure x10)
    (link x30)
    (frame x29)
    (pinned (state x24) (fuel x28) (stack-limit x27) (code-distance x26))
    (scratch x9 x11 x12 x13 x14 x15 x16 x17))
  (values …)                         ; the layout: tags, headers, kinds
  (closures …)                       ; a native closure's fields
  (code …)                           ; a code bloblet: its fields, its entry
  (frames …)                         ; their layout, their stack maps
  (state …)                          ; the fields code reads and writes
  (routines …)                       ; what the runtime does for code
  (fuel …)
  (barrier …))
```

### The clauses, as fixpt's `native` has them

Taken from `crates/fixpt-native/src/direct.rs` (its header comment is the
table) and `crates/fixpt-heap/src/layout.rs`.

- **`target`**: `arm64`, the AArch64 instruction set, little-endian.
- **`registers`**: arguments in `x1`–`x8` (past eight, the eighth a list of
  the rest), their count in `x9` on entry, the result in `x0`, the closure
  called in `x10`, the return address in `x30`, the frame link in `x29`.
  Pinned, never changed by code but as the clause on fuel says: the
  machine's state `x24`, fuel `x28`, the native stack's limit `x27`, and
  the distance from a code bloblet's reference to where its code runs
  `x26`. Every other register is the callee's to lose; nothing that is a
  value is kept in a register across a call or a routine that may collect.
- **`values`**: the tags (`fixnum` `000`, 61 bits signed; the bloblet
  pointer `100`, at its suffix; the suffix ref `010`; the header `110`; …),
  the header's fields (kind, large, fields frozen, suffix frozen, *F*,
  *B*), the immediates (`#t`, `#f`, `'()`, `#u`, characters), and the
  kinds' numbers, as `layout.rs` has them.
- **`closures`**: a native closure is a bloblet of kind `native-closure`,
  field 0 its code bloblet (`CLOSURE_WORD`), its captured values after
  (`CLOSURE_FREE0`); its code is native code when that field is at or
  past the code area's start (the state's `code-lo`), else the callee is
  called through the `foreign` routine.
- **`code`**: a code bloblet's code runs at its reference plus `x26`; field
  *k* is `8k + 4` bytes before its first instruction, read PC-relatively.
- **`frames`**: the frame's region from `x29 − 8`: a header word's room,
  the link `[x29]`, the return `[x29 + 8]`, the stack map `[x29 + 16]` (a
  fixnum: the count of fields above bit 48, the live values' mask below;
  negative, minus the count, when every value is live), values from
  `[x29 + 24]`, raw words after, 16-byte aligned. A frame keeps its code
  bloblet in a value slot, so that code running is alive. The stack map
  is stored before every call and every routine that may collect.
- **`state`**: the fields of the state at `x24` that code reads or writes,
  each by name and offset: fuel's reserve, the allocation top, the heap's
  base and the allocation limit, the arguments of a routine, the trap,
  the card table, `code-lo`, and the routines' entries.
- **`routines`**: what the runtime does for code, each a routine whose
  entry is in a state field, called by `blr` with its inputs, outputs and
  what it loses declared: call what is not native code (`foreign`), make a
  closure, allocate, call a primitive, fail (the trap, its kind in `x9`),
  poll (a time slice spent), overflow (a frame past the stack's limit).
  Routines, not inline sequences, are the contract wherever fixpt's own
  code has a sequence too intricate to standardise (a poll's is thirty
  instructions): the sequence lives in the runtime, once, and a declared
  routine stays the same while the runtime's inside changes.
- **`fuel`**: decremented in `x28` on entry to a procedure that calls and
  on a loop's back edge; at zero, the `poll` routine.
- **`barrier`**: a store of a value into a heap object marks the byte for
  its card, `cards + (address >> 9)` (a card is 64 words), the biased
  table's address in the state.

### Accepted, or refused

A program's declaration is normalised (clauses sorted by role, each
clause's own parameters in their order) and compared with the
implementation's *supported set*. Equal to one, it is that convention:
`native ≤ fx` holds of it, and its procedures are called as any native
closure is. Equal to none, the program is refused at the declaration,
naming the first clause that differs from the nearest one supported
("`frames`: the stack map declared at `[x29 + 16]`; this implementation
keeps it at …"), or the clause missing or not known.

For the first deliverable the supported set is one declaration: fixpt's
`native`, as it is. Later, an implementation may support more than one, an
older declaration among them, with the conversions the checker already
inserts between conventions (`docs/research/native-conventions.md`,
"Conventions in types").

### Generated, so that it cannot drift

fixpt's declaration is generated from the implementation's own tables
(`layout.rs`'s tags, kinds and header fields; `DState`'s offsets by
`offset_of!`; `direct.rs`'s registers, frame constants and routines; the
card shift), as `standard.fx` is generated from `lower.rs`'s table, into a
module file every program may load (`fx26:native-arm64.fx`), and a test
compares the file with what the tables say now (`FIXPT_BLESS=1` to
rewrite). Both checkers compare a program's declaration with it: the Rust
one reads it with `include_str!`, the one written in FX-26 from a
generated module of the same text, which it reads with its own reader. A change to the convention is a change to that file, in the
same commit, and a program written against the old one is refused with
the difference, not run.

### Data a generator reads

The declaration is also data: a generator written in FX-26 reads the
registers, offsets and routines' entries from it, rather than from numbers
copied out of fixpt, so kayak's generators are parametric in the
convention they emit for. Kayak's runtime publishes its own supported set,
and where the two meet, the same code runs on both.

## Where the trust is

`(io native)` marks the one trusted step: a procedure made of machine code
at a stated type and convention. The declaration does not make machine
code safe; it makes the contract the code was written to explicit,
checkable for agreement, and the same on both sides. A capability, held
rather than declared, can come later as a handle over the same primitive,
for a program that must hand the power on.

## Not yet

- **Heap images** carry no code area yet, so making an image of a program
  that holds a code bloblet is refused until they do (`docs/object-model.md`,
  "Not yet decided").
- **Other targets**: only `arm64`. A declaration for another target is
  refused, by its `target` clause.
- **Primitives by name**: a routine that calls a runtime primitive takes
  its number, which is fixpt's alone; a stable naming (by symbol, resolved
  when the procedure is made) is to decide with kayak.

## Steps, each committed and tested

1. This note.
2. The runtime: sealing a code bloblet (`Heap::seal_code`: the suffix
   frozen and flushed), a native closure of a sealed one, `native-code?`.
3. The forms in both parsers, both checkers, both compilers and the
   evaluator written in FX-26; `(io native)`. Test: a program that makes
   a leaf adding two fixnums, and one returning its own field across a
   collection that moves the field's value, on every machine.
4. `define-convention`: fixpt's declaration generated and blessed, both
   checkers comparing a program's with it, refusals naming the clause.
5. Code that is not a leaf: the routines a program's code calls (allocate,
   poll, fail, call what is not native code), made routines at state
   fields where today they are inline sequences or bare call-outs; a test
   whose code makes a frame, conses across a collection, calls a closure
   it is given, and is preempted in a loop.
6. Data a generator reads: the declaration as a value of FX-26.
