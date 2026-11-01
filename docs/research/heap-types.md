# Types as heap data

Status: design, for the user's review (2026-11-01). Nothing implemented.
Asked for by the user after Heist's request (`TODO.md` §201, item 5): a
`stage` checks its module's type again each time because the type crosses
to the staged checker as text. The user's direction: types as heap data,
with an efficient binary scheme for serialization and a readable one for
debugging.

## What crosses as text today

Every place a type leaves the checker that made it, it leaves as the text
the checker prints, and is read and checked again where it arrives:

| Boundary | What is printed | Who reads it |
| --- | --- | --- |
| `stage`, a session's steps | `M`, `E`, `R` (`n-staged`, `Staged`) | the stage's own front end, or the Rust checker (`rs-scheme-vm`, `fx-ast-eval`) |
| run-time evidence | `reify-type` and kin: the text of what a variable was instantiated at | `fixpt_runtime::evidence`, substituting names in the texts above |
| a program's `.fasl` | each kept definition's type, its uses' types, the abbreviations (`fasl.rs`) | both checkers, at each load |
| the checkers' agreement | each form's line, `define name : T ! E` | the tests |

Text was chosen because each boundary is between two type stores that share
nothing: the FX-26 checker's types are heap values in an array of its own
instance (`k-tys`), named by their index, and the Rust checker's are a
`Vec<Ty>` named by `TyId`. An index means nothing outside its store.

What text costs, measured:

- **Identity.** An abstract type is told apart only by its name: `m..t`
  once a variable's module is opened, `m.fx..t` for a load's. A printer
  that names one way where it binds another made a sealed module's type
  unreadable (§201 item 4, in both checkers); two files of one name gave
  their abstract types one name (`fasl_use_digest`'s `select`s, §200).
- **Time.** What arrives is read, elaborated and checked again: a stage of
  `'1` against a module of 60 alternatives and 40 procedures, 250 ms
  (§201 item 5); a `.fasl`'s types, much of a warm start (§200).
- **Size.** A type is written out whole wherever it is used:
  `(read (globals …))` effects of 300 names before absorption, a value
  type of 20 KB in each of s7st's stages.

## The proposal

A **type rep** is an immutable heap object holding a type in a form both
checkers import and export, and that crosses every boundary above as
itself: in the heap, as a constant in compiled code, in a `.fasl`'s image,
in a heap dump. The checkers keep their own stores for inference, since
unification needs mutable variables, and convert at the boundaries. Text
stays, as a view for people.

### Shape

A rep is a frozen bloblet: a **node table** and a root.

- Each node is one constructor of the type language (`base`, `subr`,
  `poly`, `productof`, `sumof`, `union`, `ref`, `pairof`, `moduleof`, …)
  with its parts: node indices for types, inline data for effects (a
  sorted atom list), regions, sizes, conventions, labels (symbols).
- Edges are indices into the table, not heap pointers. A recursive type is
  a cycle of indices; the rep stays an acyclic heap object, which can be
  frozen, hashed and written byte for byte.
- The table is the type's **minimal graph**, which both printers compute
  already (`minimal_classes`, `k-canon-of`). Two equal types then have
  equal tables, up to the order of nodes, which the rep fixes by walking
  from the root.

### Variables and identity

- **Bound variables** (a `poly`'s, a `dlambda`'s, a module's `abs`) are
  numbered by their binder's position (de Bruijn style), each with its
  name kept only for printing. Alpha-equivalent types have equal reps.
- **Free variables** (those a `stage` needs evidence of) are numbered holes,
  each with its name. Evidence fills a hole with another rep, a graph
  substitution, not a textual one.
- **Abstract types and generative types are objects.** A **type constant**
  is a heap object: its kind, a display name, and a **key**, with the
  representation too for a generative type. A rep names a constant by
  pointer, so identity is object identity: two modules' `t` are two
  objects whatever they are called, and nothing depends on how a printer
  names them.

The key is what lets identity survive serialization. Within one heap,
pointers suffice. Across `.fasl`s, dumps and processes, the same abstract
type must come back as the same object:

- a **generative type**'s key is its definition's stamp (file, form,
  `define-generative` name; as definition stamps already are,
  `definition_stamps`);
- an **abstract type of a load** (a module file's) is the load's file stamp
  and the label: every load of the file shares it, as the hidden global
  `%shared:…` already makes them;
- an **abstract type of a sealing** (`(the (moduleof (abs t type) …) e)`)
  is the stamp of the definition that seals and the label.

A session keeps a weak table of constants by key. Reading a rep (from a
`.fasl`, a dump, the binary form) finds each constant there, or makes it.

### Equality and caches

Each rep carries a **digest**: of its table, with constants by key and
bound variables by position. Equal digests are a fast check, with the
table compared on a match. This replaces the text and `ty_digest`
comparisons of `.fasl` loads (§200), and keys caches. A stage's front end
keeps what it elaborated of `M` by `M`'s rep, so a second stage against the
same module checks only its own code (§201 item 5).

### The two checkers

Each checker gains an **export** (its type, made a rep) and an **import** (a
rep, made a type of its store):

- the Rust checker's, in Rust, over `Ty` and the heap;
- the FX-26 checker's, in FX-26, over `k-ty` and the heap: `k-tys` holds
  heap values already, so its export copies a type's nodes out of the
  instance's array into a rep, and its import does the reverse.

Import is where the checking that text gets is not needed: a rep is well
formed by construction (an exporter made it), so importing elaborates
nothing. Where a rep comes from outside the trusted pieces (a file someone
made by hand, the binary form read from disk), a **validator** checks that
it is well formed (indices in range, kinds right, holes and binders
balanced) before import. That costs a walk, not a parse and a check.

### Serialization

- **In the heap**: a rep is ordinary data. A `.fasl`'s image and a heap dump
  carry it as they carry any value, constants included (they are objects),
  each constant written with its key so that reading it interns it.
- **Binary**: for a `.fasl`'s header, a cache file, a stream between
  processes. The node table written as it is: a node's tag in a byte,
  indices and counts as variable-length integers, symbols and constants by
  number into tables at the front (names, keys). No parsing beyond
  reading integers; validating as above.
- **Readable**: the type syntax programs are written in, printed from a rep
  (one printer, of reps, for both checkers, so the two cannot print one
  type two ways) and read into one. For messages, `,type`, tests, and
  debugging a binary form: a tool prints a rep, or a binary file of reps,
  as text.

## The migration, in steps

Each step keeps every machine working and the suite passing; the text paths
go only when nothing uses them.

1. **Reps and the Rust checker.** The rep's layout (`fixpt-heap::layout`),
   type constants and their session table, the Rust export and import, the
   digest, the validator, the readable printer and reader. Tests: every
   type of the test programs exported, imported and exported again is the
   same rep; printed, read and printed again is the same text.
2. **The FX-26 checker.** Its export and import, in FX-26. Test: the two
   checkers' exports of each test program's types are the same reps (the
   agreement test, by reps, not by lines).
3. **`stage` and evidence by rep.** A `stage`'s call site keeps `M`, `E`,
   `R` as rep constants in its code; `reify-*` make reps; evidence fills
   holes. The stage's front end imports, and caches by rep. The Rust
   checker's stage path (`stage_lower`, `stage_check`) likewise. Measure:
   §201 item 5's 250 ms, and Heist's 49.
4. **Sessions by rep**: a step's types, the pending definitions'.
5. **`.fasl`s by rep**: a header's types in the binary form, compared by
   digest, entered by import (§200's step 3, which text could not make
   cheap). Measure s7st's warm start.
6. **Text paths removed**, where nothing is left on them.

## Open questions, for the user

1. **The keys of sealed abstract types.** Keyed by the sealing definition's
   stamp, a sealing is one type however often its definition runs. A
   sealing inside a procedure, made at each call (first-class modules),
   would need a key of each run's. Is a static key per sealing site the
   intended meaning, as the checker treats it now?
2. **Trust of reps read from disk.** Validated before import (above), or
   trusted as a `.fasl`'s machine code is, until proof-carrying code?
3. **Where the binary form lives**: in the heap crate, so that the
   runtime, the CLI and both checkers share it; or a crate of its own.
4. **Order of work**: steps 1 to 3 settle Heist's item 5; 5 settles
   §200's step 3. Stop after 3 and measure, or go on?
