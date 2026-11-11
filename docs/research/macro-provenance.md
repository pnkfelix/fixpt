# Where macro-made code comes from: one provenance for both front ends

The question (`TODO.md` §249, 2026-11-11): with `table.fx`'s lookup written
as macros (the branch `table-macros`), `bootstrap::fixpoint_as_register_code`
found the two compilers' register code for `bucket-find` the same in every
instruction, and different in four of its *places*: the expressions a
macro's template wrote. The user's idea, which this note works out: a
runtime primitive that maps a source location, or a chain of them, to one
value both front ends get, so that the two cannot keep it differently. For
now an integer; later, perhaps, a heap object (§ "Later").

## What a place is, and who reads it

A register word keeps, for each expression's code, the cell where it starts
and the expression's place (`Heap::register_places`: `(cell, place)`
pairs). The compilers make them: the Rust compiler from each expression's
`Span`, the one written in FX-26 from each expression's start
(`regcode.fx`'s `r-enter-place!`, `exp-start`), through
`set-register-twin-at` (`compile-twins.fx`).

A place is for provenance alone. What the checkers find of an expression is
keyed by its place in the parser's walk, not by this
(`loads-and-places.md`). Its readers:

- `fixpt_native::jitdebug`, which finds each place's file and line through
  a resolver the session sets (`set_resolver`), for the debuggers' line
  tables: `scripts/debuggers/fixpt_gdb.py`, its lldb twin, `FIXPT_JIT_DEBUG`,
  `tests/jit_lines.rs`;
- the disassembler and the profiles that name lines;
- `tests/common`'s `same_code`, which holds stage 1's words to stage 2's,
  places too.

A place is an integer: a file's position plus its file's base, the files
`LOAD_BASE_STEP` (a billion) apart in load order (`syn.rs`,
`supply_loaded_in`).

## What each front end has for a part a template wrote

- **Rust:** the part's `Span` is the template's place (`start`, `end`, in
  the file that defines the macro) and an `expansion`, a number whose use
  site the expander keeps. The Rust compiler records `span.start`: the
  template's place, the expansion dropped.
- **FX-26:** the part's position is a *key*, `2^50 + i`
  (`macros-procedural.fx`'s `source-key`, `source-base`), one for each part
  of each expansion, and a table gives, by key, the template's place and
  the expansion that made it (`source-of`); another, each expansion's
  number, macro and use site (`macros.fx`'s `expansions`). The driver says
  an error at the use through them (`syn.rs`'s `fx26_span`). The FX-26
  compiler records the key, which means nothing outside that session.

Both know the same two things, the template's place and the use site; they
record different integers. Recording the template's place in FX-26 too
would need the compiler to see the expander's table, which it does not
(the conductor would have to give it, its effects through every
signature on the way).

## The idea: a provenance, made by the runtime

A *provenance* is a chain of places, innermost first:

1. the template's place of the part (where the macro's definition wrote it);
2. the use site of the expansion that made it;
3. if that use site was itself written by a template (a macro whose
   expansion uses a macro), that template's place and its expansion's use
   site, and so on, out to a place in a text as written.

A place written in a text as written is not a provenance: it stays what it
is, so that nothing changes for code no macro made.

Each place in a chain is written as *(file, offset)*: the file by its key
(as `%shared:KEY` names it: `fx26:table.fx`, a path as resolved), the
offset in its text; not as a position plus a base, which depends on the
order files were loaded in, and differs from one process to the next.

### Now: an integer

The runtime gives a provenance an integer, its *provenance id*:

```
id = PROVENANCE_BASE + (hash(chain) mod 2^K)
```

in a range of its own: past every file's positions and past FX-26's keys
(`PROVENANCE_BASE` `2^52`, say, `K` 50, within a fixnum). The hash is of
the chain's contents, so:

- **the two front ends get the same id for the same provenance**, and
  different ids for different ones (unless two hash alike, below): `same_code`
  holds them to one another unchanged, and a difference left is a real
  disagreement of the two expanders on where a part came from;
- **an id means the same in every process**, so that it may be kept in the
  front end's image and in a `.fasl` and read back elsewhere; an id from a
  counter could not.

The runtime keeps a *registry*, id to chain, for the readers. Two
operations:

- **`%provenance`** `(chain) → id`: the chain registered, its id given.
  Called by the Rust compiler where an expression's `Span` has an
  `expansion`, and, in FX-26, by whatever turns a key into its chain.
- **reading an id's chain**: for the resolver, the disassembler and the
  debuggers, in Rust.

Where FX-26 calls it: the expander, as it makes a key (`new-source-key`),
registers the key's chain with the runtime, `%source-key!` `(key chain)`,
and `set-register-twin-at`, a primitive, gives each key it is handed the
key's provenance id from that table. So the FX-26 compiler records keys as
it does now and needs nothing from the expander; the runtime is where the
two meet. The key table is the session's (the runtime's), as FX-26's
`sources` is now.

Two ids alike for two chains: the registry, when a chain is registered,
finds an id it holds for another chain, and says so (an error in a debug
build, a note in a release one), rather than keep one of them silently.
At 50 bits and the chains a program has, a coincidence is not expected;
the check makes one seen, not assumed away.

**Kept and read back.** Register words hold ids, so the front end's image
and a `.fasl` hold them. The image writer writes the registry's entries
for the ids its words hold, beside them; the reader registers them again.
An id read with no entry is shown as "made by a macro, from where not
known", never a wrong file and line.

### What changes for each reader

- `jitdebug`'s resolver: an id resolved to its chain; a line table gets
  the use site's line (what a debugger shows for a macro's code, most
  often), with the template's in what `fx-frame` and the lldb command say.
  To decide: which line the table gets (§ "Open").
- The disassembler: an id shown as its chain, use site first.
- `same_code`: nothing.
- `tests/jit_lines.rs`: a case of a macro's code, its lines as decided.

## Later: a heap object

The same provenance as a heap object, weakly interned, its places held by
the register words as references: the chain's parts (a file by its
interned key, offsets) readable by any heap reader, the debuggers' among
them (`fixpt_gdb.py` reads heap values already). Interning makes the two
front ends' objects the same object; a weak table lets one no code holds
go.

What makes this better later than now: it wants the image to hold the
objects as heap data that is never moved or collected, and is readable
where it is mapped, a portion of the binary in the heap's own format, an
immutable heap region (§161's static area, §242's static text). The
provenance of the front end's own words would live there, beside the text
it points into. Until such a region exists, an integer with a registry
written beside the image does the work, and the id's chain is the same
information either way: moving from one to the other changes how a place
is held, not what it says.

## Decided (the user's, 2026-11-11) and built

- **A debugger's line for a macro's code: its use**, in a text as written
  (the chain's last); `fx-frame` (gdb) and its lldb twin say the template
  and each use too (`fixpt_place_at`).
- **The chain innermost first.** Who sees the order: only the two front
  ends, which must agree, since the id is of the chain's contents; readers
  show it as they like.
- **Only keys placed in code are made ids**, when the register compiler
  places them (`regcode.fx`'s `r-place-of`), not every key as the expander
  makes it.
- **An entry lives as long as code holds its id**, but immortal code's
  (never collected: an image's, the binary's) for good.

What was built, where it differs from the above:

- **A chain's places are the integers both compilers already write**
  (`place_of`: a character past its file's base, a billion times the
  file's number in load order), not *(file key, offset)*: the two front
  ends number a program's files alike, and every place no macro made
  already agreed between them. An id is no more tied to a process than
  those places are.
- **The registry is each heap's** (`Heap::provenance`,
  `fixpt_heap::provenance`): the Rust compiler asks it for an id, and so
  does FX-26 through the primitive `provenance-id` (`%provenance-id`). A
  register word whose places hold ids is held by a weak reference; after
  each collection, an id every word that held it has died with is let go
  (one asked for, its word not yet made, is kept).
- **FX-26's register compiler needs nothing from the expander**: the
  expander's keys and expansions are in the parser's region, which the
  compiler's effects do not reach, so the conductor copies what it needs
  to the compiler's region after each parse (`keys-mirrored!`: each new
  key's template place and expansion, each new expansion's use site), in
  `parse-checked`, the bootstrap driver's `b-parse`, and the Rust driver's
  parse (`syn.rs`). The compiler turns a key it places into its chain and
  asks `provenance-id`.
- **A file read for its shape first** (`Checker::file_shapes_for`) is read
  as file 0; its forms are placed in their file later (`placed_in`), and
  now so are the uses of the expansions made in that reading
  (`fixpt_read::expansion_placed_in`), which kept file 0 and so a place in
  the program's text.
- **Readers**: `jitdebug`'s line tables take an id's use
  (`note_chain`, noted where code is placed, the heap at hand);
  `fixpt_place_at` says the chain. The machines that compile a form from
  its text written out (the CLI's sessions) place code at characters of
  that text, mapped to the form's datums (`sources::resolve`): a datum a
  macro made is now placed at its use, and `sources::describe` says its
  chain; but that mapping is by position in the text, which for a form a
  macro expanded is not always the datum the code came from (`TODO.md`
  §250).

Not yet (`TODO.md` §249): an image's and a `.fasl`'s words hold ids
whose entries are not written beside them, so read in another process
they are "made by a macro, from where not known"; entries for an image's
code to be immortal; `copy_graph_from` carrying a word's entries into the
heap it copies to.
