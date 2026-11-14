# The Rust front end's syntax in the heap, as FX-26's `syn`

Design note, 2026-11-13, the user's direction (`TODO.md` §250). Built in
stages on the branch `syn-handover`.

## Why

A session on the native convention compiled each form by writing the
Rust expander's output back out as text, which the front end written in
FX-26 read and parsed again, at position 0 of that text. Places in code
were characters of texts no one sees, every form's from 0, and a macro's
template places, in an earlier form's text, were resolved against the
current one's (`sources.rs`'s matching of a position to a datum): code a
macro made placed on a line with no code on it. Patching the matching
covers the cases found. Instead: no text between the two front ends. The
Rust reader and expander build the structure FX-26's parser takes, `syn`
(`eager-reader-types.fx`), in the heap, and the session hands it over as
it is.

## The pipeline

reader → `syn` in the heap → expander, `syn` to `syn` → parser, `syn` to
the checker's AST (`ast.rs`, unchanged). The Scheme, FX-87 and FX-91
front ends keep `fixpt_read::Syntax`; the reader builds either, through a
trait (`fixpt_read::Build`).

## Decisions

1. **Values within a phase, handles across code that runs.** The heap
   collects only at safepoints, never in an allocation, so the reader, the
   expander and the parser hold raw `Value`s through a view of the heap.
   Wherever FX-26 code runs between (a session's forms; a procedural
   macro's transformer, mid-expansion) and whatever lasts from one form to
   the next (macros' definitions and templates), they hold handles.
2. **The heap is the one that runs the code.** In a session, the session's;
   the checker is handed it at its reading entry points rather than owning
   one, so that what it expands is handed over with nothing copied; its
   handles (`Kept`) are that heap's roots, released when let go (the
   user's, 2026-11-13). Where there is no session (tests, `fixpt check`, the comparisons,
   `.fasl`s), a heap of the checker's own.
3. **A node's place is the position truth.** `syn`'s start and end:
   characters plus a file's base (the program's 0; a loaded file's a
   billion times its number; each of a session's inputs after the one
   before), and its expansion. Characters, as FX-26 counts them: its
   strings are indexed by character (UTF-32 in the heap), so a place is
   also an index into the text it read. The Rust checker's spans are in
   characters too (`fixpt_fx26::chars`; the user's, 2026-11-13):
   `heap_syn::span_of` and `at_of` are its base's arithmetic and no more,
   and what converts a span to bytes, line and column holds the text it
   is in (a message's driver, a piece cut out). At first spans stayed
   bytes, converted by a table of where each character starts, by base;
   but the program's base, 0, was any text's read as file 0, and a
   built-in module read so took the program's table (Kayak's report:
   its `load-module` past the module's length "not read"). A text read on
   the side, apart from the program (a type for the checker's tables, a
   file looked at before it is loaded), has a base of its own, below
   every file's. The Rust reader's errors, in bytes, are made characters
   where it reads (`heap_syn`'s `read_at`). Messages find file, line and
   column from the session's table of texts and bases. A node a macro
   made: its expansion, whose chain of uses the expander keeps, as FX-26's
   expander does.
4. **Symbols are the heap's.** An atom's symbol is a heap symbol, compared
   by identity; the parser maps them to the checker's `Sym`s through a
   cache.

## Stages

1. The `syn` view and builder; the reader building `syn` (a test: the same
   as FX-26's reader makes, for every program the tests read).
2. The parser reading `syn`; the expander's `Syntax` converted for it,
   meanwhile.
3. The expander on `syn`: hygiene, shapes, inference, procedural macros.
4. Sessions handing the expander's `syn` to FX-26; the text and
   `sources.rs`'s matching gone. §250's reproduction as a test. In steps:
   places in characters; the checker in the session's heap; the handover,
   a macro's code placed by its provenance (keys, as FX-26's expander
   gives `regcode.fx`'s `r-key-given!` and `r-use-given!`); the session's
   interface on handles, the `Syntax` wrappers gone. Done 2026-11-13: a
   form held is a `heap_syn::Form`, reference-counted, its slot of
   `%syntax-kept` let go at its heap's next lending after its last copy
   drops (the user's choice), and refused in another heap's lending; the
   checker's interface takes and gives `Form`s; a form run is handed over
   where it is, nothing copied. `Syntax` is left where a form is written
   out as text (messages, `.fasl`s), in the spec tests, and for the forms
   FX-26's own reader reads (`syntax_of`, `syn_of`): stage 5's.
5. `Syntax` gone from the FX-26 front end; the Rust checker timed on the
   front end itself. Done 2026-11-13. Syntax is written as text by
   `Syn::written` (the Rust reader's writer's atoms, `write_atom`). A
   quote's constant is the quote's `Form` in the AST (the user's choice):
   the lowering and the compilers read it where they run, the compilers
   through `Checker::syn_in`, which lends the heap they compile into when
   the checker's syntax is in it (a session's), so a session lowers inside
   `checking`. What FX-26's own reader reads is the checker's as it is,
   its symbols noted (`heap_syn::adopted`). A reading's digest
   (`ids.rs`) folds `syn` read into a heap aside (the user's choice), its
   atoms as the heap has them, as `readings.fx` folds them: `4/2` the
   integer `2`. `Syntax` stays where it is not the front end's: the
   Scheme the lowering makes (`Sx::syntax`), the other languages' front
   ends, and tests that hold the readers to each other.

The risk to watch: the Rust checker's speed, a heap's view dearer than a
Rust tree. Measured after stage 2.
