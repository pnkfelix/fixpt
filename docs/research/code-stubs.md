# Code stubs: every procedure's code runs, so native calls need no test

Status: kayak's request to the Fixpt team (the user, 2026-10-26: "We can
try delivering the request to the fixpt team"), from the user's design
intent for bloblets, raised in kayak's review of its departures from
Fixpt (`docs/research/departures.md`, departure 4; C230). The details are
this note's proposal, for the Fixpt team to adjust as they implement it,
and to say so in their copy.

## The intent

A bloblet's layout (fields, then a binary suffix) is meant to let a
procedure's code be *uniformly callable*: whatever a closure holds as its
code is a code bloblet, and its suffix is machine code. Native code then
calls any closure the same way, with no test of what it is. A cellular
word, which an interpreter runs, carries in its suffix a tiny stub that
dispatches to the interpreter.

## What the convention does today

The declared convention's `closures` clause (`declared-conventions.md`,
step 5):

    (closures (kind 41) (code-field 2) (first-free-field 3)
              (native-when-code-at-least code-lo))

A native call of a closure it was given (made code's, e.g.
`made-code-x86_64/frames.fx`, instructions 28 to 33):

    mov r9, [rbx-20]        ; field 2, the closure's code
    cmp r9, [r15+216]       ; at least the state's code-lo?
    jb  foreign-path        ; no: not native code; by `foreign`
    add r9, [r15+208]       ; yes: plus the distance, where it runs
    call r9

So every call of an unknown procedure pays a compare and a branch, and
a runtime must keep every heap object's address below every code
bloblet's: Fixpt by its layout (the code area at the reservation's top),
kayak's tier 1 by an order checked when its reservations are made (C230),
since its code area is a reservation of its own.

## The request

1. **Every procedure's code field holds a code bloblet in the code area,
   whose suffix runs.** For native code, as today. For a cellular word,
   a stub: the closure is already in the closure register and the count
   in the count register, so the stub is the `foreign` routine's entry,
   a tail jump:

       x86_64:  jmp [r15 + foreign]              ; 41 ff a7 20 01 00 00
       arm64:   ldr x16, [x24, #foreign]; br x16

   (as the native adapter, `fixpt-native`'s `adapter()`, less its load of
   the free value). Likewise every other kind `foreign` takes today
   (continuations, primitives as values, …): its field 2 a code bloblet
   whose stub enters `foreign`, or its own entry.
2. **Words in the code area.** A stub runs only where its bloblet is
   executable, at its reference plus the distance: so cellular words,
   which Fixpt publishes with their fields frozen already, are made in
   the code area, which never moves and which the collector marks and
   sweeps (`object-model.md`, "A collected code area").
3. **The convention says so.** The clause becomes, say,
   `(closures (kind 41) (code-field 2) (first-free-field 3) (code-always-runs))`,
   and native calls drop the test:

       mov r9, [rbx-20]
       add r9, [r15+208]
       call r9

4. **Code written for the old clause still works**, if a runtime keeps
   `code-lo` at its code area's lowest: a cellular word, now in the code
   area, passes the old test, and its stub enters `foreign`, as the old
   path did. So the change need not break `made-code*/*.fx`; new code may
   drop the test.

## What it buys

- One compare and branch fewer on every call of an unknown procedure.
- No address-order requirement between a runtime's heap and its code
  area: kayak's tier 1 drops its check (C230), and a runtime may lay its
  spaces out as it likes.
- **A patch point for tiering.** A word's stub is where its code is
  entered from native code: when a word is compiled to native code
  later, its stub can be made a jump to the compiled code (or the
  word's code field pointed at it), and every native caller then runs
  the compiled code with no change of its own.
- Native code and cellular code callable alike, which the adapters
  between conventions (`%fx26-convert`) then need for fewer cases.

## What it costs

- Every word lives in the code area: the area holds more, is swept more,
  and making a word (at load, by `eval`, by a REPL) writes through the
  area's writable view and flushes the instruction cache for its stub's
  bytes.
- Each kind of procedure needs a stub (shared, one per kind or per
  routine, not one per object, where its entry is the same).
- The stub's bytes are the target's: one per architecture, as the
  adapter's are.

## What each side does

**Fixpt** (first):
- every kind a closure or a call can hold as code given a code bloblet
  that runs, words made in the code area;
- the convention's clause, and native calls without the test (keeping
  `code-lo` meaningful for code written for the old clause);
- its machines and compilers so; tests: a made-code call of a cellular
  closure, a continuation, a primitive, with no test; the old
  `made-code*/*.fx` unchanged and passing.

**Kayak** (after the pin moves): the same in kayak-jit's routines and
tier 1 (words in tier 1's code area; the stubs; the address-order check
of C230 dropped), and in kayak's compiler to cells where it writes the
convention.

## Open questions

- Which kinds `foreign` takes today, each's stub or entry.
- Whether a word's stub should be its own bloblet (shared) or each word's
  suffix (per word, so that it can be patched when the word is compiled):
  the patch point argues for per word.
- Memory: how much the code area grows when every word is there, and
  whether words made by a REPL or `eval` should be swept as eagerly.
- Whether macOS's per-thread `MAP_JIT` toggling, kept as a hardening
  option (kayak's `TODO.md`), changes how words are written there.

## What Fixpt does (2026-10-26)

Kayak's request is above, as it came. This section is what Fixpt built,
where it differs, and the open questions decided.

### The code area in two parts

The heap's code area (`fixpt-heap`'s `heap/code.rs`) has two parts, each
walkable, each its own free list, swept alike:

- the **stubbed part**, at the area's start: what native code calls that
  is not native code. Each bloblet's suffix is the stub that enters
  `foreign` (`fixpt_heap::layout::stub`: `jmp [r15 + 288]; int3` on
  x86_64, `ldr x16, [x24, #288]; br x16` on arm64; a test checks them
  against the assemblers, and the state's `foreign` is asserted at 288);
- the **native part**, from half way: native code, as before.

The state's `code-lo` is the native part's start, not the area's. So
every test written to the older clause keeps its meaning exactly: a word
is below `code-lo` and goes to `foreign` as it did, by the caller's own
path, and needs no stub there. This differs from the request's point 4
(`code-lo` at the area's lowest, a word passing the test and its stub
entering `foreign`); the result is the same, and Fixpt's own machines
that tell native closures from cellular ones by `code-lo` (the register
machine's code, the cellular machines' native routines) need no change.

### Which kinds `foreign` takes, and each one's field 2

`foreign` (`call_foreign`, then the cellular engine's `call_value`) took,
before this change: cellular closures, cellular continuations, and the
bytecode VM's primitives (the simple ones run; the rest refused); it
refused the VM's closures ("native code cannot call back a procedure of
the bytecode VM") and anything else ("a call of what is not a
procedure"), the VM's continuations among them. A native closure never
reached it. The kinds a procedure may be (`%fx26-procedure?`) and each
one's field 2 now:

| Kind | Field 2 |
|---|---|
| `native-closure` (41) | its code, in the native part, as before (an adapter's too) |
| `cellular-closure` (38) | its word, in the stubbed part, the word's suffix the stub |
| `cellular-continuation` (39) | the heap's shared stub (`Heap::foreign_stub`); its other fields one further (`CONT_STUB` is 2) |
| `closure` (8, the VM's) | the shared stub; its code at 3, its values from 4 |
| `primitive` (19, the VM's) | the shared stub, a fifth field, last |
| `continuation` (14, the VM's) | the shared stub, a sixth field, last (`cmarks::K_STUB`) |

`foreign` takes a native closure too now (the engine calls it as it
calls one, `as_cellular`), so that code written to the older clause
never fails on one, whatever its test finds. What it refuses, it refuses
as before, and says so: a VM continuation called from made code fails
with "a call of what is not a procedure", not a crash.

### Words in the code area

Every word `make_cellular_word` makes is in the stubbed part, fields
frozen, suffix the stub, frozen and flushed. Two exceptions, and one
economy:

- A word that is only run, never a closure's, is made in the heap
  (`make_transient_word`): the one `call_value` makes for each call from
  native code, and the one `%run-word` makes to call a closure.
- Words the runtime made again and again alike are made once and kept in
  a global of their own (`Heap::shared_word`): a continuation's closure's,
  an adapter's (one per arity), `vlambda`'s (its register code too), a
  held frame's `return`, and an undefined global's.

Wherever words are copied, they stay code: a graph copied between heaps
(`copy_graph_with`) puts a code bloblet in the same part of the new heap,
and the shared stub is the new heap's own; a message between processes
(`copy_within`) shares the code area's bloblets rather than copying them.
A heap image carries the code area (format version 8): each part's words,
references counted from the heap's start, and its free blocks; loading
puts it back where it was and flushes it.

### The clause, and the code

The convention's clause is

    (closures (kind 41) (code-field 2) (first-free-field 3) (code-always-runs))

and both checkers accept the older one still in its place
(`fixpt_runtime::NATIVE_CONVENTION_OLDER`; `k-conv-older` in the checker
written in FX-26): `made-code*/*.fx` declare it, unchanged, and pass.
`native-convention` gives the new one. The convention read as data
(`fx26:convention.fx`) has a field `code-always-runs`, and keeps
`native-when-code-at-least` at the state's `code-lo` under the new clause:
a generator written before reads what it read, and its test still holds,
so `generated.fx` still makes `frames.fx`'s code byte for byte.

Fixpt's compilers drop the test: the Rust native compilers on arm64 and
x86_64 and the one written in FX-26 on x86_64 (byte for byte the Rust
one's still), at every call of a closure whose convention is `fx` or
native (`invoke`, a global's call past its guard, the control routines'
calls of thunks and receivers). A call sets the count first, which a
word's stub hands `foreign`. A callee typed `cellular` is still sent to
`foreign` directly, without loading its code.

Tests: `made-code*/stubs.fx` (`made_code.rs`, `every_procedures_code_runs`)
make code to the new clause that calls what it is given with no test,
given a primitive, a continuation, and a closure kept cellular, on every
machine, and on two under time slices of 3 and a small nursery; on the
bytecode VM, its primitive, and its continuation refused by `foreign`.
`code_area.rs`: words below native code with their stub, freed when
nothing refers to them; an image round trip of the code area. arm64's
`made-code/stubs.fx` is written to the encoding but run only on arm64.

### The open questions

- **Which kinds `foreign` takes**: above.
- **A word's stub, its own or shared**: its own, necessarily: a cellular
  closure's field 2 is its word, so the stub is the word's suffix. The
  other kinds share one. A word's suffix is a patch point, as the request
  hopes; it is frozen today, and tiering would rewrite it in place.
- **Memory**: not measured yet: how much the area holds once every word
  is there. Words made by a REPL or `eval` are
  swept as every word is: at a major collection, their words counted
  toward the next (`taken`), as a semispace's allocation is.
- **macOS's `MAP_JIT`**: Fixpt never toggles write protection: the code
  area is one shared mapping viewed twice, read+write where the heap is
  and read+execute at a distance. A runtime that toggles per thread
  would have to enable writes around every write into the area, and
  now that words live there that is every word made, and the collector
  updating any word's fields, not only native code made: an argument for
  the two views over the toggle.

### Measured

Kayak's stage 0 (d5840ee), on the default machine, three runs of each,
interleaved, on a quiet machine: before, 19.02–20.22G cycles, 44.84–44.94G
instructions; after, 18.91–19.29G cycles, 44.82–44.91G instructions; loads
and stores alike; the output the same. Making words in the code area, and
the calls without the test, cost nothing measurable here.

## A compiled word's code in the code area too (2026-11-01, `TODO.md` §210)

What this left: a cellular word was a code bloblet, but what the cellular
machine compiled of it was not. Its code was in the machine's own code
space, 256 MB a thread, reached by a slot number in the word's entry
through the machine's table, its table of where to resume beside it, kept
by a weak reference to the word and collected by copying into a space as
large. A thread's machine outlived the sessions that compiled into it and
kept the code of every heap still alive: three of a test's kept sessions,
each with its front end compiled (some 74 MB), and a fourth's, filled it,
with no way to grow (`processes`' `attempt` tests, once the arm64 modules
joined the front end).

Now, on x86_64, a compiled word's entry is its code, as a native
procedure's code field is (`layout::cellular`, `Heap::make_word_code`):

- **A code bloblet in the native part**, its suffix the code, from a
  32-byte boundary (the compiler aligns where calls return from the
  code's start; `make_code_bloblet_aligned`), then the table of where it
  resumes, by `8k`: 0, or 1 more than the byte it resumes at, an offset,
  so no address is in it. Its one field, `COMPILED_RESUME`, says where the
  table begins, in words, so that its bits are the bytes.
- **Run at its reference plus `State::code_delta`**, the code area's
  execute view's distance less a reference's tag, the same for every code
  bloblet of a heap. `NEXT`, `execute` and the machine's entry dispatch on
  the entry's tag: a fixnum is a routine's, `docol`'s for a word of cells,
  by the table; a code bloblet is jumped to. Resuming at a cell reads the
  word's own table. Register code calls a twin's entry so, and an
  adapter jumps to its twin's: neither names a slot.
- **The word keeps its code alive**, and the heap marks and sweeps it as
  any code; a copy of the word copies it, and an image carries it. The
  machine keeps nothing of a word: no slots, no table entries for words,
  no list of what it compiled, no collection of its own; its code space
  holds its own code only.
- **What leaves the process lets compiled code go**: a `.fasl` and the
  front end's caches keep the words with their entries `docol` (or, a
  register word's, 0), to be compiled again where they run. A cache that
  kept the code was 142 MB against 59, and the default machine's start
  3 ms slower for mapping it; whether a cellular machine's start would
  gain from keeping it is not measured.

The arm64 machine is not ported: it compiles nothing (`compile_word` and
the rest decline there) and runs every word's cells, until its `NEXT`,
`enter_cur`, register code's calls and adapter, and `native.fx` and
`native-arm64-regs.fx`, take the entry as x86_64's do.

Measured (x86_64, release, both builds alternated): `cellular_bench`'s
fib 27 1.21 to 1.24 ns a cell run as cells, 0.77 to 0.85 compiled (its
calls and returns: the tag's test, and the resume table read from the
word's code); its loop and its list as they were. Through the CLI, fib 32
on register code (`fx-regs-rsjit-cellcc`, `fx-regs-fxjit-cellcc`) 38 to
34 ms, a call now `call reg` to the twin's code; compiled cells
(`fx-cells-rsjit-cellcc`) 75–83 to 76–77 ms; the default machine and its
start as they were.
