# Performance, as M12 proceeds

M12 moves pieces of the tooling from Rust into FX-26, which then run on the
Rust engines, so they may well be much slower (`PLAN.md`, §11, decision 10).
This file keeps the record: what each piece costs in each form, measured the
same way each time. If the FX-26 forms become the bottleneck, that is the
signal to start on native code earlier than M10.

**Collections that move everything.** Under a bug-finding policy
(`Heap::gc_every`, which `gc-stress` sets to 1), every collection starts
to-space with a filler of a size that changes each time, so that every
object moves at every collection. Without it a copying collector tends to
put each object back where it was, and a stale Value held across a
collection still finds its object: a real rooting bug in the eager
reader's driver survived the whole `gc-stress` suite that way, until one
ordinary collection landed in its window. `(%gc-every! n)` sets the policy
from Scheme; `%gc-count`, `%gc-words-copied` and `%sro` (after Larceny's)
look at the heap from outside.

**`gc-stress` is not a benchmark.** It collects at every safepoint to shake
out rooting bugs, so it is a correctness check, and far too slow to time
anything with. At a checkpoint that touches the collector, the routine check
is a subset, about a minute:
`cargo test -p fixpt-heap --features gc-stress` and
`cargo test -p fixpt-scheme --features gc-stress --test smoke --test control --test image --test macros`.
The full `fixpt-scheme` suite under it takes well over an hour, mostly the
eager-reader tests, and is run only at milestones.

Measurements are on the development machine, as best of several runs.
Debug builds are what `cargo test` runs; release numbers come from
`cargo run --release`.

## Baselines, before M12

| what                                                           | Rust | Scheme | FX-26 | notes                                  |
| -------------------------------------------------------------- | ---- | ------ | ----- | -------------------------------------- |
| eager reader, `fixpt-fx26/tests/eager.rs` (debug, whole suite) | —    | —      | 5.5 s | Scheme and FX-26 readers, both engines |
| eager reader, Scheme suite under `gc-stress`                   | —    | 83 min | —     | collects at every safepoint            |

## The engines benchmark, through the object-model changes

`cargo run --release --example engines` (crates/fixpt-scheme/examples/engines.rs):
six small programs on each engine, totals in seconds, best of three runs.
Single programs vary by up to 40% run to run (`fib 25` on the AST engine
ranges 0.028–0.041 s), so only the totals are compared.

| after                                                                                           | AST   | bytecode | notes                                                                            |
| ----------------------------------------------------------------------------------------------- | ----- | -------- | -------------------------------------------------------------------------------- |
| before M12 (dac418f)                                                                            | 0.626 | 0.392    |                                                                                  |
| A2–A4 (every object a bloblet header; code as bloblets)                                         | 0.636 | 0.393    | no measurable change                                                             |
| A5a, first try (raw types as bloblets; the accessors check the pointer style)                   | 0.667 | 0.392    | AST ~5% slower: a branch on every node read                                      |
| A5a (code's nodes and constants as its own fields)                                              | 0.634 | 0.393    | back to baseline: a node or constant is one load at a fixed offset from the code |
| A5, first try (every object with fields a trailered bloblet, read through the generic accessor) | 0.689 | 0.416    | 6–8% slower: the trailer decoded out of line on every field read                 |
| A5, trailer read inline                                                                         | 0.656 | 0.404    |                                                                                  |
| A5, closures and AST frames at fixed offsets                                                    | 0.642 | 0.400    |                                                                                  |
| A5 done (boxes and symbols at fixed offsets; tag `010` retired)                                 | 0.628 | 0.394    | at baseline                                                                      |

The per-piece table fills in as each piece moves.

## Threaded code: the Rust inner interpreter and the native one (A′3)

`cargo run --release -p fixpt-native --example threaded_bench`: the same
threaded words on both machines, results checked equal, best of three.
A *cell* is one step of the Rust machine; the native machine counts only
word entries and taken branches (its fuel), shown for scale.

| program                               | cells  | Rust    | native   | native ns/cell | Rust / native |
| ------------------------------------- | ------ | ------- | -------- | -------------- | ------------- |
| fib 25                                | 2.31 M | 0.007 s | 0.0013 s | 0.55           | 5.4×          |
| fib 27                                | 6.04 M | 0.018 s | 0.0033 s | 0.55           | 5.4×          |
| sum-to 10M (loop)                     | 110 M  | 0.263 s | 0.077 s  | 0.70           | 3.4×          |
| sum-by-list 60k (cons, 5 collections) | 1.38 M | 0.004 s | 0.0013 s | 0.96           | 3.0×          |

For scale only, not a comparison: the engines benchmark's `fib 25` takes
0.027 s on the AST engine and 0.019 s on the bytecode VM, but that is Scheme,
with closures, frames, and generic arithmetic, where the threaded `fib` is a
hand-written Forth word on fixnums. What the table does say: the native
`NEXT` costs about half a nanosecond per cell, the Rust `match` loop about
three, and the machine's checks (fuel and stack limits at every word entry
and taken branch, tags and overflow in every primitive) leave `NEXT` the
dominant cost. `cons` calls out to Rust, which saves and reloads the
machine's registers; that is the 0.96.

## Threaded code: stencils at each optimisation level (A′4)

The same words again, now also on the stencil machine: the routines written
in Rust with `become` (`crates/fixpt-native/stencils/threaded.rs`), compiled
by the build script with the installed nightly at `-C opt-level` 0, 1, 2, 3
and `s` (debug assertions and overflow checks off at every level, since
their calls into `core` could not be copied), and placed by copying. Best of
three, ns per cell of the Rust machine:

| program                | Rust, release build | Rust, debug build | hand-encoded | stencils -O0 | -O1  | -O2  | -O3  | -Os  |
| ---------------------- | ------------------- | ----------------- | ------------ | ------------ | ---- | ---- | ---- | ---- |
| fib 27                 | 3.85                | 78.6              | 0.57         | 4.28         | 0.63 | 0.62 | 0.64 | 0.65 |
| sum-to 10M (loop)      | 2.64                | 76.6              | 0.67         | 4.11         | 0.58 | 0.58 | 0.59 | 0.59 |
| sum-by-list 60k (cons) | 2.80                | 76.4              | 0.86         | 4.20         | 0.92 | 0.90 | 0.84 | 0.89 |

Machine code: hand-encoded 2.1 KB; stencils 9.3 KB at `-O0`, 2.5–2.7 KB
otherwise. The Rust machine's release number for `fib` varies 2.9–3.9 ns
between sessions; the native ones stay within a few percent. The native
machines' own times do not depend on how the host was built, except where
they call out into it: `cons` costs 3.3 ns/cell under a debug host, whose
collector is unoptimised.

What it says:

- **Rust with `become` expresses the inner interpreter**, and optimised it
  matches the hand-encoded machine: a little slower on `fib`, faster on the
  loop. The four optimised levels are indistinguishable.
- **Why the loop is faster**: LLVM's `0branch` tests the flag before loading
  the branch offset, so the untaken path skips the offset cell with one
  `ldur [ip, #-8]` and adjusts the ip once; ours loads the offset either
  way. A scheduling lesson for our own encoder, not a different machine.
- **At `-O0` the tail calls still hold**: 110 million cells with no stack
  growth, at about the speed of the Rust machine built with `--release`,
  and 18× the Rust machine built without.

## FX-26 compiled to threaded words, on each machine (C9c-3)

`fixpt --dialect fx26 --fx26-run threaded --threaded-machine M run FILE`,
release build, best of three. The programs are FX-26, compiled by the
compiler written in FX-26 (`src/compile.fx`): `fib 27` (doubly recursive,
`<`, `+` and `-` as the machine's primitives) and a `letrec` loop counting
to one million (its `=` a runtime primitive, `prim`). "Run" is the word's
own run, timed inside the process around `%run-word`
(`FIXPT_TIME_WORDS=1`); the front end's loading, reading, checking and
compiling come to 0.11 s before it, whatever the machine.

| program      | lowered to Scheme (VM) | FX-26 evaluator | Rust machine | hand-encoded | stencils -O2 |
| ------------ | ---------------------- | --------------- | ------------ | ------------ | ------------ |
| fib 27       | 0.05 s                 | 17.1 s          | 0.041 s      | 0.0040 s     | 0.0056 s     |
| count to 1 M | 0.08 s                 | 24.7 s          | 0.083 s      | 0.024 s      | 0.026 s      |

The first two columns are wall time less startup (0.00 s lowered, 0.11 s
evaluated); `run` rather than the REPL, whose step limit stops the lowered
programs at 20 million steps.

What it says:

- **Compiled FX-26 on the native machines is as fast as hand-written
  threaded code**: `fib 27` takes 4.0 ms here and 3.3 ms as the Forth word
  of the table above, though this one has frames, closures and generic
  calls. Ten times the Rust machine, twelve times the Scheme VM.
- **A routine left to Rust costs what its way back costs.** The first
  version sent `prim` through the round trip, which copies both stacks
  each time: the loop took 0.14 s on the native machines, barely ahead of
  the Rust machine. `FIXPT_CALLOUTS=1` (the native machines' per-routine
  count of call-outs) showed two million `prim`s and nothing else; calling
  the primitive in place, with the stacks as the collector's roots where
  they lie, made it 0.024 s. The remaining cost is the call-out itself,
  about 20 ns, and the primitive's generic `=`: a compiler that knew both
  sides were fixnums could use the machine's own.
- **The evaluator is 300–400× the lowering**: an interpreter written in
  FX-26, lowered to Scheme, on the VM. It is the reference, not a way to
  run things.

## The checker written in FX-26, on the front end (C10)

`PROBE_FILE=front-end FIXPT_TIME_PHASES=1 cargo test -p fixpt-fx26 --test
checker probe_file -- --ignored --nocapture`: the whole front end (reader,
parser, checker, tables, evaluator, compiler; 4,660 lines, 738 top-level
forms), checked by each checker. Debug build, one run:

| checker                                        | time   |
| ---------------------------------------------- | ------ |
| Rust (`Checker`, reading with the Rust reader) | 0.96 s |
| FX-26: reading and parsing, in FX-26           | 63 s   |
| FX-26: checking, lowered to Scheme, on the VM  | 317 s  |

Both say the same about every form. The FX-26 checker is about 330 times
slower. It takes after the Rust checker, which recomputes each
expression's free variables at every mask, with linear environments and
lists for sets. On the Scheme VM, that is quadratic work paid many times
over. `table.fx` alone (110 lines) takes 0.86 s against 0.01 s.

## The bootstrap: the front end compiling itself (C11)

`cargo test --release -p fixpt-fx26 --test bootstrap fixpoint`. Each run
does the same work: read, parse, check and compile the front end and its
driver, 4,700 lines. Release build:

| what                                                              | time   |
| ----------------------------------------------------------------- | ------ |
| the Rust reader and checker                                       | 0.07 s |
| FX-26 read, parse and check, lowered to Scheme (C10's checker)    | 7.8 s  |
| stage 1: the Rust checker; FX-26 read, parse and compile, lowered | 1.7 s  |
| stage 2: all of it compiled, on the hand-encoded native machine   | 8.4 s  |
| the whole fixpoint test                                           | 10.5 s |

**The debug build misled.** It took 7 minutes, and a first profile of it
blamed the round trips. `sample` showed the time in `Field::mask`, slice
indexing and iterator `next`: unoptimised Rust in the heap and the Rust
machine, which the native machine calls out to. The machine code is the
same in both builds; everything it calls is not. Performance comparisons
here are release builds from now on.

**The collector grew too late.** It grew a semispace only when the live
data filled three quarters of it, and then collected again after a
sliver. With 42 million words live, stage 2 in debug collected 117 times
and copied 4.9 billion words. Keeping a semispace at least three times
what is live brought that to 16 collections and 0.67 billion words. In
debug, that took stage 2 from 315 s to 239 s.

Compiled and run natively, the front end is still no faster than lowered
to Scheme. The native machine's call-out counts and times
(`FIXPT_CALLOUTS=1`), in release, for stage 2 alone:

| routine                      | call-outs   | time   |
| ---------------------------- | ----------- | ------ |
| `prim` (a runtime primitive) | 171,536,930 | 4.08 s |
| `callcomp` (round trip)      | 260,870     | 1.24 s |
| `cons`                       | 5,101,843   | 0.97 s |
| `tailcall` to a continuation | 260,868     | 0.96 s |
| `abort` (round trip)         | 260,870     | 0.41 s |
| `withmark` (round trip)      | 90,035      | 0.24 s |
| `closure`                    | 4,111,142   | 0.09 s |

`closure` was a round trip until the numbers above were taken, and is now
a direct call-out like `prim`.

**Then, in order, each measured before and after** (stage 2, release):

| change                                                              | stage 2 |
| ------------------------------------------------------------------- | ------- |
| as above                                                            | 8.4 s   |
| `null?`, `not`, a field's read, a reference's get and set: routines | 5.3 s   |
| control on the native stacks in place, no round trip                | 4.5 s   |
| capture and reinstatement without intermediate copies               | 3.9 s   |
| `with-mark` in tail position replaces the frame's mark              | 1.9 s   |

- **Primitives as routines.** Counts per primitive (also under
  `FIXPT_CALLOUTS`) showed `null?` 101 million times and `%bloblet-ref`
  49 million, out of 171 million. The compiler now emits `lit () eq` for
  `null?`, `lit #f eq` for `not`, and the `field@` and `field!` routines
  for fields, references and `letrec`'s boxes. The native machine already
  had machine code for those routines. `prim` call-outs fell to 9.7
  million.
- **Control in place** (`fixpt-native/src/control.rs`). Prompts, marks,
  aborts, capture and reinstatement are the Rust machine's routines
  transcribed to work on the native stacks directly. A native return entry
  has the Rust machine's bits, so nothing is converted. Round trips now
  lift 57 words in all.

- **Capture without copies.** A sample showed `vector_from` and `kind`
  (a `const fn` comparing strings, run at run time) at the top. Capture
  now writes the heap vector straight from the stack, and reinstatement
  reads it with its base found once.
- **Marks in tail position.** Counting the words captured showed 3,664 a
  continuation, growing as the reader went on. The reader's top-level loop
  marks each form in tail position, which in Scheme replaces the frame's
  mark. The threaded machines stacked a new one each time, so the
  reader's continuation carried one mark per form read so far. The new
  routine `withmark-tail` has Scheme's meaning, and the compiler emits it
  for `with-mark` in tail position. Captures now average 88 words.

## Words compiled to machine code (C11a)

`NativeMachine::compile_word` places a word's routines' code inline in
cell order, with the ip kept in step, branches as jumps, and no dispatch
between cells. `cargo run --release -p fixpt-native --example
threaded_bench`, ns per cell of the Rust machine:

| program                | hand-encoded | its words compiled |
| ---------------------- | ------------ | ------------------ |
| fib 27                 | 0.57         | 0.57               |
| sum-to 10M (loop)      | 0.69         | 0.68               |
| sum-by-list 60k (cons) | 0.89         | 0.84               |

No gain on these: the dispatch removed was already cheap on this CPU,
whose branch predictor follows `NEXT`'s indirect jumps. The time is in
the routines' own work, which inlining keeps. A temporary `brk` at a
compiled word's entry confirmed the compiled code runs.

On the bootstrap's stage 2, all 4,700 lines of the front end compiled that
way, the gain is 1.9 s to 1.4 s, and the fixpoint holds
(`fixpoint_with_words_compiled`). Real gains would need a real compiler:
the top of the stack in registers, operands as immediates, the ip made
only where something reads it.

**Made by FX-26 (C11c).** The same compiler written in FX-26
(`native.fx`), compiled and running on the hand-encoded machine, compiles
all 817 words of the front end, 1.1 million instructions, in 2.7 s
(release). The words are the same as the Rust compiler's, which takes
milliseconds. Stage 2 on that code takes 1.7 s, and the fixpoint holds
(`fixpoint_with_words_compiled_by_fx26`).

## The FX-26 checker's environment and sets (after C12)

A per-word profile (`FIXPT_PROFILE`, or `probe_profile_check` in
`tests/bootstrap.rs`: cells run per word on the Rust machine, each lambda
named by where its body starts) showed where the FX-26 checker spent its
1.88 billion cells checking the front end: 43% testing whether a type was
in a walk's list of types seen, 21% looking a name up in the environment,
a list of some 900 bindings.

- **The environment is a table** (`table.fx`, now loaded before the
  checker): each name's types, innermost first, and a trail of names
  bound, so a scope is left by unbinding back to a mark.
- **A walk's seen types are marks**, an array beside the type arena, with
  a new epoch per walk: nothing to allocate or clear.
- **Each type's regions are kept** once found, since a type does not change
  once built.

The checker says the same as before on every program the tests compare.
Checking the front end now runs 0.35 billion cells:

| checker, front end            | before | after  |
| ----------------------------- | ------ | ------ |
| FX-26, lowered to Scheme      | 6.65 s | 1.60 s |
| FX-26, compiled, hand-encoded | 1.36 s | 0.37 s |
| Rust                          | 0.06 s | 0.07 s |

The next 47% is free variables: every mask recomputes them for its whole
subexpression, testing membership in lists as it goes. The Rust checker
does too. The fix is to compute them once, bottom-up, as synthesis goes.

## The comparison: each piece, Rust and FX-26 (C12)

`cargo test --release -p fixpt-fx26 --test bootstrap comparison --
--ignored --nocapture`. Each piece alone, on the bootstrap program (the
front end and its driver, 4,700 lines), release build. "Check" is the
Rust checker's parsing and checking together, and FX-26's checking of
trees already parsed. Each FX-26 piece runs in a session that has
collected away stage 1's leftovers first.

| pieces                                | read   | parse  | check  | compile |
| ------------------------------------- | ------ | ------ | ------ | ------- |
| Rust                                  | 0.00 s | —      | 0.06 s | —       |
| FX-26, lowered to Scheme              | 1.15 s | 0.04 s | 6.65 s | 0.35 s  |
| FX-26, compiled, Rust machine         | 0.54 s | 0.05 s | 9.02 s | 0.51 s  |
| FX-26, compiled, hand-encoded machine | 0.20 s | 0.03 s | 1.36 s | 0.08 s  |
| FX-26, compiled, stencils, -O2        | 0.21 s | 0.03 s | 1.47 s | 0.09 s  |

- **Compiled and run natively, every FX-26 piece beats itself lowered:**
  reading by 5.8 times, checking by 4.9, compiling by 4.4.
- **The Rust machine is the slow one.** Compiled FX-26 on it checks more
  slowly than lowered FX-26 on the bytecode VM. It is the oracle, written
  for clarity: a `match` per cell, and a bounds-checked vector per stack.
- **The Rust pieces are far ahead where the FX-26 ones copy their
  algorithms loosely.** The FX-26 checker keeps sets as lists and
  recomputes free variables at every mask, as the Rust one does with hash
  sets. It checks the front end 22 times slower. Reading, which the Rust
  reader does without checkpoints, is 50 times slower, since the eager
  reader captures a continuation for every character, by design.
- **The stencils match the hand-encoded machine** within 10%.

## The eager reader in FX-26, building syntax with positions (B8)

`cargo test -p fixpt-fx26 --test eager` (debug, whole suite, 9 tests),
the same machine, the same day:

| reader                                        | time    |
| --------------------------------------------- | ------- |
| before B8: data only                          | 11.45 s |
| B8: `syn` with spans, each carrying its datum | 13.22 s |

About 15% for the positions. A first try that made each list's datum by
converting its elements' `syn`s again, at every level, ran out of the
engine's step budget on the reader's own source; carrying each piece's
datum from when it was read fixed that.

**Open: the suite's baseline.** The table at the top says 5.5 s for this
suite before M12; it now takes 11.45 s without B8. Tests have been added
since, the largest reading the reader's own source, which has grown, so
the two are not the same work; which part of the difference is slowdown
has not been measured yet.
