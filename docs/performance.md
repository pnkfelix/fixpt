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

## M13's benchmarks: the baseline (13b)

`cargo test --release -p fixpt-fx26 --test bench -- --ignored --nocapture`.
The programs are in `tests/programs/bench`:

- `fib 30`: calls;
- a letrec loop to 10 million;
- lists built and summed, 3,000 rounds of 1,000;
- closures through a higher-order map, 3,000 rounds of 1,000;
- `tak 22 16 8`.

Each is run lowered to Scheme, and compiled by the Rust compiler (13a) and
run on each machine. Best of three, release, before any M13 optimization:

| program  | lowered  | Rust machine | hand-encoded | stencils -O2 | words compiled |
| -------- | -------- | ------------ | ------------ | ------------ | -------------- |
| closures | 348.2 ms | 571.4 ms     | 70.2 ms      | 92.5 ms      | 62.6 ms        |
| fib      | 180.6 ms | 176.6 ms     | 16.8 ms      | 24.5 ms      | 13.9 ms        |
| lists    | 301.0 ms | 393.8 ms     | 52.6 ms      | 68.8 ms      | 46.3 ms        |
| loop     | 743.6 ms | 766.3 ms     | 66.1 ms      | 119.6 ms     | 52.7 ms        |
| tak      | 50.6 ms  | 65.9 ms      | 6.8 ms       | 11.3 ms      | 4.7 ms         |

On whole FX-26 programs, words compiled to machine code (C11a) gain 10–30%
over threaded code on the hand-encoded machine, more than the
micro-benchmarks showed.

## Typed calls (13c′)

The compilers emit `tcall`/`ttailcall` for every call: the checker has
proved the callee a procedure, and a continuation is now a closure (a word
ending in `resume`), so the machines skip the closure test and the
continuation fallback. A typed tail call grows neither stack, so it skips
the stack-limit checks too; only fuel is checked. Same benchmarks, best of
three, release:

| program  | hand-encoded   | stencils -O2     | words compiled |
| -------- | -------------- | ---------------- | -------------- |
| closures | 70.2 → 68.2 ms | 92.5 → 85.0 ms   | 62.6 → 59.6 ms |
| fib      | 16.8 → 16.6 ms | 24.5 → 22.7 ms   | 13.9 → 13.0 ms |
| lists    | 52.6 → 51.2 ms | 68.8 → 64.4 ms   | 46.3 → 45.6 ms |
| loop     | 66.1 → 65.5 ms | 119.6 → 105.0 ms | 52.7 → 51.0 ms |
| tak      | 6.8 → 6.5 ms   | 11.3 → 10.5 ms   | 4.7 → 4.5 ms   |

2–12%. The stencils gain most (the loop, 12%): their call path was the
heaviest. Before `st_tcall`/`st_ttailcall` existed, every typed call on
the stencil machine went out to Rust, and it ran 2–3 times slower.

## Typed primitives (13d)

The compilers emit routines without the tests the checker's types make
needless:

- `+`, `-` and `<` at `int` become `int-add`, `int-sub` and `int-less`,
  which have no tag test. The overflow check stays.
- `car` and `cdr` take a `pairof` in FX-26 (a list is a sum), so they
  become `pair-car` and `pair-cdr`, one load each.
- `lit k; field@` becomes `field k` wherever the type says the bloblet has
  field k: boxes, records, sums, products, `bloblet-ref`. That is one
  cell instead of two, one load, and no test of tag, trailer or bounds.

The Rust machine is the oracle: it keeps every check in the typed
routines, so a wrong type traps there instead of reading wild memory. It
gains only from `field k` being one cell. Best of two runs, release,
against the typed-call figures:

| program  | Rust machine  | hand-encoded | stencils -O2 | words compiled |
| -------- | ------------- | ------------ | ------------ | -------------- |
| closures | 569.7 → 575.4 | 68.2 → 66.7  | 85.0 → 85.3  | 59.6 → 58.4    |
| fib      | 174.7 → 177.3 | 16.6 → 15.6  | 22.7 → 22.2  | 13.0 → 13.1    |
| lists    | 388.3 → 390.7 | 51.2 → 50.7  | 64.4 → 60.5  | 45.6 → 45.0    |
| loop     | 774.4 → 728.4 | 65.5 → 59.3  | 105.0 → 84.1 | 51.0 → 47.0    |
| tak      | 66.1 → 66.0   | 6.5 → 6.4    | 10.5 → 11.1  | 4.5 → 4.4      |

(ms.) The loop gains 6–20%. It is arithmetic and comparison, and the
loop's counter is read through a box, which `field 2` makes one cell. The
rest are within a few percent, and some of that is noise: those
benchmarks spend their time in calls and allocation, not in the checks.

## Self tail calls as loops, and letrec without boxes (13e, first part)

A tail call of a `letrec`-bound procedure to itself, while its name is
still that binding, becomes `slot!` of each argument, `drop` of the rest
of the frame, and a `branch` back to the word's start. A binding whose
lambda names none of its group, and itself only in such calls, needs no
box: its closure is made straight into its slot. The loop benchmark's
procedure had read its own box on each iteration (`free 1; field 2`).

The first measurement made compiled words *slower*: the loop went from 47
to 57 ms. The dump of the word's machine code showed why. A compiled word
keeps the threaded ip up to date: `sub ip, ip, #8` per cell, and a
post-indexed load per operand. That chain runs through every cell. A tail
call used to remake the ip from the callee's word, which cut the chain at
each iteration, so iterations could overlap. `branch` instead made the new
ip from the old one and a *loaded* offset, which joined the iterations
into one chain, with a load's latency in it each time. So in a compiled
word, a taken branch now remakes the ip from the word
(`ip = base + cur − (4 + 8 × (cell0 + target))`), and the loop fell to
38 ms. 13h's registers are expected to remove the chain altogether.

Best of two runs, release, against the typed-primitive figures:

| program  | Rust machine  | hand-encoded | stencils -O2 | words compiled |
| -------- | ------------- | ------------ | ------------ | -------------- |
| closures | 575.4 → 558.4 | 66.7 → 66.0  | 85.3 → 74.9  | 58.4 → 57.7    |
| fib      | 177.3 → 172.4 | 15.6 → 15.1  | 22.2 → 21.8  | 13.1 → 12.8    |
| lists    | 390.7 → 378.6 | 50.7 → 49.5  | 60.5 → 52.8  | 45.0 → 43.5    |
| loop     | 728.4 → 443.9 | 59.3 → 63.0  | 84.1 → 68.6  | 47.0 → 37.9    |
| tak      | 66.0 → 64.0   | 6.4 → 6.3    | 11.1 → 8.7   | 4.4 → 4.3      |

(ms.) The loop: 39% faster on the Rust machine, 19% compiled. It is **6%
slower on the hand-encoded machine**, which interprets `branch` and must
load its offset through the ip; the old tail call took its ip from the
closure instead. That loss is kept for the gains elsewhere. `fib` and
`tak` recur through globals, which are not yet known calls (a global can
be defined again at the REPL), so they gain nothing here.

## Register code, first version (13h′ a–b)

Each lambda's register code (PLAN.md 13h′): MacScheme-machine
instructions made by the Rust compiler from the same trees, compiled to
arm64. `RESULT` is `x0`, the arguments are in `x1`…`x8`, and the closure
running is `REG0`. A leaf keeps everything in registers. Any other
procedure keeps its parameters and `let`s in a frame, since a call or
call-out may collect. Calls between register procedures pass their
arguments in registers; returns still go by the data stack, as stack
code's do, so either kind may return to the other. What the compiler
does not do yet (`letrec`, `prompt`, `tagcase`, products and sums, among
others) stays stack code, behind an adapter. ("Words compiled" is
compiled too: it is stack code, which keeps the ip and every value in
memory as the interpreted machines do. The difference here is the
machine model.)

Best of two runs, release, against the typed-primitive and loop figures
(ms):

| program  | hand-encoded | words compiled | register code | against words compiled |
| -------- | ------------ | -------------- | ------------- | ---------------------- |
| closures | 66.8         | 58.5           | 42.1          | 1.39×                  |
| fib      | 15.7         | 12.2           | 7.2           | 1.69×                  |
| lists    | 51.0         | 44.5           | 31.1          | 1.43×                  |
| loop     | 65.3         | 38.9           | 6.6           | 5.9×                   |
| tak      | 6.3          | 4.4            | 2.3           | 1.91×                  |

Against the 13b baseline on the hand-encoded machine: `fib` 2.3×, `tak`
3.0×, `loop` 10×. `loop` is a leaf: its counter and sum stay in `x1` and
`x2`, and each iteration is a compare, two adds and a branch, with a fuel
check. In `fib` and `tak` the arguments travel in registers, and only
what lives across a call touches memory. `closures` and `lists` gain
least: they allocate, which is still a call-out to Rust, and their
procedures that use `letrec` or `tagcase` are still stack code.

## Register code for the whole front end (13h′ c)

Register code now covers 966 of the bootstrap program's 972 lambdas:
- `tagcase`, `letrec` (closures patched with a `setfield` instruction),
  products, sums, bloblets, arrays, references (`setfield`), `prompt`, and
  the control and mark operations, as call-outs.

The 6 left are three `with-mark`s in tail position (their constant space
depends on the stack frame), two standard operations used as values, and
one `set-cdr!`.

The fixpoint holds: the front end, compiled by the Rust compiler with
register code and run as register code, compiles itself to the same code
(`tests/bootstrap.rs`, `fixpoint_as_register_code`). Stage 2, the
compiled compiler compiling the whole front end, on the native machine:

| stage 2                | time   |
| ---------------------- | ------ |
| interpreted stack code | 0.8 s  |
| compiled stack code    | 0.7 s  |
| register code          | 0.56 s |

That is only about 20% better, where the benchmarks gained 1.4–6×. The
self-compile spends its time in call-outs to Rust, about 14 million of
them. `FIXPT_CALLOUTS=1`, instrumented, so slower (ms):

| call-out   | count     | time |
| ---------- | --------- | ---- |
| `prim`     | 3,950,860 | 226  |
| `cons`     | 4,760,596 | 125  |
| `callcomp` | 326,317   | 56   |
| `closure`  | 1,828,755 | 47   |
| `field@`   | 2,381,992 | 40   |
| `resume`   | 326,315   | 23   |

The commonest primitives:
- `%make-frozen` (sums and products): 546k
- `string=?`: 397k
- `%bloblet-fields`: 389k
- `char-whitespace?`: 343k
- `string-length`: 328k
- `string-ref`: 326k

The 326k continuations captured copied 39 million words of stack. So for
the real program the next lever is allocation and the common primitives
in machine code, more than cheaper calls.

The bug found on the way: in a large register word, making a return
entry needed `x16` for a large offset, and overwrote the callee's entry
address there. `FIXPT_FAULTS=1` (`fixpt_native::faults`) now reports such
a fault: the pc, the installed code it is in, and the registers.
`FIXPT_REG_RANGE` gives register code only to the lambdas in a range, for
bisecting.

## The reader suspends only when its input runs out

The eager reader suspended for every character, capturing a composable
continuation, for read-as-you-type. The self-compile fed it the whole
text a character at a time, so it made a capture and a resume per
character, 326,317 of each. `eager-feed-string` gives it a whole string.
It takes characters from the string and suspends only when the string is
used up; the REPL still feeds a character at a time, so that it can back
up on an edit. The self-compile as register code, stage 2:

| measure             | before  | after  |
| ------------------- | ------- | ------ |
| time                | 0.56 s  | 0.38 s |
| continuations taken | 326,317 | 6      |
| words allocated     | 74.6 M  | 17.5 M |
| collections         | 43      | 9      |
| time collecting     | 67 ms   | 23 ms  |

Stage 2 as compiled stack code fell from about 0.7 s to 0.5–0.6 s. What
is left is mostly call-outs to primitives (241 ms instrumented) and to
`cons` (55 ms).

## `cons`, `string-length` and `string-ref` in register code's machine code

Register code does these inline, calling out only for what it cannot do:
- `cons` bumps the heap's `top` itself, up to where a safepoint would
  collect (`Heap::inline_limit`: 75% of the semispace, the collector's own
  `COLLECT_THRESHOLD`). Past that, and always under the `gc_every`
  stress policy, it calls in, and the collection comes where it did
  before: the self-compile still makes 9 collections and allocates
  exactly the same 17,517,161 words. The limit could be the end of the
  semispace, since machine code checks at every allocation; that made no
  difference here (the call-outs reach 75% first), and 75% keeps the
  points of collection the same whichever machine runs a program, so
  that runs compare.
- `string-length` reads the suffix's first word.
- `string-ref` checks the index and loads 32 bits, calling out only when
  the index is out of range, to report it.

| measure                       | before  | after   |
| ----------------------------- | ------- | ------- |
| benchmark `lists`             | 31.1 ms | 11.9 ms |
| benchmark `closures`          | 42.1 ms | 23.6 ms |
| reading the bootstrap program | 0.12 s  | 0.09 s  |
| checking it                   | 0.17 s  | 0.16 s  |
| self-compile, stage 2         | 0.38 s  | 0.33 s  |

(All register code.) `closures` gains only from `cons`: making a closure
is still a call-out.

## The heap's memory from the system, and indices from its start

The heap's words are now one mapping from `fixpt-memmgmt`, each
semispace at a fixed place within it, and a Value's index counts from
the mapping's start rather than from the active semispace's. That
avoids the indirection a trait object would have added (+12–47% on the
benchmarks, measured and reverted). Nothing moved in the numbers: the
self-compile, stage 2, is 0.33 s as register code, with 9 collections
(about 20 ms); the benchmarks are within noise of the previous section
(`lists` 12.8 ms, `closures` 24.5 ms, `fib` 7.1 ms, `loop` 6.8 ms,
`tak` 2.2 ms).

## Lists in a region (`bench/lists-region.fx`)

`lists`, with each round's list made by `rcons` in a `letrena` of its own
and given back whole when the round ends, so the collector never sees it.
Best of several runs, two runs of the benchmark:

| machine        | `lists`      | `lists-region` |
| -------------- | ------------ | -------------- |
| lowered        | 293–295 ms   | 322–324 ms     |
| Rust machine   | 384–392 ms   | 314–321 ms     |
| hand-encoded   | 53–54 ms     | 97–110 ms      |
| stencils -O2   | 55–63 ms     | 110–128 ms     |
| words compiled | 46 ms        | 84–88 ms       |
| register code  | 12.8–13.0 ms | 68–81 ms       |

Where every `cons` calls into Rust anyway (the Rust machine), the region
wins, by what the collector no longer copies. Where `cons` is inline, it
loses badly: `rcons` is a call-out, about 20 ns each, 3 million of them.
The next step for regions' speed is `rcons` inline, as `cons` is.

### `rcons` inline

Register code now does `rcons` as it does `cons`: the heap keeps each
region's current chunk, `[fill, end]`, in a table at a fixed address
(`Heap::region_table_address`, `REGION_SLOTS` of them), and machine code
bumps the fill, calling in only for `#f`, a region with no chunk yet or a
full one, or a handle past the table.

| machine       | `lists` | `lists-region` |
| ------------- | ------- | -------------- |
| register code | 12.4 ms | 8.1 ms         |

So in a region the same program takes two thirds of the time: nothing
is copied, and the chunk, reused round after round, stays in cache. The
other machines call in for every `rcons`, as before.

### After regions as values, closures in regions, escapes and reaps

Nothing measured moved. Lowered, a `letrena` is now a `dynamic-wind` (so
that an escape ends its region), which `lists-region` does once a round:
324 ms, as before. Register code: `lists-region` 8.3 ms, `lists` 12.7 ms.
The self-compile, stage 2: 0.34 s, 9 collections in 21 ms, though the
collector now copies reaps too and marks quarantined chunks.

The Scheme suite under `gc-stress` takes about 6 minutes, run as
`cargo test --release -p fixpt-scheme --features gc-stress`. With
`--features fixpt-heap/gc-stress` instead, the tests collect at every
safepoint but at their full sizes, and run for far longer.

## Values as addresses

A Value's upper bits are now its referent's address, not a word index
from the heap's base, so machine code no longer adds a base to reach
the heap (PLAN.md, "Values as addresses, not indices"). First, what the
add cost: one more dependent add in register code's `car` and `cdr`
made `lists-region` about 5% slower and `lists` under 1%. Then, with
Values as addresses and those loads made straight from the Value:

| benchmark (register code) | before  | after   |
| ------------------------- | ------- | ------- |
| `lists-region`            | 8.7 ms  | 7.3 ms  |
| `closures`                | 24.0 ms | 23.9 ms |
| `fib`                     | 7.2 ms  | 7.3 ms  |

`lists` read 12.8 ms before and 13.5 ms after in the benchmark's table,
alternating the two builds. Run alone, five times in a fresh session,
it takes the same at both: 13.5 ms by the fifth run, with the same 167
collections and 2.7–2.8 ms of collecting. In the table it runs as
register code after four other machines have run it in that session, so
the heap it starts with differs; the gap is that, not its code. The
self-compile is unchanged: stage 2 in 0.34 s, collecting 21 ms.

The machines' `BASE` register now holds 0, so the code that still adds
it (the hand-encoded machine, the stencils, the compiler in FX-26) is
unchanged in meaning; register code no longer uses it. Inline allocation
still needs where the heap's memory starts, which it loads from the
machine's state (`State::words`).

## Register code's own calls and returns (PLAN.md 13h′ (f))

A call from register code to register code is now a `blr`, with a
return entry pushed as before (so that a continuation can capture it)
but marked, its `8k` negated. The callee's `return` sees the mark,
restores the caller's registers from the entry, and goes back to the
link, the value staying in `RESULT`: no trip through the data stack, no
resume table. A frame keeps the link in a slot of its own, raw, since
every point a `blr` returns to is 8-aligned and so reads as a fixnum (as
Larceny aligned its return points); the adapter from stack code sets
the link to 0. A capture copies entries unmarked, so a continuation
resumed returns the stack's way. With it:
- a loop's head (a backward branch's target) is 32-aligned: `loop`'s
  time had depended on where its word landed (6.5 ms or 8.7 ms, the
  same code);
- a word's trap stubs and its jump to the machine's exit are at its end,
  not after each instruction behind a branch over them.

Against the commit before, its words aligned the same, best of three:

| benchmark (register code) | before  | after   |
| ------------------------- | ------- | ------- |
| `fib`                     | 7.4 ms  | 5.8 ms  |
| `tak`                     | 2.3 ms  | 2.0 ms  |
| `loop`                    | 6.8 ms  | 5.6 ms  |
| `closures`                | 23.7 ms | 26.2 ms |
| `lists`                   | 13.5 ms | 14.9 ms |
| `lists-region`            | 7.4 ms  | 7.4 ms  |

**`ret` or `br x30`.** Returning by `ret` pairs each `blr` with its
return, and the processor predicts it from its stack of return
addresses: `fib` 5.2 ms, `tak` 1.9 ms. But `closures` recurses a
thousand deep (`map-add` is not tail recursive), which overflows that
stack, and then nearly every return mispredicts: 32 ms. By `br x30` the
return is predicted as an indirect branch, which learns the pattern:
`fib` 5.7 ms, `closures` 25.5 ms. Non-tail recursion over a list as long
as the data is ordinary in Scheme, so returns are by `br x30`.

**What `closures` and `lists` paid, found by looking.** With the old
calling convention restored, `lists` was as slow, which pointed away
from calls. `FIXPT_REGCODE_DUMP=file` now writes each register word's
machine code as `.inst` lines, which `clang -c` and `objdump -d`
disassemble. `lists`' `iota` is not a loop: its self-call is through a
global, so each of its three million iterations is a tail call, which
leaves the frame and makes a new one; and each paid a load of the link
as it left and a store as it made the frame. (`closures`' `upto` and
`total` are the same.) So the link now stays in `x30` through the body,
loaded from the frame only after a call or a call-out, which change it;
leaving the frame loads nothing. What is left is the store of the link
when the frame is made, into a slot the collector would otherwise need
initialized anyway: `closures` 25.1 ms, `lists` 13.9–14.7 ms, against
23.7 and 13.5 before. A self-call through a global made a loop (known
calls, PLAN.md item 4) removes the frame from each iteration.

## The call-outs left hot, inline (PLAN.md queue, item 3)

Register code now does these in machine code, calling out only for what
it cannot (a full heap or chunk, an index out of range, a region with no
slot):
- closure creation (`lambda`), from the heap's free space as `cons`
  is, and `%region-closure` in a region;
- sums and products (`%make-frozen`), the kind a fixnum whose bits are
  the header's kind as they are;
- `rnew` and `rmake-icell` in a region;
- `field@` (array reads), checked against the trailer's field count;
- `%bloblet-fields`, the trailer's count.

The self-compile's call-outs, stage 2 (`FIXPT_CALLOUTS=1`):

| call-out          | before    | after |
| ----------------- | --------- | ----- |
| `field@`          | 2,381,992 | 0     |
| `closure`         | 1,828,755 | 4     |
| `%make-frozen`    | 546,000   | 0     |
| `%bloblet-fields` | 389,000   | 0     |

Stage 2: 0.34 s → 0.28 s. The benchmarks make few closures and read no
arrays, and hardly move (`closures` 25.1 → 24.9 ms). Left: 2.49 million
primitives, the commonest `string=?` (448 k), `char-whitespace?`
(354 k), `%fx26-char-in?` (294 k), `%fx26-list-copy` (210 k),
`string->symbol` (166 k), `%bloblet-set!` (160 k), `symbol->string`
(158 k).
