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

**Profiling with `sample`, our code named** (2026-10-05). macOS's
`sample PID SECONDS -file OUT` names every Rust frame, but shows machine
code we made as `???  (in <unknown binary>)` and an address. With
`FIXPT_SYMBOLS=FILE` set (`%p` in it the process id), `fixpt` writes each
piece of machine code it places, and where a code collection moves it, as
`START LEN NAME` lines (`fixpt_native::symbols`): the cellular machine's
routines by name, each compiled word (`word k-check`, `register word
k-check`), the native convention's procedures (`native k-check`) and
stubs. `fixpt-symbolize FILE… -- OUT` (in `fixpt-tidy`) then names those
frames, `k-check  (in fixpt code) + 644`, and adds a summary of the samples
at the top of the stack by name, with waiting threads set apart. A global
defined as a lambda gives its word its own name in both compilers
(`name_word_for`, `c-name-for!`); an inner lambda within the one it is in,
by the `letrec` or `let` name it is bound to (or `lambda`) and where its
body starts: `k-mentions-token?/from@174485`. The probe's cell profile
adds the file and line, `check-print.fx:226`. For example:

```text
FIXPT_SYMBOLS=/tmp/syms.%p fixpt … & sample $! 10 -file /tmp/s.txt
fixpt-symbolize /tmp/syms.* -- /tmp/s.txt | less
```

Take the pid of the process started (`$!`), never one found by name: the
user's own REPL, under Emacs, has the same name.

`sample` cannot say who called a word: register code calls register code
with no native frame, so every stack of ours ends in `run_in_runtime`.
For callers, the cell profile (`FIXPT_PROFILE_PHASE=check` on
`tests/bootstrap.rs`'s `probe_phases_as_register_code`, on the Rust
machine: cells, not time, but exact and comparable between two versions)
now also counts cells by edge, a word's cells as entered from the word
run before it (`Profile::edges`); `FIXPT_PROFILE_CALLERS=k-has-name?,…`
prints each named word's callers by those cells. Better, and to do when
a profile next needs it: the Rust machine's return stack (`rs`) names
every word a cell runs under, so each cell can be counted against the
whole chain, as folded stacks (a flame graph's input) and inclusive counts
per word. For time, not cells, a sampler could walk register code's own
frames as the collector does (its stack maps), naming the chain `sample`
stops at `run_in_runtime`. Continuation marks would say the same, tail
calls collapsed as they should be, but only by marking every call in the
code measured.

**Printing a type was quadratic in the type names in scope** (2026-10-05,
found moving the front end's files into modules, `TODO.md` §34). The
self-compile's check had grown from 1.24 s to 1.65 s as the compiler
files became modules. The cell profile, before and after, put the growth
(9.97 to 13.86 G cells) almost all in `k-has-name?` (+3.7 G), and its
callers 8.7 G of 8.9 G in `k-abbrev-in`: at each node of a type it
prints, the FX-26 checker looks for a `define-type` naming it, walking
every binding in scope and keeping a list of the names seen, to skip
those shadowed. Quadratic in the scope at every node; and the check's
output prints every definition's type, a file's module's type being all
its members' types. A match is rare, so it now walks once and looks for
a shadowing binding only on a match. Check, the self-compile as register
code: 1.65 s to 0.99–1.00 s, below where it was before any file moved.

**Resolving a `select` rebuilt the whole type** (2026-10-06, `TODO.md`
§34). With the front end's files' types inside their modules, re-exported
by `(define-type t (select m t))`, check grew 1.05 s to 1.23 s and
allocated 28% more (41 M to 52 M words). The cell profile put the growth
in string building, printing; the output had grown to 564 K characters,
one module's type 65 K, `k-ty` printed whole inside it though named: a
type naming any re-export was rebuilt node by node by the substitution
that resolves its `select`s, every node new, so nothing in it was
`k-ty`'s any more. Now resolution rebuilds only the nodes that lead to a
`select` (`select_clean`, `k-select-clean`); the rest stay themselves.
Output 359 K, check 0.91 s, below where it was. On the way: a
`moduleof` prints with its descriptions' names naming what they describe
in the components after them; `k-mentions-token?`, asked of every node
printed, scans for a token without making strings; and the FX-26 select
code builds its error messages only for an error.

**Printing a module type was quadratic in its components** (2026-10-06,
`TODO.md` §34). With `check-types.fx` a module, check grew 1.16 s to
1.37 s. The cell profile of the files up to it put the most new cells in
`k-edges-of` (`check-modorder.fx`: a module's recursive groups found by
reaching from each lambda in turn, lists, cubic in its 241 lambdas); made
linear (Tarjan's components, in both checkers), it changed no time: a list
walked is cheap on register code, and cells are work, not time. The words
allocated were the clue: half again as many, in `k-cat3` and `k-cat4`, and
`fixpt check` on those files printed one line of 18 K characters, the
module's type, whose printer appended each component to the rest of the
line, a copy per component. Now `k-join` gathers its strings' characters
into one list, in an arena (`letrena`), made a string once, and a
`moduleof`'s components and a product's or sum's parts are joined by it.
The same output; check 1.42 s to 1.09 s, below the migration's start.

**A fast path that branched to `ret`; a slow path nothing reached**
(2026-10-06; the user's reading of `,disassemble-asm u32+`). In the
native convention a pure operation's fast path ended `b done` over its
slow path, and `done` was often the procedure's `ret`; and `u32+`, whose
fast path wraps and never fails, still had its 32-instruction call-out
after it, unreached. Now the assembler makes a branch to a `ret` that
`ret` (`direct.rs`, `Asm::finish`; nothing counts a code's returns, a
return address being a call's), and a fast path that never names its
slow label gets no slow path (`Asm::used`). `u32+`: 41 instructions to
4. The disassembler now shows `and_bits`'s masks from any bit.

**A re-exported type was still a copy at each use** (2026-10-06, `TODO.md`
§34). Migrating `eager-reader.fx`, the first file, took check from 1.89 s
to 28.3 s; the files before it had crept 0.91 s to 1.89 s. `sample` put
70% in `string_to_rust` under `%fx26-string-search`, from
`k-mentions-token?`: printing. Checking prefixes of the front end
(`FIXPT_PROBE_FILE`) found the cost wherever the parser's types were used,
and `fixpt check` on eager-reader and the parser printed 810 K characters
against 26 K: `syn`, and every type holding it, printed whole. The
`select` node a re-export binds stayed a `select`, so each use's
resolution rebuilt whatever led to it (the rest is kept since the entry
above), a new node per use, which the printer, by node, never knew for a
`define-type`'s. Now a `select` of a module whose binding is global is
linked, once resolved, to what it names (`resolve_selects`,
`k-link-global-select`); a family's is not, being read as the `select` it
is, nor a local module's. Check 1.15 s with eager-reader a module, 1.13 s
without (`modules/select-shown.fx`). Still to do: `%fx26-string-search`
copies its whole string to Rust at each call.

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

## Cellular[^cellular] code: the Rust inner interpreter and the native one (A′3)

`cargo run --release -p fixpt-native --example cellular_bench`: the same
cellular words on both machines, results checked equal, best of three.
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
with closures, frames, and generic arithmetic, where the cellular `fib` is a
hand-written Forth word on fixnums. What the table does say: the native
`NEXT` costs about half a nanosecond per cell, the Rust `match` loop about
three, and the machine's checks (fuel and stack limits at every word entry
and taken branch, tags and overflow in every primitive) leave `NEXT` the
dominant cost. `cons` calls out to Rust, which saves and reloads the
machine's registers; that is the 0.96.

## Cellular code: stencils at each optimisation level (A′4)

The same words again, now also on the stencil machine: the routines written
in Rust with `become` (`crates/fixpt-native/stencils/cellular.rs`), compiled
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

## FX-26 compiled to cellular words, on each machine (C9c-3)

`fixpt --dialect fx26 --fx26-run cellular --cellular-machine M run FILE`,
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
  cellular code**: `fib 27` takes 4.0 ms here and 3.3 ms as the Forth word
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
  mark. The cellular machines stacked a new one each time, so the
  reader's continuation carried one mark per form read so far. The new
  routine `withmark-tail` has Scheme's meaning, and the compiler emits it
  for `with-mark` in tail position. Captures now average 88 words.

## Words compiled to machine code (C11a)

`NativeMachine::compile_word` places a word's routines' code inline in
cell order, with the ip kept in step, branches as jumps, and no dispatch
between cells. `cargo run --release -p fixpt-native --example
cellular_bench`, ns per cell of the Rust machine:

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

`fixpt bench` (it was an ignored test, `--test bench`, until 2026-09-28;
`fixpt bench --help` says how to choose programs, machines and runs).
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
over cellular code on the hand-encoded machine, more than the
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
keeps the cellular ip up to date: `sub ip, ip, #8` per cell, and a
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

### `rcons` inline natively too (2026-09-29)

The native compiler (`fixpt_native::direct`, the `native` column of
`fixpt bench`) came after that change and never had it: every `rcons` was
a call-out, and `lists-region` took 60 ms natively, eight times the
register machine's 7.5 ms, while `lists` took 8.4. It now does as
register code does, from the same table (`DState::region_table`), calling
in for the same cases.

| machine | `lists` | `lists-region` |
| ------- | ------- | -------------- |
| native  | 8.5 ms  | 60.3 → 7.0 ms  |

Test `native/region-cons.fx`, in the native session test, under
collections.

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
calls of primitives, the commonest `string=?` (448 k), `char-whitespace?`
(354 k), `%fx26-char-in?` (294 k), `%fx26-list-copy` (210 k),
`string->symbol` (166 k), `%bloblet-set!` (160 k), `symbol->string`
(158 k).

Then, inline too, trusting what the checker proved of the operands'
types: `%bloblet-set!` (checked against the trailer, and the header's
frozen bit, since an alias's type may not say it is frozen);
`char-whitespace?` for an ASCII character; `%fx26-char-in?`; and
`string=?` of two strings. Calls of primitives 2.49 M → 1.24 M; stage 2
0.28 s → 0.22 s. Left, the commonest: `%fx26-list-copy` (210 k),
`string->symbol` (166 k), `symbol->string` (158 k), `reverse` (112 k),
`%string-hash` and `modulo` (100 k each, a table's), `string-append`
(70 k). Many of these, and of the `string=?` calls before, look like
the compiler's own habits (names handled as strings, compared one
`string=?` at a time) rather than costs to make cheaper: next, where
they are called from.

### Where the calls of primitives came from

`FIXPT_CALLOUTS=1` now also counts each primitive's calls by the word
that made them (a register word is named `lambda@N`, `N` where its body
starts in the program's text). Two of the commonest were the program's
own doing:
- **The reader's marks were quadratic.** Reading a list, the eager reader
  replaced its mark at each item, and each new mark copied every item
  read so far into a datum (`datum-list`, 188 k calls of
  `%fx26-list-copy`) and interned its name again (`datum-symbol`,
  113 k of `string->symbol`). The mark's items are now a datum grown a
  pair at a time (`datum-cons`, new, pure), and the marks' names are
  interned once.
- **A symbol's hash made a string.** `table.fx`'s `symbol-hash` hashed
  `(symbol->string s)`: a new string for each lookup (100 k), where the
  symbol keeps the hash of its name from when it was interned
  (`symbol-name-hash`, new).

Calls of primitives in stage 2: 1.24 M → 0.95 M; stage 2 0.22 → 0.20 s.
Left at the top: `modulo` (100 k, a table's bucket), and the reader's
work per atom, and the parser's names as strings (`symbol->string`
then `string=?`).

`modulo` of two fixnums is now inline too (`sdiv`, `msub`, and the
divisor's sign; a zero divisor calls out), checked against the lowering
on every combination of signs (`tests/programs/run/modulo.fx`). It was
the tables' commonest (100 k); stage 2 stays at 0.19–0.20 s, since the
call it saves was a small part of it.

## A definition's own name, known (PLAN.md queue, item 4)

A typed top-level `define` of a lambda gets a new global, which no one
assigns (a second `define` makes another, and shadows), and which holds
the lambda before the lambda can run. So in the lambda's body its own
name is known: a tail call of it with its arity is a loop, as a
`letrec`'s is, in both stack compilers (alike, cell for cell) and in
register code; other uses load the global as before. Register code's
test of whether a procedure may collect now asks whether a self-call is
in tail position; it had counted every self-call as a loop, which would
have made `fib` a leaf.

| benchmark (register code) | before  | after   |
| ------------------------- | ------- | ------- |
| `lists`                   | 13.9 ms | 8.8 ms  |
| `closures`                | 25.0 ms | 20.8 ms |
| `fib`                     | 5.8 ms  | 5.7 ms  |
| `tak`                     | 1.9 ms  | 1.8 ms  |

The self-compile, stage 2: 0.20 → 0.18 s.

### A procedure's calls of itself, by its own entry

A non-tail call of the procedure running, by its own name with its
arity (a definition's, or a `letrec`'s that knows itself), needs no
closure fetched and no word or twin checked: its closure is the one
running and its word this one. Register code's new `invokeself n` is a
`bl` to the word's own register entry, a direct call the processor
predicts outright, with the same resume points as `invoke`.

| benchmark (register code) | before  | after   |
| ------------------------- | ------- | ------- |
| `fib`                     | 5.7 ms  | 4.4 ms  |
| `tak`                     | 1.8 ms  | 1.6 ms  |
| `closures`                | 20.8 ms | 19.2 ms |

Stage 2 stays at 0.18 s.

## What a capture costs

`bench/captures.fx` captures a composable continuation 20 calls deep,
aborts with it to the prompt's handler, and resumes it at once, 20,000
times. `FIXPT_CALLOUTS=1`, register code, instrumented:

| depth | words per capture | `callcomp` | `resume` |
| ----- | ----------------- | ---------- | -------- |
| 20    | 122               | 5 ms       | 1 ms     |
| 200   | 1,202             | 25 ms      | 11 ms    |

A capture copies the stack at about 1 ns a word, plus about 0.15 µs
whatever the depth. A whole round (prompt, capture, abort, resume) is
0.56 µs at depth 20, uninstrumented (11.3 ms for the 20,000).

No program here captures often any more. The self-compile captures 6
times since the reader stopped suspending for each character, and the
REPL's reader captures once per character typed. A stack cache or
one-shot continuations (PLAN.md queue, item 7) would take the copying
out, but that is a small part of a round until the stack is hundreds of
frames deep. So it waits for a workload that captures deeply and often.

## The reader: what it called out for, not its cursors

PLAN.md's item 8 suspected the cursor the eager reader allocates for each
character. `probe_read`, now as register code, and `FIXPT_CALLOUTS=1` said
otherwise. Reading the bootstrap program (about 390k characters) made
444k calls of primitives, and the commonest was `%fx26-list-copy`
(151k), from `datum-list`: each mark the reader set was built with
`cons` and then copied to make it a datum. Then `reverse` and
`string->list` for every atom's (almost always empty) prefix, and
`%fx26-parse-number` for every atom, though most are symbols.

- The marks are built with `datum-cons`, with no copy, and a list's
  datum is its items' datum reversed with `datum-cons` too.
- An atom is parsed as a number only if it starts as one can (a digit,
  `+`, `-`, `.` or `#`).
- An empty prefix is no work.
- Register code does `datum-car`, `datum-cdr` and `datum-null?` as it
  does `car`, `cdr` and `null?`, and `char-numeric?` of an ASCII
  character in machine code.

| reading the bootstrap program, register code | before  | after   |
| -------------------------------------------- | ------- | ------- |
| calls of primitives                          | 444k    | 151k    |
| time (best of ten)                           | 39.9 ms | 29.3 ms |

The cursor made a product (one frozen bloblet, not four pairs) measured
29.0 ms, no better, so it stays as it was. What is left is some 75 ns a
character, in calls of the reader's small procedures more than in
allocation.

## Type tests and a symbol's hash in register code

The self-compile's commonest calls of primitives, after the reader's, were
type tests of datums (the parser's `datum-symbol?` and the rest) and
`%symbol-hash`, the tables' hash of a symbol key. Register code now does
them in machine code:
- `%fx26-fixnum?`, `char?` and `boolean?` by the value alone;
- `symbol?` and `string?` by the header's kind, found before the suffix
  or by the trailer, calling out only for a large object;
- `%symbol-hash` as one load, since the checker has seen a symbol.

| stage 2, register code | before | after  |
| ---------------------- | ------ | ------ |
| calls of primitives    | 673k   | 441k   |
| time                   | 0.22 s | 0.22 s |

`tests/programs/datum/` holds programs that use datums, which the
evaluator written in FX-26 does not have; every other harness runs them.

## Names as symbols, and messages made only for errors

Of stage 2's calls of primitives that were the FX-26 code's own doing
(PLAN.md's item 3′):
- The checker made the message for a definition that does not check (its
  type shown) for every definition that does, and the "is not a type",
  "is not a region" and "is not an effect" messages for every name it
  looked up. They are made now only for an error.
- The parser and the checker's `k-parse-type` found which form or type
  they had by comparing the head's name, as a copied string, with each
  keyword in turn; they compare symbols (`syn-head`), as does every other
  test of a name (`else`, `#t`), and take a name's symbol from the datum
  with no string between.

| stage 2, register code | before | after  |
| ---------------------- | ------ | ------ |
| calls of primitives    | 441k   | 336k   |
| time                   | 0.22 s | 0.19 s |

What is left of them is mostly the reader's, making each atom's text
(`reverse`, `list->string`, `string->symbol`, 42k each), and `new`
(`%make-box`, 46k), which register code now does in machine code as it
does `rnew`: 336k → 296k (stage 2 stays 0.19 s; with a collection at
every 997th safepoint it makes the same code).

## Polls only on backward branches, in compiled stack code

A word compiled to machine code as stack code checked its fuel on every
taken `branch` and `0branch`, though only a backward one can make a loop;
register code already polled only backward. Now stack code does the same
(the responsiveness tasks' R3). Words compiled, best of three:

| benchmark | before  | after   |
| --------- | ------- | ------- |
| `loop`    | 42.3 ms | 40.6 ms |
| `fib`     | 13.7 ms | 13.3 ms |
| `lists`   | 42.2 ms | 42.9 ms |

Within noise but for `loop`: a poll that is never taken costs little.

## What a word's entry poll costs: nothing measurable

Before building an analysis to leave out entry polls (the responsiveness
tasks' R5), register code was run with no entry poll at all, unsafely, as
an upper bound on what it could save:

| register code | with entry polls | without |
| ------------- | ---------------- | ------- |
| `fib`         | 4.4 ms           | 4.4 ms  |
| `tak`         | 1.6 ms           | 1.6 ms  |
| `closures`    | 19.0 ms          | 18.7 ms |
| `lists`       | 8.6 ms           | 8.6 ms  |
| stage 2       | 0.18 s           | 0.18 s  |

A poll never taken (a subtract and a branch) costs nothing measurable
here, so R5, and R8 (stack checks hoisted), are not worth building.

## Closures: what copying code into each would cost (2026-09-27)

A cellular closure is `[word][free…]`: the code (the word) is shared by
every closure of one `lambda`, and a free value is one load from the
closure register, as Larceny's closures are. Measured once, with temporary
counters in the Rust cellular machine's `CLOSURE` routine (not kept), on
the self-compile (the driver compiling the bootstrap program):

| what                                                        | count or words |
| ----------------------------------------------------------- | -------------- |
| closures made                                               | 1,382,525      |
| words allocated for them                                    | 6,734,703      |
| words more, were each lambda's code copied into its closure | 94,289,442     |
| distinct `lambda`s whose closures were made                 | 1,329          |
| words of code, all of those `lambda`s                       | 137,016        |

Copying would allocate 15 times the words (about 750 MB more over the run,
at 8 bytes a word, against 54 MB). The cost is concentrated: one `lambda`
of 41 words is made 383,286 times, one of 295 words 136,005 times, and
five more 41,000 to 79,000 times each. Loading the front end made 1,251
closures, each of a different `lambda`, exactly once: for those, copying
would cost nothing but the one copy. On the native machines copying would
also mean writing executable memory for each closure (W^X on arm64 macOS,
and an instruction-cache flush), which is far dearer than the words.

[^cellular]: "Cellular" would be called "threaded" in the Forth community: code as
a sequence of cells (references to routines, and their operands), run by an inner
interpreter. This repository says "cellular" throughout (the user's decision,
2026-09-27).

## The native convention, first-order (2026-09-28)

Native conventions step 2, in part (`docs/research/native-conventions.md`;
`crates/fixpt-native/src/direct.rs`): first-order procedures compiled
from their register code to code that calls by `bl` and returns by
`ret`, on frames of its own stack, arguments in `x1`–`x8`, the result in
`x0`, with no ip, return entry or resume table; a leaf checks nothing,
a procedure with a frame checks the stack once and fuel once on entry,
and a loop fuel on its back edge. The benchmark report's new column, the
procedure the last line calls, called directly (best of three, ms):

| program | register code | native convention | gain |
| ------- | ------------- | ----------------- | ---- |
| fib     | 4.5           | 2.4               | 1.9× |
| tak     | 1.6           | 0.8               | 2.0× |

The rest are declined: `loop`'s `letrec` procedure captures `n`, and the
others capture, allocate, or call what they are given, which waits for
steps 3 and 4. `(lambda ((x int)) x)` is now `mov x0, x1; ret`, where
the cell-for-cell compiled word was about 95 instructions.

### Joining register code's instructions (2026-09-28)

The native convention's compiler now does two of register code's
instructions as one where no branch lands between them: `reg k` read
straight by the operation after it; a compare only a `branchf` reads, as
a compare and a conditional branch with no boolean made; small constants
as immediates; a slot read back just after it is stored, from the
register; and a sum or difference made in the argument register it is
moved to. The stack's limit is pinned in `x27`, so the check is `cmp sp,
x27; b.lo`. `(lambda ((x int)) (+ x 1))` is `adds x0, x1, #8; b.vs; ret`,
and `fib`'s body 27 instructions, from 40.

| program | register code | native convention, before | after |
| ------- | ------------- | ------------------------- | ----- |
| fib     | 4.5           | 2.4                       | 1.9   |
| tak     | 1.7           | 0.8                       | 0.8   |

### Call-outs, and pairs made inline (2026-09-28)

Native code now calls out to Rust for runtime primitives and `cons`, on
Rust's stack, through the state. A call-out may collect: every native
frame runs from its frame pointer to its caller's, its words after the
link and return address are all values (`save` zeroes them), so the
collector's roots are the frames' slots, found by following the links,
with no stack maps; a collection at every safepoint (`gc_every` 1 and 7,
at least 30 000 collections) leaves `lists` right. A pair is made inline
from the heap's free space, short of the collection's threshold, as
register code makes it; the call-out only when there is no room.

| program | register code | native, every `cons` a call-out | native, `cons` inline |
| ------- | ------------- | ------------------------------- | --------------------- |
| lists   | 8.4           | 83.6                            | 8.0                   |

### Closures, and every procedure its own code bloblet (2026-09-28)

With closures (native conventions step 4), `loop`, whose `letrec`
procedure captures `n`, runs in the native convention too. Each procedure
is now a code bloblet of its own, and each frame stores it, to keep the
code alive: two instructions more per frame, which `fib` and `tak` show.

| program | register code | native convention |
| ------- | ------------- | ----------------- |
| fib     | 4.4           | 2.3               |
| tak     | 1.6           | 1.2               |
| lists   | 8.7           | 9.9               |
| loop    | 5.6           | 4.4               |

### Self-calls through the global (2026-09-28)

A top-level procedure's calls of itself by name now go through its
global, as any use of the global does (`docs/fx26.md`, "Redefinition");
only a `letrec`-bound procedure calls itself directly. What it costs:

| measured                                  | before | after  |
| ----------------------------------------- | ------ | ------ |
| fib, register code                        | 4.3 ms | 5.6 ms |
| tak, register code                        | 1.6 ms | 1.9 ms |
| fib, native convention                    | 2.2 ms | 2.4 ms |
| the front end compiling itself (fixpoint) | 7.40 s | 7.51 s |
| the same, as register code                | 2.21 s | 2.25 s |

The stack machines are unchanged, and the front end within noise, so no
site in it is rewritten; the benchmarks stay as written, measuring calls
through a global (`tests/programs/redefine/local-fib.fx` is fib bound
locally).

## `fixpt bench`, after native step 5 (2026-09-28)

`fixpt bench` (release build, best of 3, milliseconds). The native column
is the last line's call compiled in the native convention alone; `—`
where the last line is not a call on integer literals.

| program      | answer         | lowered | rust  | hand | stencils | compiled | registers | native |
| ------------ | -------------- | ------: | ----: | ---: | -------: | -------: | --------: | -----: |
| captures     | 420000         | 116.0   | 49.2  | 14.5 | 14.3     | 12.5     | 9.3       | 21.9   |
| closures     | 6003000000     | 344.0   | 686.4 | 75.7 | 86.3     | 60.2     | 24.7      | —      |
| fib          | 832040         | 180.7   | 212.5 | 16.1 | 20.7     | 13.2     | 5.8       | 2.4    |
| lists-region | 1501500000     | 334.6   | 311.7 | 96.6 | 112.7    | 83.5     | 7.0       | 157.9  |
| lists        | 1501500000     | 300.2   | 467.1 | 54.8 | 63.7     | 47.5     | 13.5      | 16.6   |
| loop         | 49999995000000 | 739.5   | 450.3 | 64.6 | 91.6     | 41.9     | 5.5       | 4.4    |
| tak          | 9              | 52.1    | 78.1  | 6.6  | 10.5     | 4.5      | 1.9       | 1.2    |

What it says of the native convention: calls (`fib`, `tak`, `loop`) are
fastest there; `lists-region` is twenty times register code's, since its
region `cons` is a call-out each (register code does it inline, which the
native compiler does not yet); `captures` copies the frames on each
capture, where register code's continuations are a stack segment; and
`lists`, whose `cons` is inline in both, is close.

## Guarded inlining of small global procedures (2026-09-28)

A call of a global procedure whose definition is a lambda of at most 20
parser-tree nodes, with no lambda, `letrec` or `prompt` inside it and no
use of its own name, is inlined in register code: the arguments made (one
that is a variable in the frame or the closure used where it is), then a
guard, then the body, in a scope of its own whose globals are those it saw
when defined; else the call. The guard is that the global still holds a
closure of the word the body was compiled to (`global g; field 2; op2imm
eq w; branchf`), so a redefinition, which makes a new closure of a new
word, is seen at once and nothing need be compiled again (the user's
choice, 2026-09-28). The native compiler decides the guard when it makes
the code where the global holds a cellular closure, as it takes such a
global's value then: where it is that word's closure, the guard is
nothing. A global holding a native closure it reads when the code runs,
so there the guard stays, testing for the closure's code (its field 2),
which was compiled from the word (`CODE_SOURCE`) and which a redefinition
replaces. Both compilers (`cellular/regcode.rs`, `regcode.fx`) inline,
and make the same register code; the REPL in the native convention, which
makes a definition's value itself, notes the lambda for inlining after
(`compile-note-inline!`). `,inliners NAME` says which globals' code
inlines NAME: those a redefinition of NAME sends back to calling it.

Stack code keeps its calls. Inlined there first, `helpers` (below) went
from 1270 to 977 ms on the machine written in Rust, but from 88 to 98 ms
on the hand-encoded one and not at all compiled: the guard and the
unbinding are seven routines, as dear as the call they save.

`helpers` is small helpers called in a loop, in the style of the front
end; the other benchmarks' procedures are recursive, and do not change.

| program | registers before | registers after | native before | native after |
| ------- | ---------------: | --------------: | ------------: | -----------: |
| helpers | 27.0             | 12.5            | 11.2          | 7.1          |

The front end has 8814 call sites inlined (in 479 procedures; `arm-sum`,
`arm-reg`, `r-emit`, `syn-start`, `k-err` most), but compiling itself as
register code takes the same time, 0.77 s, with inlining in its own code
or without: its time is in call-outs, allocation and the collector, not
in calls. Its register code is longer, which found that the assemblers
written in FX-26 (`c-cells`, `r-cells`) recursed once per item of a word;
they are loops now.

`fixpt bench`:

| program      | answer         | lowered | rust   | hand | stencils | compiled | registers | native |
| ------------ | -------------- | ------: | -----: | ---: | -------: | -------: | --------: | -----: |
| captures     | 420000         | 114.6   | 50.0   | 15.3 | 14.2     | 12.0     | 9.0       | 22.5   |
| closures     | 6003000000     | 343.9   | 703.5  | 74.8 | 84.8     | 59.7     | 25.4      | —      |
| fib          | 832040         | 180.6   | 219.4  | 15.8 | 22.9     | 13.7     | 5.9       | 2.5    |
| helpers      | 12000000       | 852.6   | 1305.1 | 89.2 | 106.4    | 54.8     | 12.5      | 7.1    |
| lists-region | 1501500000     | 333.9   | 311.5  | 97.5 | 108.8    | 83.0     | 7.3       | 158.0  |
| lists        | 1501500000     | 300.4   | 482.1  | 54.5 | 59.9     | 47.3     | 13.5      | 16.8   |
| loop         | 49999995000000 | 736.2   | 444.7  | 64.5 | 88.8     | 40.5     | 5.5       | 4.3    |
| tak          | 9              | 52.0    | 80.9   | 6.5  | 9.5      | 4.5      | 1.9       | 1.2    |

## Specializing a procedure at a lambda argument (2026-09-28)

`(map1 (lambda ((x int)) (+ x k)) xs)`, where `map1` only calls its `f`
or passes it on to itself: the call runs a copy of `map1` made for that
lambda. This is partial evaluation at a static argument (the user's
observation): the lambda is known where the call is, every recursive
call passes it unchanged, so a residual copy of `map1` is made with it
fixed, and in the copy each `(f e)` is a known lambda applied, inlined.
The lambda's captured values stay dynamic: the copy reads them from the
closure passed as `f` (`field 3` for `k`). Both compilers do it
(`r_specialize`, `r-specialize`), and make the same register code. The
copy is named for both, `map1@lambda@N`.

Redefinition stays exact. The copy's closure is made first, then the
arguments (the lambda's closure among them), then a guard that `map1`
still holds a closure of the word the copy was made from: the copy, else
the global. Inside the copy each call of itself is guarded the same way
(`invokeself`, or a jump in tail position, else the global), so a
redefinition met mid-recursion (a continuation resumed later) calls the
new `map1` as the original would. The native compiler folds the guards
where `map1` holds a cellular closure. What is specialized: a top-level
lambda of at most 60 nodes with no lambda, `letrec` or `prompt` inside,
not inlined, with a parameter used only so; the lambda at most 20 nodes,
with the arity it is called with.

`closures` now ends `(main 3000)`, the same work, so the native
convention measures it too:

| closures  | before | after |
| --------- | -----: | ----: |
| registers | 24.0   | 19.0  |
| native    | 29.8   | 33.1  |

Natively it is slower: the copy keeps the lambda's parameter and `k` in
frame slots (stored, zeroed on entry, loaded), where the original called
a native leaf closure that kept them in registers. Register code gains
because a closure call is dear there. To do: temporaries of an inlined
body in registers when no call comes between.

`fixpt bench`:

| program      | answer         | lowered | rust   | hand | stencils | compiled | registers | native |
| ------------ | -------------- | ------: | -----: | ---: | -------: | -------: | --------: | -----: |
| captures     | 420000         | 114.7   | 49.4   | 14.5 | 14.5     | 12.8     | 9.4       | 22.6   |
| closures     | 6003000000     | 345.0   | 697.2  | 75.9 | 77.8     | 60.8     | 19.1      | 33.5   |
| fib          | 832040         | 181.5   | 213.8  | 16.0 | 22.0     | 13.5     | 5.7       | 2.5    |
| helpers      | 12000000       | 868.6   | 1285.5 | 90.0 | 95.5     | 55.7     | 12.2      | 7.2    |
| lists-region | 1501500000     | 334.7   | 313.1  | 97.8 | 103.1    | 83.5     | 7.2       | 158.4  |
| lists        | 1501500000     | 298.2   | 470.3  | 54.5 | 55.5     | 47.2     | 13.5      | 17.0   |
| loop         | 49999995000000 | 738.5   | 461.5  | 65.8 | 68.7     | 39.1     | 5.6       | 4.6    |
| tak          | 9              | 51.3    | 78.0   | 6.6  | 8.6      | 4.5      | 1.9       | 1.2    |

## Common subexpressions: measured, not built (2026-09-28)

Before writing common-subexpression elimination, a probe counted, in
evaluation order (an expression counts where the same one was computed on
every path before it, with no name in it bound again between), the pure
expressions computed again:

| where                        | pure ops only | with `car`, `cdr` |
| ---------------------------- | ------------: | ----------------: |
| the front end (~900 globals) | 109           | 443               |
| every benchmark              | 0             | 0                 |

Pure ops: arithmetic, comparisons, `not`, `null?`, and `extract` of a
product, which is frozen. The front end's most repeated are `(extract g
nslot)` (13), `(extract g nreg)` (11) and `(extract r 1)` (8); with pairs,
`(car bs)` (41), `(car xs)` (29). Pairs can be written (`set-car!`), so
those would need the effect system to show no write to the pair's region
between the two.

Each reuse saves one instruction (`op1 pair-car`, `field k`; natively an
`ldur`) and costs a store at the first and a frame slot, so in register
code it is about even, and natively one load. Not built: the source
already binds what it uses much in a `let`. What inlining makes (a
helper's body repeated in its caller) the probe does not see; if that
changes the count, this is where to look again. The time goes elsewhere:
the native convention's temporaries in frame slots (the specialization's
cost, above), call-outs and allocation.

## Temporaries in registers where no call comes between (2026-09-28)

Register code kept every `let` of a procedure that calls anything in its
frame, since a call or a call-out may collect, or clobber registers.
Now a value bound in turn (a `let`'s, or, in a copy specialized at a
lambda, the lambda's parameters and captured values) is kept in a
register where nothing after it, a later init or the body, calls or
calls out: those are all that clobber registers or collect, so the
register holds a live value only where nothing can move it. At most half
the registers are so taken, the rest left for operations' temporaries.
Both compilers (`r_in_regs`, `r-in-regs`), alike; a native compiler
then maps them to machine registers.

The specialized `map-add` in `closures` keeps `x` and `k` in registers,
its frame three slots, not four; the native convention 33.5 → 30 ms
(the specialization's cost, above, recovered), register code about the
same (19–20 ms). The rest of the benchmarks and the front end compiling
itself as register code (0.80 s) are unchanged: their `let`s mostly
live across calls.

| program      | answer         | lowered | rust   | hand | stencils | compiled | registers | native |
| ------------ | -------------- | ------: | -----: | ---: | -------: | -------: | --------: | -----: |
| captures     | 420000         | 117.5   | 49.9   | 14.3 | 14.5     | 12.5     | 9.1       | 22.5   |
| closures     | 6003000000     | 344.1   | 688.2  | 75.2 | 72.6     | 59.7     | 20.1      | 31.1   |
| fib          | 832040         | 182.0   | 214.7  | 15.8 | 23.6     | 13.3     | 5.6       | 2.4    |
| helpers      | 12000000       | 873.8   | 1291.6 | 90.5 | 88.1     | 55.4     | 12.5      | 7.2    |
| lists-region | 1501500000     | 333.2   | 313.8  | 96.9 | 101.0    | 84.2     | 7.3       | 157.4  |
| lists        | 1501500000     | 298.9   | 472.8  | 54.4 | 55.6     | 47.0     | 13.6      | 17.0   |
| loop         | 49999995000000 | 735.8   | 473.6  | 65.1 | 66.3     | 46.6     | 5.5       | 4.2    |
| tak          | 9              | 51.5    | 78.9   | 6.5  | 9.3      | 4.4      | 1.9       | 1.2    |

## Constants propagated and folded, with inlining (2026-09-28)

In register code, a name bound to a constant (a `let`'s, an inlined
call's argument, a specialized lambda's argument) is bound to the
constant itself, and no code is made for it; a standard operation on
constants is folded (`+` and `-` on integers under 2^30 in size, so that
neither compiler can overflow; comparisons, `not`, `null?`, `char=?`);
an `if` whose test is known is its arm alone; a constant operand is an
immediate; a closure that captures a name bound to one gets the constant.
Both compilers (`r_const`, `r-known`), alike.

What makes the constants is inlining: in `helpers`, `(sum2 i 2)` is
`(+ (dbl i) (dbl 2))`, and `(dbl 2)` is `(+ 2 2)`, 4. What stops them is
the guard: `(dbl 2)` is 4 only while `dbl` holds what it was compiled
from, so 4 is made inside the guard, and the sum around it is not folded
further. The native compiler decides guards where the global holds a
cellular closure, but does not fold what follows.

Globals defined as constants (`(define rop-const int 3)`, much used in
the front end) are not propagated: a compatible redefinition keeps the
global and changes its value, so each use would need a guard, which
costs what the load does.

`helpers`: register code 12.5 → 10.9 ms, native 7.2 → 6.9 ms; the rest
unchanged.

| program      | answer         | lowered | rust   | hand | stencils | compiled | registers | native |
| ------------ | -------------- | ------: | -----: | ---: | -------: | -------: | --------: | -----: |
| captures     | 420000         | 118.8   | 49.4   | 14.4 | 14.2     | 12.5     | 9.3       | 22.4   |
| closures     | 6003000000     | 344.2   | 691.5  | 76.2 | 80.1     | 60.3     | 21.7      | 31.0   |
| fib          | 832040         | 181.1   | 215.8  | 16.0 | 22.5     | 12.9     | 5.6       | 2.5    |
| helpers      | 12000000       | 865.3   | 1291.8 | 90.5 | 98.6     | 55.3     | 10.9      | 6.9    |
| lists-region | 1501500000     | 334.0   | 312.7  | 98.2 | 104.8    | 83.5     | 7.4       | 158.7  |
| lists        | 1501500000     | 299.7   | 467.6  | 54.5 | 59.2     | 47.2     | 13.5      | 17.0   |
| loop         | 49999995000000 | 735.3   | 453.4  | 64.6 | 84.0     | 41.3     | 5.6       | 4.5    |
| tak          | 9              | 52.0    | 79.4   | 6.5  | 9.4      | 4.4      | 1.9       | 1.2    |

## A procedure's calls of itself, guarded (2026-09-28)

A top-level procedure's calls of itself go through its global, so that
a redefinition is seen (`docs/fx26.md`, "Redefinition"): each was a full
call, a tail one no loop. Now, in register code, they are guarded as
inlined calls are: the arguments made, then, if the global still holds a
closure of the procedure's own word, a jump back to its start (in tail
position) or `invokeself`; else the call through the global, as before.
Exact under redefinition; and a loop now, which is what can be lifted
out of (next). Not from an inlined body, whose names may be an older
global's of the same name (FX-26 has no equality on globals to tell).
Both compilers alike (`r_self_guarded`, `r-self-guarded`, which the
specialized copies' self-calls now share).

| benchmark | registers before | after | native before | after |
| --------- | ---------------: | ----: | ------------: | ----: |
| lists     | 13.5             | 9.3   | 17.0          | 12.0  |
| helpers   | 10.9             | 8.9   | 6.9           | 5.5   |
| closures  | about 20         | 18.0  | 31.0          | 26.1  |
| fib       | 5.6              | 5.4   | 2.5           | 2.4   |

The front end compiling itself as register code: the same (0.87–0.90 s
this hour, HEAD and this alike).

| program      | answer         | lowered | rust   | hand | stencils | compiled | registers | native |
| ------------ | -------------- | ------: | -----: | ---: | -------: | -------: | --------: | -----: |
| captures     | 420000         | 113.1   | 48.7   | 15.2 | 14.8     | 12.9     | 9.5       | 21.9   |
| closures     | 6003000000     | 341.9   | 681.0  | 75.0 | 79.5     | 60.0     | 18.0      | 26.1   |
| fib          | 832040         | 180.9   | 211.9  | 16.1 | 21.7     | 13.3     | 5.4       | 2.4    |
| helpers      | 12000000       | 871.5   | 1272.8 | 90.0 | 102.0    | 55.9     | 8.9       | 5.5    |
| lists-region | 1501500000     | 334.4   | 313.5  | 98.5 | 105.5    | 83.8     | 7.2       | 159.0  |
| lists        | 1501500000     | 300.3   | 464.8  | 54.5 | 59.6     | 47.1     | 9.3       | 12.0   |
| loop         | 49999995000000 | 734.4   | 452.6  | 64.7 | 71.8     | 43.2     | 5.6       | 4.6    |
| tak          | 9              | 52.1    | 77.9   | 6.5  | 9.0      | 4.4      | 1.8       | 1.2    |

## Lifting out of loops: measured, not built (2026-09-28)

A probe counted, in each loop (a procedure with a tail call of itself,
a `letrec`'s or, since the change above, a top-level one's), the pure
expressions (arithmetic, comparisons, `not`, `null?`, `extract` of a
frozen product; `car` and `cdr` counted too) whose names are all
invariant: parameters passed unchanged to every call of itself, values
captured from outside, constants. Those in the head, before the first
branch, run every iteration, so lifting them keeps what runs:

| where           | loops | invariant | in the head |
| --------------- | ----: | --------: | ----------: |
| the front end   | 311   | 21        | 3           |
| every benchmark | 13    | 2         | 1           |

About half the front end's are `car` or `cdr`, which a `set-car!` in the
loop would change (the effect system would have to say not). The rest
are `(extract gen 4)`, `(+ depth i)` and the like, each one instruction.
Global loads are not invariant under redefinition, exactly: a
continuation taken in the loop and resumed after a redefinition must see
the new value, as the loop without the lifting would. So not built:
FX-26's loops pass what they use as parameters, and the code binds
invariants outside its loops already. What made loops at all, the
guarded calls of itself above, was the gain.

## `global-guard`, one instruction (2026-09-28)

The guard of inlined, specialized and self calls was four instructions of
register code (`global g; field 2; op2imm eq w; branchf L`), which three
places each matched as a pattern: the native compiler's fold (and its
test that no branch landed inside), `,inliners`, and a rewrite for
globals holding native closures. It is one now, `global-guard g w L`
(the user's name): unless global `g` holds a closure made from word `w`,
to `L`; RESULT kept. "Made from `w`" takes both kinds: a cellular
closure of `w`, or a native closure whose code was compiled from `w`
(the code's field 2, `CODE_SOURCE`, as a closure's field 2 is its word or
its code), so the rewrite for native closures is gone. The native
compiler still decides it when it compiles, where the global holds a
cellular closure; else it is two loads and a compare, and two more for a
native closure. Both register compilers make it (`RItem::Guard`,
`r-guard-to`); the heap checks its target as a branch's; the
register-code machine and the disassembler know it. Clarity, not speed:
the times are unchanged.

## Join points (2026-09-28)

A `letrec`-bound procedure that the `letrec`'s body calls only in tail
position, that calls itself only so, and that no sibling mentions, is a
join point (the `letrec` itself in tail position): in register code no
closure is made of it and no call is made to it; its code follows the
body's, in the procedure around it, where its free names are that
procedure's own variables, and each call is its arguments into its
parameters' places and a jump. The places are registers in a leaf, or
where its body makes no call (so many as leave half of them), else frame
slots. A procedure whose `letrec`s are join points only can be a leaf.
Both compilers alike (`r_join_ok`, `r-join-ok?`).

Measured first: the front end has 27 such `letrec`s of 54, the test
programs 14 of 44; the benchmarks enter theirs once each, so they gain
nothing measurable (`loop` 4.4 → 4.2 ms native). What it saves is an
allocation and a call each time such a loop is entered.

The first version kept a join point's parameters in frame slots always:
`loop`'s code, a leaf with its parameters in registers while it was a
procedure of its own, went from 4.1 to 12.3 ms natively. Hence the
registers.

The front end compiling itself as register code takes longer, 0.87 →
0.94 s: not its code (with join points turned off in the Rust compiler
that makes stage 1, the time is the same) but the FX-26 compiler's own
work, which now asks of each `letrec` whether its bindings are join
points, a walk of its body each time it is asked, and it is asked
repeatedly (`r-collects` is called on the same subtrees many times).
Not asymptotic; a cache of the answer per `letrec` would remove it.

| program      | answer         | lowered | rust   | hand | stencils | compiled | registers | native |
| ------------ | -------------- | ------: | -----: | ---: | -------: | -------: | --------: | -----: |
| captures     | 420000         | 113.3   | 49.5   | 14.4 | 14.0     | 12.7     | 9.1       | 23.0   |
| closures     | 6003000000     | 349.4   | 691.3  | 75.3 | 82.5     | 62.5     | 19.9      | 27.7   |
| fib          | 832040         | 181.9   | 213.4  | 16.1 | 22.5     | 13.2     | 5.0       | 2.4    |
| helpers      | 12000000       | 868.7   | 1286.4 | 89.1 | 115.8    | 58.1     | 9.1       | 6.0    |
| lists-region | 1501500000     | 337.1   | 315.5  | 98.4 | 112.3    | 83.5     | 7.1       | 156.3  |
| lists        | 1501500000     | 298.2   | 466.4  | 55.2 | 68.4     | 47.4     | 9.3       | 12.4   |
| loop         | 49999995000000 | 735.0   | 457.1  | 64.3 | 96.3     | 53.2     | 4.8       | 4.2    |
| tak          | 9              | 52.0    | 78.1   | 6.6  | 11.6     | 4.5      | 1.7       | 1.2    |

## Globals found by name in a table, not a list (2026-09-28)

The FX-26 compiler kept the global environment as a list, newest first,
searched from the start for each global a name might be: every call site
asked it, some several times (whether the callee is a standard
operation, a join point, a global to inline or specialize), and the list
is some 900 long when the front end compiles itself. That is a search of
all the globals per name used, quadratic in the program. Now a table from
each name to its globals, newest first, each with its place in the order
made; a body compiled where it was written (an inlined one, a copy
specialized at a lambda) sees the globals made before it as a count,
where it saw a list's tail. The Rust compiler the same, by a map. The
same code made, by both.

Found by chasing the join points' cost to compile time (0.87 → 0.94 s):
not the question asked of each `letrec` (answered once each now, all the
same), but that every call now also asked whether its callee was a join
point, by a search of the locals and then all the globals. Join points
are locals; that is asked of the locals alone now, too.

The front end compiling itself as register code, same hour, before join
points and now: 0.91–0.94 s → 0.75 s.

| program      | answer         | lowered | rust   | hand | stencils | compiled | registers | native |
| ------------ | -------------- | ------: | -----: | ---: | -------: | -------: | --------: | -----: |
| captures     | 420000         | 116.2   | 50.0   | 15.5 | 14.9     | 12.3     | 9.0       | 22.8   |
| closures     | 6003000000     | 344.6   | 699.1  | 75.6 | 77.8     | 60.3     | 19.6      | 27.6   |
| fib          | 832040         | 181.0   | 218.4  | 15.9 | 23.5     | 13.2     | 5.0       | 2.4    |
| helpers      | 12000000       | 865.5   | 1312.7 | 89.4 | 99.7     | 56.2     | 9.0       | 6.1    |
| lists-region | 1501500000     | 335.7   | 313.4  | 99.9 | 108.2    | 85.3     | 7.2       | 159.1  |
| lists        | 1501500000     | 300.3   | 480.1  | 54.9 | 57.4     | 47.2     | 9.3       | 12.5   |
| loop         | 49999995000000 | 739.5   | 447.9  | 66.4 | 75.9     | 48.6     | 4.9       | 4.6    |
| tak          | 9              | 52.2    | 80.9   | 6.6  | 9.7      | 4.5      | 1.7       | 1.2    |

## Versions: one guard per global, at the start (2026-09-28)

The user's idea: rather than a guard at each inlined, specialized or self
call, all of a body's guards at once at its start, then a version of the
body compiled assuming every one holds (no guards inside, no slow calls),
and the plain version, as before, where any fails. Two versions, not one
per combination of globals: code at most twice the procedure's, no
blow-up.

Sound where no global can change during one run of the body. A
redefinition happens between top-level forms, so only a continuation kept
past one and resumed after, or a write to a global, could let a run see
one; and those show in the body's own effect, masked (a continuation that
cannot escape has its `comefrom` masked away): the effect summary 3
(`docs/fx26.md`, "Effect summaries"). Where the summary is 3, per-site
guards as before. Only bodies that make no closure (no lambda, `letrec`
or `prompt`) are versioned, since register code compiles a nested lambda
afresh, and a body compiled twice would compile its lambdas twice, and
theirs, exponentially.

In the fast version an inlined call and a call of itself in tail position
are no calls, so it can be a leaf, all in registers, where the plain one
has a frame; the native compiler now says per instruction whether the
frame is pushed (`lexical` reads the closure's register where it is not).
Its guards are `global-guard` each, deduplicated (`wglobal=?`, new, as
`eq?`); decided when compiling natively where the global holds a cellular
closure, as before.

Worth it only where the fast version is a leaf or loops where the plain
one calls: else all its guards run on every entry, where the plain
version's each run only on the path that reaches its call, and the front
end, whose procedures branch widely, got slower (as register code, 0.72
→ 0.87 s compiling itself). A fast version is compiled only where asking
first (a leaf, with inlined calls no calls; or its own name mentioned)
says it may pay. Both compilers alike; the summaries reach the FX-26
compiler with the facts (`checked-extracts`, `rust_facts`: `(a b n)`,
negative `n` a summary).

| benchmark | registers before | after | native before | after |
| --------- | ---------------: | ----: | ------------: | ----: |
| helpers   | 9.0              | 2.8   | 6.1           | 2.0   |
| lists     | 9.3              | 8.5   | 12.1          | 10.5  |
| closures  | 19.6             | 17.6  | 27.6          | 24.0  |

`helpers`'s `run` is now, in its fast version, a loop in registers with
`step`, `sum2` and `dbl` inlined into it, and `(dbl 2)` folded to 4. The
front end compiling itself: 0.70–0.71 s → 0.76–0.77 s (same hour),
the compiler's own work: filling the summaries' table (0.01 s), asking
whether a fast version pays, and compiling those that do (0.03 s).

| program      | answer         | lowered | rust   | hand | stencils | compiled | registers | native |
| ------------ | -------------- | ------: | -----: | ---: | -------: | -------: | --------: | -----: |
| captures     | 420000         | 111.8   | 49.1   | 14.6 | 14.5     | 12.4     | 9.2       | 21.9   |
| closures     | 6003000000     | 343.2   | 699.4  | 75.7 | 85.0     | 60.3     | 17.6      | 24.0   |
| fib          | 832040         | 180.5   | 213.7  | 16.1 | 22.0     | 13.5     | 4.9       | 2.4    |
| helpers      | 12000000       | 865.5   | 1274.3 | 89.3 | 110.0    | 55.2     | 2.8       | 2.3    |
| lists-region | 1501500000     | 332.8   | 314.4  | 96.9 | 111.8    | 82.8     | 7.2       | 156.5  |
| lists        | 1501500000     | 297.8   | 470.1  | 54.7 | 65.9     | 47.4     | 8.5       | 10.5   |
| loop         | 49999995000000 | 736.0   | 452.2  | 64.5 | 89.7     | 41.2     | 4.7       | 4.3    |
| tak          | 9              | 51.6    | 78.0   | 6.6  | 8.7      | 4.5      | 1.7       | 1.2    |

## A nested lambda compiled once (2026-09-28)

Found by the user, asking why `,disassemble-asm` of `(lambda (y) (lambda
(x) (+ y x)))` showed the inner lambda twice. A body is compiled twice
when register code is made: to stack code, and to register code, its
twin. Each pass made its own word for every lambda in the body, and each
of those words was compiled twice in turn: 2^(d-1) words for a lambda d
deep (3, 7 and 15 words in all for 2, 3 and 4 deep), each with its own
register code and machine code. The register code of a body now uses the
words its stack code just made (matched by where the lambda's body is,
its parameters, its own name and what it captures), in both compilers:
one word per lambda (`a_nested_lambda_is_compiled_once`).

The front end nests lambdas little, so compiling itself takes as long
as before (0.78 s → 0.77–0.78 s); curried code and closures returning
closures are what gain.

## Constant data made once, while compiling (2026-09-28)

A constructor is a global procedure whose body is a sum of a product,
`(sum rgb (product (1 r) (2 g) (3 b)))`: two `%make-frozen` calls each time
it runs, even `(red)`, which has no fields. Inlined in a fast version
(behind the body's `global-guard`s) and given constants, both register
compilers now make the data while compiling, once, and the code loads it:
`(red)` is `const #<sum red>`, a leaf. A sum or a product is a known
constant when its parts are, so it folds through `let`s and inlined calls
as integers do. Sums and products are frozen, and FX-26 has no `eq?`, so
no run can tell a shared one from one of its own. The FX-26 compiler makes
them with `wcell-sum` and `wcell-product`, new standard operations; the
native code loads them from its code's fields, which the collector traces.

The front end compiling itself: 0.77–0.78 s → 0.75–0.76 s.

## Operands: order kept, constants second, constant chains combined (2026-09-28)

`>` and `<=` are `<` with the operands traded, and register code ran the
second operand first: `(> (begin (set r 10) 5) (get r))` gave #t there and
#f everywhere else (`run/operand-order.fx`). Operands now trade places only
where one is a variable or a constant, which neither has an effect nor sees
one (only a definition writes a global). Otherwise the first runs first and
waits in a register (or the frame, if the second calls).

The same rule, asked by the user: where the operation does not care which
comes first (`+`, `eq`), a constant first goes second, as an immediate:
`(+ 1 x)` is `op2imm int-add 1`. And a chain of `+`, and of `-` of
constants, with one operand not a constant, adds the constants' sum at
once: `(- (+ 1 (+ 2 x)) 10)` is `op2imm int-sub 7`. Integers are exact
(overflow goes to bignums), so the order of the additions cannot matter.
Both compilers.

## Tests as jumps: `and`, `or`, `not`, no boolean made (2026-09-28)

The user recalled that Twobit made much of conditionals, and it does:
`pass2if.sch` (Clinger, 1991 and 1999) rewrites `if`s in tests, as
`(if (not E0) E1 E2)` to `(if E0 E2 E1)` and `(if (if B0 K #f) E1 E2)` to
`(if B0 E1 E2)`, because `and`, `or` and `cond` expand to nested `if`s.
FX-26's parser expands them the same way (476 `and`s and 339 `or`s in the
front end), and register code made a boolean of each compound test and
tested it again: `(if (and (< x 10) (not (= y 0))) 1 …)` was 19 arm64
instructions natively.

Both register compilers now compile a test as jumps (`r_branch_on`): to a
label if it is true, or false, and on if not. `not` turns the sense; an
`if`, which is what `and` and `or` are, becomes jumps from its parts, its
constant arms decided while compiling; a constant is a branch or nothing;
anything else is made and branched on, by `branchf` or the new `brancht`
(a register operation, 29). The native compiler fuses a comparison with
the branch after it, either kind, into `cmp` and `b.cond`. The example is
14 instructions, each test one compare and one branch. Since `and` and
`or` are on booleans only, one rule covers what Twobit needed several for.

**A regression that was a collection.** The compile phase of the front
end on itself, as register code, went 0.120 → 0.138 s with the operand
commit before this one, on 2% more cells (the Rust machine's count, the
compiler's own work). Back-to-back runs of both commits held the baseline;
`probe_phases_as_register_code` (`tests/bootstrap.rs`), which reports time
and collections per phase, showed the compile phase taking two collections
where it took one: 35.6 ms against 18.5 ms, the whole difference. The
front end grew by the new code and crossed the next threshold. So a
collection's cost, not the new code's, is the step; the heap's sizing is
what would take it back.

## The reader's allocation (2026-09-28)

The user's request, after the phase probe showed the reader allocating
18.4 M words to read the front end (some 760 KB). Allocation is now counted
by word too: the Rust machine's profile charges what each cell allocates,
by a primitive it calls as well, to the cell's word
(`FIXPT_PROFILE_PHASE=read` or `=compile` with
`probe_phases_as_register_code`).

Of the program's 16.6 M words: cursors 6.3 M (38%: `advance` made a
cursor, three pairs and a one-character list, for every character), atoms
3.4 M (a `cons` a character, then `reverse` and `list->string`), the
marks of lists 4.0 M (a mark rebuilt for each item, and the items
reversed at the end), the syntax itself 1.2 M. Continuations are not
the cost, as the user wondered: fed a whole file, the reader takes every
character from the text given ahead and suspends once, at the end; its
marks cost 5% of the read's time (0.003 of 0.060 s, measured with them
off).

The loops over characters (whitespace, line comments, atoms, strings)
now keep only the last character and where it is, and read the next
themselves: one cursor for a token, not one for each character; and an
atom's reader no longer makes a closure to read with. The read: 18.4 M →
14.5 M words, the same five collections and time (0.059 s); the compile
phase after it, 2 collections → 1 (0.134 → 0.121 s), the thresholds
moved.

What is left: closures for each atom's and list's `letrec` procedures,
called from inside a mark's thunk, so not join points (lambda lifting
would take them); the atoms' character lists; the marks of lists, whose
shape the Scheme and Rust readers share.

## Native code: shared stubs, closures made inline (2026-09-28)

The user's example, `,disassemble-asm (lambda () ((lambda ((y int))
(lambda ((x int)) (+ y x))) 3))` in the native convention: three code
objects of 114, 76 and 19 instructions, growing outward. Not the nested
lambdas compiled more than once (fixed before); each object carried its
own copy of code that depends on nothing in it.

- **Traps** (#76): each object had, for each kind of trap it could raise,
  14 instructions that record the trap and leave. Now the machine has one
  common trap (`common_trap`), and an object's stub for a kind is three
  instructions that go there, the return address still the site's.
- **Calls of what is not native code**: the routine that calls out for
  them (some 28 instructions) is the machine's too (`common_foreign`).
- **Closures** (#75): made inline, as pairs are, from the heap's free
  space when there is room short of the collection's threshold: the
  header, the free values from REG1…REGn, the code, the trailer, and the
  top bumped. When there is no room, the machine's common routine
  (`common_closure`, call-out `ClosureAny`) makes it, in four instructions
  at the site.

The example's objects: 114, 76, 19 → 54, 44, 8 instructions. `captures`
natively 22.3 → 18.4 ms; `closures` unchanged (its time is elsewhere). A
procedure that makes a closure still has a frame, for the call-out: a
leaf would need register code to count making a closure as not calling.

## Lambda lifting (2026-09-28)

The user's request, after Twobit's pass 2 (`pass2p2.sch`, Clinger 1991):
a `letrec` procedure that is only ever called need not be a closure made
each time the `letrec` runs. Both compilers lift a `letrec` group where
every member is a plain lambda only called (in any position, lambdas
inside included), with its arity; where it is not all join points
(register code's jumps are better still); and where each member takes
fewer than 6 names more (Twobit's bound) and no more than 8 arguments
(the registers). What a member takes: the locals it would capture, and
what each sibling it calls takes (Twobit's flow equations), outermost
binding first. Each member's closure, over nothing, is made once while
compiling; a call passes the added names first; a member's tail calls of
itself are still loops, storing only its own parameters. The stack code
decides, by where the `letrec` is; its register code asks and gets the
same answer and words (not in a body inlined or specialized there). A
lambda that calls a lifted procedure captures the names the call passes.
The native compiler calls such a closure's code straight, as it does a
global's (without that, `lists-region` ran its loops on the cellular
machine: 156 → 316 ms, now 160).

Measured against a baseline re-measured back to back (three runs each),
the front end on itself, as register code:

| phase   | words before | after  | collections | time before | after   |
| ------- | -----------: | -----: | ----------- | ----------: | ------: |
| read    | 14.5 M       | 13.1 M | 5 → 5       | 0.061 s     | 0.061 s |
| check   | 21.4 M       | 18.4 M | 3 → 2       | 0.534 s     | 0.530 s |
| compile | 26.1 M       | 27.3 M | 1 → 1       | 0.125 s     | 0.132 s |

About 5% less allocation in all, one collection fewer; the time about the
same. The Rust compiler alone lifting (the front end not yet grown by the
FX-26 side) had checked in 0.508 s. The compile phase does more: the
lifting's own work (every lambda's free names looked up for lifted ones,
+1.8 M cells in `c-find`), and the front end is bigger, which crossed a
table's doubling in the compiler (+4.5 M cells rehashing). Native
benchmarks unchanged: their loops are globals, not `letrec`s.

Found on the way: an error loading the front end now says where in its
files (`front_end_location`), not at the user's input's first character.

## A lambda applied at once is a `let` (2026-09-28)

`((lambda ((y int)) …) 3)` made a closure and called it, through the
unknown procedure's path. Both compilers, stack and register code alike,
now compile a plain lambda (under forms that compile to nothing) applied
to as many arguments as it has parameters as the `let` it is
(`applied_lambda`, `c-applied-let`): the arguments made in order, bound,
and the body in their scope, in tail position if the call was. Register
code then keeps a constant argument as a constant, and folds with it.

The user's example, `(lambda () ((lambda ((y int)) (lambda ((x int)) (+ y
x))) 3))` natively: three code objects of 54, 44 and 8 instructions → two
of 43 and 8. `,native ((lambda ((x int)) (+ x 1)) 41)` is now `movz x0,
#0x150`, 42. The front end has no such applications; its self-compile is
unchanged. Analyses (free names, whether code calls) still see an
application there, and so are only cautious.

## A procedure that only makes a closure is a leaf (2026-09-28)

`(lambda ((y int)) (lambda ((x int)) (+ y x)))` had a frame only because
making a closure may call out, and so collect. Where the closure is the
procedure's value, in tail position, nothing is used after that call-out
but the closure, so both register compilers now count a lambda in tail
position as not collecting (`r_collects`, `r-collects`) and let a leaf
make one (`r_lambda`'s `tail`). A leaf's free values are in registers, so
they are moved into REG1…REGn as a parallel move (`r_par_moves`,
`r-par-moves`): the first move whose destination no other reads, in order;
at a cycle, the first destination kept in RESULT. Where no free value is
in a register, the code is as before.

The machines: the native compiler's inline path needs no frame; its slow
path, where the free space has no room, makes a frame of its own (16
bytes, nothing in it for the collector) around the call to the common
routine. The hand-encoded register machine keeps a leaf's link in the
state (`leaf_link`) while it calls out, since the call-out's `blr` takes
`x30`.

The example's closure maker natively: 43 → 26 instructions (the inline
allocation, then the slow path's seven, then `ret`). Both `r_collects`
now also count a lifted procedure's added parameters when they ask
whether a call of itself is a loop.

## The reader: atoms taken whole; `substring` in time for its part (2026-09-28)

The reader's atoms were lists of characters, a pair a character, then
reversed and made a string: some 3 M of the 12.7 M words the front end's
reading took. When an atom is all in the text given ahead, as a file's
is, `read-atom-from` now takes it whole at the end, with `substring`, and
lists nothing (`mode` 0); if a feed comes in the middle (text typed a
character at a time) or an escape does, it lists what it has so far from
that text and goes on as before. A feed changes `ahead-origin` (where the
text given ahead starts, or -1), so an unchanged origin is an unchanged
text. The loop's free names and parameters were kept to Twobit's bounds,
so its procedures stay lambda-lifted (a first try had six added names
and closures again).

Found on the way, an asymptotic bug: the runtime's `substring` copied the
whole string to take a part (a 760 KB text for each atom: the read went
from 0.06 s to 150 s). It reads just the part now.

The read: 13.1 → 11.8 M words, five collections → four, 0.060 → 0.054 s.
The check phase after it now takes three collections where it took two
(the thresholds moved), so the self-compile as a whole is the same
(0.723 → 0.730 s, 58.8 → 57.9 M words).

## Conversions between conventions: adapters (2026-09-29)

A procedure of one convention given where the other is expected is
converted by `%fx26-convert`, which both checkers record with the
procedure's arity and all four compilers emit: a value already of the
kind asked for is itself; one of the other kind becomes an adapter, a
closure of that kind over it whose code calls it. A cellular adapter's
word is `free 0; tailcall n`; a native adapter's code is four
instructions into the machine's `common_foreign`. A call of a procedure of
the other convention needs nothing: every machine's call looks at its
callee's kind, as a call through `fx` does.

What a call through an adapter costs, 10^6 calls of `(lambda (x) (+ x 1))`
from a cellular loop (the `rust` machine):

| callee                              | time   |
| ----------------------------------- | -----: |
| a cellular closure, an unknown call | 0.11 s |
| a native adapter over it            | 0.53 s |

About 0.4 µs a call more: cellular code calls native code through the
runtime's `call_native`, and the adapter calls the cellular closure through
a call-out that runs it on a cellular machine of its own, for which
`call_value` builds a word each time. Nothing in the benchmarks converts,
and their times are unchanged.

Native code may now call cellular code that calls native code, to any
depth: the inner native call runs on the machine's stack below the frames
of the run that called out (a machine was in use before, and the call
failed). 300 such levels, collecting every 50 safepoints, are in
`conversions_make_adapters`.

A standard operation as a value (`(m * 5)`, `(app2 cons 7)`) is a closure
of a word the compilers make for it; that word now has register code too
(its operands already in REG1…REGn; a call-out made in a frame), and the
register compilers make the closure where the stack compilers did, instead
of declining the procedure. A name a standard operation has is no longer
"simple" to the register compilers, since it may be such a closure, made
when needed. Of every test program's forms, 102 expressions ran as
machine code before these changes, with the widened report; 115 now.

## Stack maps in native frames (2026-09-29)

A native frame now has a header word after its link and return address:
a fixnum, the mask of its slots the collector traces
(`docs/research/generational-gc.md` §1). The native compiler finds which
of register code's slots are live after each instruction, with a
backward pass over `stack`/`load` (reads) and `setstk`/`store` (writes).
Before each call, call-out and closure made in a frame, the code stores
that mask with the code bloblet's slot and the closure's. It leaves the
store out where the same mask is stored already on the only way there.
The collector's walk, the foreign call-out's copy of the frames' values,
and a continuation's copy follow the mask. `save` no longer clears the
slots, since none is read unless written.

A dead slot no longer keeps what it held: `a_dead_slot_keeps_nothing_alive`
(`programs/native/dead-slot.fx`) holds a 100 000-word array in a slot
dead across a call that collects about 30 times. Traced as before, every
slot, both versions copied the array each time. With the map, only the
version that keeps it live does.

On the way: a call-out walked every native frame to gather roots whether
or not it then collected (`maybe_collect`). It now asks the heap first
(`collection_due`), and walks only for a collection. Native times:

| program      | before | after |
| ------------ | -----: | ----: |
| captures     | 18.0   | 14.4  |
| lists-region | 155.5  | 55.4  |
| fib          | 2.3    | 2.2   |
| tak          | 1.2    | 1.0   |

(ms, best of 3; the rest unchanged. `lists-region` calls out for each
region `cons`, 20 deep and more; `captures` takes continuations, whose
copy reads each frame's mask directly.)

## A nursery, a card-marking write barrier (2026-09-29)

The heap is generational (`docs/research/generational-gc.md` §2–3):
everything is allocated in a nursery of 2^20 words, and a safepoint that
finds it full collects it alone, promoting what is live to the end of
the old semispace. The remembered set is a card table (a byte per 64
words), which a barrier after each store into an existing object marks.
That is `Heap::set_slot` for the Rust side, and six instructions after
`field!`, `global!`, `setfield` and `setglbl` in each machine that stores
inline (the hand, compiled and stencil machines, the register machine, the
native compiler).

The front end's self-compile, as register code (`probe_phases_as_register_code`),
by the nursery's size in words:

| nursery | read  | parse | check | compile | total | of which collecting |
| ------- | ----: | ----: | ----: | ------: | ----: | ------------------: |
| none    | 0.053 | 0.006 | 0.547 | 0.153   | 0.759 | 80.8                |
| 512K    | 0.050 | 0.006 | 0.522 | 0.148   | 0.726 | 70.7                |
| 1M      | 0.054 | 0.004 | 0.500 | 0.139   | 0.697 | 46.4                |
| 2M      | 0.050 | 0.005 | 0.513 | 0.134   | 0.702 | 53.7                |
| 4M      | 0.054 | 0.012 | 0.488 | 0.133   | 0.687 | 41.5                |

(seconds, and milliseconds collecting.) Where a major collection falls
moves each row by a few milliseconds. The read, whose data nearly all
lives on, pays for copying it twice (9 ms collecting → 18); the check and
the compile, which make much that dies young, gain. 1M is the default.

The benchmarks: native `closures` 25.5 → 20.6 ms, `lists` 11.3 → 8.0;
register code's `lists` 9.3 → 6.0, `closures` 19.4 → 15.0; the rest the
same. The barrier's six instructions are not seen: no benchmark stores
much into old objects.

## More than 8 values in register code (2026-09-29)

Register code took at most 8 arguments, parameters, free values or a
call-out's operands, and declined the rest: its procedure ran as cellular
code, and, natively, so did every procedure compiled with it. Larceny's
convention now carries more: REG1…REG7 the first seven, REG8 a list of
the rest, which the callee takes apart into its frame. The list costs a
`cons` per value past the seventh, at each call. With it, and with a
global's procedure the native compiler cannot compile called through its
cell instead of failing its callers, the reference benchmarks that
declined have no declines left. Native, one run each, seconds:

| benchmark             | before | after |
| --------------------- | -----: | ----: |
| `earley`              | 761.4  | 104.0 |
| `parsing`             | 125.2  | 15.7  |
| `graphs`              | 29.0   | 13.6  |
| `mlton/ratio-regions` | 3.8    | 4.2   |

## Native call-outs collect what is due (2026-09-29)

Counted with the new `FIXPT_GC_REPORT=1 fixpt eval`, `paraffins` made
657 major collections natively and 8 minor, copying 23 400 M words; the
lowered program, 12 major and 1095 minor. The native call-out called
`Heap::collect`, the major collection, whenever a collection was due,
which with the nursery meant every time it filled. It calls
`collect_due` now:

| `paraffins`    | seconds | major | minor | copied (M words), major / minor |
| -------------- | ------: | ----: | ----: | ------------------------------: |
| native, before | 56.3    | 657   | 8     | 23 403 / 3.9                    |
| native, after  | 9.7     | 8     | 664   | 328.3 / 691.5                   |
| lowered        | 17.4    | 12    | 1095  | 323.4 / 688.1                   |

The `direct` test binary, which runs native code under collections, went
from 12 s to 5 s.

## The FX-26 checker: quadratic spots, and run as register code (2026-09-29)

The user asked why the FX-26 checker took seconds where the Rust one
takes milliseconds. On `scheme-bench/set.fx`, whose effects name up to 17
globals:

| the FX-26 checker                               | as lowered Scheme | as register code | the Rust checker |
| ----------------------------------------------- | ----------------: | ---------------: | ---------------: |
| before                                          | 4.96 s            | 0.41 s           | 0.026 s          |
| name order, type printing, union, subset linear | 3.18 s            | 0.112 s          | 0.026 s          |
| the session's front end as register code        | —                 | 0.31 s           | 0.026 s          |

(The last row is `fixpt check`'s own timing, `FIXPT_TIME_PHASES=1`; the
register-code column above it is the bootstrap probe's, which reads the
program with the compiled reader too.) The front end's work in a native
run of `set.fx` with no iterations: 9.8 s before, 5.0 s after the
quadratic fixes, 0.65 s as register code.

## Primitives that never collect, in line (2026-09-29)

The fixed-width integers' operations (`u32*`, `u32-xor`, `int->u32`, …),
and `int`'s `*`, `quotient` and `modulo`, were runtime primitives called
through `prim`, which may collect: register code kept every live value in
the frame around each one, and native code switched to Rust's stack and
back. FNV-1a over 10 million numbers in `u32` took 1.4 s natively.

`fixpt_runtime::never_collects` names them now, and register code calls
them with `prim1`, `prim2` and `prim2imm` (`RESULT := p(RESULT, REGk)`, as
`op2`), which are no safepoint: the values stay in registers, and a loop
of them is a leaf. Native code does each in a few instructions where it
can (an `i32` or `u32` is the fixnum of its value: the fixnums' arithmetic,
then wrapped by one `and`, or a shift pair if signed; an `i64` or `u64`
while it fits a fixnum), and otherwise calls the primitive without a
collection, REG1…REG8, the closure and the link kept in the state. It may
allocate a bignum: allocation never collects, only safepoints do. Both
compilers also fold `int->T` of a literal that fits the type, to the
literal, so that `(u32* h (int->u32 16777619))` is `prim2imm`.

| 10 million iterations (ms)       | before | after, native | registers |
| -------------------------------- | -----: | ------------: | --------: |
| FNV-1a in `u32`                  | 1385.6 | 12.0          | 825.8     |
| FNV-1a in `u64` (mostly bignums) | 3903.9 | 1586.8        | 2631.1    |
| `int`: `*`, `+`, `modulo`        | 485.5  | 41.9          | 426.8     |

(`before` is native too. The register machine calls each one in Rust; it is
not a speed target. A `u64` past 60 bits is a bignum, so FNV-1a in `u64`
still allocated each step: see the next section.)

## `i64` and `u64` raw in native registers (2026-09-30)

An `i64` or `u64` is its exact integer everywhere (a bignum past 60 bits),
so FNV-1a in `u64` made a bignum each step, even with its operations in
line: 1.6 s for 10 million steps. The user asked for "storing 64 bits in
registers".

Native code (`fixpt_native::direct`, its `reps` pass) now keeps them raw
in registers, and only there. Register code is unchanged (it is the same
for every machine, and its registers hold values); the native compiler
works out, forward over each procedure's register code, which registers
hold raw 64 bits:

- an operation of `i64` or `u64` takes its operands raw and gives its
  value raw (a comparison and `T->int` give values); `int->T` is an
  unboxing, which wraps;
- `reg`, `setreg` and `movereg` move a register as it is;
- whatever else reads a register reads a value: a raw one is boxed first,
  in place (a fixnum where it fits, else a bignum by a call-out that does
  not collect). So nothing raw is stored in a frame, passed, returned or
  kept in the heap, and no collection sees raw bits;
- where ways meet, a register raw on one way is raw after, and the ways
  where it is a value unbox it (in line, or in a stub on a branch): a
  loop's variable is unboxed once, on the way in, and stays raw around
  the loop.

The operations are then the machine's: `add`, `mul`, `eor`, `udiv`,
`lsrv`, and unsigned comparisons for `u64`.

| 10 million iterations, native (ms) | values in line | raw  |
| ---------------------------------- | -------------: | ---: |
| FNV-1a in `u64`                    | 1586.8         | 11.0 |
| FNV-1a in `u32` (unchanged)        | 12.0           | 12.0 |

## `int` is a bignum: the cost of the tag tests (2026-09-30)

An `int` add, subtract or compare now tests that its operands are
fixnums (`orr` of the two, `tst` of the tag bits, a branch) before the
fixnums' instruction; overflow or a bignum goes out of the way, to the
runtime with no collection. `=` against a fixnum constant needs no test
(a bignum never has a fixnum's value), nor does an operand added to
itself need two. Measured old against new, back to back, natively:

| ms, native | before | after |
| ---------- | -----: | ----: |
| `helpers`  | 2.1    | 3.8   |
| `loop`     | 4.5    | 6.6   |
| `fib`      | 2.2    | 2.8   |
| `lists`    | 8.5    | 7.0   |

(Comparing words first for `=`, and testing both operands only when they
differ, was tried and was slower: a loop's test is mostly of different
words.) The way back: a version of a procedure's code for fixnums, in
which a value tested once stays known, and whose slow paths go over to the
general version.

## Start-up: the front end loaded lowered only where it runs so (2026-09-30)

Both benchmark agents saw native start-up near 2.7 s, against the
READMEs' 1.8 s. Bisected, on an empty program: 1.89 s up to `4d16831`,
2.30 s at `ec2a436` ("The session's FX-26 checker and compilers run as
register code", which said a tiny program would start 0.2 to 0.45 s
later), and 2.7 s by `8747c9d` as the front end grew. Timed by stage:

| stage (empty program, native)                               | before | after  |
| ----------------------------------------------------------- | -----: | -----: |
| the whole front end checked and lowered                     | 0.31 s | —      |
| the whole front end loaded into the Scheme engine           | 1.91 s | —      |
| the reader and parser checked, lowered and loaded           | —      | 0.05 s |
| the front end checked again, compiled to register code, run | 0.37 s | 0.37 s |
| total, wall clock                                           | 2.83 s | 0.49 s |

Since `ec2a436`, a session's checker and compilers run as register code,
but the session still loaded the whole front end lowered, for the reader
alone, which stays lowered (the eager reader steps it, character by
character). It now loads the reader and parser (the front end's first two
files, which need nothing after them, and which the reader's licence
covers). A session whose front end runs lowered (`FIXPT_FRONT_END_LOWERED=1`,
the tests' default) loads all of it, as before. Whole runs: `md5` 3.0 →
0.71 s, `pi` 2.9 → 0.59 s. The test suite went from about 147 to 135 s.
What is left of start-up is mostly the second check of the whole front
end, by the Rust checker, for the register compiler.

## `f64` raw in native registers (2026-09-30)

`f64` is the heap's boxed flonum; native code's `reps` pass keeps one raw
(its bits in an `x` register) between operations, as it does `i64` and
`u64`, and moves it into `d16`/`d17` for each: `fadd`, `fdiv`, `fsqrt`,
`frintn`, `fcmp` and the rest. Boxing is inline, two words from the free
space; unboxing a load. `int->f64` of a fixnum is `scvtf`; `f64->int`
`fcvtzs`, checked exact and a fixnum. The sum of `1/i` for `i` to 10
million:

| ms      | lowered | registers | native |
| ------- | ------: | --------: | -----: |
| `sumfp` | 757.1   | 620.9     | 30.9   |

(Native before `int->f64` was inline: 208.9, a call-out an iteration.)

## Flat arrays natively (2026-09-30)

`flatarray-ref`, `-set!` and `-length` are in line natively, by the
array's layout (field 2) and its suffix's length (the header's). A read
made a box for an `f64` element, which the `f64` operation using it then
opened: a backward pass beside `reps` (`raw_refs`) now finds a read whose
element only `f64` operations use (so the program's types make it an
`f64`), which loads the bits alone; a raw `f64` is stored as it is.

| a million f64s summed, 100 times (ms) | lowered | native |
| ------------------------------------- | ------: | -----: |
| every read a call-out                 | 8016.9  | 4942.6 |
| in line, each element boxed           | —       | 3393.3 |
| in line, raw                          | 8063.3  | 295.9  |

## A fixnum version of native code (2026-09-30)

With `int` a bignum, each add or compare tested its operands' tags. A
procedure with `int` operations now gets two versions of its native code:
a fixnum version first, then the general one. In the fixnum version the
`reps` pass also knows which registers hold fixnums (`Rep::Fix`:
constants, and `int` sums and differences, whose overflow leaves the
version): an operation on known operands tests nothing, and an unknown one
is tested once, after which it is known. Where ways meet the knowledge is
optimistic (a loop's variable, known on the way around, is known at the
head), the ways that do not know it testing it if it is live (a backward
pass). A test that fails, or an overflow, goes over to the general
version at the same instruction: the registers and the frame are the same
in both at every instruction's start, so nothing is converted.

| ms, native | before `int` was a bignum | bignum | fixnum version |
| ---------- | ------------------------: | -----: | -------------: |
| `helpers`  | 2.1                       | 3.8    | 2.0            |
| `loop`     | 4.5                       | 6.6    | 4.0            |
| `fib`      | 2.2                       | 2.8    | 2.6            |
| `lists`    | 8.5                       | 7.0    | 6.0            |

(`fib`'s argument is new at each call, and tested at each.) All 93
benchmark ports give their READMEs' answers natively; `earley` now takes
5.2 s in all (104 s in its README), `paraffins` 7.8 s (57.4).

## The front end cached (2026-09-30)

A session whose front end runs as register code checked the whole front
end with the Rust checker and compiled it at every start (0.33 s of the
0.49). The compiled word is now kept (`DONE.md` §21): copied out of the
session's heap into a heap of its own (`Heap::copy_graph_from`, which
re-interns symbols by name) and written as a heap image to the user's
cache directory (`~/Library/Caches/fixpt/` on macOS, `$XDG_CACHE_HOME/fixpt`
or `~/.cache/fixpt` elsewhere), one file for each executable. The file
begins with a key, a hash of the front end's text and of the executable's
size and time, so a rebuilt `fixpt` never reads an older one's code but
replaces it; `FIXPT_NO_CACHE=1` turns the cache off. Our own code needs no
verifying: the check is there for the facts the register compiler reads.
The image is 9.5 MB (1.18 M words), and its CRC-32, a bit at a time, took
about 35 ms of the load; with a table built at compile time the whole
load, verification included, is 22 ms.

| stage (empty program, native)                     | before | cached |
| ------------------------------------------------- | -----: | -----: |
| the reader and parser checked, lowered and loaded | 0.05 s | 0.05 s |
| the front end checked and compiled                | 0.33 s | —      |
| its image read and verified, and copied in        | —      | 0.03 s |
| the front end run (its globals made)              | 0.04 s | 0.04 s |
| total, wall clock                                 | 0.50 s | 0.19 s |

The first run of a new executable pays 0.28 s more, to write the image.
The ports give the same answers with the cache and without.

## Tail calls in leaves (2026-10-01)

A procedure whose only calls are plain calls in tail position, their
arguments collecting nothing, is now a leaf: no frame, its parameters
kept in registers, and the call's arguments moved into REG1…REGn at once
(the parallel moves loops already used), the procedure into RESULT, and
`tailinvoke`. `(lambda (f x y) (f x y))` was a frame, three stores, three
loads and a pop around the jump; it is three `mov`s and the jump. It makes
281 of the front end's 2940 bodies leaves, and 24 of the test programs'
261. Both register compilers, word for word; where a leaf runs out of
registers, the body is made as before.

Measured old against new back to back, natively: no benchmark moves past
run-to-run noise (about ±2%), nor does checking a large file. Wrappers
and argument shuffles are where it applies, and they are not where the
time goes; kept because it is right, and tidier code to read.

| benchmark | old (s)     | new (s)     |
| --------- | ----------- | ----------- |
| browse    | 10.48 10.07 | 10.05 10.27 |
| conform   | 3.59 3.57   | 3.50 3.62   |
| earley    | 5.21 5.13   | 5.12 5.13   |
| nboyer    | 5.87 6.01   | 5.85 5.85   |
| destruc   | 24.64 24.51 | 24.06 23.93 |

## Compile time in the bench (2026-10-02)

`fixpt bench` prints two tables now (README, "Reading a `fixpt bench`
table"), both in every commit message, so that a change's cost to
compiling shows beside what it does to running.

The run table is the run alone in every column. Two columns changed how
they measure:
- `lowered` counted the Rust checker and lowering until now. It is now the
  lowered Scheme's evaluation only, the bytecode engine's own quick
  compile included. The bench programs are small, so the change is small:
  fib 125.5 → 120.8, captures 105.6 → 105.1.
- `compiled` and `registers` compiled their words to arm64 in the first of
  their runs. The best of 3 hid that, but `--runs 1` did not. They are now
  compiled before the clock starts.

The compile table times each phase alone. With `--front-end` (opt-in:
it adds about 10 s, too much for every commit) a last row is the front
end itself, its files and bootstrap (here best of 3, ms; it is now run
once):

| phase             | Rust  | FX-26  |
| ----------------- | ----- | ------ |
| read              | —     | 4974.6 |
| parse             | —     | 23.0   |
| check             | 394.0 | 1385.0 |
| lower             | 14.8  | —      |
| words             | 70.1  | 756.8  |
| arm64 (cells)     | 7.0   | 978.9  |
| arm64 (registers) | 19.7  | —      |

The Rust `check` includes reading. What stands out:
- **The FX-26 reader** runs lowered on the bytecode engine, as the REPL
  runs it, and takes 5 s on the front end's 1.0 M characters: the slowest
  phase by far. It is the one piece not run as register code (above,
  "Start-up").
- **`native.fx`** takes 140 times as long as `assemble_word` (979 ms
  against 7 ms). It allocates heavily: most of the `fx` phases' 327 M words
  and 311 collections.
- The FX-26 checker is 3.5 times the Rust one, and the FX-26 compiler 11
  times.

Building this found a leak. Every call into the front end
(`%run-front-end`), and every `%run-word` of a closure, makes a
`call-closure` word: `lit` per argument, then `lit closure call n exit`.
The register machine compiled that word, and every word among its
arguments, into code space and a native slot that are never freed. That
was 2–5 KB a call; with the front end's own 26 MB of the 32 MB code space,
a few thousand calls filled it. A long REPL session under `--fx26-run
cellular` would have hit "the code space is full". It also meant that
`fx-compiled`'s first `native-assemble` had the Rust assembler compile the
whole program it was given before `native.fx`'s code replaced it.
`compile_reachable_as` now runs that word as cells and follows only the
closure it calls.

A mid-sized program, compiled only, joins the compile table by default:
`scheme-bench/peval.fx`, 954 lines, a partial evaluator. Of the ports
between 400 and 1000 lines it has the largest Rust `words` and
`registers` times and the largest `fx words`; each phase repeats within
about 2%; it adds half a second. First figures (ms): check 12.6, lower
0.5, words 2.8, arm64 0.26, registers 0.95; fx read 240, fx parse 0.17,
fx check 52, fx words 13, fx arm64 37; 13.6 M words, 13 collections.
Surveying the ports found a crash, `ocaml/boyer` under register code
(PLAN, B1).

## Higher kinds: what the checkers pay (2026-10-04)

Higher kinds add cases to the checkers' walks, and the FX-26 checker
compares effect functions' applications structurally (no intern table;
`PLAN.md`, Q11). On peval, the compile table's mid-sized program, best of
3, against the commit before:

| phase    | before (ms) | after (ms) | change |
| -------- | ----------: | ---------: | -----: |
| check    | 12.25       | 12.69      | +3.6%  |
| fx check | 51.36       | 52.05      | +1.3%  |
| fx words | 12.62       | 13.04      | +3.3%  |

Run times are unchanged within noise: higher kinds are erased before
lowering, and a program that uses none takes the paths it took.

## Loading the lowered front end in one evaluation (2026-10-05)

Profiled with `sample` (above), a bare `fixpt --dialect fx26 repl` spent
3.2 s starting, 89% of it loading the reader and front end as lowered
Scheme (`load_eager_reader`), and most of that in the Scheme engine's own
compiler: `assign::convert` cloning vectors, `malloc` and `free`, dropping
`Program`s. `Compiled::load_into` evaluated each lowered form with its own
`eval_str`, and every evaluation re-analyzes and recompiles the session's
whole program so far (`Prepared::update`), so loading N forms was
quadratic in N. Now they are evaluated in one call. Start-up 3.2 → 0.5 s
(CPU); most tests start such a session, and the suite went from 3:26 to
1:40. Each evaluation still recompiles the whole program (`TODO.md` §36).

## The reader as register code too (2026-10-05)

Profiled with names (above), a native REPL's `,load` spent most of its time
in the bytecode engine (`Vm::drive`): the FX-26 pieces are given each form
as text and read it themselves, and the reader stayed lowered Scheme, fed
from Rust a character at a time (`EagerReader`), while the checker and
compilers ran as register code. Now the reader has an entry point that
reads a whole text inside FX-26, `read-text` (as `bootstrap.fx`'s `b-read`
does), one of `FRONT_ENTRIES`, so that it runs as register code with the
rest of the front end; `syn::read_to_syns` calls it, with no step limit,
as reading the whole text is many steps where a character was a few. The
REPL's keystrokes still go through the eager reader as before. Native
REPL, `okasaki.fx` (370 lines), best of runs:

| what                     | before | after  |
| ------------------------ | -----: | -----: |
| start-up and one `,load` | 1.64 s | 0.69 s |
| each `,load` after       | 57 ms  | 14 ms  |

The output of 20 loads is the same. The suite 1:40 → 1:23; the Emacs
mode's tests 4.2 → 1.1 s.

## A `with` binds only what its body names (2026-10-07)

Making every front-end file a module re-exports each name other files use
as `(define x (with m x))`. A `with` bound every value of its module, in
both checkers (each value's type put in scope) and in both compilers and
the lowering (each value's field loaded into a slot), to use one: a
file's re-exports cost the square of its module's width, and the
generated `layout.fx`, 161 names, made it plain (the self-compile 1.549 →
1.615 s). Now the checkers record, for each `with`, only the module's
values free in its body, each with its position (`Facts::with_vals`,
`k-with-vals`), and everything after binds just those. A re-export is one
field. The self-compile, per phase (probe, back to back against the
generated files made modules):

| phase   | before                       | after                        |
| ------- | ---------------------------- | ---------------------------- |
| read    | 0.118 s                      | 0.124 s                      |
| parse   | 0.013 s                      | 0.012 s                      |
| check   | 1.188 s, 38 GCs, 15.9 M cop. | 1.042 s, 36 GCs, 4.8 M cop.  |
| compile | 0.292 s, 48 GCs, 50.3 M wds. | 0.272 s, 37 GCs, 38.2 M wds. |
| total   | 1.611 s                      | 1.450 s                      |

Below the 1.549 s from before the day's module work began. The suite
2:00 → 1:26. The evaluator written in FX-26 does the same since: it is
given the checker's record with the reshapes (`ev-begin!`), and binds a
`with`'s whole module only where there is none (`run-program`, a program
run unchecked).

## One guard: a global not written since (2026-10-07)

The fast versions had three guards: `global-guard g w` (the cell holds a
closure of word `w`, cellular or compiled from it), `value-guard g v`
(the cell holds `v`) and, for constants folded through a `with`,
`field-guard g i v`. Now there is one, as the user asked: `global-guard g
n`, that global `g` has been written `n` times. A global's cell has a
third field, its count of writes (`layout::cellular::GLOBAL_WRITES`),
which every machine's `global!` and `setglbl` adds one to: the Rust
machine, the hand-encoded cells, `native.fx`, the stencils, the
registers machine and `direct.rs`; and the REPL's definition in the
native convention, which fills a cell itself. Installing a procedure's
native closure in place of its cellular one is not a write: the same
procedure. A guard is two loads, a move and a compare, whatever the
global holds, a procedure, an immediate or a module.

The compiler says what `n` will be: the count when the program is
compiled (`wglobal-writes`), plus its own `global!`s emitted so far, plus
the form's own (a procedure calling itself through its global runs after
its definition's write; one called while the form runs falls back).
Both compilers keep these per program (`writes`, `form_writes`;
`c-writes`, a table by name, `c-form-writes`). A guard is then right
only if what the compiler assumed of the global is what it held at that
count, so knowledge is kept by the global it is of: an inline or
specialization note is seen only where its definition is (`sees`,
`c-sees?`: within the globals an inlined body was compiled with), and a
module's literal members are kept by the module's global, not its name.
Before, an inlined body naming an older `f` could inline a newer `f`'s
body, the word guard then failing every time; with counts it would have
been wrong, and the REPL test of redefinition at another type showed it.

`direct.rs` binds a call of a global holding a cellular closure to that
procedure's code (F14): it now tests the count too, so at the REPL, where
the cell soon holds the procedure's native closure (no write), the bound
call is still taken.

On the same footing, `with` in register code: in a leaf, its values in
registers, as a `let`'s, where it declined before; and in a fast version,
a member of a global module that is a literal folded, the module's
global assumed (`TODO.md` §42, constants reached by a path). Both
compilers make the same code. The front end, compiled by FX-26, HEAD then
this, back to back, twice (ms):

| run | fx words HEAD | fx words | fx M words HEAD | fx M words | fx GCs HEAD | fx GCs |
| --- | -------------:| --------:| ---------------:| ----------:| -----------:| ------:|
| 1   |        251.97 |   255.57 |           127.6 |      128.0 |         122 |    124 |
| 2   |        251.18 |   258.54 |           127.6 |      128.0 |         122 |    124 |

The first version kept the counts in a list, appended at each of the
front end's 4479 definitions and searched at each: 262 and 272 ms. The
benchmarks' run times are unchanged.

## Constant lists, unrolled (2026-10-07)

`parsing.fx` decides a token's kind by `(one-of? t k-list)`, a search of a
list made once, where the Scheme original has `case`. With the lists typed
`acyclic` (nothing writes them), both compilers make such a list once, as
constant data, while compiling, seeing through small helpers that build it;
fold `car` and `cdr` of it; and unroll a small procedure that calls itself
where it is called with one, into the tests a `case` makes, behind guards on
the procedure's global and the list's (`TODO.md` §44). Register code, at
100 iterations, best of 5, against HEAD back to back:

| run | HEAD    | unrolled | by hand |
| --- | ------: | -------: | ------: |
| 1   | 91.7 ms | 84.0 ms  |         |
| 2   | 92.0 ms | 83.6 ms  |         |
| —   |         |          | 82.9 ms |

The guards are the rest. Compiling: the FX-26 compiler asks of every call
whether it unrolls; its unroll notes and constant lists are kept by name,
apart from the other constants, so asking is a table lookup (a list of
every constant global, searched per argument, was the first try). The
front end compiled by FX-26, `fx words`: 265.4 / 261.5 → 273.5 / 265.3 ms,
with the front end itself 1.2% longer.
