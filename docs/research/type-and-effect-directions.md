# Four type and effect directions, made into tasks

PLAN.md's queue item 10 (2026-09-27): each direction the PLAN lists as
"a direction, not yet a task", explored against the code and the local
papers, and turned into tasks. The four are:
- responsiveness as an effect;
- time complexity as an effect;
- concurrency, and processes as distinct from functions;
- closures that carry their types.

The papers are the local ones in `~/Dev/LangPlay/GiffordHistory/papers/`.
Where a direction leans on work that is not local (session types, typed
assembly language, the JVM verifier, proof-carrying code), it is from
memory, and says so.

Two findings on the way were bugs, not directions:
- **Fixed now.** Under `--fx26-run threaded`, a form that loops hung the
  REPL on every machine: `%run-word` ran words with unlimited fuel, and
  the step limit bounded only the Scheme engine around it. The runtime
  now has a fuel budget for a run of a word (`Runtime::word_fuel`), which
  the session sets from its step limit for the run of a form
  (`tests/run.rs`, `threaded_forms_stop_at_the_step_limit`).
- **Open.** A heap image's words are never checked as they load:
  `image::load` runs `Heap::verify`, which checks the heap's shape, but not
  the structural check that `make_threaded_word` and `regcode::check` make
  of every new word (routines in range, operands of the right kind,
  branches onto instructions). Task C3 below.

## 1. Responsiveness as an effect

**The idea, made precise.** Two properties:
- `spin`, a type-level atom meaning "may run unboundedly". It has no
  region, so masking never removes it, and no handler discharges it.
- "Unpolled", a property of one compiled word: "may run unboundedly
  without reaching a poll". The compiler puts a poll on every cycle, so
  no final type carries it. It is an analysis, not a type.

`spin` comes from:
- a call within a `letrec` or `define-rec` group, or of a definition's
  own name;
- a call through a closure whose latent effect has `spin`, or an effect
  variable;
- a call of a continuation (`goto` into what `comefrom` captured).

Primitives are bounded, though not constant: their cost is the time
direction's business.

**What it buys: mostly nothing a call graph does not already give.** A
scan of the self-compile's lambdas (826 words) found:

| words                                                 | count |
| ----------------------------------------------------- | ----- |
| in a cycle of known calls                             | 380   |
| of those, cyclic only through self tail calls (loops) | 136   |
| making an unknown call, and otherwise in no cycle     | 9     |
| needing an entry poll, by call graph alone            | 255   |
| free to skip the entry poll                           | 571   |
| transitively free of cycles and unknown calls         | 223   |

So about 69% of words could skip their entry poll by a call-graph analysis,
with no change to the types. A typed `spin` adds at most 9 words to that.
A poll is two instructions, well predicted, so the gain is small on the
self-compile and larger on `fib`-like benchmarks. What the effect adds is
for the licence: the REPL's speculative run of a form as it is typed
could run a spin-free form with no budget.

**Hazards.**
- *Continuations.* The native machines charge no fuel when a
  continuation is resumed, so `(let ((k (cwcc (lambda (k) k)))) (k k))`
  loops with no poll (read in the code, not yet run).
- *Knots through the store.* `(set r (lambda (n) ((get r) n)))` loops
  with no recursive binding, and least-fixpoint effect inference does not
  see `spin` in it. So a `subr` type inside a `ref`, `icell` or `array`
  must be read as "may spin"; so must one that occurs negatively in a
  `dletrec` cycle (self-application).
- *Declared types.* The 380 recursive definitions all have written types.
  Rather than make them all mention `spin`, a declared latent effect is
  read as "may spin" unless it is marked total.

**Tasks.**
1. **R1 (S). Fuel for a run of a word.** *Done in this pass*: see above.
2. **R2 (S). Fuel when a continuation is resumed**, in the native
   machines' `control` call-outs and the call of a non-closure. First
   step: `(k k)` stops at the limit rather than hanging (test under the
   timeout wrapper).
3. **R3 (S). No fuel check on a forward branch in compiled stack code**
   (`fixpt-native/src/threaded.rs`, `branch` and `0branch`), as register
   code already does (`to <= i`). Test: a loop still runs out of fuel.
4. **R4 (S). Count word entries by class**, next to the cell counts in the
   engine's `Profile`: of the entries in the self-compile and the
   benchmarks, what share are words the call-graph rule says need no poll.
   This decides R5.
5. **R5 (M). The poll analysis in both compilers**: a word in no cycle of
   known calls (self tail loops aside) and making no unknown call omits
   its entry poll. `threaded.rs` and `compile.fx`, and register code from
   both, cell for cell. First step: the count, against 571 of 826.
6. **R6 (M). A `spin` atom in both checkers**, with the knot rules above,
   declared types "may spin" unless total, and the licence reporting it.
7. **R7 (S). Speculation without a budget for spin-free forms.** After R6.
8. **R8 (M, optional). Stack-depth checks hoisted** out of the 223
   transitively spin-free words into their callers.

## 2. Time complexity as an effect

**The papers.**
- *Dornic, Jouvelot and Gifford* (`loplas.pdf`). Latent times ride on
  `subr` types: integers, `long`, time variables, and sums. `plambda`
  abstracts over times. Recursion, written with `drec` types, gives
  `m = m + m′`, whose only solution is `long`. `if` is a sum (`max` is
  future work). Times are checked, not inferred.
- *Reistad and Gifford* (`lfp94.pdf`). Costs are symbolic constants
  measured per target, with `sum`, `max`, `prod N C` and `long`. Data
  types carry sizes (`(listof T N)`, `(numof N)`). Dependent costs come
  only from data-parallel primitives (`map`, `reduce`); user recursion is
  `long`. Costs are inferred by algebraic reconstruction and a
  least-fixpoint solver that gives up to `long`.

**For FX-26.**
- Time is a *component*, not an atom: effects join by union, but time
  needs `+` over `begin` and `max` over `if`. So `(subr F T (P…) R)`,
  where an omitted `T` means `long`, so that every written signature still
  means "unknown", soundly.
- The lattice: `long`, or a constant plus a multiset of time variables,
  with `max` coarsened away (sound, since times are non-negative).
- The unit is one fuel tick (a word entry or a taken branch), what the
  machines count.
- Time is never masked: private work still takes time.
- The same knots as `spin` (store, I-cells, `dletrec`, continuations) are
  forced to `long`, and for the same reason every `subr` type must carry a
  time, default `long`.

**Its relation to responsiveness.** A bounded time implies no unbounded
path; `long` is where a poll may be needed. But dropping a word's entry
poll needs only the yes-or-no fact, which is R5's. The numbers earn their
keep elsewhere:
- declared bounds, checked like effects;
- charging a whole bound once at entry, keeping fuel counts meaningful;
- budgets: the REPL's speculation limit counts VM steps, and a primitive
  is one step, so a licensed `(make-array 1000000000 0)` or a long
  `string-append` costs nearly nothing of the 200,000-step budget (read in
  the code, not tried). lfp94's size-dependent primitive costs are what
  would catch it.

**Tasks.**
1. **T1 (S). A cost-class report, language unchanged**: a pass after the
   checker that labels each definition `const c`, `param` (bounded given
   its arguments' latent times), or `long` with the reason. First result:
   the share of non-`long` definitions in the front end and the tests.
2. **T2 (S). Size-dependent speculation**: the licence refuses to run early
   a primitive whose count or length argument is a large literal, or not
   a literal. First step: `(make-array 1000000000 0)` is no longer run as
   it is typed.
3. **T3 (L). Time on `subr` types, in both checkers**: `ast.rs`, parsing
   and printing, `check.rs`, `infer.rs`, `standard.rs` (a constant for
   every entry), and `check.fx`. First step: every test passes with every
   written signature `long`. Tests: declared bounds that pass and fail,
   and each knot forced to `long`.
4. **T4 (M). Infer latent times** of definitions written without one,
   with lfp94's solver, top level only.
5. **T5 (M). A `bounded` fact to the compilers**: a word of constant time
   charges it once at entry instead of polling at each branch. After R4
   says it matters.
6. **T6 (M). Continuations and `await`**: a prompt whose body never
   invokes its capture stays bounded; `await`'s time under processes.

## 3. Concurrency, and processes as distinct from functions

**What FX had.** Lucassen's thesis, chapter 6 ("Explicit Concurrency"):
`cobegin`, whose branches may not write a region another branch reads or
writes, manifestly or through effect variables; monitors for critical
sections, with an `mcall` effect. No fairness is promised, which permits
a non-preemptive implementation on one processor: green threads. Chapter
8 compiles to dataflow graphs by the effects' interference. Futures are
rejected (§9.1.2): a future has its value's type, so its latent effect
cannot be tracked. FX-26's I-cells are the answer that has a type of its
own: `(icell T R)` and `(await R)`. FX-91's report states the goal of
scheduling for parallel execution from effects; `popl91.pdf` §1 lists
`init` among store effects and communication effects on channels.

**Three layers.**
- *Deterministic parallelism by effects.* `(par e1 … en)`, whose
  branches must not interfere. `icell-put!` gets FX's `init` effect,
  apart from `write`: init against await is dataflow synchronization,
  deterministic (Arvind's argument, from memory). Interference, per
  region:

| a \ b     | read | write | init | await | alloc |
| --------- | ---- | ----- | ---- | ----- | ----- |
| **read**  | ok   | X     | ok   | ok    | ok    |
| **write** | X    | X     | X    | X     | ok    |
| **init**  | ok   | X     | ok   | ok    | ok    |
| **await** | ok   | X     | ok   | ok    | ok    |

  An effect variable conflicts with every write, as in Lucassen. A get of
  an empty cell suspends; nothing runnable with something suspended is a
  deadlock, reported as an error.
- *Processes.* `(proc F (T…) S R)`: typed by the protocol `S` it speaks
  on one channel in region `R`, not by a result. `spawn` returns the dual
  endpoint. A `with-processes` form joins every process spawned in it, so
  no process outlives its extent, and `letrena`/`letreap` masking stays
  sound.
- *Session types* (from memory, none local): `end`, `(! T S)`, `(? T S)`,
  `choose`, `offer`, and `rec` only by name in `define-protocol`.
  `send`, `recv`, `select`, `branch`, `close` in state-passing style, with
  one communication effect `(comm R)`. FX-26 has no linear types, so
  linearity is approximated: first dynamically (a stale endpoint traps,
  as a second `icell-put!` does), then syntactically (a channel used at
  most once on each path, never captured or stored, only sent). With
  channels only parent to child, the topology is a tree, which is
  deadlock-free, and masking `(comm R)` at `with-processes` makes a
  function that talks only to its own children `pure`.

**The runtime.** Green threads first: a thread is a composable
continuation up to the scheduler's prompt, and a switch is a capture,
an abort and a resume. By "What a capture costs" (docs/performance.md) a
round is about 0.56 µs at depth 20: fine for coarse parallelism, poor
for fine-grained dataflow on deep stacks, which is the workload that
would justify the stack cache deferred in queue item 7. OS threads need a
stop-the-world collector over one heap, or one heap per thread with
messages copied between them, the second fitting session types better.

**Tasks.**
1. **P1 (S). Green threads in FX-26 itself**, no language change:
   `spawn`, `yield` and `run` over the existing delimited control, a run
   queue in a `ref`. First step: two threads interleave
   deterministically, on every machine.
2. **P2 (S). Suspending I-vars in FX-26**, from a `ref` of a sum: `get`
   parks, `put` wakes, a deadlock is an error rather than a hang.
3. **P3 (S). The cost of a switch**: `bench/threads.fx`, at stack depths
   1, 20 and 200, beside "What a capture costs".
4. **P4 (S–M). The `init` effect** for `icell-put!`, in both checkers.
5. **P5 (S). The interference relation**, table-driven, with unit tests
   for every cell.
6. **P6 (M). I-cells that suspend** in the runtime when a scheduler is
   present, and trap as now when none is.
7. **P7 (M). `par`**: parsed, checked for non-interference, lowered onto
   the scheduler. Test: a shuffling scheduler gives the same answer under
   100 seeds.
8. **P8 (M). `par-map` with a bounded effect** (Lucassen §9.2.3). First
   check whether FX-26 can bound an effect variable; if not, that is a
   type-system extension of its own.
9. **P9 (M). Processes with plain typed channels** and `with-processes`.
10. **P10 (L). Session types**, with dynamic one-shot endpoints.
11. **P11 (M). Affine channels checked statically, and `comm` masked.**
12. **P12 (L). OS threads: a design note**, starting from an inventory of
    the runtime's shared mutable state (symbols, globals, code patched in
    place).

## 4. Closures that carry their types

**What we have.**
- A word records no arity, frame size or type; `slot i`, `free i` and
  `call n` are trusted.
- `make_threaded_word` and `regcode::check` check a new word's structure,
  as the JVM's verifier checks its first pass. An image's words skip even
  that (above).
- The typed routines (`int-add`, `pair-car`, `field k`, `tcall`) trust
  the checker, and the native machines run them with no tests: a word
  made wrongly, or by hand, can break memory safety, not only raise an
  error.
- The eager reader's licence (`licence.rs`) is trust by type, but only of
  source this checker checked itself.
- Images hold no machine code: the receiving runtime makes it from cells.
- `dump-heap` and `run-image` take Scheme programs, not FX-26 ones run
  threaded.

**What "carry the type" can mean,** from weaker to stronger:
- *(a) A type, trusted.* Each word keeps its FX-26 type as a datum. Good
  for tools and for checking the two compilers agree; a guard against
  accidents only.
- *(b) A type and a certificate a small verifier checks: typed threaded
  code.* The verifier's state at a cell is the frame and data stack as
  types, the free values' types, and the effect so far; each routine gets
  a stack rule (`int-add : (int int -- int)`, `pair-car : ((pairof a b r)
  -- a) ! (read r)`). The certificate is only the signature and a full
  state at each branch target and loop head, as the JVM's stack maps are
  (from memory). The verifier then masks with the word's free and result
  types, confirming the latent effect: the licence's question, asked of
  cells rather than source. This moves the trusted base from the compilers
  and the checker to the verifier and the routines' rules. Some lowerings
  are idioms of several routines (`lit` and `prim %make-frozen` for a
  product; `int-less; lit #f; eq` for `>=`), which the verifier would
  either recognize or replace with typed routines.
- *(c) The same for register code or machine code.* Register code is
  typed assembly proper, with the rule that after anything that may
  collect only `RESULT` is live. Machine code is not needed at all, since
  images never carry it: rebuild twins and machine code from verified
  cells.

**The loader's checks, for a fragment:** structure; the identity of the
routine and primitive tables (a fingerprint, since cells hold their
numbers); imports by name, each host type a subtype of the one assumed;
primitives, each with a typed rule; each word against its certificate;
exported closures' free values against their types; the fragment's
regions renamed fresh, as `private-regions` does; and last the licence on
each export's confirmed type. The reader licence is that last step run on
types the host's own checker made; with certificates it runs on types
the host's verifier confirmed.

**Where it lives:** a new field in a word, `WORD_TYPE`. The trailer is the
runtime's; a side table is a fine first prototype. A field shifts
`WORD_CELL0`, used through its constant in some 15 files including the
`.fx` layouts and the stencils, and changes the image version.

**Tasks.**
1. **C1 (S). Each lambda's type recorded and shown** by `,disassemble`,
   in a side table; first measure how big the types are against the
   words' cells.
2. **C2 (M). `WORD_TYPE` as a field**, on every machine.
3. **C3 (S). The structural check on loading an image**: one
   `check_word`, factored from `make_threaded_word` and `regcode::check`,
   run on every word an image brings. First step: a corrupted image (a
   branch into an operand) is refused by `fixpt image verify`.
4. **C4 (S–M). Typed rules for the routines** the compilers emit, with a
   coverage test over the test programs.
5. **C5 (M). A verifier for words with no branches**, with agreement
   tests (every such word verifies) and mutation tests (a `pair-car` made
   an `int-add` is refused).
6. **C6 (M). Stack maps at branch targets**, recorded by the compiler,
   which already tracks the depth.
7. **C7 (M). Typed routines for the idioms** (`product n`, `sum`, `unit`),
   in both compilers and every machine.
8. **C8 (L). Control and regions in the verifier**, until the eager reader
   verifies whole.
9. **C9 (M). FX-26 programs run threaded, as images.**
10. **C10 (L). Fragments, and a loader that links them** with the checks
    above.
11. **C11 (S). The licence on verified types**: the eager reader, dumped
    as a fragment by one process, licensed and run by another.
12. **C12 (L, later). Verifying register code**, only if shipping twins
    turns out to be worth it.

## What to do first

The small, informative first steps, across the four:
- **R2**, **R3** and **C3**: fixes of what the exploration found, each
  small, and none needing a type-system change;
- **R4** and **T1**: measurements that decide whether R5, T3 and T5 are
  worth their size;
- **P1** to **P3**: concurrency in FX-26 itself, on the delimited control
  it already has, before any language change;
- **C1**: how big carrying types would be.

The type-system extensions proper (R6, T3, P4 onward, C5 onward) are for
the user to choose among: the decision so far is to optimize from what the
existing types already prove, and to discuss extensions after.
