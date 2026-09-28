# Native code without the interpreter's shape

Design note, 2026-09-27, with the user. For review before any code. It
replaces steps 4b and 4c of "A collected code area" (`PLAN.md`), and it
subsumes several of M13's remaining items.

## Where we are, and why change it

FX-26 compiles each `lambda` to a cellular[^cellular] word: cells, run by an inner
interpreter. Five machines run them (`--cellular-machine`): `rust`,
`native` and `stencils` interpret the cells, and `native-compiled` and
`registers` compile them to machine code. The compiled forms keep the
interpreter's shape, which came from the Forth models M12 and M13 took
(`docs/research/cellular-compilers.md`):

- **The ip in step.** At every cell boundary, compiled code leaves the
  machine exactly as the interpreter would: the ip register current, and
  operands on the data stack in memory. That lets anything happen at any
  cell boundary: a return into an interpreted caller, a callout, a trap, a
  capture.
- **Positions, not addresses.** A call pushes a return entry `(word, 8k,
  fp, closure)` on a second stack: "resume word `word` at cell `k`". A
  return must turn that position into a machine address through a
  per-word *resume table*: three dependent loads and an indirect branch,
  falling back to interpreting if the word has no machine code.
- **`docol` on every entry.** A fuel check, a data-stack and a return-stack
  check, and a pushed return entry: 19 instructions.
- **A cell compiles to its routine's whole body**, checks included.

Measured with `,disassemble-asm`: `(lambda ((x int)) x)` is 95
instructions under `native-compiled`, about 60 of them run. The shape was
worth it while bootstrapping, since every machine could be checked
against every other at every cell. It is not worth it for native code.
Two conclusions, agreed with the user:

1. **Nothing needs compiled code to be indistinguishable from the
   interpreter everywhere.** Each thing that seemed to need it can be
   served on its slow path, from metadata the compiler writes: a trap's
   position, the collector's view of frames, a continuation's capture, a
   callout's resumable state.
2. **Nothing needs a caller to be ignorant of how its callee is run.**
   FX-26 checks every expression. How a procedure is called is a fact the
   checker can know and state, as it states effects: part of the
   procedure's type, as Rust's `extern "C" fn` and `extern "Rust" fn`
   differ. Crossing from one convention to the other is then explicit, and
   costs something only where it is written.

Cells stay: they are the portable form (heap images, the interpreters,
the compiler written in FX-26, the bootstrap's fixpoint), and the
reference native code is tested against.

## Conventions in types

- **A kind, `conv`**, whose descriptions are the conventions: `cellular`
  (the procedure is a cellular closure, run by an inner interpreter),
  `native` (it is native code, run by being called), and `fx` (either of
  FX-26's own; the caller finds out which when it calls, below). A foreign
  `c` convention may come later, for calling out; it is not below `fx`,
  since `fx` dispatches cheaply only between FX-26's own conventions, whose
  values say at run time which they are, and nothing says so of another
  language's procedures (the user's, 2026-09-27).
- **Never written unless wanted** (the user's, 2026-09-27: code is still
  written at the REPL). Every convention can be left out, everywhere, and
  is inferred; a program need never mention one.
- **In every subroutine type.** `(subr (conv C) e (t …) u)`: the
  convention position is optional, and `(subr e (t …) u)` means a
  convention inferred. Composable continuations and the continuations
  `cwcc` gives carry one too.
- **Inferred, and defaulted.** A convention binder nothing solves defaults
  to the program's, which is the machine the program is compiled for: a
  checker setting, `cellular` for `rust`, `native`, `native-compiled` and
  `stencils`, and `native` for the new native compiler. A type prints
  its convention only where it differs from the program's, so programs,
  tests and both checkers' outputs are unchanged by default.
- **Polymorphism.** `(poly ((c conv)) (subr (conv c) …))`, as effects are
  bound. Higher-order code (`map`, the evaluator written in FX-26) is
  polymorphic in the conventions of the procedures it is given, and the
  native compiler makes one copy per convention it is used at (few: most
  programs use one). The standard operations are polymorphic too: the
  runtime provides each in every convention.
- **`fx`: code that need not know** (the user's, 2026-09-27). A
  procedure value already says at run time how it is run: a cellular
  closure and a native closure are bloblets of different kinds. So a call
  through `(subr (conv fx) …)` looks at the callee's kind and enters the
  interpreter or calls the code: a test and a branch per call, and no
  adapter anywhere. Hence the only subsumption between conventions:
  `cellular ≤ fx` and `native ≤ fx`, free at run time, since the value
  does not change, only what its callers may assume. Code that does not
  care (cold code, the evaluator written in FX-26, a table of handlers of
  either kind) takes `fx` and stays ignorant of what it receives; code
  that cares names a convention and calls directly. `cellular` and
  `native` are not related to each other, and nothing goes from `fx` back
  to a specific convention but a conversion.
- **Conventions compare** as equal, or by the subsumption into `fx`, in
  both checkers' `sub`. A mismatch is an error that says so, and names the
  conversion.
- **Conversions are inserted by the checker** (the user's, 2026-09-27).
  Where a procedure of one convention is given where another is expected
  (an argument, a binding, a result checked against a signature), the
  checker elaborates a conversion there: from a specific convention to
  the other, an adapter, a small procedure in the expected convention that
  calls the original in its own; from `fx` to a specific one, a check of
  the value's kind, adapting it only if it is of the other. Into `fx`
  nothing is needed. `(convention C e)` writes one explicitly, where the
  checker could not tell, or to make it visible. The lowering and
  `,code` show where conversions went, so their cost can be found.
- **Soundness.** An application's rule requires the callee's convention to
  be the one the call is compiled for; calling native code through the
  cellular convention, or the reverse, would be a crash, so this is type
  safety, not style. A call through `fx` is safe because it dispatches on
  the value's kind, which the runtime keeps truthful. `docs/research/soundness.md`'s
  core gains the convention as part of the arrow type, with the
  subsumption into `fx` and the adapter's rule. The Rust host calling
  into FX-26 (`%run-word`) is a call through `fx`: it already checks the
  closure's kind at run time.

Where conventions actually meet, in one run: the evaluator written in
FX-26 calling compiled code; the REPL, where forms meet earlier
definitions; code generated and run at run time. Those are the places
where a visible boundary is worth having.

## Native code, run natively

**Frames.** One stack of native frames per thread, in a segment of its
own (not the Rust thread's stack), so that the machine controls its
limit and can copy it for continuations. The arm64 procedure call
standard, adapted:

| what                 | where                                                                     |
| -------------------- | ------------------------------------------------------------------------- |
| arguments            | `x0`–`x7`, then the frame                                                 |
| result               | `x0`                                                                      |
| the closure called   | a register of its own, as `clo` today                                     |
| return address       | `x30`, saved in the frame by a function that calls                        |
| frame link           | `x29`                                                                     |
| pinned               | the heap's base, the machine's state, the fuel: callee-saved, as today    |
| values across a call | in the frame's slots: every Value live across a safepoint is in the frame |

A call is `blr`; a return is `ret`. There is no ip, no data stack for
operands, no return entry and no resume table.

**Safepoints and stack maps.** The collector may run only at a
safepoint: a call, an allocation that calls in, a loop's back edge where
fuel is checked. At each, the compiler writes a *stack map*: which of the
frame's slots hold Values. Registers hold no Value across a safepoint, so
the maps are all the collector needs. It walks the frames by their links,
finds each frame's code by its return address, and scans and updates the
slots that the code's map for that return address names. Nothing in a
frame is a word, a cell index or a return entry.

**Metadata lives in the code bloblet.** A function's code is a bloblet in
the heap's collected code area (`docs/object-model.md`, "A collected code
area"). Its fields hold what the code refers to (constants, and, for the
closure experiment, captured values read PC-relatively). Its suffix
holds the instructions, then the metadata, as raw words:
- the stack map at each safepoint's return address;
- each safepoint's source position, a span in the program's text, for
  traps and errors;
- the frame's size and layout.

**Finding code from a return address.** The code area never moves, so a
return address lies inside exactly one code bloblet. The area keeps an
index of its bloblets by address, updated as it allocates and sweeps, and
the collector looks each frame's return address up in it. That is also
what keeps code alive: a code bloblet some frame is running in is marked
by the walk, as a field that refers to it would mark it.

**Traps and callouts.** A trap (a type error, overflow, out of fuel)
enters the machine's common trap with the faulting address. It is
reported by looking the address up in the metadata, as an error at a
source position. A callout to Rust (a primitive, an allocation that
calls in) is a call like any other, at a safepoint; the Rust side walks
native frames with the same maps.

**Fuel and stack limits, where work is unbounded.** Fuel is checked on
loop back edges and on entry to a function that calls. A leaf with no
loop does bounded work and checks nothing: its caller or loop will. The
stack limit is checked once on entry, for the frame and its calls'
arguments. Machines no longer run out of fuel at identical points, only
at points a bounded distance apart, which the user accepts (2026-09-27);
tests compare that a run ran out, not exactly where. Whether even the
bound is needed, rather than a finite distance not known in advance, the
user may revisit.

**Continuations.** A whole continuation is the native stack from its base
to the current frame, copied into a heap object, with the frames' return
addresses and the stack maps that describe them. The collector traces a
copied stack by those maps, as it traces the live one. Reinstating copies
it back; frame links are stored as offsets within the stack, so a copy
placed elsewhere needs no fixing up. A composable continuation is the
segment up to its prompt's frame, composed by copying it onto the current
stack. Prompts and marks are frames of known kinds, found by the walk.
The live-regions count a continuation keeps (F7,
`docs/research/soundness-findings.md`) carries over unchanged.

**Closures.** A native closure is a bloblet: its code bloblet, then its
captured values; the code reads them from the closure register, as
today. The step-5 experiment, a closure *of a chosen `lambda`* whose
code is copied and whose captured values are fields read PC-relatively,
is a code bloblet whose fields are the captured values: a closure and
its code in one.

## What happens to what exists

| piece                                         | becomes                                                                                                                          |
| --------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------- |
| cellular words and cells                      | kept: the portable form, and the reference                                                                                       |
| `rust`, `native`, `stencils` machines         | kept, convention `cellular`                                                                                                      |
| `native-compiled` (cell for cell)             | retired once the native compiler covers it                                                                                       |
| register code (`regcode.rs`, `regcode.fx`)    | its intermediate form and register allocation the start of the native compiler; its twins, adapters and marked return entries go |
| native slots, per-word resume tables          | gone for native code                                                                                                             |
| the two stacks and return entries             | kept by the interpreters only                                                                                                    |
| `CodeSpace`                                   | holds only the interpreters' routines; compiled functions go in the code area                                                    |
| code-area step 4a (commons through the state) | kept: the native compiler's traps and exits go that way too                                                                      |
| code-area steps 4b and 4c                     | dropped, and replaced by the steps below                                                                                         |
| the bootstrap's fixpoint                      | unchanged: it compares cellular words; native code is compared by running it                                                     |

## Steps, each committed and tested

1. **Conventions in types**, in both checkers (done, 2026-09-28; tests in
   `crates/fixpt-fx26/tests/programs/conventions/`, and the rules in
   `docs/research/soundness.md` §2.4): the kind, the optional
   position in `subr`, `fx` and the subsumption into it, inference and
   defaulting, printing only when not the default, `(convention C e)`, the
   soundness note's rule. No change in behaviour: every program is
   `cellular` by default, and calls through `fx` dispatch on the kind the
   interpreters already check.
2. **Native frames, first-order** (in part, 2026-09-28:
   `crates/fixpt-native/src/direct.rs`, `crates/fixpt-fx26/tests/direct.rs`;
   frames on a stack of its own, `bl`/`ret`, checks only where work is
   unbounded, traps; call-outs to runtime primitives and `cons` (inline
   when there is room), which may collect: the frames are walked by their
   links, every word of each after the link and return address a value,
   so no stack maps are needed yet; globals bound when compiling.
   In the REPL, `--calling-convention native` makes the program's
   convention native in both checkers, and `,native NAME [ARG…]` shows a
   procedure's code in it and calls it; top-level forms stay cellular): the stack segment, the calling
   convention, traps and callouts, and a native compiler for code without
   closures or continuations (from register code's intermediate form),
   tested against the Rust machine on the programs that fit.
3. **The collector and native frames** (in part, 2026-09-28: each compile
   is one code bloblet in the code area, kept alive by what refers to it
   and by the call running it, reclaimed after; frames walked by their
   links, every slot a value, instead of stack maps; the code area's
   generate-run-drop test passes for this code,
   `code_compiled_and_dropped_is_reclaimed`. Still to do: code found by
   return address, for code no call roots): stack maps, the walk, code found
   and kept alive by return address, the code area's address index; under
   `gc-stress`. The code area's generate-run-drop test
   (`crates/fixpt-native/tests/code_gc.rs`) passes here.
4. **Closures and higher-order code** (in large part, 2026-09-28: each
   procedure is a code bloblet of its own, whose fields hold what its code
   reads PC-relatively (itself, the code it calls, heap constants, global
   cells, closures of globals' procedures); a native closure is a new kind,
   `[free…][code][trailer]`, free values where a cellular closure has them,
   so register code's `lexical` and `letrec` patching are unchanged; an
   unknown call loads the code from the closure's field 2 and adds a pinned
   delta to the code area's run address, and traps if it is not code in
   the code area; each frame keeps its own code bloblet, and its closure if
   it reads it, so no return-address index is needed. In the REPL, with
   `--calling-convention native`, every form is compiled so and run:
   an expression as a procedure of no arguments; a definition likewise,
   its value put in the global the compiler written in FX-26 makes for it
   (`compile-new-global`); forms compiled alone, as Larceny's REPL
   compiles them, against the globals' cells. Native code reads a global
   through its cell when it runs, so a later definition is seen; a cell
   holding a cellular closure is bound when compiling. What the native
   compiler declines runs as cellular code, and the two call each other
   (2026-09-28): cellular code calls a native closure through the
   runtime's `call_native`, its stacks rooted meanwhile; native code
   calls what is not native (an unknown call whose code is not in the code
   area) through a call-out that runs it on a cellular machine of its own,
   the native frames rooted meanwhile (`fixpt_engine::cellular::call_value`).
   A whole continuation that another run took, given a value there, is
   thrown past the native code, which is dropped, to the run that took it
   (each continuation records its run, `CONT_RUN`). `field@` is inline,
   `set-car!` and `set-cdr!` call out, and register code sees through
   `proj` to a standard operation applied.
   Still to do: a definition's initializer is checked again as an
   expression, `(the T init)`, which fails where only the definition's own
   context lets it check (a generative type's `up-` and `down-`, a
   recursion proved to end); such definitions run as cellular code. To
   compile the definition as the REPL always does, and then the closure it
   made natively, would avoid that. Also: polymorphism in conventions and a copy per convention;
   adapters between conventions): native closures, polymorphism in
   conventions and a copy per convention, adapters.
5. **Continuations, prompts and marks** on native frames; regions across
   throws.
6. **Checks where work is unbounded**: fuel and stack limits as above,
   leaves checking nothing; benchmarks against `registers`; retire
   `native-compiled` and register code's twins.
7. **The closure experiment**: closures of chosen `lambda`s as code
   bloblets reading captured values PC-relatively.

## Decided with the user (2026-09-27)

1. **Conversions are inserted by the checker**, and conventions are never
   required in the source; `(convention C e)` remains, for when it is
   wanted.
2. **Fuel runs out within a bounded distance** of where it would on
   another machine; perhaps later only within a finite one.
3. **The evaluator written in FX-26 has no special status.** It
   represents the procedures it interprets as its own data (a datatype of
   closures, primitives by name); the one machine procedure it holds is
   a continuation from `cwcc`, of the program's own convention. It is
   compiled as any program is, and is a good test of the native compiler
   because it is large.
4. **The convention for either is `fx`**, and a `c` convention, when it
   comes, is not below it.

[^cellular]: "Cellular" would be called "threaded" in the Forth community: code as
a sequence of cells (references to routines, and their operands), run by an inner
interpreter. This repository says "cellular" throughout (the user's decision,
2026-09-27).
