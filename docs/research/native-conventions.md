# Native code without the interpreter's shape

Design note, 2026-09-27, with the user. For review before any code. It
replaces steps 4b and 4c of "A collected code area" (`PLAN.md`), and it
subsumes several of M13's remaining items.

## Where we are, and why change it

FX-26 compiles each `lambda` to a threaded word: cells, run by an inner
interpreter. Five machines run them (`--threaded-machine`): `rust`,
`native` and `stencils` interpret the cells, and `native-compiled` and
`registers` compile them to machine code. The compiled forms keep the
interpreter's shape, which came from the Forth models M12 and M13 took
(`docs/research/threaded-compilers.md`):

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

- **A kind, `conv`**, whose descriptions are the conventions: `threaded`
  (the procedure is a threaded closure, run by an inner interpreter),
  `native` (it is native code, run by being called), and `any` (either;
  the caller finds out which when it calls, below). A foreign `c`
  convention could come later, for calling out.
- **In every subroutine type.** `(subr (conv C) e (t …) u)`: the
  convention position is optional, and `(subr e (t …) u)` means a
  convention inferred. Composable continuations and the continuations
  `cwcc` gives carry one too.
- **Inferred, and defaulted.** A convention binder nothing solves defaults
  to the program's, which is the machine the program is compiled for: a
  checker setting, `threaded` for `rust`, `native`, `native-compiled` and
  `stencils`, and `native` for the new native compiler. A type prints
  its convention only where it differs from the program's, so programs,
  tests and both checkers' outputs are unchanged by default.
- **Polymorphism.** `(poly ((c conv)) (subr (conv c) …))`, as effects are
  bound. Higher-order code (`map`, the evaluator written in FX-26) is
  polymorphic in the conventions of the procedures it is given, and the
  native compiler makes one copy per convention it is used at (few: most
  programs use one). The standard operations are polymorphic too: the
  runtime provides each in every convention.
- **`any`: code that need not know** (the user's, 2026-09-27). A
  procedure value already says at run time how it is run: a threaded
  closure and a native closure are bloblets of different kinds. So a call
  through `(subr (conv any) …)` looks at the callee's kind and enters the
  interpreter or calls the code: a test and a branch per call, and no
  adapter anywhere. Hence the only subsumption between conventions:
  `threaded ≤ any` and `native ≤ any`, free at run time, since the value
  does not change, only what its callers may assume. Code that does not
  care (cold code, the evaluator written in FX-26, a table of handlers of
  either kind) takes `any` and stays ignorant of what it receives; code
  that cares names a convention and calls directly. `threaded` and
  `native` are not related to each other, and nothing goes from `any` back
  to a specific convention but a conversion.
- **Conventions compare** as equal, or by the subsumption into `any`, in
  both checkers' `sub`. A mismatch is an error that says so, and names the
  conversion.
- **Conversion is explicit.** `(convention C e)`: `e`'s procedure, called
  in convention `C`. From a specific convention to the other, it makes an
  adapter, a small procedure in `C` that calls the original in its own;
  from `any` to a specific one, it checks the value's kind, and adapts it
  only if it is of the other. Where adapters go is then visible in the
  source. Whether the checker should insert them itself in checking mode,
  where the expected type says the convention, is an open question below;
  `any` makes it less pressing, since code that would need many
  conversions can take `any` instead.
- **Soundness.** An application's rule requires the callee's convention to
  be the one the call is compiled for; calling native code through the
  threaded convention, or the reverse, would be a crash, so this is type
  safety, not style. A call through `any` is safe because it dispatches on
  the value's kind, which the runtime keeps truthful. `docs/research/soundness.md`'s
  core gains the convention as part of the arrow type, with the
  subsumption into `any` and the adapter's rule. The Rust host calling
  into FX-26 (`%run-word`) is a call through `any`: it already checks the
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
arguments. The cost: machines no longer run out of fuel at identical
points, only at points a bounded distance apart. Tests compare that a run
ran out, not exactly where. This is an open question below.

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
| threaded words and cells                      | kept: the portable form, and the reference                                                                                       |
| `rust`, `native`, `stencils` machines         | kept, convention `threaded`                                                                                                      |
| `native-compiled` (cell for cell)             | retired once the native compiler covers it                                                                                       |
| register code (`regcode.rs`, `regcode.fx`)    | its intermediate form and register allocation the start of the native compiler; its twins, adapters and marked return entries go |
| native slots, per-word resume tables          | gone for native code                                                                                                             |
| the two stacks and return entries             | kept by the interpreters only                                                                                                    |
| `CodeSpace`                                   | holds only the interpreters' routines; compiled functions go in the code area                                                    |
| code-area step 4a (commons through the state) | kept: the native compiler's traps and exits go that way too                                                                      |
| code-area steps 4b and 4c                     | dropped, and replaced by the steps below                                                                                         |
| the bootstrap's fixpoint                      | unchanged: it compares threaded words; native code is compared by running it                                                     |

## Steps, each committed and tested

1. **Conventions in types**, in both checkers: the kind, the optional
   position in `subr`, `any` and the subsumption into it, inference and
   defaulting, printing only when not the default, `(convention C e)`, the
   soundness note's rule. No change in behaviour: every program is
   `threaded` by default, and calls through `any` dispatch on the kind the
   interpreters already check.
2. **Native frames, first-order**: the stack segment, the calling
   convention, traps and callouts, and a native compiler for code without
   closures or continuations (from register code's intermediate form),
   tested against the Rust machine on the programs that fit.
3. **The collector and native frames**: stack maps, the walk, code found
   and kept alive by return address, the code area's address index; under
   `gc-stress`. The code area's generate-run-drop test
   (`crates/fixpt-native/tests/code_gc.rs`) passes here.
4. **Closures and higher-order code**: native closures, polymorphism in
   conventions and a copy per convention, adapters.
5. **Continuations, prompts and marks** on native frames; regions across
   throws.
6. **Checks where work is unbounded**: fuel and stack limits as above,
   leaves checking nothing; benchmarks against `registers`; retire
   `native-compiled` and register code's twins.
7. **The closure experiment**: closures of chosen `lambda`s as code
   bloblets reading captured values PC-relatively.

## Open questions, for the user

1. **Conversions: explicit only, or inserted by the checker** where the
   expected type gives the convention? Explicit is Rust's choice, and
   keeps every adapter visible; inserted is more convenient where
   conventions meet often, as at the REPL.
2. **Fuel across machines**: is "runs out within a bounded distance" the
   right promise, rather than "at the same cell"? The alternative, a
   leaf's fixed cost charged at its known call sites, keeps counts
   identical, but only where the callee is known.
3. **The evaluator written in FX-26**: stays `threaded`, run by the
   interpreters, and calls native code only through conversions?
4. **A `c` convention** for calling Rust and C directly, later, or never?
