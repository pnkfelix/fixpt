# Forth, cellular-code[^cellular] VMs and GHC: what applies to FX-26's machine

A survey made on 2026-09-26 for the FX-26 optimizing compiler (PLAN.md,
"After M12"). A research agent wrote it without network access, so it
rests mostly on the model's knowledge of the literature. Paper titles and
venues are as remembered, and numbers marked ≈ are approximate. Check
anything before citing it.

Nothing on disk covers this ground:

- no Forth system is installed;
- `~/Dev/LangPlay/GiffordHistory/papers` holds only FX papers.

Our own measurements are in `docs/performance.md`.

## 1. Forth techniques

### Threading, and why dispatch is cheap now

- **Indirect threading:** two dependent loads and a jump.
- **Direct threading:** one load and a jump.
- **Token threading** (ours): a load, a table load and a jump.
- **Subroutine threading:** native calls.
- **Call threading:** a call and return per primitive, the slowest.

The old folklore held that interpreters are ruled by mispredicted indirect
branches (Ertl & Gregg, JILP 2003 and PLDI 2003). It no longer holds.
Rohou, Swamy & Seznec (CGO 2015, "don't trust folklore") showed that
predictors of the TAGE and ITTAGE kind predict even one shared dispatch
jump well, and Apple's cores are no different. Our C11a result is this
effect. What matters now is instructions per cell and the dependences
through memory: the stack pointer and the stack's contents.

### Stack caching

Ertl, "Stack caching for interpreters" (PLDI 1995).

- **Top of stack in a register** removes about one load and one store per
  primitive. Most Forths do it.
- **Dynamic stack caching** keeps a copy of each routine for each cache
  state.
- **Static stack caching** has the compiler pick the right variant at
  each cell. Gforth does this; so do Ertl & Gregg's papers around
  2004-05.
- Reported gains ≈ 10-30% in interpreters.

### Superinstructions and peepholes

- **Static superinstructions**, chosen by profiling, as vmgen generates
  them (SP&E 2002).
- **Dynamic superinstructions**, which copy routines end to end. These are
  Piumarta & Riccardi's selective inlining (PLDI 1998) and Gforth's
  replication, and they are our C11a. Their old ≈ 2× came mostly from
  better prediction.
- **Context threading** (Berndl et al., CGO 2005) is also mostly about
  prediction. It supports one idea we want, though: virtual branches and
  calls should become native ones.
- **Forth peepholes:** `lit x +` becomes an immediate add, `0= 0branch`
  a branch on nonzero, and `swap drop` becomes `nip`.

### Native Forth compilers

- **cmForth and colorForth** thread by subroutine, inline small
  primitives, and turn a final call into a jump. Loops are written as
  tail recursion.
- **SwiftForth** threads by subroutine, with inline primitives, a peephole
  pass, and the top of stack in a register.
- **VFX Forth** keeps a compile-time model of the stack in each basic
  block: each item is in a register, in memory, or a known constant. It
  emits code only when a value must exist, and settles the model at block
  ends and calls. It also inlines small words and turns tail calls into
  jumps. Reported ≈ several times cellular code.
- **iForth and bigForth** do much the same.
- **RAFTS** (Ertl) planned data-flow graphs per block with ordinary
  register allocation.
- **Factor** is a concatenative language with a typed-ish optimizing
  compiler. It propagates types to remove checks, unboxes, does escape
  analysis and value numbering, and allocates registers by linear scan.
- **StrongForth** is a statically typed Forth whose checker picks
  primitives.

The common pattern is an abstract interpretation of the stack over each
basic block. Each item is `reg`, `mem`, `const` or `slot i`, and code is
emitted only when something opaque consumes the value. The model is
flushed at calls, merges, and anything that looks at the stack
(collection, continuation capture).

## 2. Other VM lore

- **OCaml bytecode (ZINC, Leroy 1990)** has an accumulator register,
  fused ops (`PUSHACC n`, `BRANCHIFNOT`, `APPTERM`), and `GRAB`/`RESTART`
  for application. A top-of-stack register plus fused slot and constant
  ops gets most of the win cheaply.
- **Stack against register VMs** (Shi, Gregg, Beatty & Ertl, VEE 2005):
  register form ran ≈ 47% fewer VM instructions and took ≈ 30% less time.
  Most of the instructions removed were loads of locals, our
  `slot i`.
- **Quickening and inline caches** matter little for a statically typed
  language: the compiler specializes ahead of time.
- **Copy-and-patch** (Xu & Kjolstad, OOPSLA 2021; CPython 3.13) pays with
  stencil variants per operand kind, and holes for constants.

## 3. GHC, where it transfers

- **Eval/apply** (Marlow & Peyton Jones, "Making a fast curry"): known
  saturated calls go direct, and unknown ones go through apply routines.
  FX-26's arities are static, so *every* call can skip arity checks, and
  known calls can skip closure checks too.
- **Known, unknown and self-recursive tail calls:** a self tail call jumps
  to a local label. It is a loop.
- **Pointer tagging** (ICFP 2007): a constructor's tag in the pointer's
  low bits saves a load in case analysis.
- **Join points** (Maurer et al., PLDI 2017): a local function used only
  in saturated tail calls becomes a label, with no closure. It must be
  kept through optimization, not rediscovered after.
- **Worker/wrapper**: a worker takes raw values, and a wrapper unboxes
  for it.
- **Core-to-Core**: every pass keeps the program well-typed Core, and Core
  Lint checks it. For us: re-run the FX-26 checker on each pass's output.

## 4. Recommendations for our machine, ranked

Our data says dispatch costs ≈ 0.5 ns per cell and is predicted. What
costs is:

- data stack traffic;
- stack pointer updates;
- tag and overflow checks inside routines;
- fuel and stack-limit checks at each entry;
- the call protocol.

| rank | optimization                      | level                | static information             | payoff               |
| ---- | --------------------------------- | -------------------- | ------------------------------ | -------------------- |
| 1    | the stack in registers, per block | machine code         | each routine's stack effect    | high                 |
| 2    | typed primitives, fewer checks    | source, then cells   | types, refinement after tests  | high                 |
| 3    | self tail calls become loops      | source, then cells   | the binding is never assigned  | high, for loops      |
| 4    | known calls, direct               | source, cells, code  | arity from types, no writes    | medium to high       |
| 5    | frame slots in registers          | machine code         | control and allocation effects | medium to high       |
| 6    | join points                       | source               | escape analysis                | medium               |
| 7    | inlining and simplification       | source               | effects for safety, types      | medium, enabling     |
| 8    | superinstructions and peepholes   | cells                | typed variants                 | medium, interpreters |
| 9    | limit and fuel checks hoisted     | machine code         | stack effects, control flow    | small to medium      |
| 10   | unboxed floats                    | source, machine code | types                          | niche                |

In more detail:

- **1** turns C11a's "inline in order" into a compiler. `lit` and `slot`
  emit nothing, and `fx+` over two known items emits one `add`. The model
  is flushed at calls, call-outs and control. The ip is made only where
  something reads it.
- **2** is a source pass after checking. It rewrites `+` at `int` to an
  unchecked primitive, and `car` to an unchecked one where the pair is
  proven. The output is still FX-26.
- **3** marks a tail call to the enclosing lambda, and emits `slot!` then
  a branch back instead of `tailcall`.
- **4** adds `callk w n`: the word inline, no closure fetch, no check. In
  machine code it is a `bl`.
- **5** is where FX-26's effects give an edge no Forth or Scheme compiler
  has. A call that cannot capture a continuation or collect needs no
  spill of the slots around it.
- **7** re-runs the checker after each pass.
- **8** fuses sequences such as:
  - `slot i; slot j; <; 0branch L` into `br-slot<`;
  - `slot i; lit c; +`.

  This matters most to the Rust machine, at ≈ 3 ns per cell.
- **9**: a word's greatest stack growth is known statically, so one check
  at entry will do, with fuel checked on back edges only.

**What to build first.** 3 and 2 are cheap and help every engine. 1 is the
real compiler. 5 is where the effect system pays off.

[^cellular]: "Cellular" would be called "threaded" in the Forth community: code as
a sequence of cells (references to routines, and their operands), run by an inner
interpreter. This repository says "cellular" throughout (the user's decision,
2026-09-27).
