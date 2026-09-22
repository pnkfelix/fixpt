# fixpt

A Scheme engine written in Rust, with FX-87 and FX-91 front ends on top of it.

FX-87 and FX-91 are MIT PSRG's effect-typed languages from 1987 and 1991. Both
originals were front ends onto Scheme — `erase.lisp` and `code.scm` type-check,
then emit Scheme and hand it to `eval`. `fixpt` keeps that architecture: one
Scheme engine, two front ends that lower onto it. Conformance is checked
against the recovered originals, running under Racket, in
[`GiffordHistory`](https://github.com/pnkfelix/GiffordHistory).

See [`PLAN.md`](PLAN.md) for the design and the milestone list,
[`TODO.md`](TODO.md) for work deliberately deferred, and
[`docs/divergences.md`](docs/divergences.md) for every intentional difference
from the references.

## Status

| | |
|---|---|
| **M0** conformance corpora and golden generators | done |
| **M1** heap, Cheney collector, heap images | done |
| **M2** reader with three syntax profiles | done |
| **M3** Core IR, Scheme expander, AST engine | done |
| **M4** bytecode compiler and VM | **done: the FX-91 corpus passes compiled as well as interpreted** |
| **M5** heap dumping and single-binary builds | **done: image beside the runtime, or one standalone executable** |
| **M6** FX-87 front end | **done: 161/161 parse, 160/161 types and effects, 123/123 values** |
| **M7** FX-91 front end | **done: 182/182 parse, 182/182 types and effects, 182/182 values** — and usable from the REPL, see below |

All three deliverables of the brief are done. What follows is
[`TODO.md`](TODO.md).

```
$ cargo test              # 103 tests
$ cargo run -p fixpt-cli -- repl
fixpt 0.1.0 — scheme reader, bytecode engine
> (define (count-to n) (let loop ((i 0) (acc 0)) (if (= i n) acc (loop (+ i 1) (+ acc i)))))
> (count-to 1000000)
499999500000
> (expt 2 200)
1606938044258990275541962092341162602522202993782792835301376
> (/ 355 113)
355/113
```

Shipping a program, all three ways the design allows:

```
$ cat greet.scm
(define (main args) (display "hello") (newline) 0)

$ fixpt run greet.scm                      # just run it
$ fixpt dump-heap -o greet.heap greet.scm  # an image beside the runtime
$ fixpt run-image greet.heap
$ fixpt build -o greet greet.scm           # one file, nothing else needed
$ ./greet
hello
```

`build` appends the heap image to a copy of the `fixpt` binary, so the result
runs on a machine with no `fixpt` on it. An image records which engine made it —
compiled code carries a constants vector where interpreted code has `#f` — so
`run-image` never has to be told.

## The REPL

Arrow keys, history that persists between sessions, `^A`/`^E`/`^K`/`^U`/`^W`,
and `Tab` completion over the names the session has actually bound. The editor
is about 450 lines in `crates/fixpt-cli/src/lineedit.rs` and adds no
dependencies — deliberately, because `fixpt build` appends a heap image to a
copy of this binary, so a line-editing library would ride along in every
shipped program. Raw mode comes from `stty`, saved and restored on `Drop`,
which keeps the workspace's `unsafe_code = "deny"` intact.

**`Enter` submits only when the form is complete, and the *reader* decides.**
That is the part worth stating. The REPL used to count parentheses for itself,
which meant it did not know that the `)` in `#| ) |#` closes nothing, or that
the `(` in `|a(b|` opens nothing:

```
> (define (f x)
    #| ) |#          ← counting stops here and submits a truncated form
    x)
read error: unterminated list, expected `)`
read error: unbalanced `)`
error: unbound variable: f
```

`fixpt_read::form_status` now answers the question instead, classifying text as
`Complete`, `Incomplete` or `Invalid` — a distinction the reader can make and a
paren counter cannot. `Incomplete` opens a continuation line; anything else goes
to the reader to succeed or to report properly.

The prompt for this came from [Olin Shivers' "Eager parsing and user
interaction with `call/cc`"](https://programming-musings.org/2010/08/23/at_the_workshop/index.html),
which goes further: parse *as each character arrives*, and use continuations to
back out of the recursive descent when the user hits backspace. `fixpt` re-reads
the buffer from scratch instead, which is microseconds for a REPL-sized form and
needs no parser state kept between keystrokes. The continuation-based version is
what you want when re-reading is not affordable — and it would be a fitting use
of this engine's own re-entrant `call/cc`. [`TODO.md`](TODO.md) §1 records what
it would take and when it would start to matter.

## What a front end proves, the compiler uses

FX-87 and FX-91 know things Scheme cannot. Their checkers resolve every name to
a binding, compute an effect for every expression, and prove — by rejecting the
programs where it fails — that a standard binding can never be reassigned:
`(set! + -)` is a *type error* there, because standard bindings live in `@=`,
the immutable region.

That used to be discarded at erasure. It is now carried the way Twobit carries
its analyses (`pass2.aux.sch`) — as a quoted constant in a position where the
value is thrown away, so the emitted program is still ordinary Scheme:

```scheme
(begin '(%fx-note (integrable +) (basis checked)
                  (because "lives in @=, the immutable region"))
  (+ 1 2))
```

An engine that has never heard of `%fx-note` runs this correctly and merely
compiles it less well. One that has removes the global load and the generic
call:

```
global 26 / local / local / tail-call     ← what Scheme gets
const 1 / const 2 / prim 2 23             ← what FX-87 emits
```

Measured on FX-87, best of five: **1.21× over the compiled engine, 1.77× over
the AST engine**.

Beyond Twobit, a claim records its **basis**. `lambda.F` says a variable is free
and nothing can ask why; `.+:fix:fix` asserts its arguments are fixnums and
cannot be interrogated, so a wrong inference reaches unchecked code silently.
Here a fact is `Checked` by a type system, `Inferred` by a pass, or merely
`Asserted` — and **only `Checked` licenses removing code**. The test suite pins
that: the same claim marked `inferred` compiles back to a global load.

## Asking the REPL what to do

`,help` in any dialect. Most of it is what you would expect — `,help NAME`,
`,apropos TEXT` — answered from the running system rather than from a written
manual: Scheme reads the primitive table, and the FX dialects read a standard
environment generated from the 1987 and 1991 sources.

The one worth having is `,fits`, and it only works where there are types:

```
fx87> ,fits (pairof int bool @=)
; what accepts a value of type (pairof int bool @=):
  car : (poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((pairof t1 t2 r)) t1)))
  cdr : (poly ((r region)) (poly ((t1 type) (t2 type)) (subr (read r) ((pairof t1 t2 r)) t2)))
  null? : (poly ((r region)) (poly ((t1 type) (t2 type)) (subr pure ((pairof t1 t2 r)) bool)))
  set-car! : (poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((pairof t1 t2 r) t1) unit)))
  set-cdr! : (poly ((r region)) (poly ((t1 type) (t2 type)) (subr (write r) ((pairof t1 t2 r) t2) unit)))
  (5 more that fit anything: cons list new unique vector)
```

*I have one of these; what accepts it?* Polymorphic bindings are matched with
their binders left as unknowns — the same matching implicit projection does at a
real call site — so `car` is found without anyone instantiating it first, and
subtyping decides the rest. `,returns TYPE` asks the other direction.

A binding whose result is a bare type variable matches *every* question, so
those are counted rather than listed: `car` genuinely can produce a `bool`, and
saying so alongside `not?` and `and?` would bury the answer.

Scheme declines `,fits` rather than returning nothing — "no results" and "I
cannot ask that" are different answers, and only one of them is true.

## Trying FX-91

`--dialect fx91` selects the *language*, not just its reader: each form is
parsed, its type and effect are inferred, and it is lowered to Scheme and run on
the same engine. The REPL prints results the way the 1991 top level did — `:`
type, `!` effect, `=` value:

```
$ fixpt --dialect fx91 repl
fx91> (+ 3 4)
: int
! (maxeff)
= 7

fx91> (lambda ((r (refof int))) (^ r))
: (-> read ((r (refof int))) int)
! (maxeff)
= #<procedure>

fx91> (let ((r (new 0))) (begin (set! r 5) (^ r)))
: int
! (maxeff write read init)
= 5
```

The second one is the point of the language: the lambda is itself *pure*
(`! (maxeff)`), and the `read` it will perform when applied is latent in its
type. The third allocates, writes and reads, and says so.

Like the reference, the REPL is expression-oriented and re-checks each form in
the initial environment (`extracted/fx91/top.scm:159` resets `*tk-env*`,
`*store*` and the alpha counter every line). FX-91 has no top-level `define`;
bindings come from modules:

```
fx91> (with (module (define (square (n int)) (* n n)))
    |   (square 12))
: int
! (maxeff)
= 144

fx91> ([ (plambda ((t type)) (lambda ((x t)) x)) int ] 42)
: int
! (maxeff)
= 42
```

`,code` in the REPL shows the Scheme each form lowers to. `fixpt --dialect fx91
run FILE` runs a program without the annotations.

`--dialect fx87` works the same way, reporting in the 1987 top level's layout —
value first, then ` : type ! effect`:

```
$ fixpt --dialect fx87 repl
fx87> (+ 3 4)
7 : int ! pure

fx87> (lambda ((r (ref int @!))) (get r))
#<procedure> : (subr (read @!) ((ref int @!)) int) ! pure

fx87> (let ((x 3 @!)) (set! x 4))
#u : unit ! pure
```

The last one is effect masking: the cell really is allocated and written, but
nothing outside can observe it, so the effect is `pure`. The middle one is the
same idea from the other side — the lambda is pure, and the `read` it will
perform lives in its *type*.

## Layout

| crate | what it is |
|---|---|
| `fixpt-heap` | `Value`, the heap, the collector, heap images |
| `fixpt-read` | one reader, three lexical syntaxes |
| `fixpt-core` | the Core IR every front end targets |
| `fixpt-runtime` | numeric tower, equality, printing, primitives |
| `fixpt-engine` | the AST machine, the bytecode compiler and the VM |
| `fixpt-scheme` | the Scheme front end: expander, prelude, session |
| `fixpt-cli` | the `fixpt` binary |
| `fixpt-conform` | golden reading and normalisation |
| `fixpt-fx91` | the FX-91 front end |

## Three things worth knowing about the design

**No reference counting.** A `Value` is a tagged 64-bit word; every reference is
an offset into a flat array, never a Rust pointer. So the collector is free to
move objects, cycles cost nothing, and a heap image is a copy of a contiguous
region that loads with no relocation pass at all.

**Allocation never moves anything.** Only [`Heap::collect`] does, and only the
engine calls it, at its own safepoints, with its complete root set in hand. That
removes the classic embedding hazard — a `Value` in a Rust local going stale
because some unrelated allocation triggered a collection — by construction
rather than by discipline. `--features gc-stress` collects at *every* safepoint;
the whole suite runs green that way.

That feature answers one narrow question, though — whether every safepoint hands
the collector a complete root set — using whatever allocation the suite happens
to do. `crates/fixpt-scheme/tests/gc_workloads.rs` covers the rest, with
workloads ported from Larceny's `test/GC`, turned from benchmarks into
assertions:

| from | what it pins down |
|---|---|
| `gcbench0.sch` (Boehm's GCBench) | a long-lived tree and a long-lived array of boxed flonums survive heavy churn *intact* |
| `grow.sch` | repeatedly-doubled vectors are reclaimed — heap occupancy returns to baseline, and the workload swings it by 32,768 words, so a retained generation could not hide |
| `permsort.sch` perm8 | 40320 permutations, correct checksum, under allocation that produces no garbage at all |
| `permsort.sch` Tenperm8 | allocate-and-reclaim: occupancy returns to baseline every round |
| `permsort.sch` mergesort! | destructive `set-cdr!` over data that has already survived several collections |

The perm8 case carries an external check worth calling out. `permsort.sch`
documents the benchmark as allocating **149912 pairs** — a figure that only
comes out right if the grey-code construction shares tails exactly as Larceny's
does *and* the copying collector preserves that sharing. Both engines land
within 64 pairs of it. Losing the sharing would give 322560, so this is the one
test that would catch a forwarding-pointer bug that duplicated shared structure:
every answer would still be correct, and only the pair count would betray it.

**Both engines are explicit-stack machines.** Neither uses the Rust call stack
for Scheme recursion, so proper tail calls, unbounded recursion depth and
re-entrant `call/cc` hold in both — and the conformance suite *does* require
that they agree: the 182-case FX-91 corpus runs twice, once per engine, and
`crates/fixpt-scheme/tests/differential.rs` compares values, printed output and
error messages across the two. That test is what found a frame-reclamation bug
in the interpreter's `call-with-values`, which had been there since M3.

**The Core IR lives in the heap.** A closure is `[code, env]`, `code` holds a
flat vector of nodes, and constants sit inline — so nothing the engine executes
lives in Rust, and a dumped image can be *resumed*. Larceny's interpreter
survives a heap dump because it is written in Scheme, which makes what it
interprets ordinary heap objects; this gets the same property by the same
means.

**The compiler and the interpreter share a code object.** `Code` is
`[name, arity, rest?, body, entry, consts, frame, free]` either way; `body` is a
node vector for the AST engine and a bytecode bytevector for the VM. One shape
means `apply`, the printer and the image format need no case analysis, and a
front end gets both engines for free. The compiler adds flat closures and
assignment conversion — a captured variable is copied, so anything shared is
shared through a box — which buys about 1.6× (`cargo run --release --example
engines`) and a smaller image, since bytecode is denser than a node tree.

## Conformance

`tests/conformance/` holds corpora and goldens generated from the original
implementations:

* **FX-91** — all 182 top-level forms of the original `tests.fx`, with type,
  effect and evaluated value for each. **All three match, for all 182**: the
  program parses, infers the same type and effect, and evaluates to the same
  value as the 1991 implementation.
* **FX-87** — 155 authored expressions covering the kernel, regions, effect
  masking, subtyping and the standard types, with type and effect for each.

The goldens are checked in, so the test suite needs neither Racket nor the
archive. `reference/regenerate.sh` reproduces them, as a reviewable diff.

`docs/divergences.md` records every place `fixpt` intentionally differs from the
reference, with evidence.
