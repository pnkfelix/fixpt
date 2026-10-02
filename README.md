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

## Reading a `fixpt bench` table

Commit messages carry two tables from `fixpt bench`: how long FX-26
programs (`crates/fixpt-fx26/tests/programs/bench`) take to run, and how
long they take to compile. Times are best of 3, in milliseconds.

### The run table

Each program run every way this repository has of running FX-26, the run
alone: checking and compiling, to words and to machine code, are done
before the clock starts. (Before 2026-10-02 the `lowered` column also
counted checking and lowering, and so was higher; `docs/performance.md`
has the history.)

```
| program | answer | lowered | rust  | hand | stencils | compiled | registers | native | M words | GCs |
| fib     | 832040 | 121.5   | 209.5 | 16.1 | 21.8     | 13.2     | 6.0       | 2.7    | 0.0     | 0   |
```

Every column but `lowered` and `native` runs *cellular words*: the code
the compiler written in FX-26 (`compile.fx`) makes, a small stack-machine
code. The columns differ in what runs those words.

| column      | what ran the program                                                                                                                                                                      |
| ----------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `answer`    | the value of the program's last line, from the lowered run; a run whose answer differs has `✗` beside its time                                                                            |
| `lowered`   | the program lowered to Scheme by the Rust front end, run on the Scheme engine's bytecode VM: the baseline, and the reference answer                                                       |
| `rust`      | cellular words interpreted by the machine written in Rust (`fixpt-engine` `cellular.rs`)                                                                                                  |
| `hand`      | the same words interpreted by the hand-encoded arm64 machine: an interpreter whose routines are machine code (`fixpt-native` `cellular.rs`)                                               |
| `stencils`  | the stencil (copy-and-patch) machine, built from compiled Rust stencils (`fixpt-native` `stencil.rs`; the stencils need nightly to build, and a build without them leaves the column out) |
| `compiled`  | the hand machine, with each word compiled to arm64 before it runs                                                                                                                         |
| `registers` | the same, running each lambda's *register code* (its values in machine registers, not on the data stack) where it has some                                                                |
| `native`    | the native calling convention: the procedure the last line calls compiled straight to arm64 (`fixpt-native` `direct.rs`) and called; `—` if declined                                      |
| `M words`   | millions of words the `native` run allocated                                                                                                                                              |
| `GCs`       | collections during the `native` run, minor and major                                                                                                                                      |

`native` is the one that counts for speed; the others are kept running as
references and to catch disagreements.

### The compile table

```
| program   | check  | lower | words | arm64 | registers | native | fx read | fx parse | fx check | fx words | fx arm64 | fx M words | fx GCs |
| fib       | 0.43   | 0.01  | 0.04  | 0.01  | 0.01      | 0.02   | 0.64    | 0.02     | 1.13     | 0.20     | 0.45     | 0.1        | 0      |
| front end | 393.10 | 15.60 | 67.50 | 7.00  | 19.20     | —      | 4871.30 | 21.20    | 1366.70  | 746.80   | 984.30   | 326.7      | 311    |
```

Each phase of compiling, timed alone, from what the phase before made.
The left half is the Rust front end and back ends; the `fx` half is the
pieces written in FX-26, run as the REPL runs them. With `--front-end`,
a last row is the front end itself (its files and bootstrap), compiled
once: about 10 s more, half of it the reader, which runs lowered. It is
left out of the commit tables to keep the loop quick; turn it on to look
into compile time.

| column       | what was timed                                                                                   |
| ------------ | ------------------------------------------------------------------------------------------------ |
| `check`      | the Rust checker, reading included                                                               |
| `lower`      | lowering what it checked to Scheme                                                               |
| `words`      | the Rust compiler to cellular words, register code included                                      |
| `arm64`      | every word's cells assembled to arm64 by the Rust `assemble_word` (not placed)                   |
| `registers`  | the same, a word's register code where it has some                                               |
| `native`     | `direct.rs` compiling the procedure the run table's `native` column calls; `—` where it has none |
| `fx read`    | the reader written in FX-26: lowered, on the bytecode engine, as the REPL runs it                |
| `fx parse`   | the parser written in FX-26, as the front end's register code                                    |
| `fx check`   | the checker written in FX-26, likewise                                                           |
| `fx words`   | the compiler written in FX-26, register code included                                            |
| `fx arm64`   | every word's cells assembled to arm64 by `native.fx` (not placed), as `fx-compiled` does         |
| `fx M words` | millions of words the `fx` phases allocated                                                      |
| `fx GCs`     | their collections, minor and major                                                               |

`fixpt bench --help` says the same, `--tables run` or `--tables compile`
prints one, and `docs/performance.md` keeps the history.

## Status

|                                                  |                                                                                                                                                                                                                                                                                                 |
| ------------------------------------------------ | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| **M0** conformance corpora and golden generators | done                                                                                                                                                                                                                                                                                            |
| **M1** heap, Cheney collector, heap images       | done                                                                                                                                                                                                                                                                                            |
| **M2** reader with three syntax profiles         | done                                                                                                                                                                                                                                                                                            |
| **M3** Core IR, Scheme expander, AST engine      | done                                                                                                                                                                                                                                                                                            |
| **M4** bytecode compiler and VM                  | **done: the FX-91 corpus passes compiled as well as interpreted**                                                                                                                                                                                                                               |
| **M5** heap dumping and single-binary builds     | **done: image beside the runtime, or one standalone executable**                                                                                                                                                                                                                                |
| **M6** FX-87 front end                           | **done: 161/161 parse, 160/161 types and effects, 123/123 values**                                                                                                                                                                                                                              |
| **M7** FX-91 front end                           | **done: 182/182 parse, 182/182 types and effects, 182/182 values** — and usable from the REPL, see below                                                                                                                                                                                        |
| **M9** hygienic macros                           | **done:** `syntax-rules`; SRFI 211's `er-macro-transformer` and `ir-macro-transformer`; SRFI 139 syntax parameters — [`docs/macros.md`](docs/macros.md)                                                                                                                                         |
| **M11** FX-26, the tooling's own language        | **done, the seven-step plan:** a declared kernel with PLDI '89's control effects and typed delimited control, bidirectional checking, lowering to Scheme that carries the checker's proofs, the eager reader ported to it, and speculation licensed by effects — [`docs/fx26.md`](docs/fx26.md) |

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

`,help` can also be written *inside* a form, asking what belongs at that
position rather than what a name means:

```
fx87> (vector-ref (make-vector 3 0) ,help)
; the hole wants: int
; what produces one:
  abs : (subr pure (int) int)
  string-length : (poly ((r region)) (subr pure ((string r)) int))
  …

fx87> (,help (cons 1 2))
; the hole is applied to a (pairof int int @=)
  car : …   cdr : …   set-car! : …
```

The first argument pins the element type, so the *second* is asked about as an
index rather than as "anything". A hole nothing constrains says so —
`(car ,help)` reports `(pairof t1 t2 r)` rather than inventing something.

A hole is also answered by *running* the form up to it, so the answer is made
of values rather than types — and in Scheme, which has no types, that is the
only answer there is. In Scheme the hole is then **held**: reaching it captures
the rest of the form as a composable continuation, and `,resume` carries on
from the hole with a value, as many times as you like.

```
> (define v (vector 10 20 30))
> (list 'got (vector-ref v ,help))
; at the hole:
  the hole is argument 2 of 2 to #<primitive:vector-ref>
  argument 1 evaluated to #(10 20 30)
> ,resume 0
(got 10)
> ,resume 2
(got 30)
```

This is built on SRFI 226's control features — continuation marks, tagged
prompts, composable continuations — which the engines now provide. Each input
runs under the top level's own prompt, so the hole's continuation is the form
and nothing of the REPL. A hole reports the continuation marks around it,
which is how a program says what it wants a paused computation to show. And
exception handlers and `dynamic-wind` extents are marks too, not globals, so an
input abandoned at a hole or an uncaught error cannot leave either behind for
the next one.

This needs the form to be syntactically complete, which is not how anyone types
it: `(vector-ref v ,help` — asking while still writing — cannot be read at all.
The information wanted is in the *parser's stack* rather than in the text, which
is [`TODO.md`](TODO.md) §1's third and sharpest motivation.

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

## Trying FX-26

FX-26 is this project's own continuation of FX, and the language the tooling
is meant to be rewritten in ([`docs/fx26.md`](docs/fx26.md)). Each form is
checked, lowered to Scheme, and run, and the REPL prints in FX-87's layout:

```
$ fixpt --dialect fx26 repl
fx26> (+ 1 (cwcc (lambda (k) (k 41))))
42 : int ! pure

fx26> (define count (subr pure (int) int)
    |   (lambda (n) (if (= n 0) 0 (count (- n 1)))))
count : (subr pure (int) int) ! pure

fx26> (define t (prompt-tag int int pure @p) (make-continuation-prompt-tag))
t : (prompt-tag int int pure @p) ! (alloc @p)

fx26> (prompt t (+ 1 (abort-current-continuation t 5)) (lambda (v) v))
5 : int ! pure
```

The first one is PLDI '89's control effects. Calling `cwcc` has a
`comefrom` effect, and calling the continuation has a `goto`. Nothing outside
can reach the continuation's region, so both are masked, and the whole
expression is `pure`. The last is delimited control: the abort has a `goto`,
and the prompt for its tag catches it. Checking is bidirectional. The
signature supplies `count`'s parameter type. `cwcc`, `abort-current-continuation`
and the handler have their types worked out from what they are applied to
and what is expected of them. Written out, it is all `proj`s.

Definitions persist between inputs. As in the other FX REPLs, errors in
finished subforms are underlined as you type, and a hint says what the
argument at the cursor must be.

Outside the REPL, each of these commands takes a file, `-` for the standard
input, or program text:

- `fixpt eval INPUT` runs a whole program and prints each form's value,
  type and effect. A `.fx` file needs no `--dialect`.
- `fixpt check INPUT` runs both checkers, the one in Rust and the one in
  FX-26, and prints what they found. Where they disagree, it prints both.
- `fixpt compile INPUT` runs both compilers and shows the code, register
  code included, and says whether the two made the same.

The eager reader (see "The REPL" above) has been ported to FX-26
(`crates/fixpt-fx26/src/eager-reader.fx`). It is checked, lowered and run
like any FX-26 program, and it reads the same inputs to the same data, errors
and parse stacks as the Scheme and Rust readers. It also reads FX-26's own
lexical syntax, and the FX-26 REPL uses it to read what you type: FX-26 code
reading FX-26 code. Its control and allocation
effects are all on regions it owns. That is what makes it safe to run
speculatively. `fixpt --reader fx26 repl` checks exactly that, and then
reads the Scheme REPL's input with it.

That check is the licence FX-26's effects exist to grant
(`crates/fixpt-fx26/src/licence.rs`). The FX-26 REPL uses it too: a finished
expression whose effect is licensed runs as you type, and its value appears
before `Enter`:

```
fx26> (car (cons 1 #t))          ; = 1
fx26> (set c 5)                  ; not run early: it may (write @c)
```

The lowering is not an erasure. What the checker proved travels with the
code as `%fx-note` claims, so the compiler can use it. `,code` shows it:

```
fx26> ,code
fx26> (+ 1 2)
; (begin '(%fx-note (integrable +) (pure) (basis checked) (because "pure")) (+ 1 2))
3 : int ! pure
```

Under `--fx26-run cellular`, `,code` shows instead the cellular[^cellular] words the
compiler written in FX-26 made for each form, those it had not shown
before.

## Which compiler makes the machine code

Machine code is made in two stages, and each stage has a compiler written
in Rust and one written in FX-26:

- **Stage A, source to words.** FX-26 source becomes cellular words (and,
  for each lambda, register code). In Rust: `fixpt-fx26`'s `cellular.rs`
  and `cellular/regcode.rs`. In FX-26: `compile*.fx` and `regcode*.fx`.
- **Stage B, words to arm64.** A word's cells, or its register code,
  become arm64. In Rust: `fixpt-native`'s `cellular.rs` (`assemble_word`
  for cells, and register code) and `direct.rs` (the native calling
  convention). In FX-26: `native.fx`, for cells only.

What each way of invoking `fixpt` uses:

| invocation                                                | stage A        | stage B                        | runs on                         |
| --------------------------------------------------------- | -------------- | ------------------------------ | ------------------------------- |
| `--dialect fx26` (lowered, the default)                   | none: lowered  | none                           | the Scheme bytecode VM          |
| `--fx26-run evaluate`                                     | none           | none                           | the evaluator written in FX-26  |
| `--fx26-run cellular`                                     | FX-26          | none                           | the cellular machine in Rust    |
| `--fx26-run cellular --cellular-machine native`           | FX-26          | none                           | the hand machine, running cells |
| `--fx26-run cellular --cellular-machine stencils`         | FX-26          | Rust (stencils)                | the stencil machine             |
| `--fx26-run cellular --cellular-machine native-compiled`  | FX-26          | Rust (`assemble_word`)         | the hand machine, as arm64      |
| `--fx26-run cellular --cellular-machine fx-compiled`      | FX-26          | FX-26 (`native.fx`)            | the hand machine, as arm64      |
| `--fx26-run cellular --cellular-machine registers`        | FX-26          | Rust (register code)           | the hand machine, as arm64      |
| `--fx26-run cellular --calling-convention native`         | FX-26          | Rust (`direct.rs`)             | arm64, the native convention    |
| `fixpt bench`, every column but `lowered`                 | Rust           | Rust, or none (`rust`, `hand`) | as its column says              |
| the front end itself (`--fx26-run cellular`, any machine) | Rust           | Rust (register code)           | the hand machine, as arm64      |
| `fixpt check INPUT`                                       | none           | none                           | both checkers, compared         |
| `fixpt compile INPUT`                                     | both, compared | none                           | nothing: the code is shown      |

The rest of the detail:

- **The REPL and `fixpt eval` under `--fx26-run cellular`** are the only
  invocations whose stage A is the compiler written in FX-26. Each form is
  checked by the Rust checker first, which decides its type and effect.
  Then the checker and compiler written in FX-26 check it again and
  compile it, and the chosen machine runs the words.
- **`--cellular-machine fx-compiled`** makes each form's words arm64 with
  `native.fx` before they run: every word made of cells that the form's
  word reaches through its cells and operands, as `native-compiled` does
  with `assemble_word`. Only placing the code, and the runtime, stay in
  Rust. Stages A and B are then both FX-26, with each form still checked
  by the Rust checker too. `native.fx` makes the same instructions as
  `assemble_word` (`crates/fixpt-fx26/tests/native.rs` compares them word
  for word over the whole front end). It takes longer to make them: `,time`
  counts that as codegen. `native.fx` has no register code, so
  `fx-compiled` runs words' cells, as `native-compiled` does.
- **`fixpt bench`**'s run table compiles its programs with the Rust
  compiler (`fixpt_fx26::cellular::Compiler`), so all its compiled
  columns are Rust in both stages. Its compile table times both
  compilers' phases, `native.fx` included.
- **The front end** (the reader, checker and compilers written in FX-26)
  runs as register code, compiled by the Rust compiler and made arm64 by
  the Rust register-code assembler, whatever `--cellular-machine` says. It
  is kept in `~/Library/Caches/fixpt/` once made. So under `fx-compiled`
  the compiler that makes the machine code is written in FX-26, but it was
  itself compiled by Rust. (`FIXPT_FRONT_END_LOWERED=1` runs the front end
  lowered instead, on the Scheme VM.)
- **The native calling convention** (`--calling-convention native`)
  compiles a procedure's register code, made by the compiler written in
  FX-26, with `direct.rs`. That is Rust whatever the cellular machine is.
  What it declines runs as cellular words on the chosen machine, so there
  `fx-compiled` applies.

## Layout

| crate           | what it is                                           |
| --------------- | ---------------------------------------------------- |
| `fixpt-heap`    | `Value`, the heap, the collector, heap images        |
| `fixpt-read`    | one reader, three lexical syntaxes                   |
| `fixpt-core`    | the Core IR every front end targets                  |
| `fixpt-runtime` | numeric tower, equality, printing, primitives        |
| `fixpt-engine`  | the AST machine, the bytecode compiler and the VM    |
| `fixpt-scheme`  | the Scheme front end: expander, prelude, session     |
| `fixpt-cli`     | the `fixpt` binary                                   |
| `fixpt-conform` | golden reading and normalisation                     |
| `fixpt-fx91`    | the FX-91 front end                                  |
| `fixpt-fx87`    | the FX-87 front end                                  |
| `fixpt-fx26`    | FX-26, the tooling's own language                    |
| `fixpt-tidy`    | checks on the repository itself, run by `cargo test` |

Test programs of more than four lines or 240 characters live in files beside
their tests — `crates/*/tests/programs/<suite>/` — and come in with
`include_str!`, not as string literals. Shorter ones stay inline, next to what
they should produce. `fixpt-tidy` fails the build on a long one; the limit is
measured on the program as it would stand in a file, without the Rust around it.

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

| from                             | what it pins down                                                                                                                                                  |
| -------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `gcbench0.sch` (Boehm's GCBench) | a long-lived tree and a long-lived array of boxed flonums survive heavy churn *intact*                                                                             |
| `grow.sch`                       | repeatedly-doubled vectors are reclaimed — heap occupancy returns to baseline, and the workload swings it by 32,768 words, so a retained generation could not hide |
| `permsort.sch` perm8             | 40320 permutations, correct checksum, under allocation that produces no garbage at all                                                                             |
| `permsort.sch` Tenperm8          | allocate-and-reclaim: occupancy returns to baseline every round                                                                                                    |
| `permsort.sch` mergesort!        | destructive `set-cdr!` over data that has already survived several collections                                                                                     |

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

[^cellular]: "Cellular" would be called "threaded" in the Forth community: code as
a sequence of cells (references to routines, and their operands), run by an inner
interpreter. This repository says "cellular" throughout (the user's decision,
2026-09-27).
