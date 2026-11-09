# fixpt

`fixpt` is where **FX-26** is designed and built. FX-26 is an effect-typed
language in the line of MIT's FX-87 and FX-91. Its types say what code
*does*, not just what it returns: which memory it reads, writes and
allocates; whether it may fail to end; whether it captures continuations;
whether it sends, receives or waits; what I/O it performs. Each of those is
in the language because something acts on it. The compiler optimizes
with it, the REPL decides what it may run early by it, and the checker
refuses programs that break it.

FX-26 is also the language `fixpt`'s own tooling is written in. Its
reader, parser, checker, compiler and machine-code generators are about
78,000 lines of FX-26, and they compile and check every FX-26 program you
run. The repository exists to try design ideas for FX-26 and see them
hold up in real use. Other projects use FX-26 too, and several of its features
were built at their request.

```scheme
(define sum-to (subr pure (int) int)
  (lambda (n)
    (let ((acc (the (ref int @a) (new 0))))
      (letrec ((go (subr (maxeff (read @a) (write @a)) (int) unit)
                 (lambda (i) (if (<= i 0) #u (begin (set acc (+ (get acc) i)) (go (- i 1)))))))
        (begin (go n) (get acc))))))
(sum-to 100)
```
```
$ fixpt eval sum.fx
sum-to : (subr pure (int) int) ! pure
5050 : int ! (read (globals sum-to))
```

`sum-to` allocates a reference cell and writes it a hundred times, and its
type still says `pure`. Its cell lives at region `@a`, nothing outside can
reach `@a`, and so the checker *masks* those effects: no caller can observe
them. The loop needs no `spin`, the effect of code that may not end,
because the checker sees that `i` counts down to a bound. (The call's one
effect is reading the global `sum-to` names.)

## What the types say

**Effects are part of a procedure's type.** `(subr E (T …) R)` is a
procedure that takes `T …`, returns `R`, and has effect `E` when called.
Effects are built from atoms on regions (`(read r)`, `(write r)`,
`(alloc r)`), combined with `maxeff`. Making a procedure is pure. What it
will do is *latent* in its type, and is paid for where it is called. This
is Lucassen and Gifford's design, from FX-87.

**Masking.** An effect on a region that nothing outside an expression can
name is dropped from the expression's effect, as in `sum-to` above. Local
mutation is an implementation detail, and the type says so.

**Termination is an effect.** A procedure that may not end says `spin`.
A recursion that doesn't plainly count down to a bound is refused unless
its type says so, and the refusal says why:

```scheme
(define steps (subr pure (int) int)
  (letrec ((go (subr pure (int int) int)
             (lambda (n k) (if (= n 1) k (go (if (= 0 (remainder n 2)) (quotient n 2) (+ (* 3 n) 1)) (+ k 1))))))
    (lambda (n) (go n 0))))
```
```
fixpt: collatz.fx:3:14: `go` is declared a (subr pure (int int) int): a (subr pure (int int) int) is expected here, and this is a (subr spin (int int) int)
  beyond what is expected, it has spin; it may not end: nothing smaller, or related, is passed by the call of `go` in `go` (it counts up, but nothing fixed bounds the count above)
```

**Control is typed.** First-class continuations have effects, as in
Jouvelot and Gifford's PLDI '89 paper. Capturing one has a `comefrom`
effect, and invoking one has a `goto`. Where nothing outside can reach the
continuation, both are masked:

```
$ fixpt eval control.fx
42 : int ! pure                  ; (+ 1 (cwcc (lambda (k) (k 41))))
10 : int ! pure                  ; a prompt catching an abort to its tag
```

Delimited control (prompts, tags, `abort-current-continuation`,
composable continuations) is typed the same way. A tag's type says what
its delimited computations may do.

**Checking is bidirectional.** Definitions carry signatures, and bodies are
checked against them while types are found locally. Errors stay where they
were made, which is what checking as you type needs. The checker always
knows the type *expected* at a point, which is the question the REPL's
`,help` answers for a hole.

## Concurrency, checked

Processes have their own heaps (*places*) and communicate only by
messages and I-cells (write-once cells: a read waits until the cell is
filled). So no mutable memory is ever shared between processes, and the
types show the communication. This `ask` sends a request to a server
process and waits for its reply; its type says it sends on `@srv` and
awaits on `@r`:

```scheme
(define-type req (productof (n int) (reply (icell int @r))))
(define doubler (addr req @srv)
  (spawn (box req p)
    (letrec ((serve (subr (maxeff (receive p) (init @r) nondet spin) () unit)
               (lambda ()
                 (let ((m (receive box)))
                   (begin (icell-put! (extract m reply) (* 2 (extract m n)))
                          (serve))))))
      (serve))))
(define* ask (subr (maxeff (send @srv) (alloc @r) (await @r)) (int) int)
  (lambda (n)
    (let ((c (the (icell int @r) (make-icell))))
      (begin (send doubler (product (n n) (reply c))) (icell-get c)))))
(+ (ask 20) (ask 1))
```
```
doubler : (addr req @srv) ! (maxeff (alloc @srv) (init @r) spin nondet)
ask : (subr (maxeff (alloc @r) (await @r) (send @srv) (read (globals doubler))) (int) int) ! pure
42 : int ! (maxeff (alloc @r) (await @r) (send @srv) (read (globals ask doubler)))
```

`nondet` is an effect: a receiver may see messages in any order its
senders allow. A computation without it gives the same answer on every
run. `define*` works out which globals the body reads; the rest of the
type is the signature as written. Only *transmissible* values cross
between processes: no mutable data, and only procedures whose effects any
process may have. The checker enforces this.

`par` runs branches in parallel. It is refused when they interfere:

```scheme
(define xs (arrayof int @x) (make-array 3 0))
(par ((a (begin (array-set! xs 0 1) 0))
      (b (array-ref xs 0)))
  (+ a b))
```
```
fixpt: par-interfere.fx:5:1: `par`'s branches interfere: one has (write @x) and another (read @x), so the answer could depend on which runs first
```

`pselect` waits on whichever of several things is ready first. `race`
runs branches and keeps the first answer, and its branches must be
cancellable, a property the types show. A monitored process's failure is
sent to a watcher, not raised in its spawner.

## Specifications, tested and proved

A signature may carry `requires` and `ensures`. `fixpt test` runs the
program with them checked, then calls each procedure on inputs drawn from
its parameters' types. `fixpt verify` compiles with certificates and
proves each word against its own, handing open obligations to z3 when it is
installed:

```scheme
(define clamp (subr pure ((lo : int) (hi : int) (x : int)) int
                (requires (<= lo hi))
                (ensures r (and (<= lo r) (<= r hi))))
  (lambda (lo hi x) (if (< x lo) lo (if (< hi x) hi (- x 1)))))
```
```
$ fixpt verify clamp.fx
`clamp`: not verified
  at clamp.fx:4:53, `(- x 1)`: the ensures: false: with lo = 0, hi = 0, x = 0, the result is -1
```

## Effects as licences

The FX-26 REPL reads what you type with a reader written in FX-26, *as you
type it*. It may run code before you press `Enter`, but only code whose
effects grant a licence to (`crates/fixpt-fx26/src/licence.rs`). A
finished expression that is safe to run early shows its value while you
are still typing:

```
fx26> (car (cons 1 #t))          ; = 1
fx26> (set c 5)                  ; not run early: it may (write @c)
```

The reader itself runs under the same rule. Its control and allocation
effects are all on regions it owns, which is what makes running it
speculatively, on every keystroke, safe.

What the checker proves also reaches the compiler. Lowering to Scheme is
not erasure: facts travel with the code as `%fx-note` claims, each with
its basis. Only a `Checked` claim licenses removing code. `,code` shows
them on the machine that runs the lowering:

```
$ fixpt --machine rs-scheme-vm
fx26> ,code
fx26> (+ 1 2)
; (begin '(%fx-note (integrable %fx26-add) (pure) (basis checked) (because "pure")) (%fx26-add 1 2))
3 : (nat 3) ! pure
```

On the other machines, `,code` shows the words the compiler written in
FX-26 made.

## Written in itself

The front end that checks and compiles FX-26 is written in FX-26:
- the reader (`eager-reader.fx`), which also reads Scheme;
- the parser and module loader;
- the checker (`check*.fx`);
- the compiler to *cellular* words, a threaded code (`compile*.fx`), and
  to register code (`regcode*.fx`);
- arm64 and x86_64 code generators (`native*.fx`), for code that runs in
  the cellular machine and for native procedures;
- an evaluator, and the macro expander.

A second, independent front end in Rust implements the same language. The
two are kept in lockstep: `fixpt check FILE` runs both checkers and shows
both results where they disagree, and `fixpt compile FILE` compares the
two compilers' code. The front end is compiled once
by the Rust compiler and cached as machine code, so a small program runs
in a few hundredths of a second.

By default FX-26 runs as native machine code on arm64 (macOS or Linux) and
x86_64 Linux. Other machines (a bytecode VM, interpreters of the threaded
code, a copy-and-patch stencil machine) are kept as references, and each
benchmark runs on all of them (`fixpt machines`).

## Trying it

```
$ cargo run --release                 # the FX-26 REPL
$ cargo run --release -- help         # the commands
```

Each of these takes a file, `-` for the standard input, or program text:

- `fixpt eval INPUT` runs a program and prints each form's value, type and
  effect.
- `fixpt check INPUT` runs both checkers and prints what they found.
- `fixpt compile INPUT` runs both compilers and shows the code.
- `fixpt test INPUT [RUNS]` checks specifications as the program runs,
  then looks for counterexamples on RUNS inputs (100 by default).
- `fixpt verify INPUT [NAME …]` proves each word against its
  specifications (`,verify` in the REPL).

In the REPL, definitions persist between inputs. Errors in finished
subforms are underlined as you type, and a hint says what the argument at
the cursor must be. `,help` lists the commands. `editors/emacs/fx26-mode.el`
gives Emacs highlighting, indentation, both checkers as you type, and
`M-x run-fx26` (`editors/emacs/README.md`).

## Reading further

- [`docs/fx26.md`](docs/fx26.md): the language, feature by feature, with
  the reasons for each decision and when it was made.
- [`docs/fx26-grammar.md`](docs/fx26-grammar.md): the forms, as the parsers
  accept them.
- [`docs/research/`](docs/research/): design notes, surveys and
  proposals, some built and some not yet. Among those still in
  development: typed hygienic macros with inferred signatures
  ([`typed-macros.md`](docs/research/typed-macros.md)), staging with
  effect evidence, and effect markers
  ([`effect-markers.md`](docs/research/effect-markers.md)).
- [`PLAN.md`](PLAN.md), [`TODO.md`](TODO.md) and [`DONE.md`](DONE.md): the
  plan, the work deliberately deferred, and what was done.
- [`docs/performance.md`](docs/performance.md): measurements and their
  history.

## The rest of the repository

FX-26 runs on a Scheme engine written in Rust: a numeric tower, a
copying collector, heap images, an AST interpreter and a bytecode VM,
hygienic macros, and SRFI 226's control features. The engine started as
the base for faithful re-implementations of FX-87 and FX-91, which, like
the 1987 and 1991 originals, type-check and lower to Scheme. They pass
the conformance corpora recovered from the originals, and are still
there: `fixpt --dialect fx91 repl`, `--dialect fx87`, and
`fixpt scheme` for Scheme itself.

[`docs/repository.md`](docs/repository.md) covers those front ends, the
engine's design, the crates, the platforms, the machines and which
compiler makes their code, how to read the `fixpt bench` tables in commit
messages, shipping a program as one binary, and the milestones.
