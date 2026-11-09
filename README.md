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
hold up in real use, here and in [Heist](https://github.com/pnkfelix/heist)
("Used elsewhere", below).

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

## Recursive types, unions and intersections

**Recursive types need no names.** `(mu t T)` is a recursive type
written in place. A union, `oneof`, needs no tags where a test tells its
members apart. Here a tree is an `int`, or a list of trees:

```scheme
(define leaves (subr pure ((mu t (oneof int (listof t acyclic)))) int)
  (letrec ((leaves (subr pure ((mu t (oneof int (listof t acyclic)))) int)
             (lambda (x)
               (if (int? x)
                   1
                   (if (null? x) 0 (+ (leaves (car x)) (leaves (cdr x))))))))
    leaves))
(leaves (list 1 (list 2 3) (list (list 4)) 5))
```
```
leaves : (subr pure ((mu %2 (oneof int (listof %2 acyclic)))) int) ! pure
5 : int ! (read (globals leaves))
```

`int?` narrows `x`, so `car` and `cdr` see a list. `(cdr x)` is a list
of trees, and so a tree itself, by subtyping. And `leaves` needs no
`spin`: an `acyclic` list is finite, so the recursion ends.

**Subtyping is structural, through `mu`.** A sum with fewer tags is below
one with more, payloads are compared member by member, and recursive types
are compared as the infinite trees they unfold to. So an expression with
no variables, over naturals, is accepted where any expression over
integers is wanted:

```scheme
(define vars (subr pure ((mu e (sumof (num int) (var symbol) (add (productof (l e) (r e)))))) int)
  (letrec ((vars (subr pure ((mu e (sumof (num int) (var symbol) (add (productof (l e) (r e)))))) int)
             (lambda (x)
               (tagcase x
                 (num n 0)
                 (var v 1)
                 (add p (+ (vars (extract p l)) (vars (extract p r))))))))
    vars))
(define two-plus-three (mu e (sumof (num nat) (add (productof (l e) (r e)))))
  (sum add (product (l (sum num 2)) (r (sum num 3)))))
(vars two-plus-three)
```
```
0 : int ! (read (globals two-plus-three vars))
```

The other way is refused. A variable is not among `two-plus-three`'s
tags:

```scheme
(define bad (mu e (sumof (num nat) (add (productof (l e) (r e)))))
  (sum add (product (l (sum num 2)) (r (sum var 'x)))))
```
```
fixpt: sub.fx:13:40: a (mu %1 (sumof (#:num nat) (#:add (productof (#:l %1) (#:r %1))))) is expected here, and this is a (sumof (#:var symbol))
```

**Intersections: one procedure, several types.** `(allof T …)` is a
procedure with each member's type, from one body checked against each.
A constant folder can then keep an expression without variables free of
them. Without the `allof`, the folder would take a closed expression (a
subtype) but give back only an open one:

```scheme
(define-type closed (mu e (sumof (num int) (add (productof (l e) (r e))))))
(define-type open (mu e (sumof (num int) (var symbol) (add (productof (l e) (r e))))))
(define-type folder (allof (subr pure (closed) closed) (subr pure (open) open)))
(define fold folder
  (letrec ((fold folder
             (lambda (x)
               (tagcase x
                 (num n x)
                 (var v x)            ; a closed expression has no var: skipped there
                 (add p (let ((l (fold (extract p l))) (r (fold (extract p r))))
                          (tagcase l
                            (num a (tagcase r
                                     (num b (sum num (+ a b)))
                                     (else y (sum add (product (l l) (r r))))))
                            (else y (sum add (product (l l) (r r)))))))))))
    fold))
(define c closed (fold (sum add (product (l (sum num 2)) (r (sum num 3))))))
(define o open (fold (sum add (product (l (sum var 'x)) (r (sum num 1))))))
(define wrong closed (fold o))
```
```
fold : folder ! pure
c : closed ! (read (globals fold))
o : open ! (read (globals fold))
fixpt: fold.fx:19:22: `wrong` is declared a closed: a closed is expected here, and this is a open
```

A call takes every member its arguments fit, and its result is the meet
of theirs. Termination is judged member by member too: a length
procedure can be `pure` on `acyclic` lists and `spin` on lists that may be
cyclic, from one body. Herman and Wand's renaming over λm's syntactic
sorts is the same idea at full size
(`crates/fixpt-fx26/tests/programs/allof/swap.fx`).

## Modules are values, and a file is a module

A module is a first-class value with a type, a `moduleof`, as in Sheldon
and Gifford's design for FX-91. It needs no name: `(module item …)` is an
expression. A file is a module too, and it is written as nothing more than
a list of top-level definitions. It doesn't know it will be loaded as a
module. `counter.fx` is

```scheme
(define-generative t int)
(define zero t (up-t 0))
(define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
(define value (subr pure (t) int) (lambda (c) (down-t c)))
```

and a program loads it, uses it with `with`, and passes it to a procedure
whose type depends on the module it is given:

```scheme
(define counter (load-module "counter.fx"))
(with counter (value (inc (inc zero))))
(define twice (subr pure ((m : (moduleof (abs t type) (val inc (subr pure (t) t)))) (select m t)) (select m t))
  (lambda (m c) (with m (inc (inc c)))))
(with counter (value (twice counter zero)))
(with counter (+ zero 1))
```
```
counter : (moduleof (desc t counter.fx..t) (val zero counter.fx..t) (val inc (subr pure (counter.fx..t) counter.fx..t)) (val value (subr pure (counter.fx..t) int))) ! (read (globals %shared:counter.fx))
2 : int ! (read (globals counter))
twice : (subr pure ((moduleof (abs t type) (val inc (subr pure (t) t))) (select $1 t)) (select $1 t)) ! pure
2 : int ! (read (globals counter twice))
fixpt: main.fx:6:18: argument 1 is a counter.fx..t, where a int is expected
```

`define-generative` makes `t` a new type: `up-t` and `down-t` convert
between it and `int`, and only the file's own definitions can call them.
So outside the file a counter is not an `int`. The type of `twice`'s
first parameter asks for less than `counter` has, a module with some
abstract `t` and an `inc`, and the types after it select `t` from
whichever module is passed. ML's functors are a restricted form of these
dependent procedures. A file may also take parameters (regions, types or
other modules) from whoever loads it, and loaded files can be compiled
apart, to `.fasl` files.

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

## Used elsewhere

[Heist](https://github.com/pnkfelix/heist) is a separate project with
about 39,000 lines of FX-26 programs of its own:
- an Emacs-lineage editor;
- an R7RS Scheme, compiled to FX-26 and run through `stage`;
- a SAT and SMT solver, a port of a Scheme solver;
- a relational model finder after Alloy;
- a bounded model checker, and a control-flow analysis, each for both
  Scheme and FX-26 programs.

Several FX-26 features exist because Heist asked for them: running other
programs as processes, `attempt` and `attempt-within` for failures and
time limits, module parameters and modules with state of their own, among
others. `docs/fx26.md` says where each came from.

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
