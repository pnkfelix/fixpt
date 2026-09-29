# Porting a Larceny benchmark to FX-26

The sources are Larceny's R7RS benchmarks,
`~/Dev/LangPlay/larceny/test/Benchmarking/R7RS/src/NAME.scm`, with their
inputs in `../inputs/NAME.input`: the iteration count, the arguments, and
the expected output, in the order the benchmark's `main` reads them.
Larceny's tree is read-only: never change anything there.

`tak.fx` and `nqueens.fx` here are the models.

## The shape of a port

```
;;; NAME -- the benchmark's own first-line description.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/NAME.scm),
;;; ported to FX-26. Larceny's input: COUNT iterations of (NAME ARGS…).
;;; Answer: OUTPUT.
;;; (Then what the port changed, if anything, and why: see "Faithful".)

…the benchmark's definitions…

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 40)
(define iterations int 1)

(define* run (subr (maxeff … spin) (int T) T)
  (lambda (i result) (if (= i 0) result (run (- i 1) (NAME input1)))))
(run iterations INITIAL)
```

- One file per benchmark, `scheme-bench/NAME.fx`, named as Larceny names it.
- The last form runs the benchmark `iterations` times and is its value:
  the answer, which the header states. Larceny's own count, whatever it
  costs: the ports are reference points, run natively; say the native
  time you saw in your report, not in the file.
- Keep the original's comments that explain the algorithm, and its
  credits (author, origin) in the header.

## Faithful

Port the algorithm as written: the same data structures (lists stay
lists, vectors become arrays), the same recursion, the same allocation.
Where FX-26 needs something different, change as little as possible and
say what and why in the header:

- **Heterogeneous data** (symbolic expressions, trees of symbols and
  numbers): a `define-datatype` whose variants are the kinds of datum the
  benchmark uses, or FX-26's `datum` type and its operations
  (`datum-cons`, `datum-symbol?`, …). Quoted input data becomes a
  constructor expression (or a small builder), in the file.
- **Vectors**: `(arrayof T @heap)`, `make-array`, `array-ref`,
  `array-set!`, `array-length`.
- **Mutable variables**: `(ref T @heap)` with `new`, `get`, `set`.
- **`call/cc`**: `cwcc`; delimited control: prompts
  (`docs/fx26.md`, "Control, typed").
- **`hide`**: a global input, as above.

What FX-26 does not have: floating point, bignums (integers are 61-bit
fixnums, overflow checked), file and string I/O, hash tables as a
standard operation (a port may carry a small one of its own, written in
FX-26; `crates/fixpt-fx26/src/table.fx` is an example). A benchmark that
needs one of those in its core is **not ported**: report it, with the
reason and what it would take. Do not emulate floats in integers, and do
not replace a file's contents with a different workload; a small
input the benchmark reads may become a string or list in the file if the
work is otherwise the same, and the header says so.

## FX-26, as it bites

- Every procedure has a type, `(subr EFFECT (ARG …) RESULT)`. Effects
  are `pure`, `(read @heap)`, `(write @heap)`, `(alloc @heap)`, `spin`
  (general recursion, which the checker cannot prove ends), combined with
  `(maxeff …)`. Lists are `(listof T @heap)`; `nil` often needs
  `(the (listof T @heap) nil)`.
- A top-level recursive procedure is a `define*`: it finds the globals it
  reads itself. Procedures that call each other are one `define-rec`.
- A local `letrec` procedure must name every global it reads in its
  effect: `(read (globals append2 f))`.
- `if` needs both arms; `cond` needs `else`; `+`, `-`, `*` take exactly
  two operands.
- `docs/fx26.md` is the language; `crates/fixpt-fx26/tests/programs/`
  has hundreds of small programs (`run/`, `bench/`, `datum/`,
  `recursive/`, `control/`, `bloblet/`), and the front end
  (`crates/fixpt-fx26/src/*.fx`) is 20 000 lines of real FX-26.

## Checking and running

Every command under a time limit (`/private/tmp/claude-501/m12/t SECONDS`):

```
target/release/fixpt check scheme-bench/NAME.fx      # both checkers; errors start with `!`
target/release/fixpt eval --step-limit none --fx26-run cellular --calling-convention native scheme-bench/NAME.fx
```

The second runs it as machine code; its last line is the answer and its
type. It must equal Larceny's output. Try a smaller `iterations` first.
Also run it once lowered to Scheme (`fixpt eval --step-limit none FILE`),
with `iterations` 1 and, if needed, smaller inputs, to see the two
agree; then put Larceny's values back.

If the checker rejects something correct, or the compilers or machines
misbehave, do not change the compiler: work around it in the port if you
can, say so in the header, and report it.
