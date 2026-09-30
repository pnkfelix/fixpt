# scheme-bench: Larceny's R7RS benchmarks in FX-26

Reference points, not part of the per-commit `fixpt bench`: Larceny's R7RS
benchmarks (`test/Benchmarking/R7RS/` in Larceny's tree), ported to FX-26.
Each `NAME.fx` runs the benchmark at Larceny's own inputs and iteration
count, and its last form's value is the answer Larceny checks. How a port
is made, and what it may change, is in `PORTING.md`; each file's header
says what its port changed and why.

To run one as machine code:

```
fixpt eval --step-limit none --fx26-run cellular --calling-convention native scheme-bench/NAME.fx
```

## Ported: 51 of 75

Every port passes both checkers, gives Larceny's answer natively, and
agrees with the program lowered to Scheme (at smaller counts where the
full one takes long). Times are one native run each, alone, on
2026-09-29 (`pi` and `chudnovsky` on 2026-09-30), wall clock including
about 1.8 s of start-up (reading, checking and compiling the program), or
2.7 s for `pi` and `chudnovsky`. Start-up is about 0.5 s since 2026-09-30
(the front end's checker and compilers are no longer also loaded
lowered): `pi` now takes 0.6 s in all.

| benchmark    | answer (the last form's value)                   | native s | notes                                                                    |
| ------------ | ------------------------------------------------ | -------- | ------------------------------------------------------------------------ |
| `ack`        | 32765                                            | 6.1      |                                                                          |
| `array1`     | 1000000                                          | 25.7     |                                                                          |
| `browse`     | (837 177 1090 617 661 749 628 56 826 408 1035 4… | 12.3     | `item` datatype; `eq?` of items approximated                             |
| `bv2string`  | 0                                                | 19.8     | UTF-8 codecs written in the file; bytevectors are byte bloblets          |
| `chudnovsky` | (3141592653589793238462643383279502884197169399… | 3.0      | its one float made exact; integer square root, `expt` in the file        |
| `conform`    | ("(((b v d) ^ a) v c)" "(c ^ d)" "(b v (a ^ d))… | 14.3     | each node gets an id field (no `eq?`)                                    |
| `cpstak`     | 12                                               | 11.6     |                                                                          |
| `ctak`       | 9                                                | 119.0    | `cwcc`                                                                   |
| `dderiv`     | (+ (* (* 3 x x) (+ (/ 0 3) (/ 1 x) (/ 1 x))) (*… | 11.9     | small hash table in the file                                             |
| `deriv`      | (+ (* (* 3 x x) (+ (/ 0 3) (/ 1 x) (/ 1 x))) (*… | 10.7     | expressions are `datum`s                                                 |
| `destruc`    | ((1 1 2) (1 1 1) (1 1 1 2) (1 1 1 1) (1 1 1 1 2… | 31.3     | elements a datatype (`nil` or int)                                       |
| `diviter`    | 500                                              | 4.5      |                                                                          |
| `divrec`     | 500                                              | 8.1      |                                                                          |
| `earley`     | 2674440                                          | 104.0    | n=15; was 761.4 s, 11 procedures cellular (more than 8 values)           |
| `fib`        | 102334155                                        | 3.3      |                                                                          |
| `fibc`       | 832040                                           | 31.0     | `cwcc`                                                                   |
| `gcbench`    | 0                                                | 9.4      | float ballast kept as small boxed ints                                   |
| `generator`  | (135 324 351)                                    | 9.7      |                                                                          |
| `graphs`     | 213829                                           | 13.6     | was 29.0 s, 1 procedure cellular (more than 8 values)                    |
| `hashtable0` | 102005                                           | 5.2      | measures a table written in FX-26                                        |
| `ilist`      | ((x0 x1 x2 x3 x4 x5 x6 x7))                      | 2.2      | frozen lists                                                             |
| `lattice`    | 120549                                           | 5.6      |                                                                          |
| `list`       | ((x0 x1 x2 x3 x4 x5 x6 x7))                      | 2.5      | `eq?` on lists compared elementwise                                      |
| `listsort`   | #t                                               | 8.1      | Larceny's `sort!!`                                                       |
| `lseq`       | (135 324 351)                                    | 14.2     | `cwcc`                                                                   |
| `matrix`     | (((1 1 1 1 1) (1 1 1 1 -1) (1 1 1 -1 1) (1 1 -1… | 9.5      |                                                                          |
| `maze`       | (#\space #\space #\space #\_ #\space #\space #\… | 10.6     | `eq?` by write probe; 2 procedures run as cellular code                  |
| `mazefun`    | ((_ * _ _ _ _ _ _ _ _ _) (_ * * * * * * * _ * *… | 5.0      |                                                                          |
| `mperm`      | 199584000                                        | 46.9     | input file's expected value is stale; answer is Larceny's check for N=10 |
| `nboyer`     | 51507739                                         | 8.3      | rule base as constructors                                                |
| `nqueens`    | 73712                                            | 5.5      |                                                                          |
| `ntakl`      | 13                                               | 3.6      |                                                                          |
| `paraffins`  | 5731580                                          | 57.4     |                                                                          |
| `parsing`    | (should return this list)                        | 15.7     | 28 KB input as a string in the file; was 125.2 s (more than 8 values)    |
| `peval`      | (lambda () (list (quote z) (quote y) (quote x) … | 17.7     | `/` dropped (needs rationals); in-file reader for the examples           |
| `pi`         | ((314159265358979323846264338327950288419716939… | 2.9      | `exact-integer-sqrt` (Newton) and `expt` in the file                     |
| `primes`     | (2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59… | 9.1      |                                                                          |
| `puzzle`     | 2005                                             | 6.8      |                                                                          |
| `quicksort`  | #t                                               | 9.7      | float RNG computed exactly in integers                                   |
| `rlist`      | ((x0 x1 x2 x3 x4 x5 x6))                         | 3.2      |                                                                          |
| `sboyer`     | 51507739                                         | 4.0      | Baker's `scons` via an "unchanged" flag                                  |
| `scheme`     | ("eight" "eighteen" "eleven" "fifteen" "five" "… | 21.3     | float and port primitives are stubs never called                         |
| `set`        | (x0 x1 x2 x3 x4 x5)                              | 13.4     | hash table written in FX-26                                              |
| `stream`     | (49 168 175)                                     | 9.1      | macros expanded by hand                                                  |
| `string`     | 524278                                           | 10.4     |                                                                          |
| `sum`        | 50005000                                         | 2.7      | `sum` is reserved: renamed                                               |
| `tak`        | 12                                               | 3.1      |                                                                          |
| `takl`       | 13                                               | 3.3      |                                                                          |
| `triangl`    | (22 34 31 15 7 1 20 17 25 6 5 13 32)             | 4.6      |                                                                          |
| `vecsort`    | #t                                               | 7.8      |                                                                          |
| `vector`     | ((x0 x1 x2 x3 x4 x5 x6 x7))                      | 11.8     |                                                                          |

## Not ported: 24

Each needs something FX-26 does not have, at its core (not as a tool the
port could carry itself):

| benchmark    | what it needs                                                                       |
| ------------ | ----------------------------------------------------------------------------------- |
| `fibfp`      | floats                                                                              |
| `sumfp`      | floats                                                                              |
| `fft`        | floats                                                                              |
| `mbrot`      | floats                                                                              |
| `mbrotZ`     | floats, complex numbers                                                             |
| `nucleic`    | floats                                                                              |
| `ray`        | floats, output port                                                                 |
| `simplex`    | floats                                                                              |
| `pnpoly`     | floats                                                                              |
| `sum1`       | floats, file input, `read`                                                          |
| `cat`        | file input and output                                                               |
| `wc`         | file input                                                                          |
| `read1`      | file input, `read`                                                                  |
| `tail`       | file ports, `read-line`                                                             |
| `bibfreq`    | file input                                                                          |
| `bibfreq2`   | file input                                                                          |
| `charset`    | file input (4.4 MB)                                                                 |
| `equal`      | `eq?` and an identity hash on mutable, cyclic data                                  |
| `read0`      | the host's `read` on string ports, exception handlers                               |
| `text`       | file input, SRFI 135 text library, floats                                           |
| `dynamic`    | identity of mutable pairs (union-find), reads its input each iteration; ~2300 lines |
| `slatex`     | file I/O is the benchmark                                                           |
| `compiler`   | 11 200 lines: identity `eq?`, mutable strings, floats, file ports                   |

Floats would unblock the most: 12 need them, and 7 of those
(`fibfp`, `sumfp`, `fft`, `mbrot`, `nucleic`, `simplex`, `pnpoly`) need
nothing else. Then a file input port with `read-char`, which alone
unblocks `wc`, `bibfreq`, `bibfreq2` and `charset`. Then an identity test
(`eq?` on mutable objects), for `equal` and `dynamic`, and to retire the
workarounds in `browse`, `conform`, `maze` and `sboyer`. (Bignums, which
blocked `pi` and `chudnovsky`, came to `int` on 2026-09-30.) See
`docs/research/floats.md`.

## Copyright

The benchmarks are Larceny's, some collected by Richard Gabriel, others
collected or written by Marc Feeley and Will Clinger, converted to R6RS
by Abdulaziz Ghuloum and to R7RS by Will Clinger. Larceny's licence asks
that any redistribution bear its notices and legend:

    Copyright 1991, 1994, 1998 William D Clinger
    Copyright 1998             Lars T Hansen
    Copyright 1984 - 1993      Lightship Software, Incorporated

    The Twobit compiler and the Larceny runtime system were
    developed by William Clinger and Lars Hansen with the
    assistance of Lightship Software and the College of Computer
    Science of Northeastern University.  This acknowledges that
    Clinger et al remain the sole copyright holders to Twobit
    and Larceny and that no rights pursuant to that status are
    waived or conveyed.
