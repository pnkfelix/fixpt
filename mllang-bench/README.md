# mllang-bench: ML benchmarks, and their ports to FX-26

Reference points, not part of the per-commit `fixpt bench`. The sources
were downloaded on 2026-09-29, verbatim, at pinned commits; provenance and
licences are in `SOURCES.md`:

- `mlton-benchmark/`: MLton's benchmark suite (`benchmark/tests`), the de
  facto standard SML set, much of it from the SML/NJ suite.
- `ocaml-classic/`: the classic OCaml benchmark programs from OCaml's own
  testsuite, each with its expected output (`.reference`).
- `sandmark-benchmarksgame/`: the Benchmarks Game programs from Sandmark.

The ports are in `fx/mlton/`, `fx/ocaml/` and `fx/benchmarksgame/`. Each
file's header gives its source, what the port changed and why, its count
and its answer. MLton's driver, with its per-benchmark counts, was not
fetched, so the MLton counts are ours, chosen for about 1 to 3 s of
native run time; so are the OCaml counts where the originals' were too
small. Where an original prints its result, the port's value pins it: a
count, a checksum, or (for `kb` and `sorts`) a hash of the output equal to
the hash of the `.reference` file.

To run one as machine code:

```
fixpt eval --step-limit none --fx26-run cellular --calling-convention native mllang-bench/fx/mlton/NAME.fx
```

## Ported: 42

Every port passes both checkers, runs natively, and agrees with the
program lowered to Scheme. Times are one native run each, alone, on
2026-09-29 (`DLXSimulator`, `md5`, `pidigits`, `pidigits5`,
`psdes-random` and `smith-normal-form` on 2026-09-30), wall clock
including about 1.8 to 3.5 s of start-up.

| benchmark                      | answer                                          | native s | count and notes                                             |
| ------------------------------ | ----------------------------------------------- | -------- | ----------------------------------------------------------- |
| `benchmarksgame/binarytrees5`  | 14985902                                        | 3.2      | depth 16                                                    |
| `benchmarksgame/fannkuchredux` | 862930                                          | 2.6      | n = 9                                                       |
| `benchmarksgame/pidigits5`     | 112361924                                       | 3.9      | N = 3000 (default 27); hash of the output                   |
| `mlton/boyer`                  | #t                                              | 4.6      | 30 proofs                                                   |
| `mlton/checksum`               | 0                                               | 3.6      | (doit 2); Word8Array as a bloblet                           |
| `mlton/count-graphs`           | (0 0 1 1 2 2 4 4 20 20 250 250)                 | 25.2     | 1 `doit`, sizes 0–11                                        |
| `mlton/DLXSimulator`           | 477019433                                       | 5.1      | (doit 1); hash of the output; Word32 as `u32`               |
| `mlton/even-odd`               | #t                                              | 3.3      |                                                             |
| `mlton/fib`                    | 165580141                                       | 3.2      | 3 × fib 41                                                  |
| `mlton/flat-array`             | 1105694191                                      | 3.1      | (doit 10); Int32 overflow emulated                          |
| `mlton/imp-for`                | 10000000                                        | 2.5      | (doit 10)                                                   |
| `mlton/knuth-bendix`           | 24                                              | 6.1      | 1 completion                                                |
| `mlton/life`                   | 205                                             | 4.4      | (doit 1)                                                    |
| `mlton/logic`                  | 2                                               | 3.6      | 2 runs                                                      |
| `mlton/md5`                    | "59ebddd335d8defbcaf5b76c08c64278"              | 2.9      | 20 blocks (MLton: 100 000); Word32 as `u32` (was 3.3)       |
| `mlton/merge`                  | 0                                               | 2.6      | lists of 50 000 (MLton: 100 000): 8 MB native stack         |
| `mlton/mpuz`                   | "J = 0 I = 1 D = 8 E = 2 C = 5 B = 6 F …        | 8.2      | (doit 1)                                                    |
| `mlton/peek`                   | (640000000 580000000)                           | 6.7      | (doit 1)                                                    |
| `mlton/pidigits`               | 2881                                            | 4.5      | (doit 250): index of the 251st zero digit                   |
| `mlton/psdes-random`           | 2419669511                                      | 2.8      | 300 000 words (MLton: 150M); Word32 as `u32` (was 3.8)      |
| `mlton/ratio-regions`          | 144                                             | 4.2      | 30 × doit 24; had 1 procedure cellular (more than 8 values) |
| `mlton/smith-normal-form`      | -1027954043102083189860753402541358641712697245 | 4.5      | (doit 1); the entry the original checks for                 |
| `mlton/string-concat`          | 468705                                          | 3.4      | loop 4000                                                   |
| `mlton/tailfib`                | 701408733                                       | 3.0      | 50M × fib 44                                                |
| `mlton/tailmerge`              | 0                                               | 2.6      | (doit 200)                                                  |
| `mlton/tak`                    | 22                                              | 3.4      | 2 × tak 33 22 11                                            |
| `mlton/tyan`                   | ("a8b4c3 + 22 terms\n" "a7b5c3 + 20 ter…        | 4.7      | 3 × gb u6; the 92 basis lines                               |
| `mlton/vector-rev`             | 0                                               | 2.9      | 101 double reversals                                        |
| `mlton/vector32-concat`        | 399980000                                       | 3.3      | loop 600                                                    |
| `mlton/vector64-concat`        | 399980000                                       | 3.3      | loop 600                                                    |
| `mlton/zebra`                  | 3342                                            | 2.8      | 100 searches                                                |
| `ocaml/bdd`                    | 26116                                           | 2.8      | hwb 20, 10 tests                                            |
| `ocaml/boyer`                  | 30                                              | 4.7      | 3 × 10 proofs; 1 procedure runs as cellular code            |
| `ocaml/fib`                    | 433494437                                       | 2.6      | fib 42                                                      |
| `ocaml/hamming`                | 38618242609892126                               | 3.6      | 10 × to index 88 100; checksum of the reference numbers     |
| `ocaml/kb`                     | 242769383                                       | 6.1      | hash of the output = hash of the reference                  |
| `ocaml/quicksort`              | 60                                              | 3.6      | 30 × two sorts of 50 000                                    |
| `ocaml/sieve`                  | 121013308                                       | 3.8      | 100 × sieve 50 000                                          |
| `ocaml/soli`                   | 20277                                           | 2.9      | 100 solves                                                  |
| `ocaml/sorts`                  | 810716784                                       | 4.4      | hash of the output = hash of the reference                  |
| `ocaml/takc`                   | 140000                                          | 3.4      | 20 000 × tak 18 12 6                                        |
| `ocaml/taku`                   | 7000                                            | 4.0      | 1000 ×                                                      |

`md5` and `psdes-random` emulated Word32's bit operations with byte
tables until FX-26 had fixed-width integers; they now use `u32`, as
`DLXSimulator` does, and give the same answers. Their counts were kept, so
their times are now mostly start-up: at 100 times the count (2000 blocks,
30M words), `md5` computes in about 0.6 s where the tables took 2.7 s,
and `psdes-random` in 2.5 s where they took 5.6 s.

## Not ported

| benchmarks                                                                                             | what they need                                               |
| ------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------ |
| mlton: mandelbrot, matrix-multiply, fft, tsp, ray, zern, nucleic, barnes-hut, simple, raytrace, tensor | floats                                                       |
| mlton: output1, wc-input1, wc-scanStream                                                               | file I/O is the benchmark                                    |
| mlton: lexgen, vliw                                                                                    | feasible, not yet done: 1300 and 3700 lines, inputs to embed |
| mlton: mlyacc, model-elimination, fxp, hamlet                                                          | size: 7 000 to 23 000 lines                                  |
| ocaml: fft, almabench, nucleic                                                                         | floats                                                       |
| benchmarksgame: mandelbrot6, nbody, spectralnorm2, fasta3, fasta6                                      | floats (fasta: and text output)                              |
| benchmarksgame: regexredux2                                                                            | regular expressions, file input                              |
| benchmarksgame: knucleotide, knucleotide3, revcomp2                                                    | FASTA input from stdin, hash tables                          |
