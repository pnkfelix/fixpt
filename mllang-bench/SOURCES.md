# mllang-bench: provenance

Benchmark sources for ML-family languages, downloaded verbatim on 2026-09-29
from each suite's canonical GitHub repository at a pinned commit (fetched via
raw.githubusercontent.com).  Nothing here was built or run.  Upstream file
names are kept.

## Suites

| Directory                | Upstream repo                                                               | Commit                                   | Commit date | License                                                         |
|--------------------------|-----------------------------------------------------------------------------|------------------------------------------|-------------|-----------------------------------------------------------------|
| mlton-benchmark/         | https://github.com/MLton/mlton (benchmark/tests)                            | aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37 | 2026-09-19  | MLton HPND (LICENSE); some files carry their own headers        |
| ocaml-classic/           | https://github.com/ocaml/ocaml (testsuite/tests/misc, misc-kb, misc-unsafe) | 7da997d28b1ac57dd3a7108a865b327493fd4239 | 2026-09-29  | OCaml LGPL-2.1 w/ linking exception (LICENSE)                   |
| sandmark-benchmarksgame/ | https://github.com/ocaml-bench/sandmark (benchmarks/benchmarksgame)         | 5605805954a00497ed197c930641cddd580e1507 | 2024-08-27  | Revised BSD, Benchmarks Game (LICENSE); Sandmark repo Unlicense |

Notes:

- mlton-benchmark: each file defines `structure Main` with `doit : int -> unit`;
  the MLton driver (benchmark/main.sml) was not fetched.  Files headed
  "From the SML/NJ benchmark suite" descend from the classic SML/NJ set.
- mlton-benchmark/LICENSE is the MLton repo-root LICENSE; MLton has no
  benchmark-specific README.
- ocaml-classic: only the classic benchmark programs were taken (with their
  `.reference` expected outputs); GC-regression tests in the same
  directories were skipped.  ocaml-classic/kb/ is testsuite/tests/misc-kb.
- sandmark-benchmarksgame/SANDMARK-LICENSE.md is the Sandmark repo-root
  LICENSE.md; LICENSE there is the Benchmarks Game BSD license.

## Files

| Local file                                  | Lines | Commit       | URL                                                                                                                                        |
|---------------------------------------------|-------|--------------|--------------------------------------------------------------------------------------------------------------------------------------------|
| mlton-benchmark/tests/DLXSimulator.sml      | 2918  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/DLXSimulator.sml                    |
| mlton-benchmark/tests/barnes-hut.sml        | 1250  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/barnes-hut.sml                      |
| mlton-benchmark/tests/boyer.sml             | 931   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/boyer.sml                           |
| mlton-benchmark/tests/checksum.sml          | 46    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/checksum.sml                        |
| mlton-benchmark/tests/count-graphs.sml      | 537   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/count-graphs.sml                    |
| mlton-benchmark/tests/even-odd.sml          | 23    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/even-odd.sml                        |
| mlton-benchmark/tests/fft.sml               | 300   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/fft.sml                             |
| mlton-benchmark/tests/fib.sml               | 18    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/fib.sml                             |
| mlton-benchmark/tests/flat-array.sml        | 20    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/flat-array.sml                      |
| mlton-benchmark/tests/fxp.sml               | 15882 | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/fxp.sml                             |
| mlton-benchmark/tests/hamlet.sml            | 22901 | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/hamlet.sml                          |
| mlton-benchmark/tests/imp-for.sml           | 32    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/imp-for.sml                         |
| mlton-benchmark/tests/knuth-bendix.sml      | 602   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/knuth-bendix.sml                    |
| mlton-benchmark/tests/lexgen.sml            | 1325  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/lexgen.sml                          |
| mlton-benchmark/tests/life.sml              | 157   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/life.sml                            |
| mlton-benchmark/tests/logic.sml             | 369   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/logic.sml                           |
| mlton-benchmark/tests/mandelbrot.sml        | 74    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/mandelbrot.sml                      |
| mlton-benchmark/tests/matrix-multiply.sml   | 59    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/matrix-multiply.sml                 |
| mlton-benchmark/tests/md5.sml               | 283   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/md5.sml                             |
| mlton-benchmark/tests/merge.sml             | 31    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/merge.sml                           |
| mlton-benchmark/tests/mlyacc.sml            | 7292  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/mlyacc.sml                          |
| mlton-benchmark/tests/model-elimination.sml | 8801  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/model-elimination.sml               |
| mlton-benchmark/tests/mpuz.sml              | 141   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/mpuz.sml                            |
| mlton-benchmark/tests/nucleic.sml           | 3666  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/nucleic.sml                         |
| mlton-benchmark/tests/output1.sml           | 22    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/output1.sml                         |
| mlton-benchmark/tests/peek.sml              | 72    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/peek.sml                            |
| mlton-benchmark/tests/pidigits.sml          | 138   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/pidigits.sml                        |
| mlton-benchmark/tests/psdes-random.sml      | 73    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/psdes-random.sml                    |
| mlton-benchmark/tests/ratio-regions.sml     | 625   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/ratio-regions.sml                   |
| mlton-benchmark/tests/ray.sml               | 459   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/ray.sml                             |
| mlton-benchmark/tests/raytrace.sml          | 2388  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/raytrace.sml                        |
| mlton-benchmark/tests/simple.sml            | 931   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/simple.sml                          |
| mlton-benchmark/tests/smith-normal-form.sml | 398   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/smith-normal-form.sml               |
| mlton-benchmark/tests/string-concat.sml     | 18    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/string-concat.sml                   |
| mlton-benchmark/tests/tailfib.sml           | 23    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/tailfib.sml                         |
| mlton-benchmark/tests/tailmerge.sml         | 40    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/tailmerge.sml                       |
| mlton-benchmark/tests/tak.sml               | 20    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/tak.sml                             |
| mlton-benchmark/tests/tensor.sml            | 2971  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/tensor.sml                          |
| mlton-benchmark/tests/tsp.sml               | 492   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/tsp.sml                             |
| mlton-benchmark/tests/tyan.sml              | 1016  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/tyan.sml                            |
| mlton-benchmark/tests/vector-rev.sml        | 26    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/vector-rev.sml                      |
| mlton-benchmark/tests/vector32-concat.sml   | 19    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/vector32-concat.sml                 |
| mlton-benchmark/tests/vector64-concat.sml   | 19    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/vector64-concat.sml                 |
| mlton-benchmark/tests/vliw.sml              | 3699  | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/vliw.sml                            |
| mlton-benchmark/tests/wc-input1.sml         | 35    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/wc-input1.sml                       |
| mlton-benchmark/tests/wc-scanStream.sml     | 42    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/wc-scanStream.sml                   |
| mlton-benchmark/tests/zebra.sml             | 298   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/zebra.sml                           |
| mlton-benchmark/tests/zern.sml              | 604   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/zern.sml                            |
| mlton-benchmark/tests/DATA/chess.gml        | 271   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/DATA/chess.gml                      |
| mlton-benchmark/tests/DATA/hamlet-input.sml | 9     | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/DATA/hamlet-input.sml               |
| mlton-benchmark/tests/DATA/ml.grm           | 732   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/DATA/ml.grm                         |
| mlton-benchmark/tests/DATA/ml.lex           | 173   | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/DATA/ml.lex                         |
| mlton-benchmark/tests/DATA/ndotprod.s       | 97    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/DATA/ndotprod.s                     |
| mlton-benchmark/tests/DATA/ray              | 3     | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/benchmark/tests/DATA/ray                            |
| mlton-benchmark/LICENSE                     | 29    | aa2fd1ad9b91 | https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/LICENSE                                             |
| ocaml-classic/bdd.ml                        | 219   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/bdd.ml                         |
| ocaml-classic/bdd.reference                 | 1     | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/bdd.reference                  |
| ocaml-classic/boyer.ml                      | 880   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/boyer.ml                       |
| ocaml-classic/boyer.reference               | 1     | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/boyer.reference                |
| ocaml-classic/fib.ml                        | 11    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/fib.ml                         |
| ocaml-classic/fib.reference                 | 1     | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/fib.reference                  |
| ocaml-classic/hamming.ml                    | 93    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/hamming.ml                     |
| ocaml-classic/hamming.reference             | 100   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/hamming.reference              |
| ocaml-classic/nucleic.ml                    | 3225  | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/nucleic.ml                     |
| ocaml-classic/nucleic.reference             | 1     | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/nucleic.reference              |
| ocaml-classic/sieve.ml                      | 44    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/sieve.ml                       |
| ocaml-classic/sieve.reference               | 1     | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/sieve.reference                |
| ocaml-classic/sorts.ml                      | 4454  | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/sorts.ml                       |
| ocaml-classic/sorts.reference               | 198   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/sorts.reference                |
| ocaml-classic/takc.ml                       | 10    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/takc.ml                        |
| ocaml-classic/takc.reference                | 1     | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/takc.reference                 |
| ocaml-classic/taku.ml                       | 10    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/taku.ml                        |
| ocaml-classic/taku.reference                | 1     | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc/taku.reference                 |
| ocaml-classic/kb/equations.ml               | 100   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/equations.ml                |
| ocaml-classic/kb/equations.mli              | 18    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/equations.mli               |
| ocaml-classic/kb/kb.ml                      | 173   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/kb.ml                       |
| ocaml-classic/kb/kb.mli                     | 17    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/kb.mli                      |
| ocaml-classic/kb/kbmain.ml                  | 71    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/kbmain.ml                   |
| ocaml-classic/kb/kbmain.reference           | 273   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/kbmain.reference            |
| ocaml-classic/kb/orderings.ml               | 84    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/orderings.ml                |
| ocaml-classic/kb/orderings.mli              | 17    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/orderings.mli               |
| ocaml-classic/kb/terms.ml                   | 121   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/terms.ml                    |
| ocaml-classic/kb/terms.mli                  | 17    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-kb/terms.mli                   |
| ocaml-classic/almabench.ml                  | 331   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-unsafe/almabench.ml            |
| ocaml-classic/almabench.reference           | 8     | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-unsafe/almabench.reference     |
| ocaml-classic/fft.ml                        | 178   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-unsafe/fft.ml                  |
| ocaml-classic/fft.reference                 | 15    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-unsafe/fft.reference           |
| ocaml-classic/quicksort.ml                  | 82    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-unsafe/quicksort.ml            |
| ocaml-classic/quicksort.reference           | 2     | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-unsafe/quicksort.reference     |
| ocaml-classic/soli.ml                       | 100   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-unsafe/soli.ml                 |
| ocaml-classic/soli.reference                | 50    | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/testsuite/tests/misc-unsafe/soli.reference          |
| ocaml-classic/LICENSE                       | 203   | 7da997d28b1a | https://raw.githubusercontent.com/ocaml/ocaml/7da997d28b1ac57dd3a7108a865b327493fd4239/LICENSE                                             |
| sandmark-benchmarksgame/LICENSE             | 18    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/LICENSE          |
| sandmark-benchmarksgame/README.md           | 3     | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/README.md        |
| sandmark-benchmarksgame/binarytrees5.ml     | 44    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/binarytrees5.ml  |
| sandmark-benchmarksgame/fannkuchredux.ml    | 125   | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/fannkuchredux.ml |
| sandmark-benchmarksgame/fasta3.ml           | 95    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/fasta3.ml        |
| sandmark-benchmarksgame/fasta6.ml           | 121   | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/fasta6.ml        |
| sandmark-benchmarksgame/knucleotide.ml      | 89    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/knucleotide.ml   |
| sandmark-benchmarksgame/knucleotide3.ml     | 204   | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/knucleotide3.ml  |
| sandmark-benchmarksgame/mandelbrot6.ml      | 49    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/mandelbrot6.ml   |
| sandmark-benchmarksgame/nbody.ml            | 112   | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/nbody.ml         |
| sandmark-benchmarksgame/pidigits5.ml        | 53    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/pidigits5.ml     |
| sandmark-benchmarksgame/regexredux2.ml      | 60    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/regexredux2.ml   |
| sandmark-benchmarksgame/revcomp2.ml         | 33    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/revcomp2.ml      |
| sandmark-benchmarksgame/spectralnorm2.ml    | 44    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/benchmarks/benchmarksgame/spectralnorm2.ml |
| sandmark-benchmarksgame/SANDMARK-LICENSE.md | 24    | 5605805954a0 | https://raw.githubusercontent.com/ocaml-bench/sandmark/5605805954a00497ed197c930641cddd580e1507/LICENSE.md                                 |
