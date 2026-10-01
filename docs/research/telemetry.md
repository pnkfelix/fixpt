# Telemetry: clocks, allocation and the collector, seen from FX-26

2026-09-29. The user asked for performance-monitoring primitives in FX-26's
standard library and its runtimes: ways to see times, peak heap use, the
mark/cons ratio, how many minor and major collections ran (with regions and
reaps counted as their strategy calls for), and any other local telemetry
that helps explain performance. This note surveys what other runtimes give,
applies each kind of facility to FX-26's machines and to its type-and-effect
system, and recommends a first set of operations and a staged plan. Nothing
is implemented here.

## The recommendation, in brief

- **One region for everything observed: `@telemetry`.** Every operation that
  reads a clock or a counter has the effect `(maxeff (read @telemetry) (write
  @telemetry))`, written `observes` below (a `define-effect` abbreviation, as
  `checks` is in `check.fx`). The write is what stops a compiler from
  treating two reads as the same, dropping one, or hoisting one out of a
  loop, using the rules it already follows: the effect summary is 2,
  "anything else". `@telemetry` is a constant, so it is never masked. It is
  not licensed, so speculation never runs code that observes. Pure code
  stays pure: what a telemetry read returns is unspecified beyond
  monotonicity, so moving, duplicating or dropping pure code changes nothing
  the semantics promises (see "Typing").
- **A first set of fourteen operations** (table in "The first set"): two
  clocks (`real-time-ns`, `cpu-time-ns`); cumulative counters
  (`gc-time-ns`, `minor-collections`, `major-collections`,
  `words-allocated`, `region-words-allocated`, `words-copied`); sizes
  (`heap-words-in-use`, `peak-heap-words`); a nestable measured run
  (`telemetry-begin`, `telemetry-end`, which gives a `run-stats` product);
  `black-box`, an identity the compiler cannot see through, for benchmarks
  (named after Chez Scheme 10's operation of the same meaning);
  and `run-with-stats`, the thunk runner, with `(time e)` as a derived form
  for it. All but `run-with-stats` and `black-box` return naturals and allocate
  nothing, so reading them does not disturb what they count.
- **The heap must start recording** minor and major time apart, the longest
  pause of each kind, words promoted by minor collections apart from words
  copied by major ones, the peak of words in use (sampled on entry to each
  collection, which catches the true high-water mark), and a small stack of
  snapshots for `telemetry-begin`. None of this touches an allocation path.
  Everything is updated once per collection or once per region chunk.
- **Rust-side knobs first, as cheap wins:** `FIXPT_GC_TRACE=1` (one line per
  collection, as V8's `--trace-gc`, GHC's `+RTS -S`, Go's `GODEBUG=gctrace=1`
  and Larceny's `-annoy-user` do) and `FIXPT_GC_SUMMARY=1` (a summary at
  exit, as `+RTS -s` and `@MLton gc-summary` do), plus two fixes to what
  exists today (in "What fixpt measures today").
- **Worked examples** (next section): nine toy programs, each beside the
  Python, Node, Racket, OCaml, Java or Chez snippet it comes from. The
  typing of every proposal is checked today with `fixpt check`, over a
  mock of the operations, in `docs/research/examples/telemetry/`.

## Worked examples

Small programs, one per proposal, each next to the snippet from the
runtime the idea comes from. The rest of this note explains them.

**What is FX-26 today and what is proposed.** None of the operations below
exist in FX-26 today: there is no clock, no counter and no `@telemetry` in
standard.rs, and `%gc-count` is reachable only from fixpt's Scheme. But
everything the proposal adds to the *type system* can be written today,
because `@telemetry` is just a region constant and `observes` just a
`define-effect`. So each file under `docs/research/examples/telemetry/`
begins with a **mock prelude**: the proposed operations, written as
ordinary FX-26 definitions with the proposed types, over a fake counter
kept in a `ref` at `@telemetry`. The checker's verdicts on these files are
therefore the verdicts the proposal would give. The numbers they compute
are not measurements. Code blocks marked `; PROPOSED` use operations or
forms that are not even mocked, and were not checked.

One difference from the real thing: the mock operations are globals, so
the printed types also say `(read (globals real-time-ns …))`. The real
operations would be standard constants, like `+`, which read no global.
The types quoted below leave those `globals` atoms out.

Every file was run with `fixpt check FILE` (both checkers, which agree on
all of them) and `fixpt eval FILE`, under a 60-second limit, with the
binary in `target/release` on 2026-09-29:

| File                      | Shows                                                     | `fixpt check`     | `fixpt eval`        |
| ------------------------- | --------------------------------------------------------- | ----------------- | ------------------- |
| `time-fib.fx`             | two clock reads around `fib 25`; pinning with `black-box` | passes            | `76025`             |
| `pure-refused.fx`         | a `pure` procedure that reads a clock                     | refused, as meant | (refused)           |
| `masked-not.fx`           | `letregion` masks its own region, never `@telemetry`      | passes            | `1000` (stub clock) |
| `count-collections.fx`    | collections and words allocated while building a list     | passes            | `0` (stub counters) |
| `black-box.fx`            | a benchmark loop, dropped, hoisted and pinned             | passes            | `0`                 |
| `run-with-stats.fx`       | the typed thunk runner, on a pure and an allocating thunk | passes            | `5000125025`        |
| `place-words.fx`          | words allocated in one arena, read inside its body        | passes            | `0` (stub counter)  |
| `place-escape-refused.fx` | the same reading kept for after the arena ends            | refused, as meant | (refused)           |

The snippets from other runtimes: the Python, Node and Java ones were run
here (Python 3.14.7, Node 26.0.0, OpenJDK 21.0.11). The Chez, Racket,
OCaml, Haskell, Larceny and Erlang ones are written from the documentation or
source cited in the survey and with each example, and were not run.

### E1. Timing `fib 25`

The simplest use: read a clock, run the work, read it again. From
`time-fib.fx` (checked; the prelude is left out here):

```
(define fib (subr pure (int) int)
  (letrec ((fib (subr pure (int) int)
             (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))))
    fib))

(define* time-fib (subr observes (int) (productof (value int) (ns int)))
  (lambda (n)
    (let* ((t0 (real-time-ns))
           (v  (fib n))
           (t1 (real-time-ns)))
      (product (value v) (ns (- t1 t0))))))
```

Python (run here) and Node (run here) are the same shape, with no effect
in any type:

```python
t0 = time.perf_counter_ns()
v = fib(25)
t1 = time.perf_counter_ns()          # 75025 5278625 ns
```

```javascript
const t0 = process.hrtime.bigint();
const v = fib(25);
const t1 = process.hrtime.bigint();  // 75025 1062458n ns
```

The closest typed precedent is Haskell, whose clock is in `IO`
(`getMonotonicTimeNSec :: IO Word64`, base-4.22.0.0, GHC.Clock). Its pure
`fib n` may float out of the window too, and is forced with `seq` or
`evaluate` to pin it; FX-26's `black-box` plays that role:

```haskell
timeFib n = do t0 <- getMonotonicTimeNSec
               v  <- evaluate (fib n)
               t1 <- getMonotonicTimeNSec
               return (v, t1 - t0)
```

What it shows:
- `real-time-ns : (subr observes () nat)`, where `observes` is `(maxeff
  (read @telemetry) (write @telemetry))`.
- `fib` checks as `(subr pure (int) int)`. `time-fib` must say
  `observes`, and `fixpt check` prints its type as `(subr (maxeff (read
  @telemetry) (write @telemetry)) (int) (productof (value int) (ns
  int)))`. Every caller of `time-fib` gets the effect too.
- Because `(fib n)` is pure, the semantics lets a compiler compute it
  before `t0` or after `t1` ("Pure code stays pure", under "Typing"). The
  file's second version pins it, as Chez's manual does in its fourth
  example (E4):

  ```
  (v (black-box (fib (black-box n))))
  ```

  `(black-box n)` is summary 2, so it stays after `t0`. The outer
  `black-box` stays before `t1`. And `fib`'s call depends on the one and
  feeds the other.

### E2. What the effect checker says

A procedure that claims `pure` and reads a clock is refused.
`pure-refused.fx` (checked; refused as intended; the message is shown
without the mock's `globals` atom):

```
(define seeded (subr pure (int) int)
  (lambda (x) (+ x (real-time-ns))))
```

```
! pure-refused.fx:10:3: `seeded` is declared a (subr pure (int) int): a (subr pure (int) int)
  is expected here, and this is a (subr (maxeff (read @telemetry) (write @telemetry)) (int) int)
```

Masking removes what a body does to a region it binds, but `@telemetry`
is a constant, so it is never masked. From `masked-not.fx` (checked):

```
(define local-work (subr pure (int) int)           ; checks: r is masked
  (lambda (n)
    (letregion r
      (let ((c (the (ref int r) (new 0))))
        (begin (set c (+ (get c) n)) (get c))))))

(define* timed-local-work (subr observes (int) int) ; must say observes
  (lambda (n)
    (let* ((t0 (real-time-ns)) (v (local-work n)) (t1 (real-time-ns)))
      (- t1 t0))))
```

What it shows: `timed-local-work` returns only a difference of two
readings, yet its type says `observes`, as "Masking" (under "Typing")
intends, since its result is not a function of its argument. No other
runtime surveyed has a type that could say this. Haskell's `IO` is the
nearest, and it does not separate reading a clock from any other I/O.

### E3. Counting collections while building a list

Cumulative counters, read before and after, and differenced. From
`count-collections.fx` (checked; the counters are stubs, so the answer is
0):

```
(define* build-and-count (subr (maxeff (alloc @l) spin observes) (int) gc-delta)
  (lambda (n)
    (let* ((m0 (minor-collections)) (j0 (major-collections)) (w0 (words-allocated))
           (xs (iota n nil))
           (w1 (words-allocated)) (j1 (major-collections)) (m1 (minor-collections)))
      (product (minor (- m1 m0)) (major (- j1 j0)) (words (- w1 w0))))))
```

Python (run here: `[46, 4, 0]` collections per generation, and
`(10390103, 10390260)` bytes, current and peak):

```python
def collections(): return [g["collections"] for g in gc.get_stats()]
tracemalloc.start()
before = collections()
xs = [(i, None) for i in range(100_000)]
after = collections()
print([a - b for a, b in zip(after, before)], tracemalloc.get_traced_memory())
```

OCaml (`Gc.quick_stat`, and `Sys.opaque_identity` to keep `xs`; gc.mli
and sys.mli at commit `7da997d28b1a`):

```ocaml
let build_and_count n =
  let s0 = Gc.quick_stat () in
  let xs = List.init n (fun i -> i) in
  let s1 = Gc.quick_stat () in
  ignore (Sys.opaque_identity xs);
  (s1.minor_collections - s0.minor_collections,
   s1.major_collections - s0.major_collections,
   s1.minor_words -. s0.minor_words)
```

Racket fills a vector the caller made once (slot 3 is the collection
count; Racket 9.3 reference, runtime.html):

```racket
(define v (make-vector 12 0))
(vector-set-performance-stats! v #f) (define g0 (vector-ref v 3))
(define xs (build-list 100000 values))
(vector-set-performance-stats! v #f) (- (vector-ref v 3) g0)
```

Java sums the collector beans (run here; 0 collections for a million
small arrays with the default heap):

```java
static long gcs() { long n = 0;
  for (GarbageCollectorMXBean b : ManagementFactory.getGarbageCollectorMXBeans())
    n += b.getCollectionCount();
  return n; }
```

What it shows:
- Each counter is `(subr observes () nat)`. They are cumulative since the
  heap was made, and allocate nothing, so reading them does not disturb
  them. OCaml's `quick_stat` and Racket's filled vector take the same
  care. Python's `get_stats` builds a list of dicts each time.
- `build-and-count`'s effect is the list's `(alloc @l)` and `spin`, plus
  `observes`.
- `(iota n nil)` allocates, which is summary 2, as each counter read is.
  So the build stays between the reads even though `xs` is unused. A
  *pure* builder (one that masks its region) could move out of the window,
  and would need `black-box`, as in E1.
- A test on these numbers asserts only relations, such as `(>= words (* 2
  n))`, never values: the counts differ between machines ("Allocation
  counters").

### E4. A benchmark loop that disappears without `black-box`

From `black-box.fx` (checked). The mock `black-box` has the proposed type
`(poly ((t type)) (subr observes (t) t))`:

```
;; 1. (fib 20) is pure, ends, and is unused: summary 0, so it may be dropped.
(define* loop-dropped (subr spin (int) int)
  (lambda (k) (if (= k 0) 0 (begin (fib 20) (loop-dropped (- k 1))))))

;; 2. Consumed, but pure and loop-invariant: it may be computed once, before the loop.
(define* loop-hoisted (subr (maxeff observes spin) (int) int)
  (lambda (k) (if (= k 0) 0 (begin (black-box (fib 20)) (loop-hoisted (- k 1))))))

;; 3. Input and output through black-box: fib runs k times.
(define* loop-pinned (subr (maxeff observes spin) (int) int)
  (lambda (k) (if (= k 0) 0 (begin (black-box (fib (black-box 20))) (loop-pinned (- k 1))))))
```

Chez Scheme's manual gives the same three cases, and one more for safe
mode. This is its fourth, the pinned one (`csug/system.stex` at commit
`d9e76eb8e4f2`, https://github.com/cisco/ChezScheme):

```scheme
(time
 (let ([to-power (black-box 100)])
   (let loop ([i 1000])
     (unless (zero? i)
       ; arithmetic really performed every iteration, since `to-power` value
       ; is assumed unknown, and `expt` result is assumed to be used
       (black-box (expt 2 to-power))
       (loop (sub1 i))))))
```

OCaml's `Sys.opaque_identity` is the same operation. Its documentation
gives this loop (sys.mli at commit `7da997d28b1a`):

```ocaml
for _round = 1 to 100_000 do
  ignore (Sys.opaque_identity (my_pure_computation ()))
done
```

JMH's `Blackhole` takes the result, and reads the input from a `@State`
field so it cannot be folded (`JMHSample_09_Blackholes.java` at commit
`a194eead0136` of https://github.com/openjdk/jmh):

```java
@Benchmark
public void measureRight_2(Blackhole bh) {
    bh.consume(compute(x1));
    bh.consume(compute(x2));
}
```

What it shows:
- The checker gives `loop-dropped` the type `(subr spin (int) int)`:
  nothing in it observes, so everything a compiler may do to pure code it
  may do there.
- `loop-hoisted` and `loop-pinned` say `observes`.
- No fixpt compiler uses effect summaries yet (fx26.md, "Effect
  summaries"), so today all three loops run `fib` k times. The example
  shows what the summaries *permit*, which is what a benchmark must be
  written against.

### E5. `run-with-stats` and `(time e)`

The thunk runner, written in FX-26 over `telemetry-begin` and
`telemetry-end` as "The first set" proposes. From `run-with-stats.fx`
(checked; the two operations are stubs, and the prelude and `run-stats`
type are as in "The first set"):

```
(define* run-with-stats
  (poly ((t type) (e effect))
    (subr (maxeff e observes) ((subr e () t)) (productof (value t) (stats run-stats))))
  (plambda ((t type) (e effect))
    (lambda ((thunk (subr e () t)))
      (let* ((k (telemetry-begin)) (v (thunk)) (s (telemetry-end k)))
        (product (value v) (stats s))))))

(define* time-fib (subr observes () (productof (value int) (stats run-stats)))
  (lambda () (run-with-stats (lambda () (fib 25)))))
(define* time-list (subr (maxeff (alloc @l) (read @l) spin observes) ()
                         (productof (value int) (stats run-stats)))
  (lambda () (run-with-stats (lambda () (add-up (iota 100000 nil) 0)))))
```

```
; PROPOSED: (time e) as a derived form, read as (run-with-stats (lambda () e))
(extract (extract (time (fib 25)) stats) minor)
```

Larceny's version prints, and returns the value (`memstats.sch` and
`lib/Base/macros.sch`, on disk at commit `fef550c7d392`):

```scheme
(run-with-stats (lambda () (fib 25)))   ; prints "Words allocated: ...", "Elapsed time...: ...", ...
(define-syntax time
  (syntax-rules ()
    ((time ?expr)
     (run-with-stats (lambda () ?expr)))))
```

Chez's `sstats-difference` does the same by hand (CSUG 10.4.0, "Timing
and Statistics"). Racket's `time-apply` returns its statistics as values
("a list containing the result(s) …, the number of milliseconds of CPU
time …, the number of "real" milliseconds …, and the number of
milliseconds of CPU time … spent on garbage collection", reference 9.3,
time.html):

```scheme
(let* ([s0 (statistics)] [v (fib 25)] [s1 (statistics)])   ; Chez
  (sstats-print (sstats-difference s1 s0))
  v)
```

```racket
(define-values (results cpu-ms real-ms gc-ms) (time-apply fib '(25)))
```

What it shows:
- `run-with-stats` is polymorphic in the thunk's effect `e`, and the
  checker gives each call site `e` plus `observes`. For `time-fib` that is
  just `observes`. For `time-list` it is `(maxeff (alloc @l) (read @l)
  spin observes)`.
- The result is a product, so taking the statistics apart with `extract`
  is pure.
- Like Racket's `time-apply`, and unlike Larceny's and Chez's `time`, it
  prints nothing, since FX-26 has no output.
- Inside `run-with-stats` the call `(thunk)` has an effect variable, which
  is summary 3, so it stays between `telemetry-begin` and `telemetry-end`.
  A compiler that inlines it at `e` = `pure` would see a pure call it may
  move, which is E1's question again. So the standard definition should
  either keep its summary when inlined, or take the result through
  `black-box`. This is a detail left for stage 2.

Nesting works by tokens (proposed semantics; the stubs do not model it).
The outer run's `peak-words` is at least the inner run's:

```
; PROPOSED semantics
(run-with-stats
  (lambda ()
    (let ((inner (run-with-stats (lambda () (iota 100000 nil)))))
      (add-up (extract inner value) 0))))
```

### E6. Words allocated in one arena

A stage-3 operation (see "Regions and reaps") that takes the place as a value, as `rcons` does. From
`place-words.fx` (checked; stub counter):

```
place-words-allocated : (poly ((p place)) (subr (maxeff (read p) observes) ((place p)) nat))

(define* arena-cost (subr (maxeff observes spin) (int) int)
  (lambda (n)
    (letrena r
      (letrec ((build (subr (maxeff (alloc r) spin) (int (listof int r)) (listof int r))
                 (lambda (i acc) (if (= i 0) acc (build (- i 1) (rcons r i acc))))))
        (let* ((w0 (place-words-allocated r))
               (xs (build n nil))
               (w1 (place-words-allocated r)))
          (- w1 w0))))))
```

Keeping the reading for after the arena ends is refused.
`place-escape-refused.fx` (checked; refused as intended; the message is
shown without the mock's `globals` atom):

```
(define later (subr pure () (subr observes () nat))
  (lambda () (letrena r (lambda () (place-words-allocated r)))))
```

```
! place-escape-refused.fx:12:14: the value of `letrena r` would outlive its region: its type is
  (subr (maxeff (read @telemetry) (read r) (write @telemetry)) () nat)
```

The nearest precedent is per memory pool, not per region. The JVM gives a
usage and peak for each pool (Java SE 21, `MemoryPoolMXBean`; run here,
it prints lines such as `Metaspace 10348232`):

```java
for (MemoryPoolMXBean p : ManagementFactory.getMemoryPoolMXBeans())
    System.out.println(p.getName() + " " + p.getPeakUsage().getUsed());
```

What it shows:
- The `(read r)` and `(alloc r)` in `arena-cost`'s body are masked when
  the arena ends, and `observes` is not.
- `(read p)` in the operation's type is what ties a reading to the
  place's lifetime. It uses the rule that already keeps a closure over
  `r` inside the body, with no new check.

### E7. No collection hooks: a pull-style buffer instead

The push style, from OCaml (`Gc.create_alarm`, gc.mli at `7da997d28b1a`;
a sketch, not run) and Python
(`gc.callbacks`, run here: it prints `start 0`, `stop 0`, … while the list
is built):

```ocaml
let _alarm = Gc.create_alarm (fun () -> incr majors)   (* runs at the end of major cycles *)
```

```python
def on_gc(phase, info): print(phase, info["generation"])
gc.callbacks.append(on_gc)          # runs arbitrary code at every collection
xs = [[i] for i in range(100_000)]
```

```
; REJECTED, for contrast: what a hook would cost the types
on-collection : (poly ((e effect)) (subr observes ((subr e () unit)) unit))
;; any allocation may now run a hook of effect e, so cons could no longer
;; be (subr (alloc r) (t1 t2) (pairof t1 t2 r)): every pure procedure
;; that allocates would have to carry e.
```

The pull style, from Racket (a log receiver on topic `'GC`; each event's
data is a `gc-info` prefab; reference 9.3):

```racket
(define r (make-log-receiver (current-logger) 'debug 'GC))
(collect-garbage 'minor)
(sync/timeout 0 r)   ; a vector: the level, a message, a gc-info prefab, and 'GC
```

```
; PROPOSED: the pull-style event buffer (see "Collection event hooks")
(define-type gc-event (productof (kind symbol) (pause-ns nat) (promoted nat) (live-after nat)))
collection-events-since : (poly ((r region)) (subr (maxeff observes (alloc r)) (nat) (listof gc-event r)))
```

What it shows: a buffer the program reads when it chooses costs one more
`(alloc r)` at the read, and leaves every other procedure's type alone.

### E8. Tools, not language: the trace and the sampling profiler

These are environment variables and REPL commands, with no FX-26 syntax at
all.

```
; PROPOSED, stage 1: one line per collection on stderr
$ FIXPT_GC_TRACE=1 fixpt eval bench/lists.fx
; PROPOSED: a sampled allocation profile by source position
> ,profile (rounds 3000 0)
```

Node's `--trace-gc` line, run here (wrapped):

```
[36527:0x96880c000]  6 ms: Scavenge 1.4 (3.0) -> 0.7 (3.5) MB, pooled: 0.0 MB, 0.17 / 0.00 ms
    (average mu = 1.000, current mu = 1.000) allocation failure;
```

OCaml's `Gc.Memprof` is the model for the profiler: a sample every 1/rate
words, found by moving the allocation limit (gc.mli at `7da997d28b1a`; the
rate is "in samples per word", and "1e-4 has no visible effect on
performance"). A sketch, not run:

```ocaml
let tracker = { Gc.Memprof.null_tracker with
                alloc_minor = (fun info -> Hashtbl.replace sites info.callstack (); None) } in
let _p = Gc.Memprof.start ~sampling_rate:1e-4 tracker in
run_workload ();
Gc.Memprof.stop ()
```

### E9. Deterministic work

```
; PROPOSED (see "Deterministic work")
(define* work-of-fib (subr observes (int) int)
  (lambda (n) (let* ((w0 (work-units)) (v (black-box (fib (black-box n)))) (w1 (work-units)))
                (- w1 w0))))
```

Erlang's reductions are the model (`erlang:statistics/1`, OTP 29.1.1):

```erlang
{R0, _} = erlang:statistics(exact_reductions),
V = fib(25),
{R1, _} = erlang:statistics(exact_reductions),
R1 - R0.
```

What it shows: `work-units` has the same type as the other counters. On
one machine its difference is the same on every run, so it could be a
column in a commit's bench table where time cannot.

## What fixpt measures today

| What                                 | Where                         | Updated                                        | Notes                                                                      |
| ------------------------------------ | ----------------------------- | ---------------------------------------------- | -------------------------------------------------------------------------- |
| `gc_count`                           | `Heap` (heap.rs)              | end of each **major** collection (`collect`)   | Majors only since the nursery landed                                       |
| `minor_count`                        | `Heap`                        | end of each minor collection (young.rs)        |                                                                            |
| `words_copied`                       | `Heap`                        | both kinds                                     | Minor promotions and major copies summed                                   |
| `gc_nanos`                           | `Heap`                        | both kinds, `Instant` around each              | Wall-clock time; minor and major summed                                    |
| `max_major_nanos`, `max_minor_nanos` | `Heap`                        | end of each collection of that kind            | The longest pause of each kind (stage 1, 2026-09-30)                       |
| `peak_words`                         | `Heap`                        | start of each collection                       | Most words in use, sampled when the heap is fullest (stage 1)              |
| `trace`                              | `Heap`                        | set by `FIXPT_GC_TRACE`                        | A line per collection on stderr: kind, pause, copied, in use (stage 1)     |
| `allocated()`                        | `Heap`                        | computed from `words_allocated` and the tops   | Nursery and semispace only; exact even with inline allocation              |
| `region_words()`                     | `Heap` (regions.rs)           | at chunk turnover and region exit, plus fills  | Arenas and reaps together; no per-region total once a chunk is full        |
| `region_in_use(h)`                   | `Heap`                        | computed                                       | Per live region; for a reap, after a collection, only what was reachable   |
| `used()`, `capacity()`               | `Heap`                        | computed                                       | Instantaneous; the peak is `peak_words`                                    |
| code area `used`                     | `CodeArea` (code.rs)          | on allocation and sweep                        | Not exposed                                                                |
| `%gc-count`                          | runtime primitive (prim.rs)   |                                                | Scheme only; returns `gc_count`, so majors only                            |
| `%gc-words-copied`                   | runtime primitive             |                                                | Scheme only                                                                |
| `%gc-every!`                         | runtime primitive             |                                                | Stress policy                                                              |
| `%sro`                               | engine primitive              |                                                | Larceny's SRO. Deliberately in no language's standard environment          |
| `Profile`                            | fixpt-engine cellular.rs      | per cell, Rust machine only                    | Cells run and words allocated, by word (`FIXPT_PROFILE`)                   |
| callout counts                       | fixpt-native cellular.rs      | per call-out                                   | `FIXPT_CALLOUTS`, instrumented build path                                  |
| phase laps                           | fixpt-fx26 tests/bootstrap.rs | per phase                                      | `probe_phases_as_register_code`; `FIXPT_GC_REPORT`, `FIXPT_TIME_PHASES`    |
| summary                              | fixpt-cli fx26.rs             | at the end of `fixpt eval`                     | `FIXPT_GC_SUMMARY` (or `FIXPT_GC_REPORT`); with the peak and pauses        |
| `fixpt bench` columns                | fixpt-cli bench.rs            | the native run's last                          | `M words` allocated and `GCs`, minor and major (stage 1)                   |
| `run-word` time                      | prim.rs `%run-word`           | per run                                        | `FIXPT_TIME_WORDS`                                                         |
| `run_nanos`, `compile_nanos`         | `Runtime` (runtime.rs)        | around each form's run and its code generation | The FX-26 REPL's, natively, as cellular words, or lowered (2026-09-30)     |
| `,time E`                            | fixpt-cli fx26.rs             | per form                                       | Check, codegen and run times, then allocation and collections, for E alone |

There are no clocks at all in the Scheme runtime or FX-26's standard
environment. FX-26's standard environment has no output either, so an FX-26
`time` has to *return* its statistics, not print them.

Found while surveying. These are small, and worth fixing before any of the
rest:

1. **`Profile`'s name cache goes stale at minor collections.** It maps a
   word's raw address to its name and clears the map when `gc_count`
   changes (fixpt-engine/src/cellular.rs, `Profile::count`). Cellular words
   are made by `make_bloblet`, which allocates in the nursery when there is
   one (`Heap::bump`), and a minor collection moves them. So after a minor
   collection a new word at a reused nursery address can be charged under a
   dead word's name. The fix is to key the cache on `gc_count + minor_count`,
   as `fixpt-native/tests/cellular.rs` already counts collections.
2. **Reports that print `gc_count` now leave out the minor collections.**
   These are `probe_phases_as_register_code`'s `lap`, `FIXPT_GC_REPORT` in
   bootstrap.rs, and `%gc-count`. Larceny keeps both counts, `gc-counter`
   (all collections) and `major-gc-counter`. So should these reports.

## Survey: what other runtimes give

Where each entry comes from:
- **Larceny**: its source on disk (`~/Dev/LangPlay/larceny`).
- **Python, Node, the JVM and Lua**: checked against the installations on
  this machine (Python 3.14.7, Node 26.0.0, OpenJDK 21.0.11's `javap` and
  `jfr metadata`, Lua 5.5), and against their documentation.
- **Everything else**: checked on 2026-09-29 against official
  documentation or source online. Each entry gives the URL, and the
  version or commit where there is one.
- **MIT/GNU Scheme**: gnu.org refused the fetch (HTTP 403) and Savannah
  timed out, so the MIT entry cites MIT's own copy of the 9.2 manual.

**Larceny** (`src/Lib/Common/memstats.sch`, `doc/UserManual/syscontrol.txt`,
`src/Compiler/iasn.imp.sch`).
- `(memstats)` returns a vector built from the primitive
  `sys$get-resource-usage`. It has about a hundred fields, read through
  accessors such as `memstats-allocated`, `memstats-gc-reclaimed`,
  `memstats-gc-copied`, `memstats-gc-total-elapsed-time` and
  `-cpu-time`, `memstats-heap-allocated-max`, `memstats-heap-live-now`,
  `memstats-elapsed-time`, `memstats-user-time`, `memstats-system-time`,
  `memstats-fullgc-collections`, the maximum pauses
  (`memstats-gc-max-truegc-elapsed-time`), and per-generation vectors
  (`memstats-gen-collections`, `-promotions`, `-live-now`, `-target-size-now`).
  It also holds pause histograms in buckets of 10 ms, and remembered-set and
  simulated-barrier counters. Sizes are in words. Times are in milliseconds.
  Big counts are kept as hi/lo fixnum pairs so the runtime needs no bignums.
- `(display-memstats v ['full | 'minimal])` prints the vector.
- `(run-with-stats thunk)` takes `(memstats)` and the minor count
  `(- (gc-counter) (major-gc-counter))` before and after the thunk. It
  prints the differences (words allocated; elapsed, user and system time;
  GC time, and in how many collections, how many minor; maximum pauses;
  maximum words of memory, heap, remembered sets and runtime) and returns
  the thunk's value. `(time e)` is `(run-with-stats (lambda () e))`
  (`lib/Base/macros.sch`). `run-benchmark` runs a thunk k times under
  `run-with-stats` and checks the result.
- `(gc-counter)` and `(major-gc-counter)` are primitives, each compiled to a
  single load (globals `G_GC_CNT` and `G_MAJORGC_CNT`, bumped in memmgr.c).
  Larceny's eq-hashtables use `major-gc-counter` to know when to rehash.
  Twobit's primop table gives both *killed* = `:dead` ("never available",
  so never CSE'd) and *kills* = `:none` (they kill no other available
  expression). That is exactly the compiler contract a counter read needs.
- `(sro ptag htag limit)` returns every live object of a kind with at most
  `limit` references to it (sro.c). fixpt has it as `%sro`.
- `stats-dump-on` / `stats-dump-off` append a full dump after each
  collection. The `-annoy-user` flag prints a message at each major
  collection.
- The procedure profiler (`lib/Debugger/profile.sch`, 2008, by the user)
  samples on the timer interrupt and records the procedures awaiting values
  on the continuation.

**Chez Scheme** (CSUG for Version 10.4.0: "Timing and Statistics",
"Times and Dates" and "Black-Box Procedure" in
https://cisco.github.io/ChezScheme/csug/system.html; "Storage Management"
in https://cisco.github.io/ChezScheme/csug/smgmt.html; "Object inspection"
in .../debug.html. Checked against the manual's source, `csug/system.stex`,
`smgmt.stex` and `debug.stex` at commit `d9e76eb8e4f2` of
https://github.com/cisco/ChezScheme.)
- `(time e)` returns `e`'s values and prints the collections, the CPU and
  real time in ms (each "including … collecting"), and the bytes
  allocated, "including … bytes reclaimed". `display-statistics` prints
  running totals.
- `(statistics)` returns an `sstats` record. Its fields are `cpu`, `real`,
  `bytes`, `gc-count`, `gc-cpu`, `gc-real` and `gc-bytes` (reclaimed). The
  times are time objects, not numbers. The record has accessors
  `sstats-cpu` … `sstats-gc-bytes`, setters `set-sstats-cpu!` and so on,
  `make-sstats`, `sstats-difference` and `sstats-print`.
  - The manual defines `statistics` through `(current-time 'time-thread)`
    for `cpu`, `'time-monotonic` for `real`, and `'time-collector-cpu` and
    `'time-collector-real` for the GC fields. So Chez's CPU time is the
    thread's.
- **Correction to the first version of this note:** `(bytes-allocated
  [g])` is the bytes *currently* allocated (in use), in all generations or
  in generation `g`. It is not a cumulative count.
  - `(bytes-deallocated)` is the total freed by the collector.
  - The cumulative allocation is `(bytes-allocated)` plus
    `(bytes-deallocated)`, less `(initial-bytes-allocated)`. That is how
    `statistics` computes `bytes`.
- `(current-memory-bytes)` is the whole heap reserved from the system,
  overhead included. `(maximum-memory-bytes)` is its maximum since the last
  `(reset-maximum-memory-bytes!)`, which resets the maximum to the current
  size.
- `(collections)` counts collections.
- `(cpu-time)` and `(real-time)` are ms since startup. `(current-time
  [type])` takes the types `time-utc`, `time-monotonic`, `time-process`,
  `time-thread`, `time-collector-cpu` and `time-collector-real`.
- Collection control is in "Storage Management":
  - `collect-request-handler` is a parameter, a procedure of no arguments
    invoked "whenever the system determines that a collection should
    occur", about every `collect-trip-bytes` of allocation. It is where a
    program decides whether and what to collect.
  - `collect-notify` prints a message at each collection.
  - `collect-generation-radix` and `collect-maximum-generation` are policy.
- `enable-object-counts` makes the collector record `(object-counts)`
  (per type and generation). It is off by default because of what it costs
  the collector. `compute-size` and `compute-composition` measure an
  object's closure.
- **`(black-box obj)`** (Chez 10) returns `obj`, and "optimization passes
  make no assumptions about how `black-box` uses its argument, whether
  `black-box` has side effects, or what `black-box` returns". The manual's
  own example is a `time`d loop whose `expt` would otherwise be folded or
  dropped. This is exactly the operation the first version of this note
  called `opaque`, so the note now takes Chez's name (see "The first set").

**Racket** (Racket 9.3 reference: https://docs.racket-lang.org/reference/time.html,
.../garbagecollection.html, .../runtime.html; `time`'s output format from
`racket/collects/racket/private/more-scheme.rkt` at commit `8496bcd58b16` of
https://github.com/racket/racket).
- Clocks: `current-inexact-milliseconds`,
  `current-inexact-monotonic-milliseconds` (since 8.1.0.4),
  `current-milliseconds` (a fixnum, possibly negative),
  `current-process-milliseconds` (with an optional scope: `#f`, a thread,
  or `'subprocesses`) and `current-gc-milliseconds` (GC *CPU* time).
- `(time e)` prints `cpu time: ~s real time: ~s gc time: ~s`.
  `(time-apply proc args)` returns four values: a list of the results, CPU
  ms, real ms, and GC CPU ms. So it is a thunk runner that returns its
  statistics.
- `(vector-set-performance-stats! vec [thd])` fills a vector the caller
  supplies. With `thd` `#f` the slots are:
  - 0, 1, 2: process ms, real ms and GC ms;
  - 3: the collection count;
  - 4: thread context switches;
  - 5 to 10: internal statistics that are BC-only and 0 on Racket CS;
  - 11: the peak allocated bytes before a collection.
- `(current-memory-use [mode])` takes `#f` (reachable bytes), `'cumulative`
  (bytes allocated since start), `'peak` ("the maximum number of allocated
  bytes just before any garbage collection"), or a custodian.
  `(dump-memory-stats)` prints to the error port.
  `(collect-garbage ['major | 'minor | 'incremental])`.
- Collections are logged on topic `'GC` at level `debug` (`'GC:major` for
  majors). The data is a `gc-info` prefab with fields `mode`
  (`'major`/`'minor`/`'incremental`), `pre-amount`, `pre-admin-amount`,
  `code-amount`, `post-amount`, `post-admin-amount`, `start-process-time`,
  `end-process-time`, `start-time` and `end-time`. A `make-log-receiver`
  pulls them. This is a pull-style event stream, not a callback inside the
  collector.

**Gambit** (manual source `doc/gambit.txi`, "Measuring time" and
`gc-report-set!` under debugging; runtime `lib/_kernel.scm` and
`lib/_repl.scm`; all at commit `985c0304dd49` of https://github.com/gambit/gambit.
Rendered manual: https://gambitscheme.org/4.8.3/manual/, the newest
rendering found; `/latest/manual/` gave 404.)
- `(process-times)` returns an f64vector of user, system and real
  *seconds*. `(cpu-time)` is user plus system seconds. `(real-time)` is
  seconds since the program started.
- `(time expr [port])` returns the value and prints real and CPU ms (user,
  system), "N collections accounting for … ms real time", bytes allocated,
  and minor and major faults.
- `(gc-report-set! #t)` prints after each collection its time, megabytes
  allocated since start, heap size, live data and its proportion, and the
  movable and nonmovable bytes.
- Undocumented, in the source:
  - `##process-statistics` returns an f64vector (user, system, real, GC
    user, system and real time, the collection count, …). It **measures
    the bytes it allocates for its own result and subtracts them**.
  - `##exec-stats` is the thunk runner behind `time`.
  - `##add-gc-interrupt-job!` adds a thunk to run after each collection.

**Guile** (Guile 3.0, git master at https://git.savannah.gnu.org/cgit/guile.git:
`doc/ref/api-memory.texi`, `doc/ref/posix.texi` ("Time"),
`doc/ref/statprof.texi`, `libguile/gc.c`. Rendered at
https://www.gnu.org/software/guile/manual/html_node/Garbage-Collection-Functions.html,
which redirects to doc.guix.gnu.org.)
- `(gc-stats)` returns an alist with the keys `gc-time-taken` (run time
  accumulated around collections, in internal time units), `heap-size`,
  `heap-free-size`, `heap-total-allocated`, `heap-allocated-since-gc`,
  `protected-objects` and `gc-times`.
  - **Correction:** `gc-times` is the *number* of collections
    (`GC_get_gc_no`), not a list of times.
- `(gc-live-object-stats)`.
- `after-gc-hook` runs "after the gc, as soon as the asynchronous events
  are handled", so an async, not inside the collector.
- `get-internal-real-time` (time units since start),
  `get-internal-run-time` (processor time, system and user),
  `internal-time-units-per-second`, and `times`.
- `(statprof thunk …)` samples the stack `hz` times per second.
  `(gcprof thunk [#:loop])` samples it "soon after every garbage
  collection", which approximates where allocation comes from.

**MIT/GNU Scheme** (reference manual 9.2, "Machine Time",
https://web.mit.edu/scheme_v9.2/doc/mit-scheme-ref/Machine-Time.html; user
manual 9.2, "Garbage Collection",
https://web.mit.edu/scheme_v9.2/doc/mit-scheme-user/Garbage-Collection.html.
The gnu.org copies of the current manual refused the fetch.)
- **Correction:** `(runtime)` is process time in seconds that "does not
  include time spent in garbage collection". `process-time-clock` and
  `real-time-clock` are in ticks (1 ms at present), and
  `internal-time/ticks->seconds` converts.
- `(with-timings thunk receiver)` calls the receiver with the run time,
  the GC time and the real time, all in ticks. It is a thunk runner that
  separates GC time. `(measure-interval runtime? procedure)`.
- `(gc-flip)` collects and returns the words free afterwards.
  `toggle-gc-notification!` and `set-gc-notification!` print a line per
  collection ("GC #5: took: 0.50 (8%) CPU time, 0.70 (2%) real time; free:
  364346"). `(print-gc-statistics)` prints space use and the last 8
  collections.

**Common Lisp and SBCL** (CLHS: http://www.lispworks.com/documentation/HyperSpec/Body/m_time.htm,
f_room.htm, f_get_in.htm, f_get__1.htm. SBCL: `doc/manual/beyond-ansi.texinfo`,
`src/code/gc.lisp`, `src/code/time.lisp`, `src/code/aprof.lisp` and
`contrib/sb-sprof/sb-sprof.texinfo`, at commit `7bab5b37ac9b` of
https://github.com/sbcl/sbcl. Rendered at https://www.sbcl.org/manual/.)
- In the standard: `time`; `room` (with `t` for the detailed report);
  `get-internal-real-time`, `get-internal-run-time`,
  `internal-time-units-per-second`.
- SBCL's `time` prints real and run time split into GC and non-GC time,
  processor cycles, and "bytes consed".
- SBCL's names are all in `sb-ext`:
  - `sb-ext:*gc-run-time*` is "Total CPU time spent doing garbage
    collection". The manual says it is safe to bind it to zero to measure
    one section.
  - `sb-ext:*gc-real-time*` is the real time, likewise.
  - `sb-ext:get-bytes-consed` is bytes consed since start. "Typically
    this result will be a consed bignum": reading it allocates.
  - `sb-ext:bytes-consed-between-gcs` is the nursery size, setf-able.
  - `sb-ext:*after-gc-hooks*` runs after each collection, "in any thread".
  - `sb-ext:generation-number-of-gcs` and friends work per generation.
- `sb-sprof` samples with `:mode :cpu`, `:alloc` or `:time`.
- The allocation profiler in `aprof.lisp` (`aprof-run`) is compile-time
  instrumentation: each inline allocation sequence gets a few
  instructions, normally jumped around, which are patched to increment
  counters when the profiler is on. It is x86-64 only.

**OCaml** (`stdlib/gc.mli`, `runtime/memprof.c` and
`otherlibs/runtime_events/runtime_events.mli`, at commit `7da997d28b1a` of
https://github.com/ocaml/ocaml, trunk, 5.6.0+dev. Rendered at
https://ocaml.org/manual/latest/api/Gc.html and
https://ocaml.org/manual/latest/api/Runtime_events.html.)
- `Gc.stat` returns a record with `minor_words`, `promoted_words`,
  `major_words`, `minor_collections`, `major_collections`, `heap_words`,
  `live_words`, `free_words`, `top_heap_words` ("Maximum size reached by
  the major heap"), `compactions`, `forced_major_collections`, `stack_size`
  and more.
  - **Correction:** in OCaml 5 `Gc.stat` *causes a full major collection*
    and is deprecated ("Use full_major() followed by quick_stat()").
  - `Gc.quick_stat` does not collect, but may reflect the state at the
    last minor collection or major cycle, because of per-domain buffers.
- `Gc.counters ()` returns `(minor_words, promoted_words, major_words)`.
  `Gc.minor_words ()` "does not allocate" in native code, but is "only an
  approximation" there. `Gc.allocated_bytes`, `Gc.print_stat`.
- `Gc.create_alarm f` calls `f` at the end of major cycles, "not
  guaranteed … at the end of every major GC cycle, but … eventually".
  `Gc.delete_alarm` removes it.
- `Gc.Memprof.start ~sampling_rate ?callstack_size tracker`. The rate is
  in samples per word, and 1e-4 "has no visible effect on performance".
  `memprof.c` confirms the mechanism: when profiling, the runtime "set[s]
  the trigger at the next word which we want to sample". The allocation
  fast path is untouched.
- `Runtime_events` is per-domain ring buffers in a `.events` file,
  readable in process or from another process.
- `OCAMLRUNPARAM=v=0x400` gives "Output GC statistics at program exit".

**The SML Basis, and MLton** (Basis `TIMER`:
https://smlfamily.github.io/Basis/timer.html. MLton:
`basis-library/mlton/gc.sig`, `rusage.sig`, `rusage.sml`,
`runtime/gc/init.c`, `doc/guide/src/Profiling.adoc`, at commit
`aa2fd1ad9b91` of https://github.com/MLton/mlton (the latest release is
tagged `on-20241230-release`). Rendered at http://mlton.org/MLtonGC,
http://mlton.org/MLtonRusage, http://mlton.org/Profiling and
http://mlton.org/RunTimeOptions.)
- The Basis `Timer.checkCPUTimes` returns `{nongc, gc}`, each `{usr,
  sys}`. `Timer.checkGCTime` is "the user time spent in garbage
  collection" since the timer started. So a standard library separates GC
  time from the rest.
- In MLton:
  - `MLton.GC.collect`, `pack`, `unpack`, `setMessages` and `setSummary`.
  - `MLton.GC.Statistics` has `bytesAllocated`, `lastBytesLive`,
    `maxBytesLive`, `numCopyingGCs`, `numMarkCompactGCs` and
    `numMinorGCs`, all of type `unit -> IntInf.int`.
  - `MLton.Rusage.rusage ()` returns `{children, gc, self}`, each `{utime,
    stime}`. The `gc` part is measured only after
    `MLton.Rusage.measureGC true`.
  - Runtime options `@MLton gc-messages`, `gc-summary` and
    `gc-summary-file`.
  - `-profile alloc | count | time` with `mlprof`.

**GHC** (GHC 9.14.1 users guide, "RTS options to produce runtime statistics":
https://downloads.haskell.org/ghc/latest/docs/users_guide/runtime_control.html.
base-4.22.0.0: https://hackage.haskell.org/package/base-4.22.0.0/docs/GHC-Stats.html,
.../System-Mem.html, .../GHC-Clock.html.)
- `getRTSStatsEnabled` and `getRTSStats :: IO RTSStats` need `+RTS -T`.
  The fields:
  - counts: `gcs` and `major_gcs`;
  - bytes: `allocated_bytes`, `max_live_bytes` ("Updated after a major
    GC"), `max_mem_in_use_bytes`, `cumulative_live_bytes` (divide by
    `major_gcs` for the average live data), `copied_bytes`, and the
    `max_large_objects_bytes`, `max_compact_bytes` and `max_slop_bytes`
    maxima;
  - times: `mutator_cpu_ns`, `mutator_elapsed_ns`, `gc_cpu_ns`,
    `gc_elapsed_ns`, `cpu_ns`, `elapsed_ns`, and the nonmoving collector's
    times;
  - `gc :: GCDetails`, for the last collection: `gcdetails_gen`,
    `gcdetails_allocated_bytes`, `gcdetails_live_bytes`,
    `gcdetails_copied_bytes`, `gcdetails_cpu_ns`,
    `gcdetails_elapsed_ns`, ….
- `+RTS -s` prints a summary at exit ("bytes allocated in the heap",
  "bytes copied during GC", "bytes maximum residency", per-generation
  collections, INIT/MUT/GC/EXIT time, "%GC time", "Alloc rate",
  "Productivity"). `-S` adds a line per collection, `-t` prints one line,
  and `-T` only collects. `-l` writes the eventlog.
- `System.Mem.getAllocationCounter` and `setAllocationCounter` form a
  *per-thread* counter of bytes that "counts down".
  `enableAllocationLimit` raises `AllocationLimitExceeded` when it passes
  zero. `GHC.Clock.getMonotonicTimeNSec :: IO Word64`.

**Erlang/BEAM** (OTP 29.1.1, erts 17.1: https://www.erlang.org/doc/apps/erts/erlang.html#statistics/1,
#process_info/2, #system_monitor/2; https://www.erlang.org/doc/apps/stdlib/timer.html#tc/1.
Checked against `erts/preloaded/src/erlang.erl` and `lib/stdlib/src/timer.erl`
at commit `fa4ccccea5e2` of https://github.com/erlang/otp.)
- `erlang:statistics/1` accepts `active_tasks`, `context_switches`,
  `exact_reductions`, `garbage_collection` (`{NumberOfGCs,
  WordsReclaimed, 0}`, which "can be invalid for some implementations"),
  `io`, `microstate_accounting`, `reductions` (`{Total,
  SinceLastCall}`), `run_queue`, `runtime`, `scheduler_wall_time`,
  `wall_clock`, and the `_all` and `total_` variants.
- `process_info/2` has `heap_size`, `total_heap_size`, `memory`,
  `garbage_collection` and `garbage_collection_info`.
- `erlang:system_monitor/2` takes `{long_gc, Time}`, `{large_heap, Size}`,
  `{long_schedule, Time}`, `{long_message_queue, …}` and `busy_port`, and
  sends messages to one monitoring process. It is now "superseded by
  `trace:system/3`". Process tracing gives `gc_minor_start` and similar
  events.
- `timer:tc(Fun)` returns `{Time, Value}`, the elapsed real time in
  microseconds by default. It is a thunk runner.
  `erlang:monotonic_time/1`.
- Reductions are a deterministic count of work, which matters below.

**JVM** (Java SE 21 API: https://docs.oracle.com/en/java/javase/21/docs/api/java.management/java/lang/management/GarbageCollectorMXBean.html,
.../MemoryPoolMXBean.html, and https://docs.oracle.com/en/java/javase/21/docs/api/jdk.management/com/sun/management/ThreadMXBean.html.
Checked with OpenJDK 21.0.11's `javap` and `jfr metadata`.)
- `GarbageCollectorMXBean.getCollectionCount()` and `getCollectionTime()`
  (ms, approximate), with one bean per collector (young, old).
- `MemoryPoolMXBean.getUsage()`, `getPeakUsage()`, `resetPeakUsage()`, and
  `getCollectionUsage()` (the usage after the last collection).
- `com.sun.management.ThreadMXBean.getCurrentThreadAllocatedBytes()` and
  `getThreadAllocatedBytes(id)`.
- `GarbageCollectionNotificationInfo` (notification type
  `GARBAGE_COLLECTION_NOTIFICATION`) is delivered through
  `NotificationEmitter`. `System.nanoTime()` and
  `ThreadMXBean.getCurrentThreadCpuTime()` are the clocks.
- JFR has the events `GarbageCollection`, `GCHeapSummary` and
  `ObjectAllocationSample` (throttled sampling), all present in `jfr
  metadata`. `-Xlog:gc*`.
- JMH's `Blackhole.consume` keeps a result from being optimized away.

**Go** (development tree, go1.28, at commit `38f24c5c4659` of
https://github.com/golang/go: `src/runtime/mstats.go`,
`src/runtime/metrics/description.go`, `sample.go` and `doc.go`,
`src/runtime/debug/garbage.go`, `src/runtime/mprof.go`,
`src/runtime/extern.go`. Rendered at https://pkg.go.dev/runtime#MemStats
and https://pkg.go.dev/runtime/metrics.)
- `runtime.ReadMemStats(&m)` stops the world (`stopTheWorld(stwReadMemStats)`
  in its body). `MemStats` has `TotalAlloc`, `Mallocs`, `HeapAlloc`,
  `HeapInuse`, `Sys`, `NumGC`, `NumForcedGC`, `PauseTotalNs`, `PauseNs`
  and `PauseEnd` (circular buffers of 256), `LastGC`, `NextGC` and
  `GCCPUFraction`.
- `metrics.Read(samples)` fills a slice of named samples the caller
  supplies, and reusing the slice is encouraged. Among them:
  `/gc/cycles/total:gc-cycles`, `/gc/cycles/forced:gc-cycles`,
  `/gc/heap/allocs:bytes`, `/gc/heap/allocs:objects`,
  `/gc/heap/live:bytes`, `/cpu/classes/gc/total:cpu-seconds`, and the
  pause histogram `/sched/pauses/total/gc:seconds` (`/gc/pauses:seconds`
  is its deprecated name). `metrics.All()` describes them.
- `debug.ReadGCStats` (with `PauseQuantiles`). `GODEBUG=gctrace=1` prints
  "a single line" per collection.
- `runtime.MemProfileRate` (`512 * 1024`, the mean bytes between samples)
  drives the sampling allocation profiler behind `pprof`.
- `testing.B.ReportAllocs` and `testing.AllocsPerRun`.

**Python** (3.14 documentation: https://docs.python.org/3.14/library/gc.html,
tracemalloc.html, time.html, timeit.html. Checked on Python 3.14.7 here.)
- `gc.get_stats()` gives a dict per generation (`collections`,
  `collected`, `uncollectable`). `gc.get_count()`, `gc.get_threshold()`.
- `gc.callbacks` is a list of callables called with `"start"`/`"stop"` and
  an info dict.
- `tracemalloc.start(nframe)`, `get_traced_memory()` (current and peak),
  `reset_peak()`, `take_snapshot()` and `Snapshot.statistics('lineno')`.
  It traces every allocation exhaustively, not by sampling.
- `time.perf_counter_ns` (`mach_absolute_time()` here, 41.7 ns
  resolution), `time.process_time_ns` (`CLOCK_PROCESS_CPUTIME_ID`, 1 µs),
  `time.thread_time_ns` (`CLOCK_THREAD_CPUTIME_ID`, 42 ns).
- `timeit.Timer.timeit` turns the collector *off* while timing (checked in
  its source here).

**JavaScript** (MDN:
https://developer.mozilla.org/en-US/docs/Web/API/Performance/measureUserAgentSpecificMemory.
Node 26 documentation: https://nodejs.org/docs/latest-v26.x/api/perf_hooks.html
and .../v8.html. Node 26.0.0 checked here.)
- `performance.now()`, `performance.mark`/`measure`.
- `performance.measureUserAgentSpecificMemory()` is experimental, not
  Baseline. It returns a promise of `{bytes, breakdown}`, and needs a
  secure, cross-origin-isolated context.
- In Node:
  - `process.hrtime.bigint()`, `process.cpuUsage()`,
    `process.resourceUsage()` (`maxRSS`, page faults, …).
  - `process.memoryUsage()` (`rss`, `heapTotal`, `heapUsed`, …).
  - `v8.getHeapStatistics()` (`used_heap_size`, `total_allocated_bytes`,
    `peak_malloced_memory`, …) and `v8.getHeapSpaceStatistics()`.
  - A `PerformanceObserver` on entry type `'gc'`, whose kind is one of
    `NODE_PERFORMANCE_GC_MAJOR`, `_MINOR`, `_INCREMENTAL` and `_WEAKCB`.
- V8's `--trace-gc`, `--trace-gc-nvp`, `--trace-gc-verbose`, and Node's
  `--heap-prof`, which runs the sampling heap profiler.

**Lua** (Lua 5.5 reference manual, §6.1:
https://www.lua.org/manual/5.5/manual.html#pdf-collectgarbage. Lua 5.5
checked here.)
- `collectgarbage("count")` returns "the total memory in use by Lua in
  Kbytes", with a fraction so that times 1024 it is exact.
  `collectgarbage` also takes `"collect"`, `"stop"`, `"restart"`,
  `"step"`, `"isrunning"`, `"incremental"`, `"generational"` and
  `"param"`.
- `os.clock()` gives CPU time.
- There is no allocation counter. A host counts allocation through
  `lua_setallocf`.

### The same, by family

| Family                        | Typical names                                                                                                                                                                                                                      | Pull or push         |
| ----------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------- |
| Real, CPU and GC clocks       | Chez `real-time`/`cpu-time`/`current-time 'time-collector-real`; Racket `current-gc-milliseconds`; SML `Timer.checkGCTime`; SBCL `*gc-run-time*`/`*gc-real-time*`; MIT `with-timings`                                              | pull                 |
| Allocation counter            | Chez `sstats-bytes` (in-use `bytes-allocated` + `bytes-deallocated`); Racket `(current-memory-use 'cumulative)`; SBCL `get-bytes-consed`; OCaml `Gc.minor_words`; JVM `getCurrentThreadAllocatedBytes`; Go `/gc/heap/allocs:bytes` | pull                 |
| Collections by generation     | Larceny `gc-counter`/`major-gc-counter`; OCaml `minor_collections`/`major_collections`; GHC `gcs`/`major_gcs`; JVM one bean per collector                                                                                          | pull                 |
| Pauses                        | Larceny max pause and histograms; Go `PauseNs` ring, pause histograms; GHC per-generation pauses in `-s`                                                                                                                           | pull                 |
| Live and peak                 | Chez `maximum-memory-bytes`/`reset-maximum-memory-bytes!`; Racket `(current-memory-use 'peak)`; OCaml `top_heap_words`; GHC `max_live_bytes`; JVM `getPeakUsage`/`resetPeakUsage`; tracemalloc `reset_peak`                        | pull                 |
| Copy volume, mark/cons        | Larceny `memstats-gc-copied`; OCaml `promoted_words`; GHC `copied_bytes`                                                                                                                                                           | pull                 |
| Thunk runner                  | Larceny `run-with-stats`; Racket `time-apply`; Gambit `##exec-stats`; MIT `with-timings`; Erlang `timer:tc`; `time` everywhere                                                                                                     | pull                 |
| Per-collection trace          | V8 `--trace-gc`; GHC `-S`; Go `gctrace`; Gambit `gc-report-set!`; MIT `toggle-gc-notification!`; Larceny `-annoy-user`, `stats-dump-on`                                                                                            | push, to a file      |
| Event stream                  | Racket `'GC` log receiver; OCaml `Runtime_events`; GHC eventlog; JFR; Node `PerformanceObserver`                                                                                                                                   | pull, from a buffer  |
| Hooks and alarms              | OCaml `Gc.create_alarm`; SBCL `*after-gc-hooks*`; Guile `after-gc-hook` (an async); Gambit `##add-gc-interrupt-job!`; Python `gc.callbacks`; Chez `collect-request-handler`; Erlang `system_monitor` (a message)                   | push, runs user code |
| Sampling allocation profiler  | OCaml `Gc.Memprof`; Go `MemProfileRate`; JFR `ObjectAllocationSample`; V8 sampling heap profiler; `sb-sprof :alloc`                                                                                                                | push, sampled        |
| Exhaustive allocation tracing | Python `tracemalloc`; SBCL `aprof-run` (patched-in counters); MLton `-profile alloc`; GHC `-hc`                                                                                                                                    | instrumented build   |
| Deterministic work count      | Erlang `reductions`; GHC allocation limits as a CPU budget                                                                                                                                                                         | pull                 |
| Heap census                   | Larceny `sro`; Chez `object-counts`; CL `room`                                                                                                                                                                                     | pull, walks the heap |

Four lessons recur:
- **Keep counters cumulative, and take differences.** Larceny, Chez
  (`sstats-difference`), OCaml and Go all do this. It composes under
  nesting and costs nothing to keep.
- **Reading must not allocate, or must say what it allocated. It must not
  collect either.**
  - Racket's `vector-set-performance-stats!` fills a vector the caller
    made, as Go's `metrics.Read` fills a slice.
  - OCaml's `Gc.minor_words` does not allocate in native code.
  - Gambit's `##process-statistics` subtracts the bytes of its own result.
  - Larceny's `memstats` allocates its vector, and `run-with-stats` then
    counts that vector as the thunk's. SBCL's `get-bytes-consed` may cons a
    bignum.
  - OCaml 5 deprecated `Gc.stat` because it forces a full major
    collection.
- **Benchmarks need a black box.** Chez 10's `black-box`, JMH's
  `Blackhole` and Rust's `std::hint::black_box` all exist because an
  optimizer is free to fold or drop the work a timing surrounds.
- **Peaks need a reset, and a reset needs care when runs nest.** Chez's
  `reset-maximum-memory-bytes!`, the JVM's `resetPeakUsage` and
  tracemalloc's `reset_peak` are all global, and so is binding SBCL's
  `*gc-run-time*` to zero, which its manual warns "may interfere with
  results reported by eg. `time`". A nested timing clobbers the
  outer one's peak.

## The families, applied to FX-26

### Clocks: real, CPU, collection

- **Real time.** `std::time::Instant` is `mach_absolute_time` here: 41.7 ns
  resolution. Through Python it cost about 20 ns more than a no-op call.
  Report integer nanoseconds from a fixed origin (the heap's creation);
  2^60 ns is 36 years, so the value fits a fixnum.
- **CPU time.** `clock_gettime(CLOCK_THREAD_CPUTIME_ID)` cost about 110 ns
  here, at 42 ns resolution. `CLOCK_PROCESS_CPUTIME_ID` and `getrusage`
  cost about 470 to 520 ns, at 1 µs. FX-26 programs run on one thread, and
  the collector runs on that thread, so thread CPU time is the right clock.
  Chez's `statistics` makes the same choice: its `cpu` field is
  `(current-time 'time-thread)`.
  Reaching it needs `libc`, which fixpt-native already depends on, or an
  `extern "C"` declaration as in fixpt-memmgmt's exec.rs.
- **Collection time** is `gc_nanos`, wall-clock time, and each collection
  already pays for its two `Instant` reads. Splitting it into minor and
  major time, and keeping the longest pause of each, costs one addition and
  one `max` per collection. CPU time spent collecting would cost two more
  clock reads (about 220 ns) per collection. That is negligible next to a
  collection's milliseconds, but the machine is single-threaded, so wall
  time will do until something is not. It is stage 2.
- **Per machine.** All four machines share one `Heap` and one runtime, so a
  clock primitive is a runtime primitive like any other:
  - the lowered Scheme calls it by its `%` name;
  - cellular code calls it with `prim`;
  - register code calls it with `rop-prim`;
  - native code calls it with a call-out, at a safepoint (register code's
    `rcons` call-out measured about 20 ns, docs/performance.md).

  An inline native read is possible later. arm64's `mrs x0, cntvct_el0`
  reads the 24 MHz counter in user mode in a few cycles, but it gives ticks,
  not ns. Two call-outs of about 20 ns each around a thunk are noise, so
  inline reads are stage 3 at most.

### Allocation counters

- **What exists.** `Heap::allocated()` is already exact on every machine.
  Native and register code bump `nursery_top` (or `top`) in the `Heap`
  itself, through `top_address()`, and a call-out sees the value stored
  there. This relies on the rule every allocating call-out already obeys:
  write a top cached in a register back before calling out.
- **What it leaves out.** Region allocation is counted apart, in
  `region_words()`, including the fill of each current chunk, which machine
  code bumps through `region_table_address()`. The code area's allocation
  is not counted at all.
- **Three counters, not one.** Heap words, region words, and later code
  words. A total that mixes them hides what regions are for.
- **The counts depend on the machine.** The same program allocates
  different amounts on different machines. The Scheme engine boxes and
  captures continuations differently. The cellular machines' stacks are Rust
  vectors outside the heap. Native frames live on a stack segment of their
  own. The evaluator written in FX-26 erases regions and places, so its
  `region-words-allocated` is always 0, and everything it runs allocates in
  the heap.
- **But they are deterministic.** For a given machine, nursery size and
  input, the counts do not vary between runs. That makes words allocated,
  and the collection counts, stable numbers for regression tracking in a
  way time never is. They could be a column in `fixpt bench` and so in every
  commit's bench table.
- **Example.** E3, under "Worked examples", counts collections and words
  around building a list.
- **Consequence for tests.** Cross-machine tests (compare.rs, `fixpt
  bench`'s result column) must never print a telemetry value. A test may
  assert relations only, such as "grew by at least n words after building
  n pairs".

### Collections: minor and major, counts, times and pauses

- **Counts.** Report `minor-collections` and `major-collections` apart; the
  sum is Larceny's `gc-counter`. A major collection also empties the
  nursery (`collect` copies it), so it is not also counted as a minor one.
- **Pauses.** Keep a longest pause per kind and, in stage 2, a histogram
  with one bucket per power of two in ns: 64 counters, updated with a
  `leading_zeros` per collection. Go and Larceny both found a histogram
  more useful than a mean. Larceny's fixed 10 ms buckets are too coarse for
  minor collections that take a few ms.

### Live and peak sizes

The heap has no peak today. Three measures are cheap and well defined:

- **`heap-words-in-use`**, at the moment of the read: old-space words
  (`top - active`), plus nursery words, plus region words in use. Garbage
  included, as Lua's `count` and Racket's `current-memory-use` include it.
- **`peak-heap-words`**, the high-water mark of the same quantity. Between
  collections that quantity only grows, so its maximum is reached just
  before some collection or right now. Keeping `peak = max(peak, in_use)`
  on entry to `collect` and `collect_minor`, and taking the same `max` when
  read, gives the exact peak. Chez's `maximum-memory-bytes` and the JVM's
  `getPeakUsage` measure the same kind of thing.
- **Live after a collection.** After a major collection, `free` (the words
  copied) is exactly what is live, and its maximum is GHC's
  `max_live_bytes` and MLton's `maxBytesLive`. After a minor collection the
  old space holds live data plus tenured garbage, so it is only an upper
  bound. Record `last_major_live` and `max_major_live` (stage 2). Both are 0
  until the first major collection, which is honest: nothing measured them.

The footprint, what the system has committed, is a different measure. It
is the semispace size (`semi`, which only grows), the regions' high-water
marks (`fresh - ARENA_BASE` and `reap_fresh - REAP_BASE`, already in
`Regions`), and the code area's `top`. It belongs in the stage-2 summary.
`getrusage`'s `ru_maxrss` is the process's own version of it, and comes
for free with the CPU clock's system call if that is ever used.

### Copy volume and the mark/cons ratio

- **The ratio.** The mark/cons ratio is the words the collector marks or
  copies per word the program allocates. It is Larceny's allocated vs.
  copied, used in Clinger and Hansen's PLDI '97 comparison of collectors.
  Here, words copied by major collections divided by words allocated is
  the ratio for the whole heap. Words promoted by minor collections divided
  by nursery words allocated is the nursery's survival rate, which says
  whether the nursery is the right size. `words_copied` today sums the two,
  so the heap must count them apart: `words_promoted` (minor) and
  `words_copied_major`. `words-copied` stays their sum, the collector's
  whole copying work.
- **Scanning counts too.** Every collection, minor ones included, traces
  every live region's words as roots (`collect_minor` takes
  `self.regions.ranges()`). A large arena therefore makes every minor
  collection slower, and a counter of region words scanned (stage 2) is how
  a program would see that.
- **No floats yet.** FX-26 has no floating point (docs/research/floats.md is
  considering it), so the ratio is computed from
  the counts, for example as thousandths, where it is shown.

### Regions and reaps

`regions.rs` counts in only one place: `Regions::words`, which gains a
chunk's fill when the chunk is replaced and a region's current fill when it
ends. Per region, only `region_in_use(h)` exists. What makes sense, by
strategy:

| Counter                | Arena (`letrena`)                            | Reap (`letreap`)                                            | Cost                              |
| ---------------------- | -------------------------------------------- | ----------------------------------------------------------- | --------------------------------- |
| words allocated in it  | = words in use (nothing is freed until exit) | ≥ words in use; the difference is what collections dropped  | per handle, at chunk turnover     |
| words in use now       | `region_in_use(h)`                           | `region_in_use(h)`, after collections only what's reachable | computed                          |
| chunks taken           | yes                                          | yes, including chunks from `reap_free`                      | at chunk turnover                 |
| words copied within it | never copied                                 | at each collection, from `Copier.new[h]`                    | per collection, per live reap     |
| words scanned as roots | every collection, minor ones too             | no (traced from references)                                 | per collection                    |
| time to end it         | pushing chunks onto `free`: cheap            | `mem.release` per chunk (a system call each), quarantine    | two clock reads per exit, or none |
| quarantine size        | none                                         | chunks waiting for a collection to clear them               | computed                          |

- **Cumulative totals**: arenas and reaps entered, region words allocated
  (exists), time spent in `region_exit`, chunks released to the system,
  and the high-water marks of both areas.
- **Per region**: words allocated and words in use, read inside the body.
  A per-handle `allocated: Vec<u64>` is pushed on enter and folded into
  the totals on exit. Its value while live is `allocated[h]` plus the
  current chunk's fill. That costs nothing on machine code's inline bump.
- **Typing.** The per-place reads take the place as a value, as `rcons`
  does:

  ```
  place-words-allocated : (poly ((p place)) (subr (maxeff (read p) (read @telemetry) (write @telemetry)) ((place p)) nat))
  place-words-in-use    : the same type
  ```

  `(read p)` keeps such a call inside the body, as a closure that reads `p`
  is kept there (E6, under "Worked examples", checks both halves). That is right: after the body ends, the place no longer
  exists. What a body wants to know after it ends is in the run's
  statistics, as `region-words` in `run-stats`.

### Per-site profiles and sampling allocation profilers

- **What exists.** The Rust machine's `Profile` charges each word with the
  cells it ran and the words it allocated. That is exhaustive, and only on
  one machine.
- **The native design copies OCaml's Memprof and Go's `MemProfileRate`.**
  Native and register code already compare `nursery_top` with
  `inline_limit()` and call in when they reach it. Setting that limit to
  the next *sample point* (a geometric random distance ahead, with a mean
  of, say, 64 KiB) sends one allocation in that many through the slow path.
  There the runtime records the return address: the code bloblet, and from
  the metadata native-conventions.md already plans, a source position.
  With profiling off, the limit is what it is now, so the cost is exactly
  zero. With it on, the cost is one call-out per sample.
- **On the cellular machines**, the `prim` routine for allocation can do the
  same by counting down. The limit is also how `gc_every` already forces
  every allocation through the slow path.
- **Not for FX-26 code.** This is a tool, like `%sro`: it sees every region
  and every procedure. It belongs to the CLI and the REPL (`,profile`),
  with a report printed by the host, not to FX-26's standard environment.
  Stage 3. E8, under "Worked examples", sets it beside OCaml's Memprof.

### Collection event hooks, alarms and logs

- **No hooks.** Running FX-26 code when the collector runs (OCaml's
  `Gc.create_alarm`, SBCL's `*after-gc-hooks*`, Python's `gc.callbacks`,
  Guile's `after-gc-hook`) would mean any allocation, in any procedure,
  pure ones included, could run code with arbitrary effects. The effect
  system would have to charge that code's effect to every `alloc`, and
  purity would be gone. Native code would also have to reenter FX-26 at
  every safepoint.
- **A buffer instead.** Racket's log receiver, OCaml's `Runtime_events`
  and GHC's eventlog all take the typed-friendly shape: the collector
  appends a record to a ring buffer and the program *pulls*. Stage 3 gives
  `(collection-events-since k)`, which returns a list of `(productof (kind
  symbol) (pause-ns nat) (promoted nat) (live-after nat))`, at `observes`
  plus `(alloc r)`. Erlang's `system_monitor` threshold message has the
  same shape: a pull, filtered by the runtime.
- **For people, a trace.** `FIXPT_GC_TRACE=1` prints one line per
  collection on stderr (stage 1): kind, pause, nursery words, words
  promoted or copied, old-space words after, and live regions. This is what
  V8's `--trace-gc`, GHC's `-S`, `gctrace` and `-annoy-user` do, and it
  needs no language design at all.
- E7, under "Worked examples", shows both styles and what a hook would
  cost `cons`'s type.

### Timing a thunk

- **What `run-with-stats` needs** is a snapshot before, a snapshot after,
  and the differences, with nesting working and the snapshots' own work
  left out. Larceny's `run-with-stats` counts its own `memstats` vector,
  and its maximums are global, not per run.
- **The design.** A small stack of snapshots is kept in the `Heap`.
  `telemetry-begin` pushes the current counters and a fresh peak and
  maximum pause, and returns the stack depth as a token. `telemetry-end`
  takes the token, pops back to that depth, and builds the `run-stats`
  product.
  - `telemetry-end` reads all the counters *before* it allocates the
    product, so neither call counts itself.
  - A popped entry's peak and maximum pause are folded into the entry
    below it, so an outer run still sees an inner run's peak.
  - An escape out of the thunk (an abort to a prompt outside) leaves stale
    entries above the token. The next `telemetry-end` of an outer run pops
    them, as `region_exit(h)` ends any newer region an escape left behind.
- **What it measures.** Two call-outs, with no FX-26 allocation between
  them and the thunk. `run-with-stats` itself allocates the closure for the
  thunk before `telemetry-begin`, which is therefore not counted.
- **A result, not a printout.** `run-with-stats` returns the value and the
  statistics. FX-26 has no output. The REPL prints the product, labels and
  all, and a host can format it as Larceny's `display-memstats 'minimal`
  does.
- **Benchmarks need `black-box`.** A pure thunk's work could be hoisted out of
  a benchmark loop, or its unused result dropped, by a compiler that uses
  effect summaries. `(black-box x)` is the identity with the effect `observes`.
  Its argument must be computed, it cannot be dropped, and nothing can be
  seen through it. It is Chez 10's `black-box` (whose name it takes)
  and plays the role of JMH's `Blackhole` and Rust's `black_box`. `stay-cellular` is the precedent: an identity with a
  purpose.
- **Examples.** E1 (timing `fib 25` by hand), E4 (a loop dropped, hoisted
  and pinned) and E5 (`run-with-stats` and `(time e)`), under "Worked
  examples".

### Deterministic work

- **Steps as work.** The cellular machines count `steps`, and native code
  and register code burn fuel. A machine's step count is to it what
  Erlang's reductions are to BEAM: deterministic, cheap (already kept) and
  immune to noise.
- **Per machine.** The count is only comparable between runs on the same
  machine, since a native step is not a cellular step.
- **The operation.** `(work-units)` is stage 2, typed like the other
  counters. Its meaning per machine is: cells run on the Rust machine;
  fuel consumed natively; and the engine's step count on the lowered
  Scheme. E9, under "Worked examples", is a sketch beside Erlang's
  reductions.

## Typing

**The effect.** `observes` is `(maxeff (read @telemetry) (write
@telemetry))`. `@telemetry` is a region constant that no data is ever
allocated at. What it stands for is the machine's clocks and counters,
which "change" between any two reads.

**Why a write, when the operation only reads.** Summaries say what a
transformation may do (docs/fx26.md, "Effect summaries"):

- A summary of 1, "reads only", lets a compiler share two identical reads
  with no write between them, or drop an unused one.
- Nothing in the program ever writes `@telemetry`. So if the effect were a
  read alone, two `(real-time-ns)` calls would be the same read.
- Adding the write gives summary 2, which rules out CSE, hoisting,
  dropping and reordering between two telemetry operations. These are the
  rules that already guard `set-car!`. No new rule is needed in either
  checker, in the effect summaries or in a future optimizer.
- It is not summary 3: a telemetry read changes no global and keeps no
  continuation. So a compiler may keep a global's value known across one.
- This is Twobit's contract for `gc-counter`: never available, kills
  nothing.

**Pure code stays pure.** Allocation and time are what `pure` code "does",
and telemetry makes them observable to code that says `observes`. The
statement that keeps the guarantee:

> A telemetry operation returns an unspecified natural. Readings of a
> counter or clock never decrease within a run, and that is all the
> semantics promises.

Any transformation of pure code therefore preserves meaning: moving it,
running it twice, dropping it, speculating it, or changing how much it
allocates. Every surveyed compiler works this way in practice. GHC may
float pure work across `getCPUTime`. OCaml moves allocation across
`Gc.minor_words`. Twobit moves `cons` across `gc-counter`. The one thing
the design must add is `black-box`, for programs that need a pure computation
pinned between two readings. `spin` code is never moved early anyway: only
code the checker proved terminating can be, since `pure` excludes `spin`.

**Masking.** `@telemetry` is a constant, so no `letregion` binds it and
masking never removes it (E2, under "Worked examples", shows the checker
saying so). A procedure that reads a clock says so in its
type, even when it only returns something computed from the reading. That
is intended: its result is not a function of its arguments.

**Licences.** `unlicensed` (licence.rs) accepts reads and writes only on
regions the observer owns. `@telemetry` is not owned, so the REPL's
speculation never runs `(time …)` early, and the eager reader's entry
points could not observe without failing their licence. The effect could
be licensed, since reading a clock harms nothing the user's program holds.
But a speculative hint would then show meaningless timings, so start
unlicensed and revisit only if someone wants hints of timings.

**`private-regions` and naming.** Give `@telemetry` its own `Region`
variant (as `Globals` has one), printed `@telemetry`, rather than an
interned `Const`. Then `(private-regions @telemetry)` can be refused like
any other reserved name, and it can never be confused with a program's own
region. That means one variant in ast.rs, with the matching change in
check.fx's region representation. The rest (the atoms, the summaries,
masking, `licence.rs`) works unchanged.

**Redefinition and `define*`.** A procedure that observes has `observes`
in its latent effect. `define*` finds it like any other atom. Redefining
the procedure without the effect is compatible; redefining it with the
effect added is not. Both follow the existing rule.

**Alternatives rejected.**
- *Every allocation writes `@telemetry`.* That is the honest model, but it
  makes `cons` impure and every program's effects useless.
- *A read alone, plus a special no-CSE rule.* Every optimizer would have to
  learn the exception, in two languages.
- *A new region-less atom `observe`, like `spin`.* It needs new cases in
  both checkers, the summaries and the licence, where a region needs
  almost none. It also cannot be split later into `@clock` and `@heap`,
  which a region can (for example, if a clock should ever be licensed and
  the counters not).

## The first set

`observes` stands for `(maxeff (read @telemetry) (write @telemetry))`, and
`run-stats` for the product type below. Words are heap words of 8 bytes, as
Larceny and OCaml count them. All counts are since the heap was made.

| Operation                | Type                                                                                                              | Meaning                                                               |
| ------------------------ | ----------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------- |
| `real-time-ns`           | `(subr observes () nat)`                                                                                          | Monotonic ns since the heap was made (`Instant`)                      |
| `cpu-time-ns`            | `(subr observes () nat)`                                                                                          | This thread's CPU ns (`CLOCK_THREAD_CPUTIME_ID`), collector included  |
| `gc-time-ns`             | `(subr observes () nat)`                                                                                          | Wall ns spent collecting, minor and major (`gc_nanos`)                |
| `minor-collections`      | `(subr observes () nat)`                                                                                          | `minor_count`                                                         |
| `major-collections`      | `(subr observes () nat)`                                                                                          | `gc_count`                                                            |
| `words-allocated`        | `(subr observes () nat)`                                                                                          | Heap words allocated, inline allocation included (`allocated()`)      |
| `region-words-allocated` | `(subr observes () nat)`                                                                                          | Words allocated in arenas and reaps (`region_words()`)                |
| `words-copied`           | `(subr observes () nat)`                                                                                          | Words copied by collections: promoted by minors plus copied by majors |
| `heap-words-in-use`      | `(subr observes () nat)`                                                                                          | Old space plus nursery plus region words in use, garbage included     |
| `peak-heap-words`        | `(subr observes () nat)`                                                                                          | High-water mark of `heap-words-in-use`                                |
| `telemetry-begin`        | `(subr observes () nat)`                                                                                          | Starts a measured run; a token                                        |
| `telemetry-end`          | `(subr observes (nat) run-stats)`                                                                                 | Ends the run the token names, and any newer; its differences          |
| `black-box`              | `(poly ((t type)) (subr observes (t) t))`                                                                         | The identity, which no compiler sees through or drops                 |
| `run-with-stats`         | `(poly ((t type) (e effect)) (subr (maxeff e observes) ((subr e () t)) (productof (value t) (stats run-stats))))` | Runs the thunk between `telemetry-begin` and `telemetry-end`          |

`(time e)` is a derived form, `(run-with-stats (lambda () e))`, as in
Larceny's `macros.sch`. The statistics type is a product, so it is
immutable, pure to take apart with `extract`, and printed with its labels:

```
(define-type run-stats
  (productof (real-ns nat) (cpu-ns nat) (gc-ns nat) (max-pause-ns nat)
             (words nat) (region-words nat) (copied nat)
             (minor nat) (major nat) (peak-words nat)))
```

- **Fields.** `max-pause-ns` and `peak-words` are this run's own. The rest
  are differences. `peak-words` is the high-water mark during the run, not
  above its start, as Chez's peak after `reset-maximum-memory-bytes!` is.
- **The same on every machine.** On the lowered Scheme, and on the
  cellular, register and native machines, each operation is the same
  runtime primitive of the same heap. The values differ between machines
  only because the machines allocate and step differently.
- **Where each piece goes.** Each operation is an entry in standard.rs's
  `ENTRIES`, a `%telemetry-…` primitive in prim.rs, and a line in
  lower.rs's `STANDARD`, which `standard.fx` is generated from.
- **`run-with-stats`** is higher-order, like `with-mark`. It is defined
  once in FX-26 over `telemetry-begin` and `telemetry-end` wherever a
  standard definition written in FX-26 can live, or lowered as
  `%fx26-with-mark` is.
- **The evaluator written in FX-26** calls the same primitives, so it
  measures itself, with `region-words` always 0.
- **For fixpt's own Scheme.** The `%telemetry-…` primitives are callable
  from fixpt's Scheme too, as `%gc-count` is. So the Scheme dialect could
  have Larceny's `run-with-stats` and `time` at no extra cost.

**Cost when unused.** Nothing changes on any allocation path, inline or
not, or in any machine's code. Per collection there are a few additions and
two `max` operations next to the two `Instant` reads it already makes. Per
region chunk there is one addition. The snapshot stack is empty.

**Cost when used.** Each read is one call-out, on the order of 20 ns, and
`cpu-time-ns` adds about 110 ns for its system call. A measured run costs
two call-outs, plus the closure `run-with-stats` makes for the thunk.

## What the heap must start recording, and where

| Field (in `Heap` unless noted)                  | Updated where                                   | For                                |
| ----------------------------------------------- | ----------------------------------------------- | ---------------------------------- |
| `origin: Instant`                               | `Heap::with_semispace`                          | `real-time-ns`                     |
| `minor_nanos`, `major_nanos` (`gc_nanos` = sum) | end of `collect_minor` / `collect`              | stage 2 split; `gc-time-ns` now    |
| `max_minor_pause`, `max_major_pause`            | same                                            | `max-pause-ns`; `FIXPT_GC_SUMMARY` |
| `words_promoted`, `words_copied_major`          | same (`words_copied` = sum)                     | mark/cons ratio, survival rate     |
| `peak_in_use`                                   | entry of `collect_minor` and `collect`; on read | `peak-heap-words`, `peak-words`    |
| `snapshots: Vec<Snapshot>`                      | `telemetry-begin`/`-end`; folded on collection  | nested runs' peaks and pauses      |
| `last_major_live`, `max_major_live`             | end of `collect` (`free`)                       | stage 2                            |
| pause histogram `[u64; 64]`                     | end of each collection                          | stage 2                            |
| `Regions.allocated: Vec<u64>` per handle        | `Regions::bump` turnover, `region_exit`         | stage 2 per-place reads            |
| `Regions.entered`, `exit_nanos`, `released`     | `region_enter`/`reap_enter`, `region_exit`      | stage 2 totals                     |
| per-reap words copied                           | end of `collect`, from `Copier.new[h]`          | stage 2                            |
| `CodeArea` words allocated, swept               | `make_code_bloblet`, `sweep_code`               | stage 2                            |

The snapshots' peaks and pauses are updated where the heap updates its own
peak and pauses: each open snapshot takes the `max`. Only a program inside
`run-with-stats` pays this, and the cost is proportional to its nesting
depth.

## Stages

1. **Rust side, no language change.**
   - Fix `Profile`'s cache key and the reports that print majors alone.
   - Record the first five rows of the table above: the origin, minor and
     major time, the longest pauses, words promoted apart from words
     copied, and `peak_in_use`.
   - Add `FIXPT_GC_TRACE` and `FIXPT_GC_SUMMARY`.
   - Add words allocated and collections (minor/major) as `fixpt bench`
     columns. They are deterministic per machine, so they are the most
     useful numbers in a commit's bench table.
   - A test that `peak_in_use` is the true high-water mark (heap tests,
     with a small nursery).
2. **The first set in FX-26.**
   - Add `@telemetry` to both checkers.
   - Add the fourteen operations, `run-stats` and `(time e)`.
   - Tests that they are summary 2, never licensed, and refused in
     `private-regions`.
   - Tests that `run-with-stats` nests and survives an abort.
   - Tests of relations only (monotone; allocation grows by at least what
     was built), run on every machine.
3. **Regions, and the rest of the counters.**
   - `place-words-allocated`, `place-words-in-use`, and the region totals.
   - Major-live maxima, pause histograms and code-area counters, in the
     summary.
   - `work-units`.
   - Minor and major time as operations of their own, if anyone asks.
4. **Tools, not language.**
   - The sampling allocation profiler through `inline_limit`, reporting by
     source position through the code metadata.
   - The pull-style collection event buffer.
   - Inline clock and counter reads in native code (`cntvct_el0`, and
     loads from a counters block at a fixed address, as `top_address()`
     gives today), if a profile ever shows the call-outs matter.

## Sources

- **fixpt.**
  - `crates/fixpt-heap/src/heap.rs`: `Heap`, `collect`, `allocated`,
    `inline_limit`.
  - `heap/young.rs`: `collect_minor`.
  - `heap/regions.rs`: `Regions`, `bump`, `region_exit`, `region_words`.
  - `heap/code.rs`: `CodeArea`.
  - `crates/fixpt-runtime/src/prim.rs`: `%gc-count`, `%gc-words-copied`,
    `%sro`, `%run-word`.
  - `crates/fixpt-engine/src/cellular.rs`: `Profile`.
  - `crates/fixpt-fx26/src/standard.rs`, `lower.rs`, `licence.rs`,
    `ast.rs` (`Region`, `Atom`), `check.fx` (`define-effect`).
  - `crates/fixpt-fx26/tests/bootstrap.rs`:
    `probe_phases_as_register_code`, `FIXPT_GC_REPORT`.
  - Docs: `docs/fx26.md` ("Globals as a region", "Effect summaries",
    "Regions that end"), `docs/research/generational-gc.md`,
    `docs/research/native-conventions.md`, `docs/performance.md`.
- **Larceny** (on disk, `~/Dev/LangPlay/larceny`):
  - `src/Lib/Common/memstats.sch`: `memstats`, `display-memstats`,
    `run-with-stats`, `run-benchmark`.
  - `lib/Base/macros.sch`: `time`.
  - `doc/UserManual/syscontrol.txt`: `gc-counter`, `major-gc-counter`,
    `sro`, `stats-dump-on`, `run-with-stats`.
  - `doc/DevManual/memstats.txt`.
  - `src/Compiler/iasn.imp.sch` (primop table, `:dead`/`:none`).
  - `src/Rts/globals.cfg` (`G_GC_CNT`, `G_MAJORGC_CNT`).
  - `src/Rts/Sys/sro.c`, `lib/Debugger/profile.sch`,
    `doc/UserManual/starting.txt` (`-annoy-user`).
- **Checked locally.**
  - Python 3.14: `gc.get_stats`, `gc.callbacks`, `tracemalloc`, and the
    clocks' implementations and resolutions via `time.get_clock_info`.
    Their costs were measured by a loop, about 200 000 calls each.
  - Node 26: `v8.getHeapStatistics`, `process.memoryUsage`,
    `process.resourceUsage`, `PerformanceObserver.supportedEntryTypes`,
    and the `--trace-gc` flags.
  - OpenJDK 21 `javap`: `GarbageCollectorMXBean`, `MemoryPoolMXBean`,
    `com.sun.management.ThreadMXBean`.
  - Lua 5.5: `collectgarbage("count")`.
- **Online, read 2026-09-29** (URL and version or commit with each
  runtime in the survey). The source files were read as text in a scratch
  directory, and none was built or run:
  - Chez Scheme: `csug/system.stex`, `smgmt.stex`, `debug.stex` at
    `d9e76eb8e4f283a2bf96f58e3066327b7ab72db9`
    (https://github.com/cisco/ChezScheme); manual for Version 10.4.0.
  - Racket: reference for 9.3; `more-scheme.rkt` at
    `8496bcd58b16faa3c895ed1f67d68a8640a59b2e`.
  - Gambit: `doc/gambit.txi`, `lib/_kernel.scm`, `lib/_repl.scm` at
    `985c0304dd4977203fd8af0b3fc826d93e21e080`.
  - Guile 3.0: `doc/ref/api-memory.texi`, `posix.texi`, `statprof.texi`,
    `libguile/gc.c`, from git master on git.savannah.gnu.org (no commit id
    could be read from the server).
  - MIT/GNU Scheme: the 9.2 manuals at web.mit.edu.
  - SBCL: `doc/manual/beyond-ansi.texinfo`, `src/code/gc.lisp`,
    `time.lisp`, `aprof.lisp`, `contrib/sb-sprof/sb-sprof.texinfo` at
    `7bab5b37ac9b141dfbb5ffabd39a3d69146f92f8`.
  - OCaml: `stdlib/gc.mli`, `runtime/memprof.c`,
    `otherlibs/runtime_events/runtime_events.mli` at
    `7da997d28b1ac57dd3a7108a865b327493fd4239` (5.6.0+dev).
  - MLton: `basis-library/mlton/gc.sig`, `rusage.sig`, `rusage.sml`,
    `runtime/gc/init.c`, `doc/guide/src/Profiling.adoc` at
    `aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37`.
  - SML Basis `TIMER` page (generated 2004-04-12).
  - GHC: users guide for 9.14.1; base-4.22.0.0 on Hackage.
  - Erlang: OTP 29.1.1 documentation; `erlang.erl`, `timer.erl` at
    `fa4ccccea5e227aeff90c3022922435720ccf9b6`.
  - Go: `src/runtime/mstats.go`, `metrics/description.go`, `sample.go`,
    `doc.go`, `debug/garbage.go`, `mprof.go`, `extern.go` at
    `38f24c5c4659b7b8f468e5a2544412e9532e55e9` (go1.28 development).
  - Lua 5.5 reference manual; MDN's `measureUserAgentSpecificMemory`
    page; Java SE 21 API; Python 3.14 and Node 26 documentation.
- **For the worked examples, read 2026-09-29.** Sources were read as
  text, and none was built or run:
  - Chez Scheme: the `black-box` entry and its four examples, and the
    `time` and `sstats-difference` entries, in `csug/system.stex` at
    `d9e76eb8e4f283a2bf96f58e3066327b7ab72db9`
    (https://raw.githubusercontent.com/cisco/ChezScheme/d9e76eb8e4f283a2bf96f58e3066327b7ab72db9/csug/system.stex).
  - OCaml: `Sys.opaque_identity` in `stdlib/sys.mli`, and `quick_stat`,
    `create_alarm` and `Memprof` in `stdlib/gc.mli`, at
    `7da997d28b1ac57dd3a7108a865b327493fd4239`
    (https://github.com/ocaml/ocaml).
  - JMH: `jmh-samples/src/main/java/org/openjdk/jmh/samples/JMHSample_09_Blackholes.java`
    at `a194eead0136bb66e5e59e4fdb2e18543e730929`
    (https://github.com/openjdk/jmh).
  - Racket: `time-apply` and `current-gc-milliseconds` in the 9.3
    reference, https://docs.racket-lang.org/reference/time.html.
  - Haskell: `getMonotonicTimeNSec`,
    https://hackage.haskell.org/package/base-4.22.0.0/docs/GHC-Clock.html,
    and `evaluate`,
    https://hackage.haskell.org/package/base-4.22.0.0/docs/Control-Exception.html.
  - Larceny, on disk at `fef550c7d3923deb7a5a1ccd5a628e54cf231c75`:
    `run-with-stats` in `src/Lib/Common/memstats.sch`, `time` in
    `lib/Base/macros.sch`.
  - Run here: the Python snippets (`time.perf_counter_ns`,
    `gc.get_stats`, `tracemalloc`, `gc.callbacks`) on 3.14.7; the Node
    ones (`process.hrtime.bigint`, `--trace-gc`) on 26.0.0; the Java
    ones (`GarbageCollectorMXBean`, `MemoryPoolMXBean`) on OpenJDK
    21.0.11.
