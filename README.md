# fixpt

A Scheme engine written in Rust, with FX-87 and FX-91 front ends on top of it.

FX-87 and FX-91 are MIT PSRG's effect-typed languages from 1987 and 1991. Both
originals were front ends onto Scheme — `erase.lisp` and `code.scm` type-check,
then emit Scheme and hand it to `eval`. `fixpt` keeps that architecture: one
Scheme engine, two front ends that lower onto it. Conformance is checked
against the recovered originals, running under Racket, in
[`GiffordHistory`](https://github.com/pnkfelix/GiffordHistory).

See [`PLAN.md`](PLAN.md) for the design and the milestone list.

## Status

| | |
|---|---|
| **M0** conformance corpora and golden generators | done |
| **M1** heap, Cheney collector, heap images | done |
| **M2** reader with three syntax profiles | done |
| **M3** Core IR, Scheme expander, AST engine | done |
| **M4** bytecode compiler and VM | next |
| **M5** heap dumping and single-binary builds | |
| **M6** FX-87 front end | |
| **M7** FX-91 front end | |

```
$ cargo test              # 56 tests
$ cargo run -p fixpt-cli -- repl
fixpt 0.1.0 — scheme reader, AST engine
> (define (count-to n) (let loop ((i 0) (acc 0)) (if (= i n) acc (loop (+ i 1) (+ acc i)))))
> (count-to 1000000)
499999500000
> (expt 2 200)
1606938044258990275541962092341162602522202993782792835301376
> (/ 355 113)
355/113
```

## Layout

| crate | what it is |
|---|---|
| `fixpt-heap` | `Value`, the heap, the collector, heap images |
| `fixpt-read` | one reader, three lexical syntaxes |
| `fixpt-core` | the Core IR every front end targets |
| `fixpt-runtime` | numeric tower, equality, printing, primitives |
| `fixpt-engine` | the AST machine (and, from M4, the bytecode VM) |
| `fixpt-scheme` | the Scheme front end: expander, prelude, session |
| `fixpt-cli` | the `fixpt` binary |

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

**Both engines are explicit-stack machines.** Neither uses the Rust call stack
for Scheme recursion, so proper tail calls, unbounded recursion depth and
re-entrant `call/cc` hold in both, and the conformance suite can require that
the interpreter and the compiler agree on every case.

## Conformance

`tests/conformance/` holds corpora and goldens generated from the original
implementations:

* **FX-91** — all 182 top-level forms of the original `tests.fx`, with type,
  effect and evaluated value for each.
* **FX-87** — 155 authored expressions covering the kernel, regions, effect
  masking, subtyping and the standard types, with type and effect for each.

The goldens are checked in, so the test suite needs neither Racket nor the
archive. `reference/regenerate.sh` reproduces them, as a reviewable diff.

`docs/divergences.md` records every place `fixpt` intentionally differs from the
reference, with evidence.
