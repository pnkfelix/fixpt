# Performance, as M12 proceeds

M12 moves pieces of the tooling from Rust into FX-26, which then run on the
Rust engines, so they may well be much slower (`PLAN.md`, §11, decision 10).
This file keeps the record: what each piece costs in each form, measured the
same way each time. If the FX-26 forms become the bottleneck, that is the
signal to start on native code earlier than M10.

**`gc-stress` is not a benchmark.** It collects at every safepoint to shake
out rooting bugs, so it is a correctness check, and far too slow to time
anything with. At a checkpoint that touches the collector, the routine check
is a subset, about a minute:
`cargo test -p fixpt-heap --features gc-stress` and
`cargo test -p fixpt-scheme --features gc-stress --test smoke --test control --test image --test macros`.
The full `fixpt-scheme` suite under it takes well over an hour, mostly the
eager-reader tests, and is run only at milestones.

Measurements are on the development machine, as best of several runs.
Debug builds are what `cargo test` runs; release numbers come from
`cargo run --release`.

## Baselines, before M12

| what | Rust | Scheme | FX-26 | notes |
|---|---|---|---|---|
| eager reader, `fixpt-fx26/tests/eager.rs` (debug, whole suite) | — | — | 5.5 s | Scheme and FX-26 readers, both engines |
| eager reader, Scheme suite under `gc-stress` | — | 83 min | — | collects at every safepoint |

## The engines benchmark, through the object-model changes

`cargo run --release --example engines` (crates/fixpt-scheme/examples/engines.rs):
six small programs on each engine, totals in seconds, best of three runs.
Single programs vary by up to 40% run to run (`fib 25` on the AST engine
ranges 0.028–0.041 s), so only the totals are compared.

| after | AST | bytecode | notes |
|---|---|---|---|
| before M12 (dac418f) | 0.626 | 0.392 | |
| A2–A4 (every object a bloblet header; code as bloblets) | 0.636 | 0.393 | no measurable change |
| A5a, first try (raw types as bloblets; the accessors check the pointer style) | 0.667 | 0.392 | AST ~5% slower: a branch on every node read |
| A5a (code's nodes and constants as its own fields) | 0.634 | 0.393 | back to baseline: a node or constant is one load at a fixed offset from the code |
| A5, first try (every object with fields a trailered bloblet, read through the generic accessor) | 0.689 | 0.416 | 6–8% slower: the trailer decoded out of line on every field read |
| A5, trailer read inline | 0.656 | 0.404 | |
| A5, closures and AST frames at fixed offsets | 0.642 | 0.400 | |
| A5 done (boxes and symbols at fixed offsets; tag `010` retired) | 0.628 | 0.394 | at baseline |

The per-piece table fills in as each piece moves.
