# Performance, as M12 proceeds

M12 moves pieces of the tooling from Rust into FX-26, which then run on the
Rust engines, so they may well be much slower (`PLAN.md`, §11, decision 10).
This file keeps the record: what each piece costs in each form, measured the
same way each time. If the FX-26 forms become the bottleneck, that is the
signal to start on native code earlier than M10.

Measurements are on the development machine, as best of several runs.
Debug builds are what `cargo test` runs; release numbers come from
`cargo run --release`.

## Baselines, before M12

| what | Rust | Scheme | FX-26 | notes |
|---|---|---|---|---|
| eager reader, `fixpt-fx26/tests/eager.rs` (debug, whole suite) | — | — | 5.5 s | Scheme and FX-26 readers, both engines |
| eager reader, Scheme suite under `gc-stress` | — | 83 min | — | collects at every safepoint |

The per-piece table fills in as each piece moves.
