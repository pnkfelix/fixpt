# Kayak's stage 0: the Fixpt workload to speed up

Oct 24, 2026 · @Felix

Kayak asks Fixpt to run one long program faster: kayak's compiler, written in FX-26, compiling itself under `fixpt run`. Each run takes about 610 s today. This one workload sets the length of kayak's full pre-commit check, 642 s.

What matters is how fast compiled FX-26 code runs once it is loaded. Loading and compiling the program is about 1% of the run, so faster loading alone does not help.

## The workload

Kayak's stage 0 runs Fixpt on kayak's compiler: `kfx/prelude.fx` and the 16 files that `kfx/kfx.unit` lists, joined into one file of about 17,100 lines. Fixpt is built at kayak's pin, `4caffc2`, and runs on its fastest machine:

```
fixpt --dialect fx26 --fx26-machine fx-regs-rsjit-nativecc \
      run kfx.fx -- kfx/kfx.unit OUT_DIR
```

The compiler reads its own sources and writes the Rust in `boot/src/kfx/`, which must come out byte for byte the same. The check starts three of these runs at once, each in its own directory:

1. A plain compile.
2. `--replay LOG`: the same compile, its I/O replayed from a log the Rust build recorded.
3. `--cache MEMOS`: the same compile, starting from memos the Rust build wrote.

All three take about the same time, so speeding up one alone does not help.

## Today's numbers

Fixpt takes about 610 s for the compile that kayak's Rust build of the same compiler does in 0.8 s, roughly 750 times slower. Measured on Linux x86\_64 with 128 cores, at pin `4caffc2`, on 2026-10-23.

| What | Time |
| --- | --- |
| Fixpt, one stage 0 run, three at once (`fixpoint.sh` from start to end) | 601 s alone, 616 s beside the rest of the check |
| Fixpt, the same compiler on a 6-line program (load, check, compile, run) | 6.7 s |
| kayak's Rust build of the compiler, the same compile | 0.8 s |
| kayak's full check | 642 s |
| the rest of the check, which waits for stage 0 | done at 524 s |

The tiny program's 6.7 s sets an upper bound on Fixpt's load and compile cost. The other 600 s or so is the compiler running.

## How to reproduce it

From a kayak checkout at commit `4b92eb5` or later:

```
scripts/fixpt.sh                     # builds the pinned Fixpt; prints its path
mkdir /tmp/s0
time python3 -I scripts/stage0.py kfx/kfx.unit /tmp/s0
diff -r /tmp/s0 boot/src/kfx         # must be empty
```

`scripts/stage0.py` joins the files and runs the command above. To time a newer Fixpt, run the same `fixpt` command with that build in place of the pinned one. For a quick comparison, `tests/kfx/loaded-select.kfx` takes the place of `kfx/kfx.unit OUT_DIR`; it shows the fixed cost and nothing more.

## What would help, and what would not

Only execution speed moves this number. A precompiled or image form helps only if the code it holds runs faster. If it only loads faster, it saves the 6.7 s fixed cost or less.

Kayak has no profile of where Fixpt spends the 600 s. A profile of the plain run is the first thing to look at. One lead turns up without a profile: Fixpt says 13 of the compiler's procedures run as cellular code, because each "has no register code":

- From kayak's checker (`kfx/check.kfx`, `kfx/check-defs.kfx`): `cv-where`, `cv-effdefs`, `cv-dts`, `cv-aliases`, `cv-binds`, `cv-group`, `cv-tvars`, `cv-facts`, `cv-file`, `cv-pos`.
- `prep-inner`, `prep-name`, `prep-forms`.

How much of the run these 13 account for is not yet known.

Any speedup also shortens a standalone run of kayak's `fixpoint.sh`.

## Target and how to measure it

The target is a stage 0 run of about 490 s or less, roughly 20% faster than today. At that point the check no longer waits for Fixpt: it would take about 524 s instead of 642 s. Below that, kayak's own cells-program stage is what the check waits for, so further gains shorten stage 0 but not the check.

The measure is the wall time of `scripts/fixpoint.sh` with the three runs at once, on the same machine. Every run's output must still match `boot/src/kfx/` byte for byte. Kayak moves its pin (`FIXPT_REV`) to a faster Fixpt as soon as one lands, and reports the new time back.
