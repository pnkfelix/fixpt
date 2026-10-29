# Request to Fixpt: time spent loading from `.fasl`s that need not be

Status: drafted 2026-10-28 by Heist, for the user to take to the Fixpt
team. Against Fixpt ec7a02b0 (Heist's subtree). Measured on Heist's
`combo/`, a program of 15 module files. Prototyped in a scratch build only;
Heist's Fixpt is unchanged.

## What was measured

combo, from `.fasl`s, starts in 0.49 s; an empty FX-26 program in 0.18 s.
Profiled with a build that has line tables and frame pointers, the load
does three avoidable things, and the start of every run two more.

| Change, prototyped | combo (CPU) | empty program (CPU) |
|---|---|---|
| none | 0.51 s | 0.21 s |
| `takes_modules_at` reads only the first form | 0.39 s | 0.21 s |
| `embedded_in_self` reads only the executable's trailer | 0.34 s | 0.16 s |
| no CRC of images (an upper bound: a measure, not a proposal) | 0.29 s | 0.11 s |

(The profiling build's empty program is 0.04 s slower than the release
one's, for its 64 MB executable; see the second item.)

## The prompt

Three costs of loading, two of them on every run, measured on a program
of 15 module files loaded from `.fasl`s (Heist's `combo/`, 0.49 s to start,
of which 0.18 s is an empty program's):

1. `parse::takes_modules_at` reads a whole source file with
   `Reader::read_all` to look at its first form; its own comment says "the
   rest is not read". It is called on every load, from eight paths
   (`supply_loaded_in`, `parse_load` under `fasl_load` and `type_loads`, …),
   `.fasl` or not. It was 19% of start-up, and most of what looked like
   `fasl_load`'s, `parse_module`'s and `supply_loaded_at`'s time. Reading
   only the first datum (`Reader::read`, then
   `takes_modules(std::slice::from_ref(&first), …)`) took combo's load from
   0.30 s to 0.18 s.
2. `image_run::embedded_in_self` reads the whole executable (18 MB) on every
   run, to find an embedded image whose trailer is its last 16 bytes.
   Reading the trailer first, and the rest only if `EMBED_MAGIC` is there,
   saves 0.05 s of every run.
3. `image::load` checks a CRC-32 over every image. The front end's cached
   image is now 21 MB (the comment beside `crc32` says 9.5 MB), so this is
   about 0.05 s of every run, and a little more for each `.fasl`. A faster
   CRC (slicing-by-8), or a cheaper check for a file keyed by the
   executable that wrote it, would recover most of it.

With all three, combo starts in 0.29 s rather than 0.49 s. For comparison,
lockpick's Larceny loads the same solver's compiled libraries in 0.32 s.
The `(the T %fasl-value)` re-check of a load, and the image's reading and
linking, were small (a few percent each) once the first item was fixed.
