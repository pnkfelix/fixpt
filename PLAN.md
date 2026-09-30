# `fixpt` — a Rust Scheme engine with FX-87 and FX-91 front ends

## At a glance (kept current; last updated 2026-09-30)

Where things stand. Below it is the plan as it grew, oldest first (the
contents are at the end of this section); the details behind this summary
are in the last section, "Log: the glance's details", and in
`docs/performance.md`, `docs/fx26.md` and `docs/research/`.

**Done**
- **The original deliverables** (§0; M0–M7, M9): the Scheme engine (AST
  and bytecode engines, heap images, standalone binaries, hygienic
  macros), FX-87 (161/161 parse, 160/161 type and effect), FX-91
  (182/182).
- **FX-26** (M11, M12): the language, and its reader, parser, checker and
  compiler written in FX-26, bootstrapped to a fixpoint, on
  cellular[^cellular] machines in Rust and arm64. The Rust versions stay
  as oracles: both checkers, and both compilers, must agree.
- **FX-26's type system** (2026-09-27; `docs/fx26.md`): places and regions,
  `letfreeze`; `acyclic` data (named `finite` until 2026-09-28,
  `docs/research/acyclic-regions.md`); `spin` with size-change
  termination; parametric and generative types; lemmas; the `data` kind;
  sizes (`nlist`, `nat`). Globals are a region; redefinition follows one
  rule at the REPL and in files, in both checkers; the REPL is
  incremental.
- **Soundness** (`docs/research/soundness*.md`): a formal core with
  progress and preservation proved, control included; holes F1–F9 and A2
  found and fixed.
- **M13, the compilers** (`docs/performance.md`): the Rust compiler to
  cellular words; register code (the MacScheme machine); guarded inlining,
  specialization at a lambda, versions (a fast body under guards at its
  start), join points; effect summaries in both checkers; constants folded,
  constant data made once; operands in written order, constant chains
  combined; tests compiled as jumps.
- **The native convention** (`docs/research/native-conventions.md`), steps
  1–5 in large part (the collector's part of step 3 is below): conventions
  in types; native frames, `bl`/`ret`; code in the heap's collected code
  area; closures and higher-order code; prompts, marks and continuations
  on native frames. Native and cellular code call each other, nested to
  any depth; a conversion between conventions makes an adapter
  (`%fx26-convert`), and a procedure of the other convention is called as
  through `fx` (2026-09-29). Closures and pairs made inline; one common
  trap, foreign call and closure call-out per machine. Of every test
  program's forms, as the REPL runs them, 117 expressions run as machine
  code; the three declined call `stay-cellular` by design.
- **Tools**: `fixpt check|compile|eval INPUT` (both checkers, both
  compilers); `sexp-edit`, `edit` included; the phase probe
  (`probe_phases_as_register_code`), with collections and allocation by
  word.

- **Reference benchmarks** (2026-09-29, not in the per-commit bench):
  `scheme-bench/`, 51 of Larceny's 75 R7RS benchmarks ported; and
  `mllang-bench/`, MLton's suite, OCaml's classic programs and the
  Benchmarks Game (sources and provenance), 42 ported (2026-09-30: `pi`,
  `chudnovsky`, `pidigits`, `pidigits5`, `smith-normal-form` and
  `DLXSimulator`, which bignums and `u32` unblocked; `md5` and
  `psdes-random` redone in `u32`). Native start-up is 0.19 s (2026-09-30;
  it had grown to 2.7 s; the front end's register code is now cached:
  `docs/performance.md`, "Start-up" and "The front end cached"). Each README lists
  answers, native times, and what blocks the rest (mostly floats, file
  I/O, `eq?` on mutable objects, bignums).
- **Research notes** (2026-09-29, sources checked): `docs/research/floats.md`
  (boxed flonums as the uniform form, unboxed where types say; NaN-boxing
  worked out and declined), `telemetry.md` (an `@telemetry` effect and
  fourteen operations), `async.md` (a scheduler over prompts, structured
  concurrency as region scoping). Each has open questions for the user.

**In progress**
- **The collector** (the user's, 2026-09-29;
  `docs/research/generational-gc.md`): done, all four. Stack maps (each
  native frame's header word, a mask of its live slots); a card-marking
  write barrier in the heap and in every machine that stores inline; the
  cards as the remembered set, with a crossing map; a nursery of 2^20
  words, collected alone, everything live promoted at once. The
  self-compile 0.759 → 0.697 s. Later, if the numbers ask: a survivor
  space (the read phase copies its data twice), card-limited scanning of
  the regions and the code area, which a minor collection scans whole.
- **The native convention, after step 4**: steps 6 (checks where work is
  unbounded; retire `native-compiled` and register code's twins) and 7
  (the closure experiment). A copy of polymorphic code per convention
  waits on calls in a specific convention no longer looking at their
  callee's kind, which is all it would save.
- **The reader's allocation** (the user's): 18.4 → 11.8 M words to read
  the front end (a cursor a token, lambda lifting, atoms taken whole from
  the text); left are the marks of lists, whose shape the Scheme and Rust
  readers share. The self-compile's collections move between phases as
  allocation drops; its total time is about the same.
- **Lambda lifting** is in both compilers (2026-09-28): 5% less
  allocation in the front end's self-compile, one collection fewer, time
  about the same. Later, maybe: as a Twobit-style pass that rewrites the
  program (checkable again, and printable by a `fixpt expand`).

- **Bugs the benchmark ports found** (native path; the lowered one is
  right; queue Q1). Fixed (2026-09-29): `car` of `nil` crashing machine
  code; a native abort not finding a prompt cellular code installed, and
  its cost growing with the stack; an inlined `extract` from an earlier
  form getting field -1; frames too large for one `stp`; register
  exhaustion on long operand chains; more than 8 values in register
  code; a product argument slow natively; an 8 MB native stack; native
  call-outs making major collections where a minor one was due
  (`paraffins` 56 s native, now 9.7; lowered 17). Left: precise globals
  effects doubled `set.fx`'s native time: no, its checking time (the
  native code costs the same; entry below). Q3's counts done: minor
  collections counted, their copying and time apart, regions and code in
  `allocated()`, and `FIXPT_GC_REPORT=1 fixpt eval FILE`.
- **A soundness hole in size inference** (found writing the GADT note's
  examples, `docs/research/examples/gadts/vec-head-hole.fx`): `head` of
  `(poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) t))` applied
  to `(the (nlist int 0) nil)` passes both checkers when `n` is inferred
  (`n + 1 = 0` has no solution, so `n` is left `finite`, and `(+ finite
  1)` is `finite`, which size 0 fits), then fails at run time. Given
  explicitly, `(proj head int 0)` is refused. Fixed (2026-09-29, F10):
  inference solved `n = -1`; a solved size must now be shown no less
  than 0 by the facts in scope, in both checkers (`sizes/solved-*.fx`).
- **Variadic procedures, then `list`** (the user's order, 2026-09-29):
  `vsubr`, `vlambda` and `apply` in both checkers, the lowering, and
  every machine, natively with the count in `x9`; `list` in the standard
  library, its pairs made in line natively, at any region (the user's
  choice). A soundness hole found and fixed (F11): `apply` now copies its
  list unless it is at `acyclic`. The front end, the test programs, the
  examples and the benchmarks now write their lists with `list` (a lint
  for `(cons A (cons B … nil))` in the front end). What is left: an
  `(nlist int n)`, where `list` gives no size, and pairs that are not lists.
- **`.fx` size limits** (the user's, 2026-09-29): 1000 lines and 100
  characters, met by extracting subroutines and splitting files, never by
  re-wrapping (`fixpt_tidy::fx_size`, debt in `fx-size-debt.txt`). Every
  hand-written `.fx` file is within both: the front end, the test programs
  and the examples; the debt list is empty. The two generated files
  (FX-87's `standard.fx`, FX-91's `fx-module.fx`) are exempt (the user's).
  Later: a lint for indentation (`TODO.md` §16).

**Next**, roughly in order. **Soundness first** (the user's, 2026-09-30):
whatever is known or suspected to let a checked program go wrong comes
before everything else, known holes before proofs.
- S1. Done (2026-09-30): **the `acyclic?` gap**, F13: shown a
  use-after-free on every path, and fixed in both checkers with data at a
  place, `(t data p)` (`docs/research/shapes.md`, the framing: regions,
  places and shapes as three axes).
- S2. Done (2026-09-30): **the proof notes' status**. F8 and F9 (closed
  in 9f877ba) re-verified against today's checkers: their probes and tests
  refused, both checkers agreeing. `soundness.md` reconciled: C3 proved on
  both size paths, T3's remaining caveat stated as §4.6's, T5 conjectured
  with no known counterexample; F10–F13 added to its tables.
- S3. Done (2026-09-30): **the depth bounds**. Each of the five, in both
  checkers, gives up by refusing or asking for `spin` or a proof, never by
  accepting (`soundness-findings.md`, after A2); subtyping has none (a
  coinductive trail). The re-check found the FX-26 checker without the
  Rust one's Fourier–Motzkin step, so the two disagreed on chained size
  facts; ported.
- S4. **A3, the host's `datum`s**: acyclic by contract only (Scheme calling
  an `fx:` global); a `read` with datum labels would break it. Enforce at
  the boundary, or certify what such a `read` makes.
- S5. **The proof obligations** (item 4 below, moved here): T3 in full (a
  composable continuation's effect need not describe what its frames
  touch), T4 lemma erasure, T5 termination of `spin`-free code (a logical
  relation over region levels, and size-change proved), T6 space (a
  harness measuring space against `S_place`). Probe each new rule with
  the soundness agent before building on it.

Then the queue in "The queue after the
benchmark ports and the research (2026-09-29)", below: Q1 native-path
bugs (done); Q2 integers (done: every path traps alike; `i32`/`i64`/
`u32`/`u64`, wrapping, their operations in line natively, `i64` and `u64`
raw in native registers, `int` a bignum, a fixnum version of native code,
literals past a fixnum); Q3 telemetry's counts (stage 1 done);
Q4 floats (done: `f64` boxed, `f32` an immediate); the front end's
register code cached (done, `TODO.md` §21.1); Q5 `eq?` and address-hashed tables (done:
one pure `eq?`, `eqtable`; left: the ports' workarounds);
Q6 flat arrays (done); Q7 `consof` and disjoint unions; Q8 generic operations
by dictionary; Q9 separate compilation; Q10 async; Q11 language
friction. Then, as before:
1. Done (2026-09-28): an immediately applied lambda as a `let`;
   procedures that only make a closure as frameless leaves; lambda
   lifting (the check phase 14% less allocation).
2. Versions of bodies with closures; guards per segment between
   `comefrom`s (the user's).
3. The rest of known calls; heap sizing (a collection landing in a phase
   is a step in its time). (The nursery and its write barrier: done,
   2026-09-29.)
4. Moved to the top, as S5 (2026-09-30): the soundness obligations.
5. Sizes N5c: inequalities, "at most n" results, array bounds.
6. The front end written in FX-26: quick wins, then the split into
   `src/fx-rsmirror/` and `src/fx-idiomatic/`.
7. GADTs (N4, to design with the user); a top effect; confirming types
   at run time (CF1–CF5); concurrency and actors.
8. Smaller: `nlist` error messages; the language gaps the survey found;
   M8 docs and polish.
9. Fixed-width integers: now Q2 (the user's, 2026-09-29).
10. Far future: a k-CFA, for what the types do not already say.
11. Maybe never (the user's, 2026-09-30): `eqv?`, R7RS's (numbers and
    characters by value, otherwise `eq?`), for tables keyed by any value
    (`TODO.md` §19).

**Decided with the user (2026-09-29)**: `int` becomes a bignum;
`i32`/`i64`/`u32`/`u64` for fixed widths; `f32` and `f64` (`f64` boxed
where needed); polymorphism by passing dictionaries or tags, not by a
copy of the code per type.

**Decided against, or waiting on the user**
- Speed is judged by native code only (the user's, 2026-09-28):
  superinstructions (13g) are dropped, and so are the cell-for-cell
  compiled words' gaps. Interpreters must still not be asymptotically
  slow.
- Measured and not built: common subexpressions (109 in the front end,
  none in the benchmarks), lifting out of loops (3).
- Waiting on the user ("don't worry about those yet"): region `cons`
  inline natively (`lists-region`), cheaper captures. Deferred:
  `define-rec*`. Not scheduled: M10, a full native compiler.

**Unknown**
- Whether code free of `spin` always ends: T5 is conjectured, and false
  until each hole is closed; a proof wants a logical relation.
- How much space programs take against the model: no harness measures it.
- How GADTs should meet subtyping, what regions a top effect covers, and
  which of the two front ends bootstraps: each needs a decision with the
  user.
- Older items may still be done but unmarked; when one is found, mark it
  where it is written.
- Known, in a test harness only: a session that runs the Rust front end
  with a native runner checks a redefinition with the checker written in
  FX-26's `check-more`, which rejects one that breaks a dependent where
  the REPL breaks it with a note (`redefine/knot-spin.fx` in the report
  `every_test_program_runs_natively_as_cellular`).

**Contents** (the plan as it grew): §0 What this is; §1 Findings from the
archive; §2 Architecture; §3 The core runtime; §4 The core Scheme engine;
§5 FX-87; §6 FX-91; §7 Conformance harness; §8 Milestones; §9 Risks; §10
Decisions (2026-09-20); §11 M12, with its phases, "After M12", "M13
plan", "The queue", "The next queue", "Progress, and what the queue
gained", "A collected code area", "Kept open, deliberately" and
"Decisions (2026-09-25)"; "The queue after the benchmark ports and the
research (2026-09-29)"; then "Log: the glance's details".

## 0. What this is

Three deliverables, in dependency order:

1. **A core Scheme engine in pure Rust.** Not a complete RnRS, but every feature
   it *does* have is spelled the RnRS way (target: R7RS-small flavour, with
   R5RS influence where it simplifies, notably mutable pairs).
2. **Two distinct extensions of that engine**: an FX-87 implementation and an
   FX-91 implementation, each a front end that type/effect-checks its own
   language and lowers to the core engine — exactly the architecture the
   originals used (`erase.lisp` for FX-87, `code.scm` for FX-91 both emit
   Scheme and hand it to `eval`).
3. **Both interpreted and compiled execution**, shared by all three languages:
   an AST machine and a bytecode compiler + VM over one common runtime.

Semantic conformance is checked against `~/Dev/LangPlay/GiffordHistory/`'s
Racket ports of the original implementations (verified working on this machine).

### Naming

`fixpt` — the binary and workspace. Crates are `fixpt-*`.

---

## 1. Findings from the archive that drive the design

Read before planning; these are the constraints that actually shaped it.

| Source                                                                                                                | What it tells us                                                                                                                                                                                                                                                                                                                                                                       |
| --------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `extracted/fx91/{abstract,token,sugar,kind,typecheck,unify,constraints,eval,free,substitution,standard,code,top}.scm` | FX-91's complete structure: mutation-based unification with `forward!` union-find nodes, ACUI effect constraints solved as Horn-clause satisfiability (Dowling–Gallier), `poly~` type schemes, value-restriction via `expansive?`, first-class modules with `up-`/`down-` coercions, `select` dependent types, `rename-moduleof` alpha-renaming.                                       |
| `mit-psrg-fx/fx87/old-impl/{syntax,type-check,inequal,kind-check,erase,sugar,standard}.lisp`                          | FX-87 is *checking*, not inference — but has **more** description machinery: three kinds (`type`/`effect`/`region`), subtyping/subeffecting (`type-less?`/`effect-less?`/`region-less?`), effect masking (`erase-effect`), circular types built with `set-car!` and compared with a cycle `trail`, and a bigger standard library (`oneof`/`recordof`/`vsubr`/`promise`/`port`/`sexp`). |
| `extracted/fx91/tests.fx`                                                                                             | 182 top-level forms. The live reference processes 168 and then dies evaluating form 168 — `nil~: undefined`, a genuine gap in the plain port's runtime (the `fx91-hashlang` runtime supplies `fx-nil~`). Types/effects are fine for all 182.                                                                                                                                           |
| `HISTORY.md` §"Coverage audit"                                                                                        | Known reference gaps to plan around: `[e d1 d2]` proj-sugar is real FX-91 but unreachable through the port's reader; multi-segment dot-notation `a.b.c` is recursive (`(with a (with b c))`), not a literal field name; `(define (f (x int)) ...)` shorthand; `input`; `does` is gated off by default.                                                                                 |
| `fx91-hashlang/lang/reader.rkt`, `fx87-hashlang/lang/reader.rkt`                                                      | Both dialects case-fold symbols; FX-87 reads `#t`/`#f`/`#u` as *symbols*; FX-91 reads `#u` as the symbol `#U` but `#t`/`#f` as real booleans. The reader is genuinely per-dialect.                                                                                                                                                                                                     |
| `larceny/src/Compiler/pass{1,2,3,4}*.sch`                                                                             | Pass structure worth borrowing: alpha-renamed core grammar, nodes annotated in place with free/assigned/referenced sets. Worth *not* borrowing: fifteen passes and four native back ends.                                                                                                                                                                                              |
| `larceny/src/Rts/Sys/heapio.{c,h}`                                                                                    | Heap image format: version word, roots, word count, data — all pointers base-0 relative so load needs no relocation. We take this idea and drop the split/dumped variants.                                                                                                                                                                                                             |

### Reference implementations are runnable here

```
/Applications/Racket v9.3/bin/racket    # v9.3, fx-lang linked as a user package
$ racket fx87/typecheck.rkt   →  3 => (int . pure);  (the pure bool 3) => USER ERROR
$ racket fx91/check.rkt       →  ": <type>  ! <effect>  = <value>" per form
```

This is the single most important fact for the project: **every conformance
answer can be generated, not guessed.**

---

## 2. Architecture

```
                   ┌──────────────┐  ┌──────────────┐  ┌──────────────┐
  front ends       │ Scheme       │  │ FX-87        │  │ FX-91        │
                   │ expander     │  │ check+erase  │  │ infer+codegen│
                   └──────┬───────┘  └──────┬───────┘  └──────┬───────┘
                          │                 │                 │
  reader (per-dialect syntax profiles) ─────┴─────────────────┘
                          │
                   ┌──────▼────────────────────────────────┐
  shared middle    │  Core IR  (arena of nodes + passes)   │
                   └──────┬───────────────────┬────────────┘
                          │                   │
                 ┌────────▼──────┐   ┌────────▼─────────┐
  engines        │ AST machine   │   │ bytecode compiler│
                 │ (interpreted) │   │  + VM (compiled) │
                 └────────┬──────┘   └────────┬─────────┘
                          └─────────┬─────────┘
                   ┌────────────────▼──────────────────────┐
  runtime          │ values · heap · Cheney GC · primitives │
                   │ symbols · globals · ports · images     │
                   └───────────────────────────────────────┘
```

Key property: **FX-87 and FX-91 are front ends, not interpreters.** They
produce Core IR, so both automatically get the interpreter, the bytecode
compiler, heap dumping and single-binary builds — which is how requirement 3
("interpreted and compiled") is satisfied for all three languages without
writing three of everything.

### Crates

| Crate           | Contents                                                                     | Rough size |
| --------------- | ---------------------------------------------------------------------------- | ---------- |
| `fixpt-heap`    | `Value`, tagged-word heap, object layouts, Cheney GC, image dump/load/verify | 2.5k       |
| `fixpt-runtime` | symbols, globals, numerics, strings/vectors, ports, errors, primitive table  | 3k         |
| `fixpt-read`    | syntax profiles, lexer, reader, spans, `write`/`display`                     | 1.2k       |
| `fixpt-core`    | Core IR arena, binding/env, pass framework, standard passes                  | 1.5k       |
| `fixpt-engine`  | `interp` (AST machine) + `vm` (compiler + bytecode VM)                       | 4.5k       |
| `fixpt-scheme`  | Scheme dialect: special forms, `syntax-rules`, prelude                       | 2.5k       |
| `fixpt-fx87`    | FX-87 front end                                                              | 5k         |
| `fixpt-fx91`    | FX-91 front end                                                              | 6k         |
| `fixpt-cli`     | the `fixpt` binary                                                           | 0.8k       |

Dependencies kept deliberately thin: `num-bigint`/`num-integer` for exact
integer arithmetic, `clap` in the CLI crate only. The heap, GC, reader, engines
and both type checkers are dependency-free.

---

## 3. The core runtime (requirement: no ref-counting, heap-dumpable)

### 3.1 Value representation

A `Value` is a `u64` with a 3-bit low tag. Object references are **word offsets
into a `Vec<u64>` heap, never Rust pointers** — this is what makes ref-counting
unnecessary, makes a moving collector possible, and makes a heap dump a
`write_all` of the vector.

```
tag 000  fixnum            i61, value = (w as i64) >> 3
tag 001  pair              (w >> 3) = word index of a 2-word car/cdr cell
tag 010  object            (w >> 3) = word index of a header word
tag 011  immediate         subtag in bits 3..8: #f #t () #u eof unspecified char
tag 100  reserved
tag 101  reserved
tag 110  reserved
tag 111  forwarding        GC-internal only
```

Object header: `len:32 | typecode:8 | flags:8 | HDR:8`. Object types: `String`,
`Symbol`, `Vector`, `Bytevector`, `Flonum`, `Bignum`, `Ratnum`, `Closure`,
`Code`, `Box`, `Record`, `RecordType`, `Port`, `Continuation`, `Values`,
`Promise`, `HashTable`, `Environment`. FX's runtime shapes (`*module*`,
`*sum*`, `*product*`) are ordinary `Record`s — no new object kinds.

### 3.2 Collector

**Cheney semispace copying collector.** Chosen over mark-sweep because it
compacts, which makes a dumped image contiguous and relocation-free. Roots are
the VM/interpreter stack, the globals vector, the interned-symbol table, and an
explicit shadow root stack. Not generational — the user said not to bother, and
the object model above admits a generational upgrade later without changing
`Value` or the image format.

### 3.3 GC safety in Rust — the one real hazard

A `Value` sitting in a Rust local is stale after a collection. Two mechanisms,
both explicit:

* **Safepoints.** Collection can only happen at declared safepoints (procedure
  entry, backward branches, explicit `gc_check`), where every live value is
  already in a rooted structure.
* **Root scopes.** Primitives that allocate more than a bounded amount take a
  `&mut Ctx` and use `let r = ctx.root(v);` RAII guards. `#[must_use]`, so
  forgetting one is a compile-time nag rather than a Tuesday-afternoon
  heisenbug.

A debug feature (`gc-stress`) collects at *every* safepoint; the whole test
suite runs under it in CI.

### 3.4 Heap images — all three shipping modes the user asked for

Format (deliberately simpler than Larceny's three variants — one variant):

```
magic "FIXPTHP\0" | version u32 | flags u32 | word_count u64 | root_count u32
[ heap words, all references base-0 relative ]
[ root words ]
[ crc32 ]
```

Because Cheney already compacted to a contiguous region and every reference is
base-relative, **dump = write, load = read**. No relocation pass exists.

| Mode                     | Command                                                             | Mechanism                                                                                                                      |
| ------------------------ | ------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| Decoupled runtime + heap | `fixpt run --heap prelude.heap prog.scm`                            | separate `.heap` file                                                                                                          |
| Coupled single binary    | `fixpt build prog.scm -o prog`                                      | copy the runtime binary, append the image + an 16-byte trailer (`magic`,`len`); `./prog` self-loads by reading its own trailer |
| Statically embedded      | `FIXPT_EMBED_HEAP=x.heap cargo build -p fixpt-cli --features embed` | `build.rs` + `include_bytes!`                                                                                                  |

Compiled code objects live *in the heap*, so a `.fasl` is just a heap image
whose root is a top-level thunk. "Compile a program" and "dump a heap" are the
same operation with different roots — the thing Larceny got right, minus the
thing it never shipped (the appended-trailer single binary).

---

## 4. The core Scheme engine

### 4.1 Reader with pluggable syntax profiles

Requirement: *"you'll need to support other reader syntaxes."* The reader is
parameterised by a `SyntaxProfile`:

```rust
pub struct SyntaxProfile {
    case_fold: CaseFold,               // None | Down
    brackets: BracketMode,             // Paren | SymbolConstituent | ProjSugar
    dispatch: HashMap<char, Dispatch>, // '#' macros
    symbol_extra: &'static str,        // e.g. '@' leading for FX-87 regions
    datum_labels: bool, block_comments: bool, datum_comments: bool,
}
```

Three profiles ship:

| Profile  | Case      | `#t`/`#f`                     | `#u`            | `[ … ]`              | Notes                                          |
| -------- | --------- | ----------------------------- | --------------- | -------------------- | ---------------------------------------------- |
| `scheme` | sensitive | booleans                      | —               | parentheses          | R7RS: `#\c`, `#u8(`, `#;`, `#\|…\|#`, labels   |
| `fx87`   | folded    | **symbols** `\|#t\|`/`\|#f\|` | symbol `\|#u\|` | symbol constituents  | `@region` symbols                              |
| `fx91`   | folded    | booleans                      | symbol `#U`     | **`(proj …)` sugar** | reconstructs the reader macro the archive lost |

The reader produces Rust-side spanned `Syntax` values (so error messages have
real source locations and the compiler never touches the GC heap), with a
`Syntax → Value` conversion used by `quote` and a `Value → Syntax` conversion
used by runtime `eval`.

### 4.2 Core IR — built for static analysis

An arena (`Vec<Node>` + `NodeId`), not a tree of boxes, so passes can annotate
in place and analyses can use dense side tables:

```
E ::= Const(Value) | Ref(Var) | Set(Var,E) | If(E,E,E) | Seq(E*)
    | Let(Var*, E*, E) | LetRec(Var*, Lambda*, E)
    | Lambda(Formals, Body) | App(E, E*)
```

Alpha-renamed at expansion time (unique `VarId`s). Side tables hold free
variables, assigned variables, arity, source spans, and — this is the hook FX
uses — arbitrary per-node analysis results.

Passes (four, not Larceny's fifteen): free-variable/assignment analysis →
assignment conversion (box mutated variables) → lexical addressing / closure
conversion → primitive inlining + constant folding.

### 4.3 Two engines, one calling convention

Both are **explicit-stack machines**. Neither uses the Rust call stack for
Scheme recursion, so both get proper tail calls, unbounded recursion depth,
identical `call/cc` semantics, and precise stack scanning for free.

* **`interp`** — walks Core IR nodes with an explicit control stack; chained
  heap environment frames (O(lexical depth) variable lookup).
* **`vm`** — Core IR → stack bytecode (~50 ops), flat closures (O(1) lookup),
  code objects allocated in the heap.

`call/cc` in both is "copy the machine stack slice into a heap object"; invoking
restores it. Full re-entrant continuations, `dynamic-wind`, `values`. Each
engine restores only its own continuations; that's the sole documented
difference and it is not observable from Scheme.

Beside the frames, both engines keep a **mark stack** (Flatt & Dybvig's
attachments, `fixpt-runtime/src/cmarks.rs`): continuation marks, tagged prompts
and `dynamic-wind` extents, each recorded as the frame depth and stack height it
belongs to. That is what supports SRFI 226's composable continuations and
aborts, and it keeps exception handlers out of globals. The representation is
shared, so the two engines agree on it by construction. Added 2026-09-24,
after M7; `TODO.md` §9 has the details and what is still approximate.

Every conformance test runs under **both** engines and the results must agree —
differential testing is the main defence against engine-specific bugs.

### 4.4 RnRS scope — explicit in/out

**In.** Proper tail calls; `lambda` with rest args; `define` incl. internal
defines; `set!`; `quote`/`quasiquote`; `let`/`let*`/`letrec`/`letrec*`/named
`let`; `do`; `cond` (incl. `=>`); `case`; `and`/`or`/`when`/`unless`/`begin`;
`delay`/`force`/`make-promise`;
`define-record-type`; `call/cc`; `dynamic-wind`; `values`/`call-with-values`;
SRFI 226's continuation marks, tagged prompts, `abort-current-continuation` and
`call-with-composable-continuation`;
`apply`; `eval` + environment specifiers; `raise`/`with-exception-handler`/
`guard`/`error` + error-object accessors; textual string and file ports;
`read`/`write`/`display`; the list/char/string/symbol/vector/bytevector
libraries; exact integers (fixnum + bignum + ratnum) and inexact `f64`.

**Also in, though R7RS dropped it:** `set-car!`/`set-cdr!` and mutable pairs —
because **FX-91's `listof` is genuinely mutable-pair-based** and the reference
implementation depends on it. Documented as an R5RS-compatible extension.

**Added in M9.** `define-syntax`/`let-syntax`/`letrec-syntax` with hygienic
`syntax-rules`, by Clinger & Rees renaming. The expander's scope chain made it
an addition rather than a rewrite, as intended. The derived forms (`let`,
`cond`, `case`, `do`, `when`, …) stay native expander forms, which is what most
Schemes do, but they are now hygienic, and R7RS §7.3's `syntax-rules`
definitions of them run and agree. See [`docs/macros.md`](docs/macros.md).

**Out, and documented as such.** Complex numbers; the full exactness-contagion
corner cases; `syntax-case` (see `docs/macros.md` for why ER/IR instead); R6RS libraries and
`define-library`; full Unicode normalisation/`char-ready?`; threads.

---

## 5. FX-87 front end

Mirrors `old-impl/`'s own decomposition so that divergences are easy to localise
against the reference.

* **Reader**: `fx87` profile.
* **Syntax** (`syntax.rs`): kinds `type`/`effect`/`region`; descriptions —
  regions (`@x`, `runion`), effects (`pure`, `read r`, `write r`, `alloc r`,
  `maxeff`), types (`bool`, `unit`, `subr`, `poly`, `ref t r`, plus the standard
  library's `int`/`char`/`float`/`string`/`symbol`/`null`/`uniqueof`/`pairof`/
  `listof`/`vectorof`/`oneof`/`recordof`/`promise`/`vsubr`/`port`/`sexp`),
  `dfunc`/`dlambda`/application/`dlet`/`dletrec`.
* **Expressions**: literals, variables, `begin`, `the`, `lambda`, application,
  `letrec`, `plambda`, `proj`, `plet`, `pletrec`, `if`, `set!`, plus the
  standard special forms (`record`/`record-set!`/`select`, `oneof`/`tagcase`/
  `one`/`one-set!`, `delay`, `vlambda`, `new`). Sugars: `and or let let* cond
  do plet* dlet*`.
* **Descriptions are an arena too** (`Vec<DescNode>` + `DescId`) — the original
  builds *circular* types with `set-car!` and compares them with a cycle
  `trail`; an arena of indices reproduces that exactly without `Rc<RefCell<…>>`.
* **Static analysis**: kind checking; then type/effect *checking* against
  explicit ascriptions, with subtyping (`type-less?`), subeffecting
  (`effect-less?`), region containment (`region-less?`), and **effect masking**
  (`erase-effect`: drop effects on regions not free in the result type or
  environment) — FX-87's signature feature.
* **Lowering**: type erasure → Core IR, mirroring `erase.lisp`.
* **Top level**: `define`, `pdefine`, `load`, expression.

**Known-incomplete in the original, therefore stubbed here too, loudly:** the
`struct`/`structof`/`convert`/`abstract`/`extract` ADT cluster (nine
identifiers called but never defined; `*support-adts*` defaults off).

## 6. FX-91 front end

* **Reader**: `fx91` profile, *including* the `[e d1 … dn]` → `(proj e d1 … dn)`
  reader sugar. The original reader macro is lost and the Racket port can't
  reach the feature at all; we control our reader, so we implement it properly
  and gain a case the reference can't check — flagged as a documented,
  intentional divergence with the report's §2.4.9 grammar as the authority.
* **Syntax**: kinds `type`/`effect`/`(dfunc k…)`; descriptions — variables,
  `dlambda`, application, `select`, `maxeff`, `subr`/`->`, `poly`, `poly~`
  (internal type schemes), `moduleof`, `sumof`, `productof`; effect constants
  `read`/`write`/`init`, `pure` = `(maxeff)`.
* **Expressions**: literals, variables, `lambda`, `let`, `plambda`, `proj`,
  `module`, `with`, `extend`, application, `if`, `open`, `close`, `begin`,
  `load`, `the`, `does`, `sum`, `product`, `tagcase`, `extract`.
* **Desugaring**: `and or let* letrec cond do match`; dot-notation, implemented
  **recursively** per §2.4.7 (`a.b.c` → `(with a (with b c))`) — the bug the
  Racket `#lang` has and the original doesn't; `match` with constructor and
  quasiquote patterns; `define`/`define-typed` shorthands incl. the
  `(define (f (x int)) …)` and `(define [f (t type)] …)` forms; `define-datatype`
  expanding to `define-abstraction` + `define-description` + per-tag
  constructor/destructor pairs; `moduleof`'s `abs`/`desc`/`val` grouping sugar.
* **Static analysis** — the substantial piece, ported structurally from
  `typecheck.scm`/`unify.scm`/`constraints.scm`:
  * kind checking (`kind.scm`);
  * mutation-based unification with union-find `forward!` nodes — an arena of
    description nodes with a `parent` field, path-compressed;
  * generalisation to `poly~` schemes with the value restriction (`expansive?`);
  * **ACUI effect constraints** solved as propositional Horn satisfiability
    (Dowling–Gallier), per Jouvelot & Gifford POPL'91;
  * dependent `select` types and `rename-moduleof` alpha-renaming;
  * inferability (`inferability.scm`) and description normalisation with beta/eta
    reduction (`eval.scm`).
* **Lowering**: → Core IR, mirroring `code.scm`'s `*module*`/`*sum*`/`*product*`
  runtime shapes (as `Record`s) and the `up-`/`down-` identity coercions.
* **Runtime**: the `fx` module's primitives — `bool`, `unit`, `refof`, `int`,
  `float`, `char`, `string`, `sym`, `permutation`, `uniqueof`, `listof`
  (mutable pairs!), `vectorof`, `sexp`. `input-stream`/`output-stream` get real
  I/O here, which the Racket port explicitly doesn't have.

---

## 7. Conformance harness

### 7.1 Golden generation (offline, needs Racket)

`reference/` holds small Racket drivers run by `cargo xtask goldens`:

* `fx87-golden.rkt` — mirrors `erase.lisp`'s `top-level` dispatch
  (`pdefine`/`define`/expression), prints one normalised `type . effect` record
  per form.
* `fx91-golden.rkt` — mirrors `top.scm`'s `fx91` loop: parse → typecheck →
  `unparse-dexp` type and effect → evaluate, with the evaluation in a handler so
  the 14 forms the port can't evaluate record `<eval-error: nil~ undefined>`
  instead of killing the run. The missing `nil~`/`cons~` bindings are supplied
  from the `fx91-hashlang` runtime so we can get values for those too, recorded
  separately as `augmented` goldens.

Outputs are checked into `tests/conformance/{fx87,fx91}/*.expected`, so the Rust
test suite runs with no Racket installed. Regenerating is an explicit,
reviewable diff.

### 7.2 Normalisation

Both sides go through the same canonicaliser before comparison — the reference
prints gensym counters (`fail-2877`, `letrec-2036`) and unification-variable
numbers (`*UNIF*-123`) that are run-dependent:

* renumber gensyms and unification variables by order of first appearance;
* sort `maxeff` operands by canonical printed form;
* canonicalise alpha-renamed description variables;
* `#<procedure:…>` → `#<procedure>`; sort `*module*` association lists.

### 7.3 Corpora

| Suite            | Source                                                                                                                                                               | Size                            |
| ---------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------- |
| FX-91 static     | `extracted/fx91/tests.fx`                                                                                                                                            | 182 forms × (type, effect)      |
| FX-91 dynamic    | same                                                                                                                                                                 | 168 values + 14 augmented       |
| FX-87            | `mit-psrg-fx/fx87/library/*.fx` (tak, complex, church-numerals, deriv, dna, polynm, hash, takl, symbol-tab) + an authored expression suite run through the reference | ~13 programs + ~200 expressions |
| Scheme           | authored R7RS assertion suite                                                                                                                                        | ~400 assertions                 |
| Differential     | every case above                                                                                                                                                     | interp vs. vm must agree        |
| GC stress        | every case above                                                                                                                                                     | `--features gc-stress`          |
| Image round-trip | every case above                                                                                                                                                     | dump → load → rerun → identical |

### 7.4 Divergences are a deliverable

`docs/divergences.md` records, with evidence, every place we intentionally
differ from the reference — the recursive dot-notation, `[]`-projection,
`nil~`, real stream I/O, the FX-87 ADT stubs, and the archive bugs listed in
`HISTORY.md`. A conformance case may be marked `expected-divergence`, which
requires *both* outputs to be recorded. No silent disagreements.

---

## 8. Milestones

Each ends with a working, tested, demoable artifact. I'd like to check in with
you at each boundary rather than disappear for the whole thing.

| #      | Milestone                                                                                                    | Demo at the end                                                                                                                                                                                                                                                                                                                                                                                                              |
| ------ | ------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| M0 ✅  | Workspace, golden generators                                                                                 | `reference/regenerate.sh` produces the checked-in `.expected` files: 182 FX-91 cases (type, effect, value), 155 FX-87 cases (type, effect)                                                                                                                                                                                                                                                                                   |
| M1 ✅  | `fixpt-heap`: values, heap, Cheney GC, image dump/load/verify                                                | `fixpt image info/verify`; 22 tests, green under `gc-stress`                                                                                                                                                                                                                                                                                                                                                                 |
| M2 ✅  | `fixpt-read`: profiles, reader, writer, spans                                                                | 21 tests; all 182 FX-91 and 155 FX-87 forms read and round-trip                                                                                                                                                                                                                                                                                                                                                              |
| M3 ✅  | `fixpt-core` + `fixpt-runtime` + `fixpt-scheme` + `interp`                                                   | `fixpt repl` works: bignums, rationals, proper tail calls, re-entrant `call/cc`, `dynamic-wind`, `guard`, records, promises. Green under `gc-stress`                                                                                                                                                                                                                                                                         |
| M4 ✅  | `vm`: bytecode compiler + VM                                                                                 | flat closures, assignment conversion, 19 opcodes. FX-91's 182 cases pass **compiled as well as interpreted**; 9 differential tests require both engines to agree on values, output *and* error text; ~1.6× faster                                                                                                                                                                                                            |
| M5 ✅  | Images & shipping                                                                                            | Core IR lives in the heap, so an image is resumable. `fixpt dump-heap` (image beside the runtime), `fixpt build` (one standalone executable, no `fixpt` needed on the target), `fixpt run-image` (either). An image records which engine made it, so nothing has to be told                                                                                                                                                  |
| M6 ✅  | `fixpt-fx87`                                                                                                 | 161 cases: **161/161 parse, 160/161 type and effect, 123/123 value** of those the archive's evaluating path can answer. Driven from the CLI as `fixpt --dialect fx87 repl\|run\|eval`                                                                                                                                                                                                                                        |
| M7 ✅  | `fixpt-fx91`                                                                                                 | **182/182 on all three levels** — parse, type and effect, and evaluated value. Driven from the CLI: `fixpt --dialect fx91 repl\|run\|eval`, presenting results in the 1991 top level's `:`/`!`/`=` notation                                                                                                                                                                                                                  |
| M8 🔶  | Docs & polish                                                                                                | `docs/` mapping every component to its 1987/1991 counterpart; benchmarks (`cargo run --release --example engines` is the start). Collector workloads from Larceny's `test/GC` already landed in `tests/gc_workloads.rs`                                                                                                                                                                                                      |
| M9 ✅  | hygienic macros                                                                                              | `define-syntax`/`let-syntax`/`letrec-syntax`/`syntax-rules`, hygienic by renaming (Clinger & Rees); the built-in derived forms hygienic too; R7RS §7.3's own macro definitions of the derived forms pass against the built-ins. SRFI 211 `er-macro-transformer` and `ir-macro-transformer`, with `begin-for-syntax`. SRFI 139 syntax parameters, `identifier-syntax`, `syntax-error`. See [`docs/macros.md`](docs/macros.md) |
| M11 ✅ | FX-26: the tooling's own language (the seven-step plan, done 2026-09-25)                                     | effects as licences, bidirectional checking, typed delimited control; the eager reader ported to it first. Direction and plan: [`docs/fx26.md`](docs/fx26.md)                                                                                                                                                                                                                                                                |
| M12    | FX-26, bootstrapped: its interpreter and compiler written in FX-26, over a new object model shared with Rust | three phases — bloblets, FX-26 over bloblets, bootstrapping. See §11 and [`docs/object-model.md`](docs/object-model.md)                                                                                                                                                                                                                                                                                                      |
| M10    | *(future)* native code generation                                                                            | the bytecode/heap-image design is kept amenable to it; not scheduled                                                                                                                                                                                                                                                                                                                                                         |

Rough total ~26k lines of Rust. M6 and M7 are each comparable in size to
everything before them; M7 is the hardest (inference + ACUI + modules).

---

## 9. Risks, and what I'd do about them

1. **FX-91 inference exactness.** Generalisation × ACUI × dependent `select`
   types × module renaming is where the subtlety lives.
   *Mitigation:* port the algorithm **structurally** — same function
   decomposition and same names as `typecheck.scm`/`unify.scm`/`constraints.scm`
   — rather than reinventing it. The Racket port proved that strategy works.
   Conformance is per-form, so failures localise to one of 182 expressions.
2. **FX-87 circular types + effect masking.** Cycle-safe comparison and region
   liveness are both easy to get subtly wrong.
   *Mitigation:* arena + explicit `trail`, mirroring `inequal.lisp`; the authored
   expression suite targets masking specifically.
3. **GC/Rust value staleness.** Addressed by safepoints + `#[must_use]` root
   guards + a `gc-stress` CI job that collects at every safepoint.
4. **Reference bugs.** Several are documented in `HISTORY.md` and one (`nil~`) I
   hit directly.
   *Mitigation:* implement correct behaviour, record the divergence with
   evidence, keep both outputs in the golden file. Never silently "conform" to a
   bug or silently deviate from one.
5. **Scope.** This is a large build.
   *Mitigation:* the milestone boundaries above are real check-in points; M0–M5
   stand on their own as a usable Scheme even if you want to re-scope M6/M7.

---

## 10. Decisions (confirmed by the user, 2026-09-20)

1. **`syntax-rules` — deferred.** Not in the critical path; scheduled as M9.
   The expander keeps a macro-transformer seam so it lands as an addition.
2. **Compiled story confirmed** as bytecode + heap images + single binary. No
   C-source back end. Native code generation is a later project (M10); the
   Core IR, code-object layout and heap-image format are all designed to admit
   it without redesign.
3. **Exact rationals kept**, so `/` behaves per R7RS.
4. **Correctness over bug-fidelity confirmed.** We implement the correct
   behaviour and record every intentional difference from the reference in
   `docs/divergences.md`, with evidence and both outputs. This is deliberately
   the opposite of the Racket port's "preserve the original, bugs included"
   rule, and it is what "conformance" means in this project.

---

## 11. M12: bootstrapping FX-26 (planned 2026-09-25)

**The goal.** The FX-26 interpreter and compiler are written in FX-26. What
stays in Rust:
- **A bootstrap interpreter**, for as long as there is FX-26 to bootstrap.
- **The garbage collector.**

Between them, the value representation is shared by both halves: the
**bloblet**, specified in [`docs/object-model.md`](docs/object-model.md).

**A bloblet** is a header, then tagged fields, then an untraced binary
suffix, with every tagged pointer pointing at the start of the suffix.
Fields are named by negative offset from there, so code can reach its own
metadata at fixed offsets, and new fields can be prepended. Records,
vectors, bytevectors, strings, numbers, closures and code all become
bloblets, and the collector stops needing to know what anything is.

**The method, taken from the eager reader.** Each piece moved into FX-26
keeps its Rust version as the oracle it is checked against on the same
inputs, and then as stage 0. Retiring a Rust piece is a separate decision,
made piece by piece.

### Phase A: the object model (`fixpt-heap`, in Rust)

1. **`docs/object-model.md`**, reviewed and committed. *(Done.)*
2. **One specification table**: tags, header bits, kinds, and the reserved
   trailer. The Rust constants are generated from it, and later an FX-26
   module too, with a test that the two agree. *(Done: `fixpt-heap`'s
   `layout.rs`, with `src/layout.fx` and `src/native-layout.fx` generated
   from it and checked by `tests/layout.rs`.)*
3. **Bloblets in the heap, alongside today's objects:**
   - allocation, through the layout/placement interface, with the default
     placement;
   - the four-step construction protocol, whose header changes once, before
     publication;
   - the two frozen flags;
   - the trailer and the backward scan;
   - bloblet pointers (tag `100`), and forwarding through them, including the
     second forward for trailer-less bloblets;
   - tracing, verification, and a new heap image version.

   Tested under `gc-stress`, and with deliberately trailer-less bloblets so
   the backward scan runs. *(Done: everything since is built on them.)*
4. **Code as bloblets**, compiled form: constants and metadata in fields at
   fixed negative offsets, which are part of the layout specification, and
   bytecode as the suffix. Closures hold bloblet pointers. *(Done
   2026-09-25.)* The *cellular* form, with the program in the fields, is a
   new execution mode with an inner interpreter. It is built with the native
   inner interpreter, A′3, where the Rust bootstrap version is its oracle.
5. **The other types, one at a time**: vectors, bytevectors, strings (UTF-32),
   flonums, bignums, records, boxes and the rest. At the end, the collector no
   longer needs to know what anything is: `ObjType::payload_is_scanned` and
   tag `010` are retired. Pairs stay as they are.

### Phase A′: a native core (in Rust, arm64 first)

In the Forth vision a code bloblet's suffix is machine code, even for
cellular code, where it is the inner interpreter. So a small native core
belongs to M12. M10 keeps a full native compiler.

A1. **`fixpt-native`**, the one crate where `unsafe` is allowed:
    - executable memory, mapped with `MAP_JIT` on macOS;
    - writing and executing toggled per thread;
    - instruction-cache invalidation, which is the "seal" step of the object
      model;
    - calls into a code bloblet's suffix, and back out to `extern "C"`
      runtime functions.

    Every unsafe block states the rule it relies on. *(Done 2026-09-26, with
    one change: the code space is mapped twice, read+write and
    read+execute, instead of toggling `MAP_JIT`, because the measurements
    in `docs/object-model.md` showed that lets fields beside code change
    with no flush and no re-protection.)*
A2. **An arm64 encoder**, in Rust, covering only the instructions needed:
    loads, stores, arithmetic, branches, calls and returns. It is our own
    code generation, not copies of Rust-compiled code, whose position
    independence and extent Rust does not promise. It is the stage-0 oracle
    for the FX-26 compiler's own encoder. *(Done 2026-09-26; each encoding
    is checked against the system assembler, which is used only as that
    oracle.)*
A3. **A native inner interpreter** (`NEXT`) as the suffix of cellular code
    bloblets, run beside the Rust bootstrap interpreter and checked against
    it. *(Done 2026-09-26, as `fixpt_engine::cellular` (the Rust machine,
    and the word layout, `layout::cellular`) and `fixpt_native::cellular`.
    A change from the text above: the heap is not executable and moves, so
    a word's entry is a routine *number*, and the routines live in the code
    space. That also keeps machine addresses out of heap images. Cells are
    token-cellular primitives or words. Both machines check fuel and stack
    limits at word entry and taken branches, and agree on every trap but
    underflow, which the native machine turns into a guard-page fault.
    Measured in `docs/performance.md`: about 0.55 ns per cell natively,
    5× the Rust machine.)*
A4. **Stencils**: primitives written in Rust with `become`, compiled by the
    build script with the installed nightly, and copied into the code space
    beside the hand-encoded ones; checked against them and measured.
    *(Done 2026-09-26: the whole machine as stencils, at `-O0` through
    `-Os`, with no relocations, so placed by copying; every level checked
    against the Rust machine by the same tests. Optimised, they match the
    hand-encoded machine; see `docs/performance.md` and the addendum in
    `docs/research/copy-and-patch.md`.)*

### Phase B: FX-26 over bloblets

6. **FX-26's view of bloblets:**
   - a type along the lines of `(bloblet (fields T…) R)`;
   - reads by field and by byte, and code-pointer types;
   - the construction protocol and `seal` as primitives, with the `init`
     effect, so a record's fields count as uninitialised until stored and
     frozen fields offer no writes;
   - the layout module generated in step 2.

   *(Done 2026-09-26, but for the `init` effect and code-pointer types,
   which wait for their first user, the compiler in step 11: construction
   initialises every field at once, so nothing is seen uninitialised. See
   `docs/fx26.md`, "Bloblets". Scheme has the same operations as `%bloblet`
   primitives, which write only bloblets a program made.)*
7. **The data types the tooling needs, built on bloblets:**
   - records and sum types (`oneof`/`tagcase`);
   - tables;
   - symbols as values.

   *(Sums, products, `tagcase`, `define-datatype` (FX-91's), arrays and
   symbols done 2026-09-26; see `docs/fx26.md`. Tables too, written in
   FX-26 over arrays (`src/table.fx`), with parametric type abbreviations
   and `plambda` checked against `poly` added to make that writable. Modules are deferred until the checker in FX-26 spans
   several files; reserved form names are the cost meanwhile.)*
8. **Reader data with source positions**, so the FX-26 reader feeds the
   checker directly and the Rust reader leaves the FX-26 path.
   *(Done 2026-09-26: the reader builds `syn` values with spans, equal to
   the Rust reader's `Syntax` on every text tried; see `docs/fx26.md`. The
   Rust reader stays the default for speed, and the FX-26 path is
   `run_program_read_by_fx26`.)*

### Phase C: bootstrapping

*(Revised 2026-09-26, before starting it, by checking that every step's
inputs come from an earlier step. The first version had no compiler from
FX-26 to cellular code, which the user pointed out; checking the rest the
same way found no FX-26 AST in FX-26, a cellular machine that knew only
Forth's primitives, and no way for FX-26 code to make a cellular word or run
one.)*

9. **FX-26 in FX-26, up to running it:**
   - **9a. A parser in FX-26**: `syn` (step 8) to an AST, a
     `define-datatype`, with the Rust parser's desugarings. Checked by
     unparsing both ASTs on every test program. The compiler and the checker
     both start from it. *(Done 2026-09-26: `src/parser.fx`, compiled with
     the reader as one program and licensed with it. Its trees print, spans
     included, exactly as the Rust parser's do, on test programs and on
     `table.fx`. Descriptions stay as written, for step 10. Not yet:
     `define-datatype`, which the Rust side expands as it reads and the
     FX-26 side does not. Sums and products now have kinds of their own,
     `sum` and `product`, so data can be printed and walked without its
     type.)*
   - **9b. An evaluator in FX-26** over that AST: FX-26's reference
     semantics, written in FX-26. Checked against the same programs lowered
     to Scheme. *(Done 2026-09-26: `src/evaluator.fx`, with control:
     the program's prompt tags, continuations, mark keys and `cwcc`
     escapes are the evaluator's own, one level up. Every test program that
     checks runs to the same value both ways, read and parsed by the FX-26
     front end; so do shadowing definitions. Not yet: bloblets' frozen
     flags.)*
   - **9c. The cellular machine grows what FX-26 needs**: frames and
     locals, closures, calls with arguments, globals, and calls out to the
     runtime's primitives. In the Rust machine, the hand-encoded machine and
     the stencils, each checked against the others as now. Plus a checked
     `%make-word` (what `WordBuilder` checks, since the native machine
     trusts a word's cells) and a way for Scheme and FX-26 to run a word on
     the native machine, which needs a hook: `fixpt-runtime` sits below
     `fixpt-native`. *(In the Rust machine, done 2026-09-26, after checking
     the design against Larceny's MacScheme machine (`note13-malcode`), at
     the user's suggestion: a first try that allocated a heap frame per
     call and linked environments was replaced before anything was built on
     it. A call's arguments stay on the data stack as its frame (`slot i`);
     closures are flat (`free i`), the running one a register as
     MacScheme's REG0; return entries are `(word, k, frame pointer,
     closure)`; calls allocate nothing; `tailcall` slides the new frame
     down. Globals are cells, as MacScheme's; `prim p n` calls the
     runtime's primitives. Words are checked in one place,
     `Heap::make_cellular_word`, for the builder, `%make-word` and FX-26
     alike; `%run-word` runs one through `Runtime::run_word`. The native
     machines trap on the new routines until 9c's native half. Boxing is
     the compiler's, and only `letrec`'s need it.)* *(Control done
     2026-09-26: a prompt is two return entries, where to resume and a
     marker with its tag, handler and the data stack's height; the body runs
     as a closure above them. A composable continuation copies the stacks
     above its prompt into a `cellular-continuation`, and composing it
     rebases frame pointers and prompts' heights; `cwcc` takes everything;
     marks are return entries too. Every test program that checks without
     `extract` runs the same compiled as lowered, control ones included.)*
     *(Native half done 2026-09-26: the hand-encoded machine and the
     stencils run `slot`, `slot!`, `free`, `global`, `global!`, `call`,
     `tailcall` and `return` in machine code, with return entries of the
     same bits as the Rust machine's (`d` and the frame pointer are
     fixnums), so the stacks are roots as they lie. `prim` calls the
     runtime's primitive in place; the rest (closures, control, marks)
     make a round trip, the stacks lifted into a Rust machine for one
     routine and put back. Every compiled test program, control included,
     gives the same value on all three machines; `fixpt --cellular-machine
     rust|native|stencils` picks one.)*
   - **9d. A compiler in FX-26 from the AST to cellular words**, emitting
     bloblets. Checked three ways on the same programs: the evaluator, the
     lowering to Scheme, and the cellular words on the native machine.
     *(First part done 2026-09-26: `src/compile.fx`, on the Rust cellular
     machine. Every test program without `extract` or control gives the
     same value compiled, evaluated and lowered. `extract` needs a
     product's field order, which only its type says: it waits for step
     10. Control waits for the machine's continuations.)*
10. **The FX-26 checker written in FX-26**, over the 9a AST, checked against
    the Rust checker on every test program: FX-26 checking FX-26. *(Done
    2026-09-26: `src/check.fx`, the Rust checker's rules and messages,
    with inference, prompts, bloblets, sums and the two-pass top level.
    Descriptions are read from the parser's syntax in the Rust parser's
    order, so the first error is the same. Compared, up to the order of
    atoms in a `maxeff`, on every test program and on every program
    written into the crate's tests: 170 agree, 90 of them rejections,
    each with the same message at the same place. On the whole front end,
    itself included, it agrees on all 738 forms, at about 330 times the
    Rust checker's time (`docs/performance.md`). With it came:*
    - *`define-datatype` in the FX-26 parser, expanded as `top.rs` does;*
    - *`extract` in the FX-26 compiler, from the field positions the
      checker records, so the compiler now compiles checked programs;*
    - *the rest of the standard library in the compiler, from a table
      generated from the lowering's (`src/standard.fx`).*

    *With these, every program in the tests that checks (80) compiles and
    runs as it does lowered.)*
    *(The bootstrap, 2026-09-26: the FX-26 compiler, run lowered to Scheme,
    compiles the front end (reader, parser, checker, tables, evaluator,
    compiler) and a driver, `src/bootstrap.fx`, to one cellular word:
    stage 1. That word, run on the native machine, gives the driver. The
    driver reads, parses, checks and compiles the same text, entirely by
    compiled FX-26: stage 2. The two words are the same code, cell for cell
    (`tests/bootstrap.rs`, `fixpoint`). On the way:*
    - *the standard operations that Scheme ran as procedures of its own
      became runtime primitives, so cellular code calls them too;*
    - *`%run-word` calls a cellular closure as well as a word.)*
11. **Native code from FX-26**: a word's cells compiled to machine code, by
    an encoder written in FX-26 (the Rust one its oracle) or by placing
    stencils, and installed as the word's entry routine, one word at a time,
    as decision 6 describes. Checked by running the same programs cellular
    and compiled. *(Revised 2026-09-26, tracing each step's inputs. The
    hand-encoded machine's routines read their operands through the ip,
    and the ip walks the cells. So a word's native code can be its cells'
    routines inlined in order, with the dispatch between them removed and
    the ip kept exactly in step. Traps, call-outs, safepoints and return
    entries then see the same state as cellular code, and the two mix
    freely. Operands are still read from the cells, so a collection that
    moves the word changes nothing.)*
    - **11a. Native words, from Rust.** A word gets native code by having
      its entry field set to a native slot above the ordinary routines;
      any machine without that code runs the cells, so the Rust machine
      stays the oracle. A native slot's code has two entries: as a cell
      (`docol`'s work) and as a closure's body (after `call`). Returns
      into a native word resume in native code through a table of resume
      addresses per call site. Branches become direct jumps. Checked by
      running every compiled program, and the bootstrap, with every word
      made native. *(Done 2026-09-26: `NativeMachine::compile_word`.
      Every differential test and every compiled program agree with their
      words compiled, and the bootstrap's fixpoint holds with stage 2's
      words compiled. The gain is small, 1.9 s to 1.4 s on stage 2 and
      none on the micro-benchmarks, since `NEXT`'s indirect jumps predict
      well here; see `docs/performance.md`.)*
    - **11b. The arm64 encoder in FX-26**, instruction by instruction the
      Rust one's (`fixpt-native/src/arm64.rs`), checked against it on
      every instruction 11a emits. *(Done 2026-09-26: `src/arm64.fx`, with
      no bitwise operations: fields are added and shifted by
      multiplying. 6,956 encodings agree with the Rust encoder, refusals
      included.)*
    - **11c. Native words, from FX-26**: 11a's compiler written in FX-26
      over that encoder, making the same bytes as the Rust one for every
      word of the bootstrap. Installed through a runtime hook, as
      `%run-word` is, since `fixpt-runtime` sits below `fixpt-native`.
      *(Done 2026-09-26: `src/native.fx`, over what the machine's
      generator says of itself (`native-layout.fx`, generated). The
      compiler reads words through three pure primitives; the Rust side
      only reserves room and places the code
      (`NativeMachine::reserve`, `install`). Every word of the front end,
      817 of them, 1.1 million instructions, is the same from both
      compilers (`tests/native.rs`). And the fixpoint holds once more with
      every word compiled to machine code by the FX-26 compiler, itself
      compiled and running natively: stage 2 runs on code FX-26 made
      (`fixpoint_with_words_compiled_by_fx26`).)*
12. **The comparison**, Rust pieces against FX-26 ones, with no piece
    retired (decision 8). *(First report 2026-09-26, in
    `docs/performance.md`: each piece alone on the bootstrap program, Rust,
    FX-26 lowered, and FX-26 compiled on each cellular machine. Compiled
    FX-26 on the native machines now beats lowered FX-26 in every piece;
    the Rust checker is still 22 times faster than the FX-26 one.)*

### After M12: what the user asked for next (2026-09-26)

- **An optimizing compiler for FX-26, in Rust and in FX-26.** It takes
  Twobit as a model, and Forth compilers and cellular-code VMs, since much
  may be won on the cellular code itself (peephole optimization,
  superinstructions, stack caching). It keeps Twobit's principle: each
  transformed program is still a well-formed program of the source
  language with the same meaning, carrying at most the analysis added.
  Research on Twobit's passes and history, and on Forth and cellular-code
  compilers, comes first.
- **A printer for compiled forms**: the cellular code in a word's
  bloblet, shown from the REPL, cell by cell, with routine names and
  operands. *(Done 2026-09-26: `fixpt_runtime::disasm`, `%disassemble`,
  FX-26's `disassemble`, and `,disassemble E` in the FX-26 REPL under
  `--fx26-run cellular`. Globals' cells now carry their names. The
  cellular REPL keeps earlier definitions, so later forms can use
  them.)*
- **Research for the compiler**: `docs/research/twobit.md` and
  `docs/research/cellular-compilers.md`.
- **Closures that carry their types** (a direction, not yet a task). A
  cellular closure is a bloblet, so it could carry its type, or enough
  for a checker to confirm the type from its fields and code:
  foundational proof-carrying code. With heap images, and fragments of
  them, loaded into other runtimes, that would let a runtime trust code it
  did not compile.
- **The FX-26 checker's free variables**, computed once rather than at
  every mask (`docs/performance.md`).

### M13 plan: an optimizing compiler for FX-26, in Rust and in FX-26

Drafted 2026-09-26 from `docs/research/twobit.md` and
`docs/research/cellular-compilers.md`, tracing each step's inputs.

**Principles**

- **Every pass is source to source over the FX-26 kernel.** Its output is
  a well-formed FX-26 program with the same meaning (Twobit's rule). What
  a pass proves goes into the program as more specific names, for example
  an unchecked primitive where the operands' types are known, or as
  annotations the checker ignores. Tests re-run the checker on each pass's
  output (GHC's Core Lint).
- **Each pass is written in Rust first and then in FX-26**, the Rust one
  its oracle, compared on the corpus as the checker and the machine-code
  compiler were.
- **Every optimization is measured before it stays**, with the figures in
  `docs/performance.md`. Larceny kept fusions that turned out to be
  slower.

**Steps**

- **13a. A Rust compiler to cellular words.** It makes the same words as
  `compile.fx` for every program, cell for cell. `compile.fx` has had only
  the Scheme lowering as its oracle, so there is nowhere yet to test a
  pass in Rust end to end. *(Done 2026-09-26:
  `fixpt_fx26::cellular::Compiler`, over the Rust checker's forms. It
  makes the same words as `compile.fx` for every test program and for the
  whole bootstrap program, and its words run as the lowering does
  (`tests/rust_compiler.rs`).)*
- **13b. Benchmarks.** A small suite in FX-26 (`fib`, loops, lists, a
  closure-heavy program), plus the bootstrap's stage 2. Each is run on
  every machine, and a harness compares a program with and without a
  pass. *(Suite and baseline done 2026-09-26: `tests/programs/bench`,
  `tests/bench.rs`, and the table in `docs/performance.md`.)*
- **13c. Self tail calls become loops.** A tail call of the enclosing
  procedure, through a binding never assigned, becomes a jump back to the
  start of the word: frame slots rewritten, and no `tailcall`.
- **13d. Typed primitives.** After checking, `+` at `int` becomes an
  unchecked primitive, and so do `car`, the field reads and the rest where
  types prove them. The machines get routines without the checks. Overflow
  checks stay. *(Done 2026-09-26: `int-add`, `int-sub`, `int-less`,
  `pair-car`, `pair-cdr` and `field k`, from both compilers, on every
  machine. The Rust machine, as oracle, keeps the checks. The loop gains
  6–20%; see `docs/performance.md`.)*
- **13e. Known calls.** A call whose callee is known (a `letrec`-bound
  lambda, or a global never assigned) calls the word directly: `callk w n`,
  with no closure fetched and no check. A lambda that does not escape
  needs no closure (let-conversion). *(First part done 2026-09-26: self tail calls of
  `letrec`-bound procedures are loops, and a binding that names none of
  its group but in such calls has no box; in both compilers, with
  `tests/programs/run/loops.fx`. A compiled word's taken branch remakes
  the ip from the word, which the loop needed. Open: globals, which the
  REPL may define again, so known only under block compilation of a whole
  program; `callk`; let-conversion of lambdas that do not escape.)*
- **13f. Inlining and simplification.** Small known procedures are
  inlined, non-tail calls first (Twobit), with constant folding, copy
  propagation, and dead code removed where its effect allows.
- **13g. Superinstructions.** Sequences of cells are fused, chosen by
  profiling the bootstrap: `slot; slot; <; 0branch`, `slot; lit; +`,
  `global; call`. This helps the Rust machine and the stencils most.
- **13h. Machine code: the stack in registers.** The machine-code compiler
  models the stack over each basic block, as VFX Forth does: `lit` and
  `slot` emit nothing until a value is needed, and the model is flushed at
  calls and control. Frame slots are kept in registers across calls that,
  by their effects, cannot capture a continuation or collect. Stack-limit
  and fuel checks are hoisted to entries and back edges. *(Superseded 2026-09-26 by 13h′ below: the user asked for
  values in registers the MacScheme machine's way, not a Forth stack
  cached in registers.)*
- **13h′. Register code: the MacScheme machine.** (Designed 2026-09-26.)
  Larceny Note 13 (`doc/LarcenyNotes/note13-malcode.html`) defines the
  machine:
  - `RESULT`, an accumulator;
  - `REG0`, the procedure running;
  - `REG1`…`REGr`, general registers, the arguments on entry;
  - frames on a stack, made by `save n` and used by `store k,n`,
    `load k,n` and `stack n`;
  - `setrtn`/`invoke n`/`return`: a call leaves the callee in `RESULT`,
    the arguments in `REG1`…`REGn`, and a return address in the frame.

  Values live in registers, and a frame holds only what must survive a
  call. Our cellular machine already has `REG0` (`clo`) and frames, but
  passes every value through the data stack. The plan:

  1. **An IR, in Rust** (`fixpt_fx26::regcode`). Each lambda becomes
     MacScheme instructions, made from the checker's trees as the cellular
     compiler's are. Twobit's pass 4 is the model: register targeting, a
     frame made lazily (only on paths that call), `store` only of what is
     live across a call, `load` after. Primitives are `op1`/`op2`/`op2imm`,
     typed as 13d made them. The IR can be shown (`,disassemble`) and has
     an interpreter in Rust, the oracle, run against the lowering on every
     test program.
  2. **The moving collector decides where values may be.** A Value may be
     in a machine register only between points that can collect. Anything
     that can collect is a call-out, the same as the cellular machines:
     allocation, a runtime primitive, control, a call. Before one,
     everything live is stored to the frame; after it, loaded again. The
     frame is on the data stack, the root the collector already scans, so
     a continuation captured at a call-out holds it too. A return point
     loads what it needs from the frame, which is what lets a captured
     continuation resume there.
  3. **Machine code, in `fixpt-native`.** Registers:
     - `RESULT` in `x0`;
     - `REG1`…`REG8` in `x1`…`x8`, with arguments past eight on the data
       stack;
     - `REG0` in `CLO`;
     - the machine's other registers as they are now.

     Calls between register procedures use the register convention.
  4. **Two entries per compiled procedure,** so register code and
     cellular code call each other. The *register entry* takes arguments in
     registers. The *cellular entry*, the word's usual one, moves a
     cellular frame's arguments into registers and continues. A register
     call to a callee without register code pushes a cellular frame and
     enters the word. A return entry says which convention returns to it.
  5. **Checks where they are needed:** fuel and stack limits at entry and
     on back edges, and an argument count never, since arities are static.
  6. **Order:**
     - (a) the IR and its interpreter, for all of FX-26;
     - (b) machine code for the procedures the benchmarks need, with the
       rest still cellular behind the two entries, and measured;
     - (c) every form, until the bootstrap runs as register code;
     - (d) known calls (`callk`, 13e) as direct branches;
     - (e) the compiler written in FX-26 to match, instruction for
       instruction, as for the cellular compilers.
     - (f) *(The user, 2026-09-26: "support distinct calling conventions
       for the two kinds of code, but allow calls between each other.")*
       Calls already differ: registers or a stack frame, with an adapter
       for stack code entering register code. Returns do not yet: every
       return goes by the data stack and the resume table. Register code
       should return in `x0`, straight to the caller's resume code, and
       take the stack's way only when it returns to stack code; a return
       entry or a captured continuation says which convention its resume
       point expects. *((a) and (b) done 2026-09-26, the IR made by the Rust compiler
     and tested by running every test program as register code against
     the lowering, with no separate interpreter. `fib` 1.7×, `tak` 1.9×
     and `loop` 5.9× faster than compiled cellular words; see
     `docs/performance.md`. (c) done the same day: 966 of the bootstrap's
     972 lambdas as register code, and the fixpoint holds as register
     code. Stage 2 takes 0.56 s against 0.7 s as compiled stack code,
     since call-outs dominate: allocation and the common primitives in
     machine code come next.)*
- **13i. Join points.** A local procedure used only in saturated tail
  calls becomes a label in its word.

Order: 13a and 13b, then 13c and 13d (cheap, and they help every
machine), then 13e and 13f, then 13h, the largest win on the native
machines, then 13g and 13i.

**Revised 2026-09-26: the type system first.** The user's direction is to
get what we can from the type and effect system we have before anything
else, and before talking about extending it. So the first optimization is
**typed calls (13c′)**, ahead of the self-call loops of 13c, which fold into
known calls (13e).

A call whose callee the checker typed as a subroutine needs no test that
it is a closure, no fallback for continuations, and, in tail position, no
stack-limit checks. Tracing what that assumes found two places where the
type does not yet promise a closure:

1. **A composable continuation is a subtype of `subr`**, so a `subr` value
   can be a continuation object. Every callable becomes a closure:
   `callcomp` and `callcc` give a closure whose word resumes the
   continuation (a new `resume` routine), and `marks-of` unwraps it.
2. **Procedures not yet defined.** A typed global has its cell before its
   definition runs, and a `letrec` box has no value until it is filled;
   both hold `#u`. When their type is a subroutine, they start instead as
   a closure whose word traps: "called before it was defined".

Then the compilers, in Rust and in FX-26, emit `tcall n` and
`ttailcall n`: `call` and `tailcall` without those tests. Every machine has
them: the Rust machine, the hand-encoded one, the stencils, and the
machine-code compilers in Rust and FX-26. Measured against the 13b
baseline. 13d, typed primitives, follows on the same principle. *(Typed calls done 2026-09-26: 2–12% on the benchmarks.)*

### The queue (written 2026-09-26, at the user's request)

What is agreed, or was raised in the work and not yet written down, in
the order it will be done. Each is committed when done, and marked here.

1. **Values as addresses** (below, "Values as addresses, not indices"):
   decided by the user, for after the regions work, which is done.
   *(Done 2026-09-26; the other machines' adds of a `BASE` of 0 remain.)*
2. **Register code's own returns** (13h′ (f)): a return in `x0`, straight
   to the caller's resume code; the data stack's way only when it returns
   to stack code.
   *(Done 2026-09-26: a `blr`, a marked return entry, and a return by
   `br x30`; `fib` −22%, `tak` −13%, `loop` −18%. `closures` and `lists`
   paid for the link on every tail call through a global, which
   `FIXPT_REGCODE_DUMP` showed; the link now stays in `x30`, and they are
   within 6% of before, `docs/performance.md`. Such self-calls made loops
   is item 4.)*
3. **The call-outs left hot** (`docs/performance.md`, "Where the
   self-compile's time goes"): closure creation (1.8 M in the
   self-compile), `%make-frozen` for sums and products (546 k),
   `field@`, `string=?`, `%bloblet-fields`, `char-whitespace?`; and the
   region allocators other than `rcons` (`rnew`, `rmake-array`,
   `rmake-icell`, `rmake-bloblet`, `rlambda`'s closures), inline as
   `rcons` is.
   *(Done 2026-09-26 but for `rmake-array` and `rmake-bloblet`, which no
   program here calls often: they wait for one that does.)*
3′. **Why the compiler written in FX-26 calls primitives so often**
   (raised by the user 2026-09-26): 1.24 million calls in stage 2 after
   item 3, many apparently from names handled as strings (`string=?`
   chains such as `standard-primitive`'s, `string->symbol` and back).
   Count where they come from, and change the FX-26 code where the count
   is its own doing.
   *(Begun 2026-09-26: the reader's quadratic marks and the symbol
   hash's strings, `docs/performance.md`; 1.24 M → 0.95 M. Then
   2026-09-27: the reader's marks as data, type tests and a symbol's hash
   and `new` in machine code, names compared as symbols in the parser and
   `k-parse-type`, and the checker's error messages made only for errors:
   673k → 296k, stage 2 0.22 → 0.19 s. What is left is mostly the
   reader's making of each atom's text (`reverse`, `list->string`,
   `string->symbol`, 42k each) and the checker's report of each
   definition's type, which it returns as text.)*
4. **Known calls** (13e and 13h′ (d)): `callk`, a direct call of a known
   word with no closure fetched; let-conversion of lambdas that do not
   escape.
   *(Done in part 2026-09-26: a definition's own name is known, its tail
   self-calls loops; a non-tail self-call is `invokeself`, a `bl` to the
   word's own entry. `lists` 13.9 → 8.8 ms, `fib` 5.7 → 4.4. Open: calls
   of other known procedures, whose word is known when the program is
   compiled (a later definition's call of an earlier one); and
   let-conversion. Measured 2026-09-27: `tak` as two definitions calling
   each other by `invoke` takes 1.0 s for 500 rounds, against 0.82 s as
   one calling itself by `invokeself`, so a known call could save up to
   about a fifth of a call-bound program's time. A `bl` to another word
   needs its entry placed first, which the words' installation does not
   yet order; waiting on a call-bound workload.)*
5. **Register code from the compiler written in FX-26** (13h′ (e)).
   *(Done 2026-09-26: `src/regcode.fx`, a port of `cellular/regcode.rs`,
   called by `compile.fx` through `c-register-code` when `c-registers` is
   set (`compile-registers!`); `set-register-twin` makes the register word.
   It declines where the Rust one does, noting it in a flag rather than
   returning early. Every test program's register code is the Rust
   compiler's, cell for cell (106 register words), and so is the whole
   bootstrap's, made by the compiler in FX-26 running as register code.
   The REPL's `--fx26-run cellular --cellular-machine registers` makes
   it too.)*
6. **A nursery, and a write barrier with a remembered set** (raised by
   the user 2026-09-26, "make it toggleable"): the nursery's size zero
   by default, so that it costs nothing when off; measured against the
   semispaces alone. A reap collected on its own, from the stacks and the
   regions nested in it, is the typed version of the same idea ("Regions
   that end").
   *(Deferred 2026-09-26, pending the user's word: collection is about
   20 ms of the self-compile's 180 ms, and the benchmarks keep little
   live, so a nursery has little to save now; while the barrier must be on
   every store of a reference, in the heap's API (which would have to keep
   stores of Values apart from stores of raw words everywhere) and in
   three machine-code paths (the hand-encoded machine's `field!`, register
   code's `setfield` and inline `%bloblet-set!`). Reaps give the same for
   what is typed as local to a region, with no barrier. Worth it when a
   workload shows collection costing more.)*
7. **Continuations cheaper to capture**: one-shot continuations, or a
   segmented stack (a stack cache, as Clinger, Hartheimer and Ost
   describe), measured on a benchmark that captures heavily (the
   self-compile's reader captured 326 k times through `callcomp`).
   *(Deferred 2026-09-26: `bench/captures.fx` measures a capture at
   about 0.15 µs plus 1 ns a word of stack, and nothing captures often
   now. The self-compile captures 6 times since the reader suspends only
   when its input runs out; see docs/performance.md, "What a capture
   costs". Worth it for a workload that captures deeply and often.)*
8. **The reader's cursor**: the eager reader allocates a cursor for each
   character it reads; a cursor kept in place, or a reader that returns
   its position without allocating.
   *(Done otherwise 2026-09-26: the cursor was not the cost. The reader's
   calls of primitives were: its marks copied by `datum-list`, and every
   atom parsed as a number. 39.9 → 29.3 ms reading the bootstrap program;
   a cursor as one product measured no better. See docs/performance.md,
   "The reader: what it called out for".)*
9. **Tidying the regions work**: the checker's record of each
   allocation's region (`NodeFacts::alloc_region`), no longer used to
   allocate, removed from both checkers; the FX-26 checker's free
   variables computed once rather than at every mask.
   *(Done 2026-09-26: `alloc_region` removed. The FX-26 checker's mask
   now looks only for the regions whose atoms a free variable decides,
   and stops walking once each is seen: stage 2, 0.23 → 0.22 s. Found
   once for every node, carried up by `k-synth`, would take the rest,
   at most 0.01 s more.)*
12. **The REPL's `,code` under `--fx26-run cellular`** (raised by the user
    2026-09-26): it shows the form's lowering to Scheme, which is not what
    runs there; it should show the words the compiler in FX-26 made, as
    `,disassemble` does for a value.
    *(Done 2026-09-26: under `--fx26-run cellular`, `,code` shows the
    words the compiler written in FX-26 made for the form, those it had
    not shown for an earlier one, since each form is compiled with every
    definition before it.)*
11. **A lint on the size of a lambda's body** (raised by the user
    2026-09-26): not a rule of FX-26, but a check that keeps a body from
    growing past what a reader can follow (`check.fx`'s `k-parse-type`,
    whose cases want to be helpers of their own). Perhaps after adopting a
    module system, FX-91's, which would give helpers somewhere to live.
10. **The type and effect directions** below ("Responsiveness as an
    effect", "Time complexity as an effect", "Concurrency, and processes
    as distinct from functions", "Closures that carry their types"):
    each explored, and concrete tasks drawn from it.
    *(Done 2026-09-27: `docs/research/type-and-effect-directions.md`,
    with tasks R1–R8, T1–T6, P1–P12 and C1–C12 and which to do first.
    R1, a cellular run's fuel from the session's step limit, is done: a
    looping form hung the cellular REPL. Found open: an image's words are
    not checked as they load (C3). A resumed continuation was thought to
    charge no fuel, but a loop through one stops at the limit (R2,
    tested).)*

### The next queue (with the user, 2026-09-27)

In the user's order:
1. **Places and regions**: split what FX-26 calls a region into places
   (for allocation) and regions (for analysis), toward `letfreeze`
   (`docs/research/places-and-regions.md`, its "Steps"): places a kind of
   their own (done), the lifetime order by nesting, bounded region
   binders and allocators taking a place and a region, `heap` as a place,
   `letfreeze` and `(const p)`; written outlives constraints later.
2. **Confirming a type at run time**: `confirm`, sizes, and walking
   cyclic data without diverging (`docs/research/confirmation.md`,
   CF1–CF5).
3. **Responsiveness**: the `spin` atom, waiting on the user's choice of
   explicit or implicit (`docs/research/type-and-effect-directions.md`,
   R6, R7). R1–R4 are done; R5 and R8 are dropped, since an entry poll
   costs nothing measurable.
4. **Concurrency and processes**, after the Actor model and Erlang, local
   and distributed (`docs/research/actors-and-distribution.md`, A1–N6).
5. **A top effect** (raised by the user, 2026-09-27): `any`, for code
   meant to grow with the language, as an interpreter's `eval` does.
   Before it is useful: it can never be masked, so what regions does it
   cover? Literally all of them would let it write frozen data and other
   programs' private regions. More likely it means any effect on the
   regions reachable from what it is given, plus `spin` and control.
   R7 (no step budget for forms free of `spin`) is withdrawn, 2026-09-27:
   free of `spin` means ends eventually, not soon (`(ack 4 2)` is `pure`).
   Bounds known versus merely finite belong to cost analysis (Reistad and
   Gifford, `GiffordHistory/papers/lfp94.pdf`), later.
6. **GADTs** (raised by the user, 2026-09-27; planned in
   `docs/research/gadts.md`, stages N1–N6; N1–N2, generative types with
   checked variance, N3, lemmas, and N6 with CF0, the `data` kind and
   `acyclic`, done 2026-09-27): sums whose variants refine
   their type's parameters, so that a `tagcase` arm learns them. They meet
   the size indices of `confirm` (CF3, CF4), where a variant's type would
   say its size, and the typed interpreter this repository keeps growing,
   whose `eval` could then be given a precise type.
8. **Two FX-26 front ends** (the user's, 2026-09-27): the present one keeps
   mirroring the Rust, as the oracle agreement tests need; a second uses
   FX-26's features as fully as it can (nominal ids, regions by role,
   per-procedure effects, `finite` and `data`), and must agree on outputs
   only, so tests become three-way. Staged: the reader and parser first
   (they change rarely); the checker after N1–N3 (`docs/research/gadts.md`);
   then decide which bootstraps. Each uses the kind of type that states what
   its data is: the mirror is nominal wherever the Rust is (`TyId`, `DVar`,
   `Sym` as generative types, not `int`); the idiomatic one is structural
   where the data is (`syn`, `datum`, trees, and types as `finite` data, so
   that size-change can see a walk of a type shrink: today `k-check-mode`
   peels `poly`s off a type held as an `int`, and must say `spin`).
   In directories named for which is which: `src/fx-rsmirror/` and
   `src/fx-idiomatic/`.
7. **Parametric datatypes** (done 2026-09-27; `docs/fx26.md`): `define-datatype`
   with parameters, and type families that mention themselves with the same
   parameters (regular, so tied as a knot, not expanded without end:
   today `(define-type (tree (r region)) … (tree r) …)` is refused). Needed
   for trees in a place the caller chooses, `(acyclic p)` in an arena;
   the front end's trees in plain `acyclic` need none. A first step toward
   GADTs (6).

### Progress, and what the queue gained (2026-09-27, later)

Done since the list above was written:
- **Sizes** (`docs/research/sizes.md`): N5a (`(nlist T n)`, `finite`,
  `confirm-length` with a literal), N5b (size variables, facts from
  `null?`), N5d (`nat` and `(nat s)`, facts from comparisons, `length`,
  `confirm-length` with a run-time length, `confirm-nat`, `string-length`
  and `array-length` as naturals, size-change bounded below by a `nat`).
  `vec` was renamed `nlist`.
- **`sexp-edit`** (`crates/fixpt-tidy`): structural edits of `.fx` by
  definition name, and an `order` report of uses before definitions.
- **Soundness** (`docs/research/soundness.md`, `soundness-regions.md`,
  `soundness-findings.md`): K26, a core of FX-26, with a small-step
  semantics over places and regions; progress and preservation proved,
  control included; no use after free, frozen never written and `finite`
  acyclic proved. Holes found and closed in both checkers: F1 (known
  procedures by binding), F2 (reads of data frozen into a place are an
  effect on it), F3 and F9 (`cwcc` says `spin` unless its continuation can
  only leave, and its receiver captures no continuation), F4 and F8 (a size
  may be forgotten as `finite` only where it is given back, or sizes one
  parameter), F5 (the self-application test's depth bound says "may loop"),
  F6 (`no-escape` only for first-order data), F7 (a whole continuation's
  throw ends the regions it leaves), A2 (a generative name whose
  representation is a parameter is no constructor).

New, in rough order:
1. **Soundness, still open**: effect soundness T3 in full (a composable
   continuation's effect need not describe what its frames touch); lemma
   erasure T4; termination of code free of `spin`, T5, conjectured, which
   wants a step-indexed or Kripke logical relation over region levels and a
   proof of size-change; the space theorem T6, which wants a harness that
   measures space against `S_place`. Probe each new rule with the
   soundness agent before building on it.
2. **N5c**: inequalities between size variables (Fourier–Motzkin),
   existential sizes for results such as `filter`'s ("at most n"), and
   array sizes with bounds from facts (CF4).
3. **Quick wins in the front end written in FX-26**
   (`docs/research/fx-idiomatic-opportunities.md`): finite bucket spines in
   `table.fx`; loops bounded by `>=` or a `nat` rather than `=`, so the
   array copies need no `spin`; tighter declared effects (`len`, `nth`,
   `drop`, `syn-nil?`); products for the 57 unmutated pairs in `check.fx`;
   sums for the integer codes (kinds, variance, region forms); an `opt`
   type for the `-1` sentinels and "none or one" lists; finite lists in the
   compiler's refs; structured errors instead of re-parsed messages.
   Those that change no message go in the mirror; the rest wait for
   `src/fx-idiomatic/`, whose first files are `table.fx`, then `arm64.fx`,
   then `parser.fx`, and `check.fx` last.
4. **Language gaps the survey found**: size-change cannot see that a
   helper's result is a part of its argument (`nth`, `drop`, `syn-items`:
   why the parser needs `spin`); a datatype's constructor gives the whole
   datatype, not its variant, and there is no "all but one variant" type;
   no `opt` in a prelude; no identity equality or hash on mutable objects;
   no test of whether an I-cell is full; no append-only (arena) effect; no
   handlers for named effects, so global failure tags cannot be masked; no
   modules polymorphic in their regions; no productivity for the eager
   reader; no termination measure over state for walks of graphs. A top
   effect (5) was needed nowhere in the front end.
5. **Error messages for `nlist`**: say "a (nlist t n), where a (pairof t
   (nlist t n) finite) is expected" in terms of lengths.
6. **`,apropos` and `,help` over every namespace** (the user's,
   2026-09-27). *(Done 2026-09-27: `Checker::description_entries`; each hit
   labelled by kind; `,apropos KIND TEXT` narrows it.)*

### A collected code area (with the user, 2026-09-27)

Two wants: a program that generates code, runs it and drops it must never
run out of room for code; and code must be able to reach GC-traced values
through fields of its own bloblet, PC-relatively, as the bloblet design
intends. Today native code goes in `CodeSpace`, a bump allocator never
collected. Design: `docs/object-model.md`, "A collected code area". Steps,
each committed:
1. The design, and a test that generates, compiles, runs and drops words
   past one code space's room (`crates/fixpt-native/tests/code_gc.rs`,
   ignored until step 4; it fails at round 278 today). *(Done 2026-09-27.)*
2. The code area in `fixpt-heap`: a shared mapping over its part of the
   reservation, first-fit allocation, marking and scanning within the
   copying collection, and a sweep; tested with plain bloblets, under
   `gc-stress` too. *(Done 2026-09-27: `fixpt-heap`'s `heap/code.rs`,
   `tests/code_area.rs`. The shared mapping waits for step 3, which needs
   it.)*
3. The execute view, and a test that runs a code bloblet reading its own
   field PC-relatively across a collection that moves the field's value. *(Done
   2026-09-27: `fixpt-memmgmt`'s `exec.rs`, made when the area is first
   used; `Heap::code_exec_address` and `Heap::flush_code`;
   `crates/fixpt-native/tests/code_exec.rs`.)*
4. The native machines compiling into the code area, their tables cleared
   when what they name is freed; step 1's test passes. *(4a done
   2026-09-27: word code reaches the machine's trap and exit through its
   state, so no branch leaves it. 4b and 4c are replaced by
   `docs/research/native-conventions.md`, whose step 3 makes step 1's test
   pass.)*
5. Closures as code bloblets whose captured values are fields their code
   reads PC-relatively (the experiment that prompted this; measurements in
   `docs/performance.md`, "Closures: what copying code into each would
   cost").

The alternative, running code from the semispaces, was set aside because
bloblets can live in a non-moving area the collector traces; it stays open
should fragmentation call for moving code.

### Kept open, deliberately

- **Values held by Rust across calls, typed away.** (Raised 2026-09-26,
  after two rooting bugs in `eager.rs` and one in a test.) At the
  embedding boundary, a Value from `Session::global_value` or a call's
  result gets a lifetime borrowed from the session (`Held<'s>`), and
  whatever may collect takes `&mut Session`, so holding one across such a
  call is a borrow error; keeping one means rooting it and fetching it
  again. `gc-arena`'s `'gc` and V8's `Local<'s>`/`HandleScope` are the
  precedents. The engines keep raw Values, whose stacks are roots by
  construction. It is the region discipline, in Rust's types: the heap a
  region, a held Value a read of it, a call that may collect the effect
  that ends it. *(Done 2026-09-26 as a handle API, at the user's urging
  not to wait: `Session::rt` is private to its module, so no code driving
  a session, `eager.rs` included, sees a raw Value. Results are
  `Handle`s, rooted and stamped, released by `Session::scope`; contents
  are read in `Session::view`, whose `Local`s cannot leave it or run
  anything; Values are built in `Session::make`, which cannot call the
  engine. The machinery (engines, the help system's inspection, tests of
  internals) uses `runtime_unrooted`, a name that says what it gives up.
  `gc-arena`'s compile-time brand remains possible on top.)*
- **A collector without safepoints.** (Raised 2026-09-26, after Cliff
  Click's Pauseless GC at Azul, later C4.) The cellular machine's state is
  Values in root arrays and word-relative offsets, so it could be collected
  between any two cells; the native machine holds an absolute ip and the
  heap's base in registers, rebuilt at call-outs, so it would need either
  a map for every pc or a collector that never moves what a running
  mutator holds. The Pauseless approach, a self-healing read barrier and a
  not-marked-through bit, fits: indexes are 61 bits, so a Value has a
  spare high bit, every bloblet field is tagged, suffixes are untraced,
  and derived pointers are owner plus offset. Its payoff is concurrency,
  which the system does not have yet.
- **Regions that end: `letrena` and `letreap`.** (Raised 2026-09-26.) Masking says
  effects on a region cannot be observed outside an expression; freeing
  the region needs more: that nothing in it is reachable after. For
  `(letregion r body)`: `r` in no free variable's type (masking checks
  this already); `r` nowhere in the result type, latent effects included
  (`regions_in` walks them); and, new with first-class control, no
  continuation captured in the body escaping it, since a continuation's
  type says nothing of the data its frames hold: the body's masked effect
  must have no `comefrom`. Assignment needs nothing more: storing into a
  longer-lived structure puts `r` in that structure's type. Two layers:
  the checker rule (allocation still in the collected heap), then arenas
  the collector treats as roots while live and resets at exit, sound
  under those conditions (MLKit pairs regions with a collector). A kernel
  form, so written twice.

  *(The checker rule done 2026-09-26, as two forms with the one typing
  rule, differing only in how memory is managed, a hint of the lifetimes
  the programmer expects.)*
  - **`letrena r`**, an arena: bump allocation, reset in one step when the
    body ends, never collected before then, though scanned as roots
    (its objects may point into the heap).
  - **`letreap r`**, a regional heap: collected as it runs, and dropped
    whole at the end. Nothing outside a region can point into it, so a
    reap can be collected from the stacks (and the regions nested inside
    it) alone: a nursery whose "no old-to-young pointers" comes from the
    types, with no write barrier.

  The user chose the two explicit forms, with no `letregion` that lets
  the implementation choose. For now both allocate in the heap, which is
  always correct. The groundwork for either, in order:
  1. The checker records each allocation site's region, so the compilers
     know which allocations go to a region. Allocations made through
     region-polymorphic procedures need regions passed at run time (Tofte
     and Talpin); direct ones come first.
  2. Somewhere for region objects to live. Chosen (2026-09-26): a
     segmented heap in one address range reserved up front, from
     `fixpt-memmgmt` (a crate below the heap that may use `unsafe`, the
     user's choice after the measurement below). *(First step done: the
     heap holds `fixpt_memmgmt::Words`, and each semispace has address
     space of its own, so it grows in place, with nothing copied or moved.
     No slower than the `Vec` it replaces, and collection a little faster.)* A Value is an index from a base that never moves;
     segments have roles (to-space, arena, reap, later a nursery), and a
     table indexed by `index >> segment bits` says each one's role.

     What the system allows (`tests/reserve.rs`, 2026-09-26, 128 GB of
     memory, 16 KB pages):
     - it reserves, and even maps writable, 64 TB (2^46) without
       complaint, about 500 times memory plus swap, so it commits nothing
       until a page is touched;
     - every page written becomes resident: a first touch costs about
       0.5 µs per page close together, and 2–3 µs far apart, as page
       tables are made too;
     - past physical memory it would not refuse, but compress, swap and
       at last kill the process.

     So the heap sets its own limit, with an error of its own, and
     reuses its segments rather than touching fresh ones.

     How the heap reaches that memory (measured 2026-09-26). `fixpt-heap`
     may not use `unsafe`, and cannot depend on `fixpt-native`, so memory
     that `fixpt-native` reserved would reach the heap through a trait
     object. With the heap's words behind one (`Box<dyn HeapMemory>`),
     everything that goes through the heap's accessors slowed:
     - lowered to Scheme: `closures` +47%, `lists` +27%, checking the
       bootstrap +43%;
     - the Rust machine: +15%;
     - the self-compile as register code, through its call-outs: +12%.

     Compiled code (which addresses the heap directly) and the collector
     (which takes its slice once) were unchanged. A large zero-filled
     `Vec<u64>`, sized to the heap's maximum, is committed lazily just as
     the reservation is (`crates/fixpt-heap/tests/lazy.rs`), and costs
     nothing per access.
  3. Reset when control leaves the body by an abort, as well as by a
     return. Continuations cannot come back in, which the rule forbids.
  4. The collector scans arenas as roots, collects reaps, and scans reaps
     as roots when it collects the heap.

  *(Arenas, first cut, 2026-09-26: `heap/regions.rs`, and register code.)*
  Each `letrena` is its own arena; the question was only how to lay them
  out. All of them in one stack of words, each marked on entry and reset
  to its mark on exit, is **not sound**, even with no polymorphism: in
  `(letrena r0 (letrec ((f (lambda (n) (letrena r1 … (cons-in-r0 …) … (f …))))) …))`
  the `cons` in `r0` happens while `r1`, newer, is live, so it lands
  above `r1`'s mark and is freed when `r1` ends, though `r0` may hold it.
  So each region has chunks of its own (64 KiB, reused once it ends), as
  Tofte and Talpin's do, and an allocation names its region by a handle.
  Regions still end newest first, so a handle is a position in a stack of
  live regions, and ending one ends any newer an escape left behind.
  - The heap: `region_enter`, `region_exit`, and `in_region(h, f)`, under
    which a primitive's allocation goes to region `h`; too big for a
    chunk, it goes to the heap. The collector scans the live regions'
    words as roots, before the Cheney scan; `verify` walks them.
  - Register code first, by the checker's record of each `cons`'s
    region; replaced the same day (below).

  *(Regions as values, 2026-09-26, the user's design.)* Which region an
  allocation goes to is said in the program, not inferred: a
  `letrena`'s or `letreap`'s name is also a variable of type
  `(region r)`, and `(rcons r x y)` allocates in it. Plain `cons` is the
  heap's, whatever its type says. So a closure that allocates in a
  region captures it as it captures any variable, in every compiler
  alike (the Rust stack compiler and `compile.fx`, which must agree
  cell for cell, and register code); and a procedure may take a region
  as an argument, Tofte and Talpin's region passing made explicit.
  - Both checkers: the type `(region r)`, the name bound in the body.
  - Every back end: a `letrena` is `%region-enter`, the body with the
    handle bound (not in tail position), then `%region-exit h v`, which
    gives back `v`; a `letreap` binds `#f`, which `%region-cons` takes as
    the heap. The evaluator written in FX-26 erases regions.

  The alternative the user raised: an allocator in a parameter, which a
  body could point at a region, so that every allocation in its dynamic
  extent goes there. Not now: explicit is simpler to trust.

  Next, in order:
  1. *(Done 2026-09-26.)* `rnew`, `rmake-array`, `rmake-icell` and the
     form `(rmake-bloblet r bytes e …)`, each a primitive under
     `Heap::in_region`. Products and sums have no region (immutable,
     their types name none), so they stay the heap's.
  2. *(Done 2026-09-26.)* Closures in a region: `(rlambda r ps body …)`,
     whose latent effect has `(read r)` (calling it reads the closure, so
     its type mentions the region), made by `%region-closure h fv … w`.
     No `rplambda`: a `plambda` may generalize an `rlambda`, whose only
     effect is allocating the closure; the value restriction is about
     mutable data, and a closure holds only variables bound outside.
  3. *(Done 2026-09-26.)* `rcons` inline in register code: each region's
     current chunk, `[fill, end]`, in a table at a fixed address, which
     machine code bumps. `lists` in a region: 8.1 ms, against 12.4 ms in
     the heap.
  4. *(Done 2026-09-26.)* An escape ends the regions it leaves:
     - the cellular machines (Rust and native): a prompt's entry keeps
       how many regions were live, above the data stack's height in its
       last word, and an abort to it ends any newer. A composable
       continuation's prompts, reinstated, take the count live then: every
       live region is older than they now are, and none entered in what
       was captured is live, since the checker lets no region's body be
       resumed (without that, an abort to one could end an older region
       still in use). A whole continuation keeps its counts.
     - lowered code: a `letrena` is a `dynamic-wind` whose after ends the
       region, which the Scheme engine's aborts and escapes run.
     - an error: the session ends every region when a form is done.
  5. *(Done 2026-09-26.)* `letreap`: a region the collector collects
     with the heap. A Cheney scan over to-space and each live reap's new
     chunks together, until neither has more; what is reachable in a reap
     is copied into new chunks of its own, and the old chunks' pages go
     back to the system. The chunks reaps take also start collections, as
     the heap's filling does. A reference an ended reap left, in a frame's
     dead slot say, must never be followed into another reap's objects, so
     an ended reap's chunks go into quarantine: a collection that meets a
     reference into one marks it, and after each collection the unmarked
     ones are free to reuse. (An arena's are reused at once: the collector
     never follows a reference into an arena.) All reaps share one area,
     16 GiB of address space as the arenas' is; each reap is a list of
     64 KiB chunks from it, growing as it needs. When the area is used up,
     their allocation, and their copies, go to the heap.

     A first version never reused a reap's chunks, from an area of 2 TiB:
     mapping and unmapping that took about 3 ms per heap (1.3 ms and
     1.9 ms), which slowed every test that makes heaps (the heap's own from
     0.01 s to 0.2 s), and would have allowed only some 30 heaps in a
     process, whose address space the system caps at 64 TiB.
  6. The checker's record of each allocation's region
     (`NodeFacts::alloc_region`) is no longer used to allocate; it may go.

- **Responsiveness as an effect.** (Raised 2026-09-26.) Distinguish "may
  diverge without reaching a poll" from "every unbounded path polls, and
  every callee does too". A poll (the native machine's fuel and limit
  check, or an interrupt check) discharges the effect, as a handler masks
  one; Koka's `div` is the coarse version. It would let a word with no
  backward branch that calls only such words skip the check at entry. The
  cellular machines already check exactly at word entry and taken branches,
  the only ways to run unboundedly, so the check points are where the
  effect would be discharged.

- **Values as addresses, not indices.** (Decided by the user, 2026-09-26,
  for after the regions work.) A Value's upper 61 bits are a word index
  from the heap's base, so machine code keeps `BASE` in a register and
  adds it to every heap access. That pays for itself only when references
  are compressed (32-bit fields, as the JVM's compressed pointers), and
  ours are not: "we aren't a JVM here". The reasons it was an index
  (images load anywhere, the heap used to move when it grew, the heap is
  safe Rust indexing a slice) no longer need the machine code to use one:
  - the heap is now at a fixed address (`fixpt-memmgmt`), so it no longer
    moves;
  - the heap never dereferences a Value, so it can turn an address into a
    slice index, `(raw − base) / 8`, in safe code;
  - an image is already rebased to word 0 as it is dumped, and loading it
    would add the new base in one walk.

  So a Value will hold the byte address, tag in its low bits. The heap
  subtracts the base; machine code does not add it, and frees the `BASE`
  register. Many `add …, BASE, …` sites change: in the hand-encoded
  machine, the stencils, register code and `native.fx`. Measure first
  what the add costs on the list-heavy benchmarks, where it sits between
  dependent loads. Compressed references (32-bit fields) are not planned.

  *(Done 2026-09-26, in two steps.)* The add cost about 5% on
  `lists-region` and under 1% elsewhere (one more dependent add in
  `car`/`cdr`). A Value is now its referent's address; the heap keeps
  its own word numbering and converts where it makes or reads a Value
  (`Heap::ix`), the collector likewise, and an image is relocated as it
  is loaded. The machines' `BASE` register holds 0, so the code that
  adds it keeps its meaning; register code no longer adds it
  (`lists-region` 8.7 → 7.3 ms). Inline allocation loads where the
  heap's memory starts from the state (`State::words`). Left: the
  hand-encoded machine, the stencils and `native.fx` still add a `BASE`
  of 0; removing those adds frees `x19`, which could then hold where the
  heap's memory starts, for allocation with no load.
- **Recursion made explicit: I-cells.** (Raised by the user 2026-09-26:
  "make the imperative nature of mutual recursion explicit".) Seven
  options are compared in `docs/research/recursion-and-initialization.md`.
  The user chose I-cells (Arvind; Id, pH) to prototype first:
  - a type `(icell T R)`, written once;
  - `make-icell`, `icell-put!` and `icell-get`;
  - a new effect `(await R)` for a read, which is ordered after writes to
    `R` but commutes with other reads.

  Sequentially, a read of an empty cell traps and a second write is an
  error. Concurrently, a read would suspend the reader on the cell. *(Prototype done 2026-09-26:
  - both checkers, the lowering, the evaluator written in FX-26, both
    compilers, and runtime primitives, which every machine reaches
    through `prim`;
  - `docs/fx26.md`, `tests/icells.rs` and `tests/programs/run/icells.fx`.

  A procedure can tie its knot with cells in a region nothing outside
  names, and masking keeps it `pure`. Not yet:
  - ~~`letrec` and recursive `define` still backpatch implicitly~~:
    gone. A `letrec` or `define-rec` binds only lambdas, and nothing is
    declared ahead (2026-09-26);
  - reads are not yet ordered by the optimizer, which moves nothing yet;
  - a read of an empty cell does not suspend, since there are no
    processes;
  - calls through a filled cell are not known calls.)*
- **Redefinition at the REPL: shadowing or late binding.** (Raised by the
  user 2026-09-26: "usual Scheme REPL semantics don't eagerly resolve the
  global reference and keep it fixed forever … but we can work with
  this.") Today a second `define` makes a new binding (ML's top level):
  sound without re-checking, and it makes a global as fixed as a `letrec`
  binding, which known calls use. Scheme's late binding could come back
  without losing that. A redefinition at the same type assigns the old cell.
  Typed calls depend only on the type, so they survive it untouched. Code
  that assumed the old value (loops, `callk`) records which cell it
  assumed, and the redefinition reverts that code to `global g; tcall n`.
  Words are heap data, so the reversion patches cells in place, and
  recompiles any word compiled to machine code. A redefinition at a new
  type re-checks the forms that mention the name, and either recompiles
  them or reports those that no longer check. So known calls should
  carry their global's cell, so that they can be found.
- **Time complexity as an effect.** (Raised by the user 2026-09-26, as a
  type-system direction for after M13's "type system first" work.) FX's
  own line did this:
  - Dornic, Jouvelot and Gifford's polymorphic time systems for
    estimating complexity (`GiffordHistory/papers/loplas.pdf`);
  - Reistad and Gifford's static dependent costs
    (`GiffordHistory/papers/lfp94.pdf`).

  It is the quantitative form of the responsiveness effect above. Code
  whose cost is statically bounded cannot run away, so it needs none of
  the fuel checks the machines make at word entries and taken branches.
  Bounds could also be declared and checked, as effects are.

- **Concurrency, and processes as distinct from functions.** (Raised by
  the user 2026-09-26.) FX-26 has no concurrency story yet. It may want
  its own forms for defining and declaring processes, apart from
  functions. A process could be typed by what it communicates rather than
  what it returns, which is where session types, which the user has also
  raised, would come in. This is for when the type system is extended.

- **The cellular REPL's state.** Under `--fx26-run cellular` or
  `evaluate`, each form is compiled with the definitions before it re-run.
  So a definition's state does not survive from one form to the next: a
  reference set by an earlier expression is fresh again. A session that
  keeps its compiled globals between forms would fix this.

- **Pinned code, with raw return addresses into it.** Possibly pinned only
  speculatively, with moving still possible at the cost of rewriting return
  addresses.
- **Sealing into a code space, and page-aligned suffixes**, so that fields
  stay writable while instructions are protected.
- **What the trailer holds**, beyond its tag and its purpose.
- **Native code (M10)**, which is where suffix alignment and pinning start to
  matter.

### Decisions (with the user, 2026-09-25)

1. **The name is "bloblet"**, which is unique when searched for.
2. **The trailer is the fast path, not an invariant.** The hard invariants
   are:
   - every bloblet starts with a header;
   - every field is tagged;
   - every tagged pointer points at the suffix start.

   A backward scan finds the header when there is no trailer. The trailer's
   contents are reserved.
3. **Mutability is per bloblet, chosen at allocation**, for the fields and the
   suffix independently. There is no global immutability; the effect system
   allows immutability-based optimisations later.
4. **Construction** allocates with `F = 0` and the whole size as suffix,
   zeroes the would-be fields, then changes the header once to the final
   field count, before the bloblet is published. The allocator is not
   required to hand out zeroed memory.
5. **Strings stay UTF-32.**
6. **The bootstrap interpreter reads bloblets directly**, including cellular
   ones, and compiled forms replace them incrementally, as in Forth.
7. **The FX-26 compiler written in FX-26 emits bloblets directly**: cellular
   and bytecode code bloblets. The Scheme pipeline leaves the FX-26 path.
   What the checker proved goes into the code's metadata fields. Annotated
   Scheme remains how FX-87 and FX-91 run. This supersedes, for FX-26 only,
   the 2026-09-21 choice to lower to annotated Scheme.
8. **No Rust piece is retired during M12.** When it is done, the Rust and
   FX-26 versions are compared together.
9. **The Rust pieces are not a fixed specification.** A Rust subcomponent's
   semantics may be revised where the overall design calls for it. The
   FX-26 version of a piece may do more, or be more expressive, than its
   Rust counterpart.
10. **Native code may come before M10.** FX-26 pieces running on the Rust VM
    may be very slow, as the eager reader already is. Their performance
    against the Rust counterparts is tracked as M12 proceeds, in
    [`docs/performance.md`](docs/performance.md). If it becomes the
    bottleneck, starting on native code is on the table then, not deferred.
11. **`unsafe` lives in two crates: `fixpt-native`, and `fixpt-memmgmt`.**
    Every other crate keeps `unsafe_code = "deny"`. Native code is
    generated by our own encoder, arm64 first, since this machine is Apple
    Silicon. *(Amended 2026-09-26 by the user: `fixpt-memmgmt`, below
    `fixpt-heap`, gives the heap memory reserved from the system, which it
    holds directly. `fixpt-native` sits above the heap, so memory from it
    could reach the heap only through an indirection, measured at 12–47%
    wherever Rust touches the heap.)*
12. **Nightly Rust is allowed for the stencils, and only there.** The user is
    willing to use unstable Rust where it expresses what we need.
    `become` (`explicit_tail_calls`) works on the installed nightly and
    guarantees the tail jumps a cellular inner interpreter is made of, even
    at `-O0` (`docs/research/copy-and-patch.md`, addendum). `fixpt-native`'s
    build script compiles stencils with `rustc +nightly`, and the workspace
    stays on stable.

[^cellular]: "Cellular" would be called "threaded" in the Forth community: code as
a sequence of cells (references to routines, and their operands), run by an inner
interpreter. This repository says "cellular" throughout (the user's decision,
2026-09-27).

## The queue after the benchmark ports and the research (2026-09-29)

What the reference benchmarks (`scheme-bench/`, `mllang-bench/`) and the
research notes (`docs/research/{floats,telemetry,async,separate-compilation,
logical-types,polytypic}.md`) found, and the user's decisions on them,
as an ordered queue. Smaller friction is in `TODO.md` §§ 12–15.

### Decided with the user (2026-09-29)

1. **`int` is a bignum.** An exact integer of any size: a fixnum while it
   fits, a bignum past that. Today the lowered path gives bignums (it
   runs Scheme's `+`) and every compiled machine traps on overflow, so
   the machines disagree; they must agree on the bignum answer.
2. **Fixed-width integers:** `i32`, `i64`, `u32`, `u64`, for machine
   words, bit operations and speed where the width is the point. Their
   arithmetic **wraps** (the user's, 2026-09-29). `int` arithmetic that
   overflows a fixnum **promotes** to a bignum.
3. **Floats: `f32` and `f64`.** An `f64` is boxed where a uniform word is
   needed (the heap's flonum, a 16-byte bloblet), not by changing the
   runtime's representation; unboxed where the types allow
   (`docs/research/floats.md`).
4. **Dictionaries and tags over specialization.** Polymorphic code is one
   copy that is passed what it needs (a dictionary, a layout descriptor,
   a type representation, a tag), not a copy per type. The compilers may
   specialize where a dictionary is known, as they specialize at a known
   lambda today, but that is an optimization, not the mechanism. This
   revisits the polytypic note (deriving whole copies) and the flat-array
   idea (layout descriptors, not monomorphization).

### The queue

**Q1. Native-path bugs the ports found.** Each has a reproduction in the
ports' headers or `/private/tmp/claude-501/*` (to be moved into tests):
- Done (2026-09-29): `car`/`cdr` of `nil` crashed every machine-code
  machine (one unchecked load); each now checks the tag and traps. Q7's
  `consof` can drop the check where the type proves a pair.
- Done (2026-09-29): a native abort did not find a prompt that cellular
  code installed, nor cellular code one native code installed; an abort
  finding none now goes on to the other machine (`NativeExit::Abort`).
  Its cost no longer grows with the stack (the search stops at the first
  prompt).
- Done (2026-09-29): an inlined `extract` from an earlier form got field
  -1 (the FX-26 compiler's facts are keyed by position in one form's
  text), and its callers silently ran as cellular code. A body kept for
  inlining or specialization now has its fields resolved when kept
  (`c-resolve-extracts`); a definition that runs as cellular code says so,
  by name. Other facts keyed by position (conversions, effect summaries)
  are still lost in such bodies; separate compilation's S2 generalizes
  the fix.
- Fixed (2026-09-29): register code for more than 8 values (arguments,
  parameters, free values, a call-out's operands: a bloblet's fields).
  Larceny's convention: REG1…REG7 hold the first seven, REG8 a list of
  the rest; the callee takes it apart into its frame; stack code calls a
  register word of more than 8 parameters as stack code. `earley`,
  `graphs`, `parsing` and `ratio-regions` now have no declines. Also: a
  procedure that calls `stay-cellular` is not inlined or specialized
  (it made its callers cellular: `aborts.fx`'s `mid` never ran natively),
  and a global's procedure the native compiler cannot compile is called
  through its cell, the rest compiled natively, where it used to fail
  them all. Still to do: a constant list of the rest made at compile
  time; prompt bodies of more than 8 free values.
- Also fixed (2026-09-29): frames too large for one `stp` (two
  instructions now; a frame past 60 slots is unmapped, header -1, zeroed
  on entry and traced whole, `native/wide-frame.fx`); a long right-nested
  operand chain ran out of registers (the operand's register is now taken
  after the operand is computed); `fixpt compile` names each definition
  the Rust compiler made no register code for, and why.
- Resolved (2026-09-29): a product argument was slow natively (10M
  calls: 3.4 s against 0.5 s). Measured again after the inlined-`extract`
  fix: 10M calls not inlined, a product or two ints, take the same time,
  and native is ahead of lowered in both.
- Fixed (2026-09-29): the native stack was a fixed 8 MB, and recursion
  a million deep overflowed it natively. It is 512 MB of zeroed memory,
  committed only as it is touched (a run's resident size is unchanged):
  ten million frames. Segmenting it (the async note's stack segments) is
  for later. A collection still walks every native frame, so a deep
  stack makes each minor collection slow; a watermark would fix that.
- Fixed (2026-09-29): native collection slowed as live data grew
  (`paraffins` 57 s native, 20 s lowered). Counted (Q3): 657 major
  collections copying 23 400 M words, 8 minor. The native call-out made
  `collect`, a major collection, whenever one was due, so every nursery
  that filled was collected with the whole heap. It makes the one due
  now: 8 major, 664 minor, 9.7 s. Test: a native run that fills the
  nursery makes minor collections only.
- Measured (2026-09-29): precise globals effects did not make `set.fx`'s
  native code slower. With `cmps`, the effect naming 17 globals, written
  `(read @globals)` instead, the run takes 6.6 s against 13.1 s, but
  with no iterations 3.5 s against 9.8 s: the benchmark itself costs the
  same (identical register and machine code, identical call-outs), and
  the difference is the front end. The FX-26 checker takes 5.0 s against
  2.8 s, the Rust checker 25 ms against 11 ms (`FIXPT_TIME_PHASES=1
  fixpt check`), compiling the same. Each global read is an atom of its
  own, so effect joins and subsumption grow with the globals named.
  Looked into (2026-09-29), the user asking why the FX-26 checker is
  100x the Rust one. Two causes:
  - The FX-26 checker's own costs, on `set.fx` run as register code
    (`FIXPT_PROBE_FILE=… probe_phases_as_register_code`, with
    `FIXPT_PROFILE_PHASE=check` for cells by procedure): 0.41 s. Global
    names were ordered character by character through `symbol->string`;
    every type printed searched its whole text for its own `%n` (quadratic
    in the type); `k-union` and `k-within?` were quadratic in the atoms.
    Now `string-compare`, `symbol-compare` and `string-search` are
    standard operations (runtime primitives), and union and subset walk
    sorted effects once: 0.112 s (coarse: 0.063 -> 0.037 s). The Rust
    checker: 0.025 s.
  - The session runs the front end as lowered Scheme on the bytecode VM,
    about 28x its register code (`fixpt check`'s FX-26 checker on
    `set.fx`: 4.96 -> 3.18 s with the fixes above). Done (2026-09-29):
    the session's checker and compilers run as register code
    (`Fx26Session::front_end_compiled`, on in the CLI; the front end
    compiled when first loaded, its 19 entry points rebound to call the
    compiled ones by `%run-front-end` on the hand register machine; the
    reader stays lowered). `set.fx`: the FX-26 checker 3.31 -> 0.31 s
    (the Rust checker 0.026 s); the front end's work in a native run
    5.0 -> 0.65 s. A tiny program starts 0.2-0.45 s later (the front end
    checked again by the Rust checker, and compiled). To do: reuse the
    load's check, and a cached image (Q9 S0); the reader as register code.
  Still to do: the reference tables' times should leave out checking.
- Fixed (2026-09-29): a standard operation as a value takes the arity of
  the runtime primitive it runs as (`runtime-primitive-arity`), so
  `char-downcase` and the like are values in both compilers; `parse-int`
  is `parse-nat` (a natural number or -1; signed numbers are
  `parse-number`'s), and a radix past 2…36 fails instead of panicking.
- A redefinition check in the harness-only session path (`knot-spin`).

**Q2. Integers**, in this order: (a) every path traps alike; (b) the
fixed-width integers, wrapping; (c) a bignum library written in FX-26,
limbs `u32` computed in `u64`, so it never overflows into bignums itself
(Larceny's bignums are Scheme too, `src/Lib/Common/bignums.sch`); (d) the
machines' overflow paths call it, and big literals are built as constants.
The lowered path keeps the Scheme engine's bignums, an oracle for the
library.
- Done (2026-09-29): lowering and every machine agree: overflow traps
  everywhere. `+ - *` lower to `%fx26-add`/`-sub`/`-mul`, which fail
  "integer overflow" past a fixnum (the lowered path promoted to a
  bignum); the machines' `*`, which called the generic `*` and promoted
  too, is `%fx26-mul`. Test `overflow_traps_on_every_machine`. The
  lowered column of `fixpt bench` got faster (fixnum primitives, not the
  generic ones). Then:
- Done (2026-09-30, the user's "make int a bignum first"): `int` is an
  exact integer on every path (`docs/fx26.md`, "`int` is a bignum").
  Built on the runtime's bignums (`num::int_op`, `num_bigint`, which the
  lowered path already used), not (c)'s library in FX-26, which can
  replace it later behind the same call-outs: faster natively, and the
  machines agree with the lowered path by construction. Every machine's
  `int-add`, `int-sub`, `int-less` and a new `int-eq` (for `=`, which
  compiled to `eq`, the same word) keep the fixnums' case in line and
  call the runtime otherwise, with no collection; stencils and the hand
  machine by their call-out. Tests `ints_are_bignums_on_every_machine`,
  `ints_are_bignums_natively`, `bignums_run`. The cost, natively: each
  `int` add or compare tests its operands' tags (`helpers` 2.1 → 3.8 ms,
  `loop` 4.5 → 6.6, `fib` 2.2 → 2.8, measured old against new). Done
  (2026-09-30): a fixnum version of each procedure's native code with
  `int` operations, in which a value tested once stays known and an
  overflow or a bignum goes over to the general version at the same
  instruction (`docs/performance.md`, "A fixnum version of native code"):
  `helpers` 2.0, `loop` 4.0, `fib` 2.6. Not done: literals past a fixnum (neither
  parser reads one; `(* 1000000000000 1000000000000)` does); the FX-26
  evaluator has no fixed-width operations. The first plan was: the fixnum
  fast path stays one `adds` and a branch;
  the branch goes to a call-out that makes or uses a bignum (the Scheme
  engine's `N::Big` and `num_bigint`) instead of trapping. Comparison,
  `=`, `quotient`/`modulo`, hashing and printing take bignums;
  `array-ref` of a bignum index is out of range. Both checkers unchanged
  (`int` is still `int`); the compilers' constant folding must not
  assume 61 bits; the front end's machine-word arithmetic moves to `i64`
  or `u64`.
- Done in part (2026-09-29): `i32`, `u32`, `i64`, `u64`, whose
  arithmetic wraps, in both checkers, with 18 operations each, named by
  type (`u32*`, `u32-xor`, `int->u32`, `u32->int`; the user's choice over a
  width argument or overloading), as runtime primitives on every path
  (`docs/fx26.md`, "Fixed-width integers"; test
  `fixed_width_integers_on_every_machine`). An `i32`/`u32` is the fixnum
  of its value (the user's choice, over an immediate with a subtag; so
  `f32` should be asked again); an `i64`/`u64` the exact integer.
- Done (2026-09-29, the user's "the i32/i64/u32/u64 parts first"): the
  operations in line. They, and `int`'s `*`, `quotient` and `modulo`,
  never collect (`fixpt_runtime::never_collects`); register code calls
  them by `prim1`/`prim2`/`prim2imm`, values kept in registers, and native
  code does each in a few instructions, else calls it with no collection.
  FNV-1a in `u32`, 10M steps: 1386 → 12 ms natively; an `int` loop of
  `*` and `modulo`, 486 → 42 ms. Found on the way: `u64->int` (and
  `i64->int`) gave a bignum `int`, and `quotient` of the least fixnum by
  −1 one too, which compiled code, taking `int` for a fixnum, added as a
  pointer (the register machine answered wrongly): both now fail
  "integer overflow", as `+` and `*` did, until `int` was a bignum (then
  they gave bignums). And the
  register machine's inline `modulo` read a bignum as a fixnum.
- Done (2026-09-30, the user's "storing 64 bits in registers"): `i64`
  and `u64` raw in native registers, and only there (`fixpt_native::
  direct`'s `reps` pass over register code, which is unchanged): boxed
  (the exact integer, as everywhere else) where a value is read, so no
  frame, heap object or collection sees raw bits; unboxed on the ways
  into a place where they are raw, so a loop's variable stays raw. FNV-1a
  in `u64`, 10M steps: 1587 → 11 ms natively. Not done, and not needed
  yet: raw in frame slots (a raw value live across a call is boxed into
  the frame), raw across calls, and a boxed form other than the exact
  integer. The first plan was: `i32`/`u32`
  immediate (a word's upper half, a subtag); `i64`/`u64` raw in native
  registers and in frame slots outside the stack map, boxed as a
  bloblet with an 8-byte suffix in uniform positions, like `f64`. Bit
  operations (`and`, `or`, `xor`, `not`, shifts) on them; conversions
  to and from `int`. Unblocks `md5`, `psdes-random`, `DLXSimulator`, and
  the front end's word arithmetic.
- Unblocks `pi`, `chudnovsky`, `pidigits`, `smith-normal-form`.

**Variadic procedures** (the user's request, 2026-09-29): FX-87's
`(vsubr E T R)`, `vlambda` and `apply`, the count passed at every call
(the user's choice, Larceny's way, so that `apply` spreads a list). Done:
both checkers (`vsubr` generative type 0, variadic calls, `vlambda` read as
`%vlambda` of a one-list lambda), the lowering (Scheme's), and every
machine through a cellular wrapper and the routine `rest`; natively (same
day), the wrapper's register twin begins `vargs`, and every native call
passes its count in `x9`; `apply` in both register compilers
(`docs/fx26.md`, "Variadic procedures"). A standard `list`, its pairs made
in line by register code (same day). To do: fixed parameters before the
rest.

**Q3. Telemetry, stage 1** (`docs/research/telemetry.md`): done
(2026-09-30): the longest pause of each kind, the peak of words in use,
`FIXPT_GC_TRACE` (a line per collection), `FIXPT_GC_SUMMARY` (the report,
with those), and `M words` and `GCs` columns for the native run in
`fixpt bench`. Stage 2 (the FX-26 operations, `@telemetry`, `black-box`)
waits on the user's answers in the note. Fix the counts first. Done (2026-09-29): minor collections counted with major ones
(`Heap::collections`, `%gc-count`, the phase probe, `FIXPT_GC_REPORT`,
which `fixpt eval` now reads too); `minor_words_copied` and
`minor_nanos` apart; region and code-area allocation in `allocated()`;
the engine profile's name cache keyed on every collection. Then peak live words,
pause times per kind, `FIXPT_GC_TRACE`/`FIXPT_GC_SUMMARY`, and
allocation and collection columns in `fixpt bench`. Stage 2: the FX-26
operations under an `@telemetry` effect, and `black-box`.

**Q4. Floats** (`docs/research/floats.md`, S0 onwards): `f64` boxed
everywhere with the right answers (unblocks 10 Larceny and about 17 ML
benchmarks); `f32` immediate; then floats in native registers and raw
frame slots; float arrays as flat arrays (Q6); calling convention for
float arguments later, if measurements ask. Before floats in frames:
continuation capture must keep raw words (a captured frame as a bloblet
of its own kind), and native code must save `d8`-`d15` or not use them.
- Done (2026-09-30, the user's: named `f64` and `f32`, literals `2.`):
  `f64` on every path, the evaluator's included (`docs/fx26.md`, "Floats:
  `f64`"): base types `f64`, `f32` in both checkers; literals through both
  readers and parsers, both checkers and all four compilers; 33 operations
  as runtime primitives; natively raw in registers by `reps` (bits in `x`
  registers, each operation through `d16`/`d17`; never in frame slots, so
  neither continuations nor `d8`-`d15` needed changing). `sumfp`-like, 10M
  steps: 757 ms lowered, 31 ms native.
- Done (2026-09-30): `f32`, an immediate of its own (subtag 9, the bits in
  the upper half; the user's choice over the fixnum shape), 25 operations
  and conversions on every path and the evaluator (which also gained
  `int->string`); natively in line in `s` registers.
- Done (2026-09-30, with Q6): `(flatarrayof T R)`, `docs/fx26.md`, "Flat
  arrays".

**Q5. Identity: `eq?` on mutable objects, and address-hashed tables.**
Done (2026-09-30; `docs/fx26.md`, "Identity"; `TODO.md` §19): one `eq?`,
`(poly ((t type)) (subr pure (t t) bool))`, exact on mutable objects and
atoms, and on immutable data and procedures `#t` only if equal (the
user's choice); `eq` in line on every machine, and in the evaluator.
`(eqtable k v kr r)`, keyed by a dictionary `(identity k kr)` only the
standard procedures make, hashed by address, one stamp (the collection
count) where Larceny has tablets. Left: the ports' workarounds, and
`equal` and `dynamic`; maybe never, `eqv?` (item 11 of "Next"); later, `uniqueof` for interning (identity with
contents read purely, `TODO.md` §19), and Larceny's old and young tablets, so that a
minor collection rehashes only young keys (`TODO.md` §19). What was planned:
Every batch of ports hit the missing identity test (`equal`, `dynamic`
blocked; workarounds in `browse`, `conform`, `maze`, `sboyer`, `peval`,
`logic`, `boyer`, `hashtable0`). A typed `eq?` per kind of mutable
object (pairs, refs, arrays, bloblets), then `eq?`-hashed tables. Objects
move, so an address hash goes stale at a collection: Larceny's answer
(`src/Lib/Common/hashtable.sch`) is three tablets per `eq?` table, for
keys whose hash does not depend on the address (fixnums, chars,
symbols' own hashes), for old keys hashed by address and stamped with
`(major-gc-counter)`, and for young keys stamped with `(gc-counter)`. A
lookup searches them, and only on a miss, if a stamp is stale, rehashes
that tablet (young entries into the old tablet, since a minor
collection promoted them) and retries; a rehash that a collection
interrupts is retried; `reset-all-hashtables!` runs before a heap dump.
Our nursery promotes everything live at a minor collection, which is the
case this handles exactly. It needs from the runtime: an address hash,
whether a key's hash is address-sensitive (and young or old), a
collection counter that counts minor collections (Q3's fix) and a
major-only one, both readable cheaply; and a type story (the counters
under `@telemetry`, or a table type whose operations carry the effect).

**Q6. Flat arrays and a `flat` kind** (the user's idea, 2026-09-29).
Done (2026-09-30) as `(flatarrayof T R)` of the scalar flat types, with no
kind: a standard generative type over `(arrayof T R)`, self-describing at
run time, so that its operations are polymorphic in `T`, and made by a
layout, `(flatlayout T)`, which only flat types have (dictionary passing).
Natively in line; an `f64` element read raw where only `f64` operations
use it (a backward demand pass beside `reps`), and stored raw. A sum over
a million `f64`s, 100 times: 3375 ms (a box per element) → 296 ms native,
8063 lowered. Left: products and sums of flat data flattened (unboxed
data types, the user's question), region allocation (`rmake-flatarray`).
The first idea was: a
kind for types that carry no references (`int` as fixnums, `bool`,
`char`, the fixed-width integers, `f32`, `f64`, products of those),
and arrays of them as a bloblet suffix: no scanning by the collector, no
write barrier, bulk copy and fill as byte moves. Polymorphism over the
kind by a layout descriptor passed at run time (decision 4); flat arrays
at statically known element types first. Name to settle (`flat`, `bits`,
`plain`; `(flat-arrayof T R)` or a representation chosen by kind).

**Q7. Logical types, restricted** (`docs/research/logical-types.md`),
and with them facts through the disjunctive side of `or` and `and`
(occurrence typing; the conjunctive side is done, 2026-09-30):
first `consof`, a pair that is not `nil`, which `null?` narrows to (and
which lets native `car` stay one load); then unions of members with
disjoint run-time shapes, `(union T …)`, introduced only by subsumption
and eliminated by narrowing a variable (`typecase`, shape predicates);
intersections of procedure types (`overload`) later. Its open questions
are the user's.

**Q8. Generic operations by dictionary** (`docs/research/polytypic.md`,
revised by decision 4): first the standard environment's gaps (`bool=?`,
`datum=?`, string and symbol ordering, a hash combiner, `list->array`,
`array->list`); then generic `equal`, `hash`, `->datum`, `compare`,
`map`/`fold` as one definition each over a type representation or a
dictionary passed at run time, with the compilers specializing only
where it is known. (The `acyclic?` soundness gap it found is S1, first
in "Next".)

**Q9. Separate compilation** (`docs/research/separate-compilation.md`),
and with it modules, which the prelude and an FX-26 standard library wait
on (`TODO.md` §22). `docs/research/modules.md` (2026-09-30): second-class
units now, as Sheldon's `input` layer, with macros in units and their
interfaces; Sheldon's first-class modules later, as values units export;
open questions for the user in its §7:
S0 a saved heap image of the loaded front end, keyed by a hash of its
files and the binary; S1 checker snapshots at file boundaries; S2 facts
keyed by (file, offset) (with Q1's `extract` fix); S3 an optional
`(unit …)` header with `.fxi` interfaces both checkers write alike;
later stages as the note has them. Its open questions are the user's.

**Q10. Async** (`docs/research/async.md`): S0, a scheduler written in
FX-26 over prompts on a virtual clock, with tests on every machine; then
cancel scopes and channels, the Rust reactor, the benchmark that decides
stack segments. Before building: check continuation capture across nested
machine runs, and settle which reading of the soundness note's
`(Region)` rule is meant. Its open questions are the user's.

**Q11. Language friction the ports hit** (`TODO.md` §§ 12–15). Begun
2026-09-30: the standard operations of §14 (`docs/fx26.md`, "Standard
operations the ports wanted"), but `map`/`for-each`/`fold`, which wait on
a prelude written in FX-26; `letrec` bodies checked against the expected
type; reader errors placed; a `let` passing a `poly` to its body; types
naming types defined after them; `define*`'s missing-`spin` error; a local
`letrec`'s globals inferred; effect mismatches with a line of what is
beyond. A prelude for `map` and kin, and moving primitives out of Rust
into an FX-26 standard library, waits on modules (the user's; `TODO.md`
§22, with what was measured). Waiting on the user: prompt answer types,
`quote` of non-symbols, shadowed standard names. The list as
it was: local `letrec`
effects must list every global read transitively (infer them as
`define*` does); a `letrec` body is not checked against the expected
type; types cannot name types defined after them; one answer type per
prompt tag; `quote` takes only symbols; no `error`; missing `remainder`,
`zero?`, `list`, `append`, `map`, `max`/`min`, `char<?`, `string<?`,
`char-upcase`, `vector->list`, `list->vector`; `length` only on frozen
lists; `sum` is reserved; standard names silently shadowed; reader errors
always at 1:1; effect-mismatch messages print both whole sets.

## Log: the glance's details (moved here 2026-09-28)

The glance's long entries, as they stood on 2026-09-28, when it was cut
down to a summary. Newest work is also in `docs/performance.md`.

**The collected code area, the native convention, the REPL and globals**
(was item 0):

**In progress: a collected code area** ("A collected code area", below;
   the user's, 2026-09-27): native code in a non-moving, mark-swept section
   of the heap, so code no longer reachable is reclaimed, and code can
   reach GC-traced fields of its own bloblet PC-relatively. Steps 1–3 and
   4a done; the rest waits on **native code without the interpreter's
   shape** (`docs/research/native-conventions.md`, decided with the user
   2026-09-27): calling conventions in function types, native frames with
   stack maps instead of the ip in step and resume tables, and seven steps
   that replace 4b and 4c. Step 1 done (2026-09-28): conventions in both
   checkers, `(subr (conv C) …)`, `fx`, conversions inserted by the
   checker and `(convention C e)`. Step 2 in part: first-order procedures
   compiled to native frames and `bl`/`ret` (`fixpt_native::direct`),
   `fib` and `tak` about 2× register code, the identity lambda two
   instructions; `--calling-convention native` and `,native NAME` in the
   REPL; call-outs and inline `cons`, collecting with native frames as
   roots (`lists` as fast as register code). Step 3 in part: the code in
   the heap's collected code area, reclaimed when dropped. Step 4 in large
   part: closures and higher-order code; with `--calling-convention native`
   the REPL compiles and runs every expression as machine code; what it
   declines runs as cellular code, and native and cellular code call each
   other, continuations thrown past native code included. Of the test
   programs' forms, 52 run as machine code and 49 are declined: 11 for
   continuations and prompts (step 5), 35 because a definition's
   initializer does not check outside its definition (generative types'
   coercions, proved recursion; to do: compile the definition, then its
   closure natively), 3 for procedures with no register code. Then the rest of 4, and
   5–7. The REPL is incremental (2026-09-28), as Larceny's is: each form
   is checked after the ones before (`check-more`) and compiled alone
   against the globals' cells the compiler keeps; nothing is replayed.
   With `--calling-convention native`, definitions run in the native
   convention too: the global made by the compiler, filled with the value
   a native thunk computes; native code reads globals through their cells
   when it runs (but binds a cellular closure when compiling).
   Redefinition at the REPL (2026-09-28, with the user): a global's uses
   always refer to what it is now; one of a type every use can take keeps
   the global; one they cannot re-runs its users, breaking those that no
   longer check until they are defined again (the default), or keeps them
   on the old one, or is refused, as asked. Files too (2026-09-28, the
   user's decision): one rule, in both checkers (`top_defining`,
   `k-defining`), which say what a form runs (`checked-tops`); a value kept
   as it was is bound, `(define d (let ((g g)) …))`, so the REPL's choices
   are only break or refuse (`,redefine b|r`). A procedure's calls of
   itself by name go through its global too, as in Larceny; `letrec` binds
   one locally (the user's, 2026-09-28). A redefinition that would close a
   cycle through globals needs `spin` in its type. Globals are a region
   (2026-09-28, with the user; `docs/fx26.md`): naming `g` reads `(globals
   g)`, within `(read @globals)`; `define*` finds a procedure's globals
   precisely; both checkers, every program, and the front end (through
   `(read @globals)`) say so; compatibility counts what a redefinition
   reads; a procedure whose calls read its own global says `spin`, with
   no exception for recursion (the user's, 2026-09-28): one proved to end
   calls itself through a local `letrec`. Deferred (the user's,
   2026-09-28): `define-rec*`, until something motivates it; a way to name
   a set of globals as a region may come first (`define-effect` already
   names one as an effect). A lint finds loops written as recursion
   (non-tail self-calls stepping only an index, `fixpt-tidy`); the front
   end has none (2026-09-28, after an assembler overflow). A question
   answered: an ownership bit fits in a reference's high bits.

**The compilers, and smaller items** (were items 5–7):

5. M13's rest, the transformations first (the user's, 2026-09-28: more
   for the effort than fixed-width types): inlining (13f) done in part
   (2026-09-28): a call of a small global procedure is inlined in register
   code behind a guard that the global still holds the closure it was
   compiled from, so a redefinition needs no recompiling (the user's
   choice); both compilers, `docs/performance.md`; `,inliners NAME` says
   which globals' code inlines NAME. A recursive higher-order global
   called with a lambda at a parameter it only calls is specialized: a
   copy made for the lambda (partial evaluation at a static argument),
   guarded as inlining is (the user's example, `(map (lambda (x) (+ x 1))
   xs)`, 2026-09-28); register code 24 → 19 ms on `closures`, native
   slower until an inlined body's temporaries stay in registers. Common
   subexpressions measured and not built (109 pure recomputations in the
   front end, none in the benchmarks, each worth one instruction;
   `docs/performance.md`). Done too (2026-09-28, the user's list): an
   inlined body's temporaries and `let`s in registers where no call comes
   between; constants propagated and folded, with inlining (the guard
   keeps them inside it); a top-level procedure's calls of itself guarded,
   so a tail one is a loop (`lists` 13.5 → 9.3 ms); lifting out of loops
   measured and not built (3 in the front end's heads). Versions (the
   user's, 2026-09-28): a body's guards all at its start, a fast version
   assuming them (a leaf, or a loop, where it pays) and the plain one;
   sound where the body's effect keeps no continuation for later and
   writes no global (effect summaries, both checkers); `helpers` native
   6.1 → 2.0 ms. To refine: guards per segment between `comefrom`s (the
   user's), and versions of bodies with closures. Done too (2026-09-28): a
   nested lambda compiled once, not 2^(d−1) times at depth d (the user
   spotted it in `,disassemble-asm`); constructors of constants made once
   while compiling (`wcell-sum`, `wcell-product`); operands in the order
   written (register code ran `>`'s second first, a bug), a constant
   second as an immediate and constant chains of `+` and `-` combined (the
   user's question); tests as jumps, `and`/`or`/`not` making no boolean,
   with a `brancht` (Twobit's `pass2if.sch`, the user's recollection). A
   collection landing in a phase shows as a step in its time
   (`probe_phases_as_register_code`): heap sizing is its fix. Speed is judged
   by the native convention's code only (the user's, 2026-09-28: the
   interpreters must not be asymptotically inefficient, but their constant
   factors do not matter): superinstructions (13g)
   are dropped, and so are the cell-for-cell compiled words' gaps
   (`--cellular-machine native-compiled`, about 95 instructions for the
   identity). Next, for native code: join points (13i), the rest of known
   calls, a nursery with a write barrier, a lint on a lambda's size; and,
   when the user says (2026-09-28: "don't worry about those yet"), region
   `cons` inline natively (`lists-region`, 158 ms native against 7 in
   register code) and cheaper captures (`captures`).
6. Smaller: `nlist` error messages; the language gaps the survey found;
   M8 docs and polish; M10, a full native compiler, is not scheduled.
   (Done, 2026-09-28, the user's: `,disassemble` of a native closure
   shows the cellular word and register code it was compiled from, each
   code bloblet keeping its word, `CODE_SOURCE`; `,disassemble-asm` its
   machine code.)
7. Fixed-width integers, low priority (the user's, 2026-09-28): `i32` and
   `u32` kept in a word's upper half (`v << 32`, a fixnum to the collector,
   so frames stay scannable), with wrapping `+`, `-` and compare one
   instruction each and no overflow stub, which also makes code smaller;
   packed arrays of them in a bloblet's suffix; `i64` and `u64` only once
   native frames have stack maps (step 3), since they need all 64 bits
   unboxed (the problem Larceny solved for flonums by boxing).
