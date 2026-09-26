# `fixpt` — a Rust Scheme engine with FX-87 and FX-91 front ends

**Status: approved 2026-09-20; M0–M7 complete — the three deliverables of §0 are
done. See the milestone table in
§8 and `README.md` for what runs today.**

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

| Source | What it tells us |
|---|---|
| `extracted/fx91/{abstract,token,sugar,kind,typecheck,unify,constraints,eval,free,substitution,standard,code,top}.scm` | FX-91's complete structure: mutation-based unification with `forward!` union-find nodes, ACUI effect constraints solved as Horn-clause satisfiability (Dowling–Gallier), `poly~` type schemes, value-restriction via `expansive?`, first-class modules with `up-`/`down-` coercions, `select` dependent types, `rename-moduleof` alpha-renaming. |
| `mit-psrg-fx/fx87/old-impl/{syntax,type-check,inequal,kind-check,erase,sugar,standard}.lisp` | FX-87 is *checking*, not inference — but has **more** description machinery: three kinds (`type`/`effect`/`region`), subtyping/subeffecting (`type-less?`/`effect-less?`/`region-less?`), effect masking (`erase-effect`), circular types built with `set-car!` and compared with a cycle `trail`, and a bigger standard library (`oneof`/`recordof`/`vsubr`/`promise`/`port`/`sexp`). |
| `extracted/fx91/tests.fx` | 182 top-level forms. The live reference processes 168 and then dies evaluating form 168 — `nil~: undefined`, a genuine gap in the plain port's runtime (the `fx91-hashlang` runtime supplies `fx-nil~`). Types/effects are fine for all 182. |
| `HISTORY.md` §"Coverage audit" | Known reference gaps to plan around: `[e d1 d2]` proj-sugar is real FX-91 but unreachable through the port's reader; multi-segment dot-notation `a.b.c` is recursive (`(with a (with b c))`), not a literal field name; `(define (f (x int)) ...)` shorthand; `input`; `does` is gated off by default. |
| `fx91-hashlang/lang/reader.rkt`, `fx87-hashlang/lang/reader.rkt` | Both dialects case-fold symbols; FX-87 reads `#t`/`#f`/`#u` as *symbols*; FX-91 reads `#u` as the symbol `#U` but `#t`/`#f` as real booleans. The reader is genuinely per-dialect. |
| `larceny/src/Compiler/pass{1,2,3,4}*.sch` | Pass structure worth borrowing: alpha-renamed core grammar, nodes annotated in place with free/assigned/referenced sets. Worth *not* borrowing: fifteen passes and four native back ends. |
| `larceny/src/Rts/Sys/heapio.{c,h}` | Heap image format: version word, roots, word count, data — all pointers base-0 relative so load needs no relocation. We take this idea and drop the split/dumped variants. |

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

| Crate | Contents | Rough size |
|---|---|---|
| `fixpt-heap` | `Value`, tagged-word heap, object layouts, Cheney GC, image dump/load/verify | 2.5k |
| `fixpt-runtime` | symbols, globals, numerics, strings/vectors, ports, errors, primitive table | 3k |
| `fixpt-read` | syntax profiles, lexer, reader, spans, `write`/`display` | 1.2k |
| `fixpt-core` | Core IR arena, binding/env, pass framework, standard passes | 1.5k |
| `fixpt-engine` | `interp` (AST machine) + `vm` (compiler + bytecode VM) | 4.5k |
| `fixpt-scheme` | Scheme dialect: special forms, `syntax-rules`, prelude | 2.5k |
| `fixpt-fx87` | FX-87 front end | 5k |
| `fixpt-fx91` | FX-91 front end | 6k |
| `fixpt-cli` | the `fixpt` binary | 0.8k |

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

| Mode | Command | Mechanism |
|---|---|---|
| Decoupled runtime + heap | `fixpt run --heap prelude.heap prog.scm` | separate `.heap` file |
| Coupled single binary | `fixpt build prog.scm -o prog` | copy the runtime binary, append the image + an 16-byte trailer (`magic`,`len`); `./prog` self-loads by reading its own trailer |
| Statically embedded | `FIXPT_EMBED_HEAP=x.heap cargo build -p fixpt-cli --features embed` | `build.rs` + `include_bytes!` |

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

| Profile | Case | `#t`/`#f` | `#u` | `[ … ]` | Notes |
|---|---|---|---|---|---|
| `scheme` | sensitive | booleans | — | parentheses | R7RS: `#\c`, `#u8(`, `#;`, `#\|…\|#`, labels |
| `fx87` | folded | **symbols** `\|#t\|`/`\|#f\|` | symbol `\|#u\|` | symbol constituents | `@region` symbols |
| `fx91` | folded | booleans | symbol `#U` | **`(proj …)` sugar** | reconstructs the reader macro the archive lost |

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

| Suite | Source | Size |
|---|---|---|
| FX-91 static | `extracted/fx91/tests.fx` | 182 forms × (type, effect) |
| FX-91 dynamic | same | 168 values + 14 augmented |
| FX-87 | `mit-psrg-fx/fx87/library/*.fx` (tak, complex, church-numerals, deriv, dna, polynm, hash, takl, symbol-tab) + an authored expression suite run through the reference | ~13 programs + ~200 expressions |
| Scheme | authored R7RS assertion suite | ~400 assertions |
| Differential | every case above | interp vs. vm must agree |
| GC stress | every case above | `--features gc-stress` |
| Image round-trip | every case above | dump → load → rerun → identical |

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

| # | Milestone | Demo at the end |
|---|---|---|
| M0 ✅ | Workspace, golden generators | `reference/regenerate.sh` produces the checked-in `.expected` files: 182 FX-91 cases (type, effect, value), 155 FX-87 cases (type, effect) |
| M1 ✅ | `fixpt-heap`: values, heap, Cheney GC, image dump/load/verify | `fixpt image info/verify`; 22 tests, green under `gc-stress` |
| M2 ✅ | `fixpt-read`: profiles, reader, writer, spans | 21 tests; all 182 FX-91 and 155 FX-87 forms read and round-trip |
| M3 ✅ | `fixpt-core` + `fixpt-runtime` + `fixpt-scheme` + `interp` | `fixpt repl` works: bignums, rationals, proper tail calls, re-entrant `call/cc`, `dynamic-wind`, `guard`, records, promises. Green under `gc-stress` |
| M4 ✅ | `vm`: bytecode compiler + VM | flat closures, assignment conversion, 19 opcodes. FX-91's 182 cases pass **compiled as well as interpreted**; 9 differential tests require both engines to agree on values, output *and* error text; ~1.6× faster |
| M5 ✅ | Images & shipping | Core IR lives in the heap, so an image is resumable. `fixpt dump-heap` (image beside the runtime), `fixpt build` (one standalone executable, no `fixpt` needed on the target), `fixpt run-image` (either). An image records which engine made it, so nothing has to be told |
| M6 ✅ | `fixpt-fx87` | 161 cases: **161/161 parse, 160/161 type and effect, 123/123 value** of those the archive's evaluating path can answer. Driven from the CLI as `fixpt --dialect fx87 repl\|run\|eval` |
| M7 ✅ | `fixpt-fx91` | **182/182 on all three levels** — parse, type and effect, and evaluated value. Driven from the CLI: `fixpt --dialect fx91 repl\|run\|eval`, presenting results in the 1991 top level's `:`/`!`/`=` notation |
| M8 🔶 | Docs & polish | `docs/` mapping every component to its 1987/1991 counterpart; benchmarks (`cargo run --release --example engines` is the start). Collector workloads from Larceny's `test/GC` already landed in `tests/gc_workloads.rs` |
| M9 ✅ | hygienic macros | `define-syntax`/`let-syntax`/`letrec-syntax`/`syntax-rules`, hygienic by renaming (Clinger & Rees); the built-in derived forms hygienic too; R7RS §7.3's own macro definitions of the derived forms pass against the built-ins. SRFI 211 `er-macro-transformer` and `ir-macro-transformer`, with `begin-for-syntax`. SRFI 139 syntax parameters, `identifier-syntax`, `syntax-error`. See [`docs/macros.md`](docs/macros.md) |
| M11 ✅ | FX-26: the tooling's own language (the seven-step plan, done 2026-09-25) | effects as licences, bidirectional checking, typed delimited control; the eager reader ported to it first. Direction and plan: [`docs/fx26.md`](docs/fx26.md) |
| M12 | FX-26, bootstrapped: its interpreter and compiler written in FX-26, over a new object model shared with Rust | three phases — bloblets, FX-26 over bloblets, bootstrapping. See §11 and [`docs/object-model.md`](docs/object-model.md) |
| M10 | *(future)* native code generation | the bytecode/heap-image design is kept amenable to it; not scheduled |

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

1. **`docs/object-model.md`**, reviewed and committed.
2. **One specification table**: tags, header bits, kinds, and the reserved
   trailer. The Rust constants are generated from it, and later an FX-26
   module too, with a test that the two agree.
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
   the backward scan runs.
4. **Code as bloblets, in both forms:**
   - *compiled*: constants and metadata in fields, bytecode as the suffix;
   - *threaded*: the program in the fields, run by the Rust bootstrap
     interpreter as the inner interpreter.

   Closures hold bloblet pointers, and frames hold a code pointer and an
   offset.
5. **The other types, one at a time**: vectors, bytevectors, strings (UTF-32),
   flonums, bignums, records, boxes and the rest. At the end, the collector no
   longer needs to know what anything is: `ObjType::payload_is_scanned` and
   tag `010` are retired. Pairs stay as they are.

### Phase A′: a native core (in Rust, arm64 first)

In the Forth vision a code bloblet's suffix is machine code, even for
threaded code, where it is the inner interpreter. So a small native core
belongs to M12. M10 keeps a full native compiler.

A1. **`fixpt-native`**, the one crate where `unsafe` is allowed:
    - executable memory, mapped with `MAP_JIT` on macOS;
    - writing and executing toggled per thread;
    - instruction-cache invalidation, which is the "seal" step of the object
      model;
    - calls into a code bloblet's suffix, and back out to `extern "C"`
      runtime functions.

    Every unsafe block states the rule it relies on.
A2. **An arm64 encoder**, in Rust, covering only the instructions needed:
    loads, stores, arithmetic, branches, calls and returns. It is our own
    code generation, not copies of Rust-compiled code, whose position
    independence and extent Rust does not promise. It is the stage-0 oracle
    for the FX-26 compiler's own encoder.
A3. **A native inner interpreter** (`NEXT`) as the suffix of threaded code
    bloblets, run beside the Rust bootstrap interpreter and checked against
    it.

### Phase B: FX-26 over bloblets

6. **FX-26's view of bloblets:**
   - a type along the lines of `(bloblet (fields T…) R)`;
   - reads by field and by byte, and code-pointer types;
   - the construction protocol and `seal` as primitives, with the `init`
     effect, so a record's fields count as uninitialised until stored and
     frozen fields offer no writes;
   - the layout module generated in step 2.
7. **The data types the tooling needs, built on bloblets:**
   - records and sum types (`oneof`/`tagcase`);
   - tables;
   - symbols as values.
8. **Reader data with source positions**, so the FX-26 reader feeds the
   checker directly and the Rust reader leaves the FX-26 path.

### Phase C: bootstrapping

9. **An FX-26 interpreter written in FX-26**, running threaded bloblets.
   Checked against the Rust bootstrap interpreter on the same programs.
10. **The FX-26 checker written in FX-26**, checked against the Rust checker
    on every test program: FX-26 checking FX-26.
11. **The FX-26 compiler written in FX-26**, replacing threaded bloblets with
    compiled ones one at a time. Checked by running the same programs
    interpreted and compiled.
12. **Retiring Rust pieces**, one at a time and deliberately. Each keeps its
    Rust version as oracle and stage 0 until decided otherwise.

### Kept open, deliberately

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
6. **The bootstrap interpreter reads bloblets directly**, including threaded
   ones, and compiled forms replace them incrementally, as in Forth.
7. **The FX-26 compiler written in FX-26 emits bloblets directly**: threaded
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
11. **`unsafe` lives in one crate, `fixpt-native`.** Every other crate keeps
    `unsafe_code = "deny"`. Native code is generated by our own encoder,
    arm64 first, since this machine is Apple Silicon.

