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
4. **Code as bloblets**, compiled form: constants and metadata in fields at
   fixed negative offsets, which are part of the layout specification, and
   bytecode as the suffix. Closures hold bloblet pointers. *(Done
   2026-09-25.)* The *threaded* form, with the program in the fields, is a
   new execution mode with an inner interpreter. It is built with the native
   inner interpreter, A′3, where the Rust bootstrap version is its oracle.
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
A3. **A native inner interpreter** (`NEXT`) as the suffix of threaded code
    bloblets, run beside the Rust bootstrap interpreter and checked against
    it. *(Done 2026-09-26, as `fixpt_engine::threaded` (the Rust machine,
    and the word layout, `layout::threaded`) and `fixpt_native::threaded`.
    A change from the text above: the heap is not executable and moves, so
    a word's entry is a routine *number*, and the routines live in the code
    space. That also keeps machine addresses out of heap images. Cells are
    token-threaded primitives or words. Both machines check fuel and stack
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
FX-26 to threaded code, which the user pointed out; checking the rest the
same way found no FX-26 AST in FX-26, a threaded machine that knew only
Forth's primitives, and no way for FX-26 code to make a threaded word or run
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
   - **9c. The threaded machine grows what FX-26 needs**: frames and
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
     `Heap::make_threaded_word`, for the builder, `%make-word` and FX-26
     alike; `%run-word` runs one through `Runtime::run_word`. The native
     machines trap on the new routines until 9c's native half. Boxing is
     the compiler's, and only `letrec`'s need it.)* *(Control done
     2026-09-26: a prompt is two return entries, where to resume and a
     marker with its tag, handler and the data stack's height; the body runs
     as a closure above them. A composable continuation copies the stacks
     above its prompt into a `threaded-continuation`, and composing it
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
     gives the same value on all three machines; `fixpt --threaded-machine
     rust|native|stencils` picks one.)*
   - **9d. A compiler in FX-26 from the AST to threaded words**, emitting
     bloblets. Checked three ways on the same programs: the evaluator, the
     lowering to Scheme, and the threaded words on the native machine.
     *(First part done 2026-09-26: `src/compile.fx`, on the Rust threaded
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
    compiler) and a driver, `src/bootstrap.fx`, to one threaded word:
    stage 1. That word, run on the native machine, gives the driver. The
    driver reads, parses, checks and compiles the same text, entirely by
    compiled FX-26: stage 2. The two words are the same code, cell for cell
    (`tests/bootstrap.rs`, `fixpoint`). On the way:*
    - *the standard operations that Scheme ran as procedures of its own
      became runtime primitives, so threaded code calls them too;*
    - *`%run-word` calls a threaded closure as well as a word.)*
11. **Native code from FX-26**: a word's cells compiled to machine code, by
    an encoder written in FX-26 (the Rust one its oracle) or by placing
    stencils, and installed as the word's entry routine, one word at a time,
    as decision 6 describes. Checked by running the same programs threaded
    and compiled. *(Revised 2026-09-26, tracing each step's inputs. The
    hand-encoded machine's routines read their operands through the ip,
    and the ip walks the cells. So a word's native code can be its cells'
    routines inlined in order, with the dispatch between them removed and
    the ip kept exactly in step. Traps, call-outs, safepoints and return
    entries then see the same state as threaded code, and the two mix
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
    FX-26 lowered, and FX-26 compiled on each threaded machine. Compiled
    FX-26 on the native machines now beats lowered FX-26 in every piece;
    the Rust checker is still 22 times faster than the FX-26 one.)*

### After M12: what the user asked for next (2026-09-26)

- **An optimizing compiler for FX-26, in Rust and in FX-26.** It takes
  Twobit as a model, and Forth compilers and threaded-code VMs, since much
  may be won on the threaded code itself (peephole optimization,
  superinstructions, stack caching). It keeps Twobit's principle: each
  transformed program is still a well-formed program of the source
  language with the same meaning, carrying at most the analysis added.
  Research on Twobit's passes and history, and on Forth and threaded-code
  compilers, comes first.
- **A printer for compiled forms**: the threaded code in a word's
  bloblet, shown from the REPL, cell by cell, with routine names and
  operands. *(Done 2026-09-26: `fixpt_runtime::disasm`, `%disassemble`,
  FX-26's `disassemble`, and `,disassemble E` in the FX-26 REPL under
  `--fx26-run threaded`. Globals' cells now carry their names. The
  threaded REPL keeps earlier definitions, so later forms can use
  them.)*
- **Research for the compiler**: `docs/research/twobit.md` and
  `docs/research/threaded-compilers.md`.
- **Closures that carry their types** (a direction, not yet a task). A
  threaded closure is a bloblet, so it could carry its type, or enough
  for a checker to confirm the type from its fields and code:
  foundational proof-carrying code. With heap images, and fragments of
  them, loaded into other runtimes, that would let a runtime trust code it
  did not compile.
- **The FX-26 checker's free variables**, computed once rather than at
  every mask (`docs/performance.md`).

### M13 plan: an optimizing compiler for FX-26, in Rust and in FX-26

Drafted 2026-09-26 from `docs/research/twobit.md` and
`docs/research/threaded-compilers.md`, tracing each step's inputs.

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

- **13a. A Rust compiler to threaded words.** It makes the same words as
  `compile.fx` for every program, cell for cell. `compile.fx` has had only
  the Scheme lowering as its oracle, so there is nowhere yet to test a
  pass in Rust end to end. *(Done 2026-09-26:
  `fixpt_fx26::threaded::Compiler`, over the Rust checker's forms. It
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
  call. Our threaded machine already has `REG0` (`clo`) and frames, but
  passes every value through the data stack. The plan:

  1. **An IR, in Rust** (`fixpt_fx26::regcode`). Each lambda becomes
     MacScheme instructions, made from the checker's trees as the threaded
     compiler's are. Twobit's pass 4 is the model: register targeting, a
     frame made lazily (only on paths that call), `store` only of what is
     live across a call, `load` after. Primitives are `op1`/`op2`/`op2imm`,
     typed as 13d made them. The IR can be shown (`,disassemble`) and has
     an interpreter in Rust, the oracle, run against the lowering on every
     test program.
  2. **The moving collector decides where values may be.** A Value may be
     in a machine register only between points that can collect. Anything
     that can collect is a call-out, the same as the threaded machines:
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
     threaded code call each other. The *register entry* takes arguments in
     registers. The *threaded entry*, the word's usual one, moves a
     threaded frame's arguments into registers and continues. A register
     call to a callee without register code pushes a threaded frame and
     enters the word. A return entry says which convention returns to it.
  5. **Checks where they are needed:** fuel and stack limits at entry and
     on back edges, and an argument count never, since arities are static.
  6. **Order:**
     - (a) the IR and its interpreter, for all of FX-26;
     - (b) machine code for the procedures the benchmarks need, with the
       rest still threaded behind the two entries, and measured;
     - (c) every form, until the bootstrap runs as register code;
     - (d) known calls (`callk`, 13e) as direct branches;
     - (e) the compiler written in FX-26 to match, instruction for
       instruction, as for the threaded compilers.
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
     and `loop` 5.9× faster than compiled threaded words; see
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
  Click's Pauseless GC at Azul, later C4.) The threaded machine's state is
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
  4. A prompt that records how many regions are live, and an abort that
     ends the newer ones. Until then, the regions an escape leaves live
     only until the next ending of an older region.
  5. `letreap`, a heap of its own.
  6. The checker's record of each allocation's region
     (`NodeFacts::alloc_region`) is no longer used to allocate; it may go.

- **Responsiveness as an effect.** (Raised 2026-09-26.) Distinguish "may
  diverge without reaching a poll" from "every unbounded path polls, and
  every callee does too". A poll (the native machine's fuel and limit
  check, or an interrupt check) discharges the effect, as a handler masks
  one; Koka's `div` is the coarse version. It would let a word with no
  backward branch that calls only such words skip the check at entry. The
  threaded machines already check exactly at word entry and taken branches,
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

- **The threaded REPL's state.** Under `--fx26-run threaded` or
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
    guarantees the tail jumps a threaded inner interpreter is made of, even
    at `-O0` (`docs/research/copy-and-patch.md`, addendum). `fixpt-native`'s
    build script compiles stencils with `rustc +nightly`, and the workspace
    stays on stable.

