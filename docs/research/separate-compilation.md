# Separate compilation for FX-26

A research note, 2026-09-29. Nothing here is implemented. It answers four
questions: what separate compilation FX-26 can do as it stands; which small
changes would enable more of it without losing FX-26's character; what FX-91
and FX-87 had, and what later systems do; and a staged plan with open
questions for the user. The sources are listed at the end. Each on-disk
paper is cited by path and PDF page (in the FX-91 report and Sheldon's
thesis, the PDF page is the printed page). Repository files are cited by
path and line, as of commit `eaab38f`.

**In brief.** FX-26 has no units today, but it has most of what a unit
system needs:
- an incremental REPL that checks and compiles one form against a summary
  of the forms before it (the checker's environment, the compiler's global
  cells);
- a redefinition rule that already decides when dependents must be checked
  again;
- inlining guarded by the identity of the global's closure, so it never has
  to be recompiled for correctness;
- an initial environment written as `(name type)` text, which is an
  interface file in all but name.

What it lacks is identity that is not "a name in one flat program". Global
regions are keyed by `Sym`, generative types by their index in the checker,
and the compiler's facts by byte offsets in one text. Three things are also
not persisted: checked state, compiled words, and native code.

The recommendation runs in four stages:
1. Cache first, with no language change: an image of the loaded front end,
   and snapshots of the checker at file boundaries.
2. Fix position-keyed facts, which also fixes the known "inlined `extract`
   gets field -1" bug.
3. Add a small, optional `unit` header with imports and exports. Interfaces
   are written by the checker in the standard environment's own format, and
   linking reuses the redefinition rule as a cutoff test.
4. Later, carry compiled units as fragments, the C10 of
   `type-and-effect-directions.md`.

From FX-91, adopt `input`'s idea of a closed file stamped for identity, and
abstract effects, bounded. Skip first-class modules for now.

## 1. Today

### What a program is

A program is one sequence of top-level forms: `define`, `define*`,
`define-rec`, `define-type`, `define-effect`, `define-generative`,
`private-regions`, and expressions (`crates/fixpt-fx26/src/top.rs`
lines 1–24). Types and effect abbreviations are declared ahead, in a first
pass over the whole text (`declare_ahead`, `top.rs` 766–786). Values are
not: "a definition sees only the definitions before it" (`docs/fx26.md`
87–100). The soundness note models a program's definitions as nested
`let` and `letrec` (`docs/research/soundness.md` 60).

The front end written in FX-26 is twelve files, 13,545 lines by `wc -l`
today (about 1,550 top-level forms). `lib.rs` joins them into one text
(`front_end`, `FRONT_END_FILES`) and checks that text as a single program;
`front_end_location` maps an offset in it back to `file:line:col`. A scan of
top-level names shows the files form a DAG:
- the leaves are `eager-reader`, `table`, `layout`, `standard`, `arm64` and
  `native-layout`;
- `native.fx` uses `parser`, `layout`, `compile`, `arm64` and
  `native-layout`, but not `check`;
- the only forward "references" the scan finds are names used as locals
  (`items`, `top`, `env`, `code`), which the checker should confirm.

The files keep their names apart by prefix, by hand: `k-` for the checker,
`c-` for the compiler, `r-` for register code, `n-` for native, and so on.
Their state lives in shared region constants (`@t`, `@k`), and they declare
`(read @globals)` throughout (`docs/fx26.md` 207–210). That is a module
system by convention.

### What the REPL keeps between forms

The REPL is incremental, "as Larceny's is: each form is checked after the
ones before (`check-more`) and compiled alone against the globals' cells
the compiler keeps; nothing is replayed" (`PLAN.md` 1830–1832). So the
REPL already compiles a unit, one form, against a summary of everything
before it. The summary is not a file, though. It is live state in several
places:

| State kept                                             | Where                                                                                                                            | Keyed by                                  |
| ------------------------------------------------------ | -------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------- |
| each global's type                                     | Rust `Checker::env`, `global_slots` (`check.rs` 44–148); FX-26 `k-env`, `k-global`                                               | name (`Sym` / symbol), newest wins        |
| type, family and effect abbreviations                  | `dscope`                                                                                                                         | name                                      |
| generative types                                       | `Checker::generatives`, a `Vec`; comparison by index                                                                             | index in this checker                     |
| which conversions see inside, and which are identities | `inside`, `transparent`, `conversions`                                                                                           | name, index                               |
| lemmas, used by subtyping                              | `lemmas`                                                                                                                         | order proved                              |
| known procedures (a call runs code the checker saw)    | `known`                                                                                                                          | (name, place in `env`)                    |
| private regions                                        | `private_regions`, uninterned fresh regions                                                                                      | identity of the fresh region              |
| definitions and their free globals, for redefinition   | `defs` (`top.rs` 60–67, 234–265), `broken`                                                                                       | name                                      |
| facts for lowering and compiling                       | Rust `NodeFacts` by `ExpId`; FX-26 `k-facts` by `(start end)` byte offsets (`check.fx` 529–553)                                  | expression, or offset in the current text |
| globals' cells, with order of creation                 | `c-genv-index` (`compile.fx` 215–222), `c-push-global` (1623)                                                                    | name, then creation count                 |
| inlinable and specializable bodies                     | `c-inlines`, `c-specials` (`compile.fx` 1381–1420, `c-record-inline` 1563): parser tree, word, `c-genv-now`                      | name                                      |
| native code's bindings                                 | each code bloblet's fields: global cells, closures of globals' procedures bound when compiling (`native-conventions.md` 258–280) | heap address                              |
| the front end itself                                   | checked by Rust and lowered to Scheme text on every load (`session.rs` 193–199, `compile_program_as` 170–183)                    | nothing: redone each session              |

### What a compiled form depends on

- **Types and effects of what it names.** Types print and read back,
  recursive ones as `(mu %d …)` (`docs/fx26.md` 221–232). The initial
  environment is already a list of `(name type-text)` (`standard.rs`
  `ENTRIES`), and both checkers read it: FX-26's `check-program` takes it
  as `standard`. A summary of a checked prefix could be written the same
  way.
- **Precise globals lists.** A type may say `(read (globals below limit))`
  (`docs/fx26.md` 173–219). These are names, meaningful only in one flat
  namespace. They count towards redefinition compatibility ("what it reads
  is within what the old one read", 212–215). They also drive
  `no_reaching_itself` (`top.rs` 163–190).
- **Inlined bodies and specializations.** A call of a small global is
  inlined in register code behind a guard that the global still holds the
  closure it was compiled from, "so a redefinition needs no recompiling"
  (`PLAN.md` 1866–1874). The body is a parser tree whose free names resolve
  against the globals as they were (`c-genv-now`). Its facts are looked up
  by byte offset. That is why "an inlined `extract` from an earlier form
  gets field -1" (`PLAN.md` 91): `check-more` resets `k-extracts` per
  batch (`check.fx` 6371–6379), so an earlier form's offsets are gone.
- **Field indices and datatype layouts.** These are fixed by types.
  Products are compared label for label with equal lengths (`check.rs`
  1683–1685), and a sum's tag is a symbol at run time. A type-compatible
  change therefore never moves a field.
- **Effect summaries** (0–3 per expression, `docs/fx26.md` 292–304) decide
  where versions and folding are sound. They are per-expression facts too,
  keyed like the extracts.
- **Native code** reads globals through their cells, but binds a cell that
  holds a cellular closure when compiling (`native-conventions.md`
  270–274). Images hold no machine code
  (`type-and-effect-directions.md` 296). FX-26 programs run cellular are
  not dumpable yet (297; C9).

### Separate-compilation options as FX-26 stands

1. **Concatenation.** This is what the front end does now. It is correct
   but not separate: an edit anywhere means reading, checking and lowering
   all twelve files again. The self-compile's check phase is about 0.5 s of
   0.7 s (`docs/performance.md` 1900–1910), and loading the pieces costs
   0.11 s before a program runs (128).
2. **An image of the loaded front end.** `fixpt dump-heap` already writes a
   Scheme session's heap, compiled code included (`PLAN.md` 312–335). The
   pieces are loaded lowered into a Scheme session under `fx26-reader:`.
   Dumping that session once, keyed by a hash of the twelve texts and of the
   binary, gives separate compilation's most common benefit (not
   re-checking what did not change) with no language change. The
   `standard26` reading, "read once, as it takes the reader a while"
   (`session.rs` 664–672), belongs in the same image.
3. **Snapshots at file boundaries.** The Rust checker's state after file
   *k* depends only on files 1..*k*. Keyed by the hash of that prefix, it
   can be kept: in memory for the test suite, where every test that loads
   the pieces pays today, or on disk once it can be
   serialized. An edit to `regcode.fx` then re-checks only `regcode.fx`
   and what follows it. This is prefix caching, the SML "build linearly in
   strict bottom-up order" model (Leroy 1994, p. 109). It is sound by
   construction, since it is the same program. The FX-26 checker's state
   is heap data, so its snapshot is an image.
4. **The REPL's `check-more` as a linker.** Loading a file at the REPL
   already checks it against the session's summary and compiles it against
   the kept cells. What is missing is a way to skip the check when the file
   was checked before against the same summary. That is exactly what an
   interface stamp gives (§2).

### What checking a file against a summary needs, and what breaks

| Concern                          | Today                                                                                      | What breaks across units                                                                             | Fix                                                                                                         |
| -------------------------------- | ------------------------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| global identity                  | a `Sym`; a redefinition makes a new global of the same name                                | two units' private `helper`s collide, and `(globals helper)` means whichever is newest               | a global is (unit, name); a private name never appears unqualified outside its unit                         |
| precise globals effects          | names of any global                                                                        | an export's type names a private global the importer cannot name                                     | widen private names to the unit's globals region in the interface (§2.3)                                    |
| redefinition                     | re-check users by free names (`users_of`)                                                  | users in other units are not in `defs`                                                               | the same rule at unit grain: a changed interface re-checks dependents unless every export fits (§2.4)       |
| `no_reaching_itself`             | a procedure whose effect reads its own global says `spin`                                  | reading a whole unit's region can reach itself only if a unit's globals are redefined from inside it | same rule as `@globals` today (`top.rs` 182–187), applied to the unit region                                |
| generative identity              | index in this checker's `generatives`                                                      | two runs number differently; the index means nothing in a file                                       | (unit, name), with `rep` in the interface, since safety analyses look through the name                      |
| private regions                  | fresh uninterned per program                                                               | an export's type may mention one (the reader's entry points do)                                      | stamped (unit, name) constants, fresh to everyone else, as now                                              |
| lemmas                           | a list subtyping consults                                                                  | an importer's subtyping must see the exporter's lemmas                                               | lemmas are exports; a lemma is a proof, so exporting one is coherent                                        |
| known procedures and conversions | `known`, `conversions` by binding                                                          | size-change and self-application need to know an import is a lambda, or an identity conversion       | a flag per export in the interface                                                                          |
| termination                      | size-change within a `define-rec` group; calls outside trust the callee's `spin`-free type | nothing, as long as a group never spans units                                                        | groups stay in one unit; knots across units use I-cells, as `docs/fx26.md` 443–445 already says             |
| facts                            | FX-26: byte offsets in one text                                                            | offsets repeat across files; `check-more` forgets them                                               | key by (file, offset), or carry facts in the tree; needed anyway for the field -1 bug                       |
| inlining and specialization      | parser tree + word + genv count, guarded by the closure's identity                         | the importer's guard must name the exporter's word, and the body's facts must travel with it         | interfaces carry bodies with facts and an implementation stamp; the guard fails if the stamp differs (§2.5) |
| native code's bound globals      | heap addresses when compiling                                                              | not persistable                                                                                      | keep machine code out of units; regenerate on load, as images already do                                    |
| declared-ahead types             | the whole text's `define-type`s first                                                      | a type in one file may mention a later file's                                                        | ahead only within a unit; across units, only imports (the front end's DAG already fits)                     |
| initialization order             | textual                                                                                    | units must run in an order consistent with imports                                                   | imports form a DAG, run before the importer, as in Racket and Chez                                          |

## 2. Small changes that keep FX-26's character

FX-26 is a REPL-first, Scheme-like, effect-typed language that infers where
it can. Each change below is weighed by what it costs that.

### 2.1 A unit is a file, with an optional header

**Proposed** (nothing here exists):

```
(unit parser
  (import eager-reader table)            ; units this one sees, which run before it
  (export parse-program syn top           ; values and types; everything, if omitted
          (effect parses)                 ; an effect abbreviation, transparent
          (region @p)))                   ; a private region its exports' types mention
```

- A file with no header is a unit that imports the units before it and
  exports everything, which is today's behaviour. The REPL is the
  anonymous last unit.
- Within a unit, nothing changes. Types are declared ahead, and values see
  only what is before them.
- Across units, a unit sees exactly its imports' exports. This is the
  "sees only those before" rule, one level up.
- Names are not qualified in source unless they clash: `(import (table
  as t))` gives `t:make-table`. The prefixes the front end uses by hand
  would become optional.

*Cost:* one form, one more thing the parser reserves (`unit`), and
qualified names in messages. It is not a module language. A unit is not a
value, has no functors, and is not a type.

### 2.2 Interfaces written by the checker

The `.fxi` is written by the checker, never by hand (**proposed**). It has
the same shape as `standard.rs`'s `ENTRIES`:
- `(name type)` for each export, in a canonical print, with `maxeff` atoms
  sorted so the two checkers' outputs are byte-equal;
- the unit's type, family and effect abbreviations;
- generative types, with their representation and variance;
- lemmas;
- flags for known lambdas and conversions;
- the private regions exported;
- the stamps of the interfaces it was checked against;
- optionally, unfoldings (§2.5).

The stamp is a hash of the file with the unfoldings left out. This is
GHC's fingerprint (users guide, "Recompilation checking") and Racket's
SHA-1 over the compiled form plus dependencies (`raco make` §1). It is also
Sheldon's fourth option, "compute a checksum for the input file and the
files it inputs" (thesis p. 40).

*Cost:* none to the language. Printing types is already done. Printing
effects canonically is new, since the FX-26 checker's atom order differs
from Rust's today (`docs/fx26.md` 797–799).

### 2.3 Precise globals across units

Options, in increasing cost:

| Option                                      | An export's type says                                                | Cost                                                                                        |
| ------------------------------------------- | -------------------------------------------------------------------- | ------------------------------------------------------------------------------------------- |
| a. qualify                                  | `(read (globals parser:need))` for any global, exported or not       | leaks private names; every internal change of what is read changes the interface            |
| b. widen private names to the unit's region | exported names as they are; the rest as `(read (globals-of parser))` | one new region form, `(globals-of U)` ⊆ `@globals`; precise within the unit, coarse outside |
| c. named abstract effect, bounded           | `parses`, known to importers only as `≤ (read (globals-of parser))`  | abstract effect constants in the checker; the bound is needed for licences and masking      |
| d. effect variable                          | nothing new: `(poly ((e effect)) …)`                                 | no change; only for higher-order code, as today                                             |

Recommend (b). Globals are "only read and written, and never masked"
(`docs/fx26.md` 179–180), so a unit region loses nothing that masking would
have used. `no_reaching_itself` treats it as it treats `@globals`: reading
it needs `spin` only when a global of that unit is redefined from inside
it. Redefinition compatibility stays exact within a unit. Across units it
becomes "still within the unit's region", which is what makes (b) a cutoff:
a unit whose export types did not change does not disturb its importers.

Option (c) is FX-91's `(abs id effect)` (below). Keep it for when a real
client wants to hide what it reads. An unbounded abstract effect could not
be licensed, since the licence has to see regions (`docs/fx26.md` 535–541).

### 2.4 Linking is redefinition at unit grain

At load, each import's current interface is compared with the one the
dependent was checked against. This is the rule `top_defining` already
applies to a redefinition (`top.rs` 100–133):
- if every export the dependent used has a type that is a subtype of the
  one it was checked at (`fits_old`), the dependent is linked without
  being checked again;
- otherwise it is checked again from source; if it fails, its definitions
  are broken until it is fixed.

This is CM's cutoff recompilation (Blume, CM manual p. 5, citing Adams,
Tichy and Weinert 1994). It is also Sheldon's "illusion that the file
system is immutable" (LFP '90 PDF p. 5), done by stamps rather than times.
No new rule is added to the language, only a larger grain for an old one.

*Cost:* the dependent records which exports it used. `record` already
computes free globals per definition (`top.rs` 252–265).

### 2.5 Cross-unit inlining under guards and stamps

An unfolding in the `.fxi` is the parser tree (as `syn`, which both
checkers read) together with its own facts and the exporter's
implementation stamp. The importer inlines it behind the same guard as
today. At link, the guard's expected word is bound to the exporter's word
only if the stamps match. Otherwise it is bound to a sentinel that never
matches, and the call is made normally. So a changed implementation never
forces its importers to be recompiled for correctness, only for speed:
- GHC recompiles importers when an unfolding changes, and offers
  `-fomit-interface-pragmas` to trade that away ("only when M's exports
  change their type");
- OCaml offers `-opaque`;
- FX-26's guards give both at once.

Versions of a body stay sound. They depend on effect summaries of the
body's own expressions, which travel with it, and on the callee being what
the guard checks.

*Cost:* unfoldings grow interfaces. Limit them to what `c-record-inline`
already selects (20 nodes, 60 for specialization).

### 2.6 Initialization order

A unit's top level runs once, after its imports, as Racket's "Module
requires cannot form cycles" and Chez's "once invoked, the library is not
invoked again" (CSUG §10.5). A cycle between units is an error. A knot
across units is an I-cell or a `ref`, which the types show; this is the
design `recursion-and-initialization.md` already chose for knots that are
not `define-rec` groups.

### 2.7 Carriers: images, fragments, native code

- Stages 1–2 need only what exists: Scheme heap images of lowered code.
- A unit's compiled cellular words, with an import table (unit, name,
  assumed type) and an export table, is the fragment of C10
  (`type-and-effect-directions.md` 323–333). Its loader's checks are
  already listed there: "imports by name, each host type a subtype of the
  one assumed; … the fragment's regions renamed fresh, as
  `private-regions` does". That is §2.4 for compiled code.
- Machine code is regenerated from cells on load, as images already
  assume. It can be cached later, keyed by stamps, if load time asks for
  it.

## 3. FX-91, FX-87 and later work

### FX-91: what the report actually has

*Report on the FX Programming Language* (Gifford, Jouvelot, Sheldon,
O'Toole; MIT/LCS-TR-531 per `extracted/fx91/README`), at
`~/Dev/LangPlay/GiffordHistory/papers/fx91-report.pdf`:

- **Goal.** FX-91 "provides a module system that supports programming in
  the large [SG90]" (p. 2). "The F X module system permits types and values
  to be packaged as first-class module values. Because modules are
  first-class values, F X does not require a separate configuration
  language" (p. 3).
- **Kinds** are `type | effect | (->> k …)` (§2.1, p. 6), so modules can
  abstract effects.
- **Interfaces are types.** `(moduleof (abs id k) … (desc id dx) … (val id
  tx) …)` is "the type of modules that export the abstract descriptions …,
  the transparent descriptions … and the values" (§2.2.6, p. 10), with
  width and depth subtyping.
- **Modules** are `(module (define-abstraction id k dx) …
  (define-description id dx) … (define id e) … (define-typed id tx e) …)`.
  Values "can be mutually recursive". "For each non-effect abstract
  description", `up-id` and `down-id` convert in and out (§2.3.11, p. 18).
  An effect abstraction has no conversions: it is simply opaque outside.
- **Using a module.** `(select e id)` names an exported description: "The
  effect of e must be pure to prevent type abstraction violation" (§2.2.9,
  p. 11). `(with e0 e1)` opens a pure module expression (§2.3.19, p. 23).
  `(extend e0 e1)` combines modules (§2.3.5, p. 15). Dot notation `id1.id`
  and `id1..id2` are sugar (pp. 27–28).
- **Files.** `(input literal)`: "The expression in the file named literal
  is produced as a value. No free variables are allowed in a input file,
  except if defined in the fx module" (§2.3.8, p. 17). The only unit of
  separate compilation is a closed expression, typically a module, linked
  by ordinary application.
- **The reference implementation** (`extracted/fx91/typecheck.scm` 633–695)
  spells it `load` (`token.scm` 354–360). It caches each loaded file's type
  and effect in `foo.fxt`, checked against the file's write date. It writes
  that cache only if no unification variable is left free. That is an
  interface file of exactly one type, generated by the checker.

Sheldon and Gifford, LFP '90 (`papers/lfp90.pdf`, PDF p. 5, §2.3 "Linking
and Separate Compilation"): "our system … is its own linking language. All
that remains is to provide a means for getting values out of a file system
… The file named in an input form must exist at compile time so that its
type can be known." They need identity for abstract types selected from a
file: "we must provide the illusion that the file system is immutable. Our
current implementation attaches the last update time to the input node."
Sheldon's thesis (`papers/mthesis.pdf`) lists the options for that
identity: compiled files only, user stamps, inferred max-of-stamps, or
checksums (p. 40). It adopts the first as "the simplest", and notes that
"Incremental compilation schemes for FX are the subject of current
research". It suggests interfaces kept in a separate file "packaged as a
transparent binding in another module" (p. 45). It also observes that
second-class systems that unbox by representation "necessitate recompiling
all users of a module when the module changes" (p. 9).

### FX-87

The FX-87 manual (MIT/LCS/TR-407) is not available
(`GiffordHistory/papers/README.md`). The interpreter's port is, at
`~/Dev/LangPlay/GiffordHistory/fx-lang/fx87/private/impl.rkt`:
- `load` reads a file's forms into the top level (7317–7364).
- `compile` writes a "rather crude FX 'compiler' or 'fasloader'" file of
  `(compiled-define name type value)` and `(compiled-pdefine name kind
  value)`: a type per definition and its type-erased value. Loading one
  trusts the types ("very few checks are made"), and compiling "has no
  effect on the current interpreted environment" (7376–7387, 7415–7530).
- Only `define` and `pdefine` are allowed in compiled files (7466).
- Top-level definitions are held until every free name is defined, then
  interned as one group (`try-to-intern`, 7599), which is the opposite of
  FX-26's "sees only those before".

### Adopt, adapt, skip

| FX-91 / FX-87 feature                                  | Verdict      | Why                                                                                                                                                                  |
| ------------------------------------------------------ | ------------ | -------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `input`: a closed file, its type known at compile time | adapt        | a unit is a file; but FX-26's files see their imports, not only `fx`, since the front end's files are not closed                                                     |
| `.fxt` type cache, stamped (FX-91 implementation)      | adopt        | exactly §2.2, with a content hash in place of a write date (Sheldon's own fourth option)                                                                             |
| `moduleof` interfaces as types; width subtyping        | adapt        | the `.fxi` is a list of `(name type)`; linking checks subtyping per export (§2.4); no module *type* yet                                                              |
| `(abs id effect)`: abstract effects                    | adapt, later | as bounded named effects (§2.3 c); unbounded ones would defeat licences                                                                                              |
| `define-abstraction` with `up-`/`down-`                | already      | `define-generative` (`docs/research/generative-types.md`); unit export lists supply the hiding it deferred to `private-regions`                                      |
| `select` needing a pure module expression              | keep in mind | only matters for first-class modules; second-class units are pure by construction                                                                                    |
| first-class modules, `with`, `extend`, dependent types | skip for now | the tooling needs no module values; they would make type identity a run-time matter that both checkers and heap images must agree on (`generative-types.md` 100–104) |
| FX-87 compiled files: types + erased values            | adapt        | a fragment with an import table; FX-87 trusted its types, where FX-26 should check them on link (C10)                                                                |
| FX-87's order-independent top level                    | skip         | FX-26 chose "sees only those before" on purpose (`recursion-and-initialization.md`)                                                                                  |

### Later work

| System                   | What it does                                                                                                                                                                                                                                                                | For FX-26                                                                                                   |
| ------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| SML modules (Leroy 1994) | SML "is defined as 'an interactive language', implying that users are expected to build their programs linearly in strict bottom-up order" (p. 109); manifest vs abstract types make separate compilation work                                                              | FX-26's REPL is in that tradition; transparent `define-type` across units is Leroy's "manifest" types       |
| SML/NJ CM                | "separate compilation and type-safe linking", "cutoff-recompilation" (manual p. 5); binfiles and stable libraries (§11, p. 31)                                                                                                                                              | §2.4's cutoff; a stable library is the front end's image                                                    |
| OCaml `.cmi`/`.cmx`      | `.cmx` holds "information for cross-module optimization"; `-opaque` drops it, reducing "compilation time, both on clean and incremental builds" (manual ch. "Native-code compilation", options); flambda optimizes across units "so long as the .cmx files … are available" | unfoldings in `.fxi`, optional; guards make `-opaque` unnecessary for correctness                           |
| GHC `.hi`                | interfaces with fingerprints per declaration; `-fomit-interface-pragmas`: importers "recompiled less often (only when M's exports change their type…)"                                                                                                                      | stamps; the trade GHC makes by flag, FX-26's guards make automatically                                      |
| MLton                    | "Whole-program compilation is an integral part of the design of MLton and is not likely to change"; it "often reduces or eliminates the run-time penalty that arises with separate compilation"                                                                             | the bootstrap and `fixpt build` may stay whole-program; separate compilation is for check time and the REPL |
| Chez Scheme libraries    | `enable-cross-library-optimization` includes information "to enable propagation of constants and inlining of procedures defined in the library into dependent libraries" (CSUG 9.5 §12.6); `compile-whole-program`                                                          | the same split: per-unit objects for development, whole program for shipping                                |
| Racket                   | modules instantiated after their requires, no cycles (Reference §1.1.9); recompiled when a dependency's SHA-1 "for its compiled form plus dependencies" changes (`raco make` §1)                                                                                            | initialization order and stamps                                                                             |
| Koka                     | effect types inferred and part of every signature; `alias` declarations name types and effects; `pub` marks exports (spec)                                                                                                                                                  | effect abbreviations as exports (`(effect parses)`), private by default is worth considering                |

Eff was not checked. Koka's handling of effect rows in its compiled
interfaces was not found in its public docs, so nothing here claims how it
works.

## 4. Recommendation

### Stages

| Stage | What                                                                                                           | Language change      | Gives                                                                          |
| ----- | -------------------------------------------------------------------------------------------------------------- | -------------------- | ------------------------------------------------------------------------------ |
| S0    | image of the loaded front end (and `standard26`), keyed by a hash of the twelve texts and the binary           | none                 | each session and test skips the front end's load; the most for the least       |
| S1    | checker snapshots at file boundaries, keyed by prefix hash; in memory first (tests), images for the FX-26 side | none                 | editing `regcode.fx` re-checks two files, not twelve                           |
| S2    | facts keyed by (file, offset) in both checkers and both compilers                                              | none                 | fixes "inlined `extract` gets field -1"; a precondition for everything after   |
| S3    | global and generative identity as (unit, name); `unit` header; `.fxi` written by both checkers, byte-equal     | the header, optional | files checked against summaries; the front end's hand prefixes become optional |
| S4    | link by `fits_old` per export (cutoff); `(globals-of U)` for private globals in interfaces                     | one region form      | an implementation change re-checks nothing downstream                          |
| S5    | unfoldings in `.fxi`, guards bound by implementation stamp                                                     | none                 | cross-unit inlining without recompilation for correctness                      |
| S6    | fragments: a unit's cellular words with import/export tables, checked on link (C9, C10)                        | none                 | compiled units on disk; machine code regenerated on load                       |
| later | bounded abstract effects; first-class modules if a client needs them                                           | yes                  | hiding what a unit reads; FX-91's module values                                |

S0 and S1 should come first. Stage S0's benefit can be measured before any
design is settled: time a session's startup and the suite before and
after. S2 is a bug fix in its own right.

### What each side needs (S2–S5)

- **Rust checker** (`check.rs`, `top.rs`): `Region::Global` keyed by
  (unit, name); generatives by (unit, name); `declare_ahead` per unit; an
  interface printer (types exist; effects sorted canonically) and reader
  (the `ENTRIES` path); `defs` recording which imports each definition
  used; the link check as `fits_old` over imports.
- **FX-26 checker** (`check.fx`): the same, rule for rule. `k-facts` gains
  a file. `check-more` stops forgetting earlier forms' facts, or facts move
  into the trees. Its interface print must equal Rust's byte for byte, a
  new agreement test beside `effect_summaries_agree`.
- **Rust compiler** (`cellular.rs`) and **FX-26 compiler** (`compile.fx`,
  `regcode.fx`): `c-genv-index` keyed by (unit, name); `c-inlines` entries
  gaining a unit, a stamp, and their facts; a guard's expected word taken
  from a link table rather than a heap pointer in the compiling session.
- **Lowering** (`lower.rs`): per-unit global prefixes, as
  `compile_program_as`'s `prefix` already does for one program.
- **Session/CLI**: `fixpt check|compile` writing `.fxi` beside an input;
  a REPL `,load` that links a unit by stamp; a REPL `,enter U` for
  redefining inside a unit.

### Open questions for the user

1. **Scope first.** Is the target the front end's own edit–check loop
   (S0–S1 suffice), the test suite's time (S0), user programs split into
   files (S3 on), or the two front ends sharing units (`fx-rsmirror`,
   `fx-idiomatic`)? The last would argue for doing S3 before the split.
2. **Exports by default.** Should a unit with no `export` export everything
   (REPL-friendly, today's behaviour), or nothing but what it lists
   (Koka's `pub`, better hiding)?
3. **Precise globals across units.** Is (b), widening private names to
   `(globals-of U)`, acceptable? Or should interfaces qualify every name,
   (a), at the cost of interface churn? (c) is deferred unless you want
   hiding of effects now.
4. **Redefinition across units at the REPL.** May a form at the REPL
   redefine an imported global (the rule would re-check dependents in every
   unit), or only after `,enter` into the defining unit, as Racket
   restricts `set!` of another module's variables?
5. **Stamps.** Content hash (Sheldon's fourth option, GHC, Racket) or
   compiled-files-only (Sheldon's first, the FX-91 implementation's
   write date)? This note assumes a content hash.
6. **Unfoldings by default.** Should interfaces carry them always (GHC
   `-O`), or only with a flag? Guards make both correct; the difference is
   interface size and load time.
7. **Whole-program for shipping.** Should `fixpt build` and the bootstrap
   stay whole-program, as MLton and Chez's `compile-whole-program` do, with
   units only for development?
8. **FX-91 modules.** Is there any client in view for first-class module
   values or `(abs id effect)`, or do they stay out until one appears (as
   `docs/fx26.md` 815–819 says: "Modules … wait until the checker written
   in FX-26 spans more than one file")? This note would read that
   condition as met by S3's units, not by module values.

## Sources

On disk (read-only):
- `~/Dev/LangPlay/GiffordHistory/papers/fx91-report.pdf`. Gifford, Jouvelot,
  Sheldon, O'Toole, *Report on the FX Programming Language* (FX-91), the
  DVI of 1993-05-26 rendered by `dvipdf` (per `papers/README.md`). Pages 2,
  3, 6, 7, 10, 11, 15, 17, 18, 23, 27, 28.
- `~/Dev/LangPlay/GiffordHistory/papers/lfp90.pdf`. Sheldon and Gifford,
  *Static Dependent Types for First Class Modules*, LFP '90. PDF p. 5, §2.3.
- `~/Dev/LangPlay/GiffordHistory/papers/mthesis.pdf`. Sheldon, *Static
  Dependent Types for First-Class Modules*, S.M. thesis, MIT. Pp. 9, 31, 40,
  45.
- `~/Dev/LangPlay/GiffordHistory/papers/README.md`. The FX-87 manual
  (TR-407) is not available.
- `~/Dev/LangPlay/GiffordHistory/extracted/fx91/typecheck.scm` 633–695,
  `token.scm` 354–360, `README`. The FX-91 reference implementation's
  `load` and `.fxt` cache.
- `~/Dev/LangPlay/GiffordHistory/fx-lang/fx87/private/impl.rkt` 7317–7530,
  7599. The FX-87 interpreter (BETA-0), ported: `load`, `compile`,
  compiled files, `try-to-intern`.

Online (read 2026-09-29):
- Xavier Leroy, *Manifest types, modules, and separate compilation*, POPL
  1994, pp. 109–122: <https://xavierleroy.org/publi/manifest-types-popl.pdf>
  (p. 109 quoted).
- Matthias Blume, *CM: The SML/NJ Compilation and Library Manager (for
  SML/NJ version 110.40 and later), User Manual*, May 21, 2002:
  <https://www.smlnj.org/doc/CM/new.pdf> (p. 5 §1; p. 31 §11).
- OCaml manual 5.2, native-code compilation, option `-opaque`:
  <https://ocaml.org/manual/5.2/comp.html>. Flambda, §1:
  <https://ocaml.org/manual/5.2/flambda.html>.
- GHC User's Guide, separate compilation (interface files, recompilation
  checking): <https://ghc.gitlab.haskell.org/ghc/doc/users_guide/separate_compilation.html>.
  Optimisation flags (`-fomit-interface-pragmas`,
  `-fexpose-all-unfoldings`):
  <https://ghc.gitlab.haskell.org/ghc/doc/users_guide/using-optimisation.html>.
  Current version as served on 2026-09-29.
- MLton guide, `WholeProgramOptimization.adoc` and `Features.adoc`, at
  MLton commit `aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37`:
  <https://raw.githubusercontent.com/MLton/mlton/master/doc/guide/src/WholeProgramOptimization.adoc>,
  <https://raw.githubusercontent.com/MLton/mlton/master/doc/guide/src/Features.adoc>.
- Chez Scheme User's Guide 9.5: libraries §10.2, §10.5, §10.6,
  <https://cisco.github.io/ChezScheme/csug9.5/libraries.html>. Compiler
  controls §12.4, §12.6,
  <https://cisco.github.io/ChezScheme/csug9.5/system.html>.
- Racket Reference §1.1.9, modules and module-level variables:
  <https://docs.racket-lang.org/reference/eval-model.html>. `raco make`
  §1: <https://docs.racket-lang.org/raco/make.html>. Current versions as
  served on 2026-09-29.
- Koka language specification (`alias`, `pub`, `import`), at Koka commit
  `facb7932ce6871fdb063f762a304bd8238f35fba`:
  <https://raw.githubusercontent.com/koka-lang/koka/master/doc/spec/spec.kk.md>.
  The Koka book: <https://koka-lang.github.io/koka/doc/book.html>.
