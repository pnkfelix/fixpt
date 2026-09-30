# Modules for FX-26: Sheldon's first-class modules against Racket's macros

Research note, 2026-09-30. Answers the question the user asked: land a
second-class `unit` system now (`docs/research/separate-compilation.md`,
queue item Q9), meaning to add first-class modules later, or build
Sheldon and Gifford's first-class, statically dependent modules now? And
do Sheldon's design and Racket-style macros — a module declaring its own
language, macros exported from modules — fit together, conflict, or fit
only with care?

Primary sources read directly for this note: Sheldon and Gifford, *Static
Dependent Types for First Class Modules*, LFP 1990 (read in full,
`~/Dev/LangPlay/GiffordHistory/papers/lfp90.pdf`); Sheldon, *Static
Dependent Types for First-Class Modules*, MIT S.M. thesis, 1990 (read in
full, `~/Dev/LangPlay/GiffordHistory/papers/mthesis.pdf`); the FX-91
report (introduction and module grammar read directly,
`~/Dev/LangPlay/GiffordHistory/papers/fx91-report.pdf`); and every FX-26
design note this repository already has on separate compilation,
generative types, shapes and macros. Three parallel agents read the wider
literature — Racket's macro and unit system, the ML module tradition
through 1ML, and Swift/Rust/Scala/Backpack — each against primary sources,
cited individually below and collected in the sources table (§8).

## 1. The answer

**Land second-class units now, exactly as `separate-compilation.md`
already proposes, and treat first-class modules as a later layer units
can produce as ordinary values but never be promoted into.** This was
already the recommendation of that note, made without considering
macros; this note tests it against the macro question and finds it holds,
for an independent reason.

**Racket-style macros and Sheldon-style first-class modules do not
conflict, but they cannot be the same construct. They must be layered —
and the layering is not a compromise invented for FX-26, it is the
layering both source systems already use internally.**

The reasoning, each step sourced:

1. **A macro transformer is a compile-time procedure that must be fully
   resolved, and fully erased, before any run-time value exists.** Racket
   enforces this with a phase system: `require-for-syntax` imports
   compile-time (phase 1) bindings, `require` imports run-time (phase 0)
   ones, and the two are never allowed to mix — "the module system
   enforces a separation between different phases, i.e., compile-time
   variables are never resolved to run-time values that happen to be
   loaded" (Flatt, *Composable and Compilable Macros: You Want It When?*,
   ICFP 2002, §2). Hygienic binding resolution is a pure operation on
   syntax objects and a compile-time binding table (Flatt, *Binding as
   Sets of Scopes*, POPL 2016) with no run-time component at all, and the
   compiler is required to be able to "strip all compile-time code from
   the final deliverable" (ICFP 2002, §4.2) — sound only because no
   run-time behaviour ever depended on which macros ran. A first-class
   run-time module value cannot carry a macro in this sense, because a
   macro has no run-time representation once expansion finishes.
2. **Sheldon's modules are exactly a run-time value in the sense phase
   separation forbids for macros.** `(mod ((t type int)) ((x t (up-t
   0))))` is an ordinary expression, evaluated at run time, storable,
   passable, returnable; its only restriction is on module expressions
   that appear *inside a type* (§2 below). A module value under Sheldon's
   rules can be built by arbitrary, even effectful, computation — his own
   running example is a pair implementation chosen by
   `(read-string-from-keyboard)` (LFP90 §2.2) — which a macro transformer
   can never be, on pain of making expansion depend on execution.
3. **But Sheldon's module *types* (`modof`) are static in exactly the
   sense phase separation asks for.** A `select` inside a type must have
   an effect free of reads (Design Constraint 1, enforced by the effect
   system), and two selects are equal only when *textually* identical —
   no evaluation, ever, in the type checker (LFP90 §2.1.3, §4.4). This is
   already a "compile-time-only" artifact in Sheldon's own design, just
   not called a phase.
4. **Racket's own architecture already splits exactly this way, and the
   static half already carries macros.** Racket's `module` (plus `#lang`,
   phases, `require-for-syntax`) is the static, acyclic, textual layer —
   the one that owns macro expansion. Racket's `unit` — a *different*
   construct, confusingly close in name to what FX-26's own design notes
   call a "unit" (see the terminology table in §4) — is first-class,
   signature-typed, and linked at run time, "analogous to function
   application" (Owens and Flatt, *From Structures and Functors to
   Modules and Units*, ICFP 2006, §2.3). Units are the dynamic layer;
   modules are the static one. And a Racket *signature* — the static type
   a unit is checked against — can itself carry macros: "Each
   `define-syntaxes` form in a signature declaration introduces a macro
   that is available for use in any unit that imports the signature"
   (Racket Reference §7.1, `define-signature`, read directly). This is
   the confirmation of the working hypothesis under test: **macros attach
   to interfaces, not to module values**, and Racket already does this,
   not speculatively but as a documented, if lightly-used, feature.
5. **Sheldon himself saw this question and set it aside on purpose.**
   Chapter 1 of the thesis, footnote 1, defining "module": "This is not
   the most general definition. There is no reason why modules may not
   also contain macros, for example. However, a more general definition
   would only add confusion arising from issues not relevant to the
   current project" (thesis p. 8). So the incompatibility the user
   suspects is not a subtle problem this note discovered — it is a
   problem the paper's own author flagged in 1990 and explicitly deferred.
   Nothing in the thirty-five years since answers it directly; Racket's
   signature macros are the closest thing to an answer, and they answer a
   narrower question (macros in a *second-class*, unit-style interface,
   not macros riding along with a genuinely first-class module value).
6. **One honest caution, found directly in the sources, not inferred:**
   even Racket's own flagship statically-typed dialect does not support
   this combination today. Typed Racket's `define-signature` "does not
   support uses of `define-syntaxes`" (Typed Racket Reference §5, *Typed
   Units*). So "a nontrivial static type-and-effect checker, plus macros
   in interfaces" is not a solved problem to copy — it is open
   engineering that Racket itself has not done for its own typed
   language. FX-26, with a dependent effect checker considerably more
   demanding than Typed Racket's, should expect the same.

So: **not incompatible, but not the same thing either, and combinable
only by keeping macros on a static interface layer that a checker with
real static obligations (Sheldon's effect-purity restriction on selects;
FX-26's own effect and region discipline) can still make sense of** — which
is new work for FX-26, not a transplant.

## 2. Sheldon's design: what the LFP90 paper and thesis actually say

Testing the main session's working hypothesis against the primary
sources directly (not the secondary notes already in this repository),
point by point.

| Claim under test                                                                                                                                          | Verdict   | Source                                                                                                                                                                     |
| --------------------------------------------------------------------------------------------------------------------------------------------------------- | --------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Modules are values: `(mod ((t type int)) ((x t 3)))`, typed by `(modof …)`, used by `with` and `select`                                                   | confirmed | LFP90 §2.1.1–§2.1.4; the literal example is `(mod ((t type int)) ((x t (up-t 0))))`, typed `(modof ((t type)) ((x t)))`                                                    |
| Dot sugar: `M.x` is `(with M x)`; in a type, `M.t` is `(select M t)`                                                                                      | confirmed | LFP90 §2.1.3, p. 194: "We also overload the conventional dot notation. In a description, it is sugar for select. In a value expression, it is sugar for a with expression" |
| A type may contain a value expression: `(f 2).t`                                                                                                          | confirmed | LFP90 §1.2: "if the expression (f 2) has a module type … then (f 2).y has type (f 2).t"                                                                                    |
| Dependent subroutines: a later parameter's type, or the result type, depends on an earlier parameter's *value*; ML functors are a restricted form of them | confirmed | LFP90 §2.2, verbatim: "Dependent subroutines are the basis of module linking … Functors in ML are a restricted form of dependent subroutines."                             |
| Two `select`s are equal only if textually identical                                                                                                       | confirmed | LFP90 §2.1.3, p. 203: "Two select forms are equivalent iff they are textually identical." No evaluation in the checker, by design (§4.4).                                  |
| A module expression inside a type must not read the store; the effect system enforces this                                                                | confirmed | LFP90 §2.1.2, Design Constraint 1, enforced by the `select` kind rule requiring the module expression's effect not contain `read`                                          |
| `let` bindings are opaque: a `let`-bound module value's selects are not interchangeable with its defining expression's                                    | confirmed | LFP90 §2.1.4, §2.2, spelled out at length with the keyboard-input example; formalized in the `let` typing rule (§4.3)                                                      |
| Files enter by `(input "file")`; the file must exist at compile time; the file system is treated as immutable                                             | confirmed | LFP90 §2.3: "The file named in an input form must exist at compile time so that its type can be known … we must provide the illusion that the file system is immutable."   |
| A real implementation would wrap each file in `(with library …)`                                                                                          | confirmed | LFP90 §2.3: "A real implementation would have a standard library in scope for such files by implicitly enclosing the code in all files in a `(with library ...)`."         |

Three further points, found in the thesis, that refine the picture beyond
what was already summarized in `separate-compilation.md`:

- **All recursion — type and value — goes through module abstraction.**
  The thesis's kernel language (Appendix A) differs from FX-87 by
  dropping FX-87's transparent recursive types outright: "Recursion in
  both the description and value domains is accomplished using the
  module proposal in the thesis. This implies the demise of transparent
  recursive descriptions" (thesis p. 51). This is the same move FX-26
  makes with generative types — "recursion through the name is never
  expanded" (`docs/fx26.md`, "Generative types") — except Sheldon's
  system has *no other* route to recursion at all, where FX-26 keeps
  equi-recursive `dletrec`/`mu` for ordinary structural types and adds
  generative types as a second, iso-recursive route. Sheldon's choice was
  forced by wanting `select` equality to be decidable by inspection: a
  transparent recursive type would need to be compared by unrolling,
  which the whole textual-equality scheme is built to avoid.
- **Stamping files is explicitly known to be insufficient by itself**, and
  the thesis says why, in a passage not previously quoted in this
  repository's notes: "a file may hide the fact that it imports from
  another file. It merely places the input inside an abstraction" (thesis
  §3.4, p. 39). A file's last-write-time stamp changes when *that* file
  changes, but if it imports another file through a module abstraction,
  changing the inner file does not touch the outer file's own timestamp.
  Sheldon lists four fixes — compiled files only, a user-supplied stamp, a
  stamp inferred as the max over everything a file inputs (explicitly
  credited to ML's structure-sharing tags, "inspired by the implementation
  of the sharing mechanism in ML [MacQueen 88]"), or a checksum — and
  implements the first because it is simplest, leaving the others as
  future work. **FX-26's own proposed answer already avoids the hiding
  problem**, and does so by combining Sheldon's own two other options: a
  unit's `.fxi` stamp is a content hash, not a timestamp (Sheldon's fourth
  option, matching GHC's and Racket's practice), *and* every `.fxi`
  separately records `(checked-against …)`, the stamps of the interfaces
  it was itself checked against (`separate-compilation.md` §2.2, Example
  5) — which is Sheldon's third option (infer a stamp as the max over
  everything a file inputs, "inspired by the implementation of the
  sharing mechanism in ML") made exact rather than inferred: a consumer
  does not need to guess whether something a unit imports, however deep,
  has changed since the unit hid that dependency inside its own
  abstractions; the recorded chain of `checked-against` stamps says so
  directly, one hop at a time, with no timestamp and no hiding.
- **Sheldon's system has no manifest/transparent type exports** — every
  abstraction is opaque even to itself across module boundaries, which
  the thesis calls out as awkward on its own account. Its worked ML
  comparison (thesis §4.1.5, "Sharing") shows a `LEX` module and a
  `SYMBOLTABLE` module that both need to agree on one `Symbol` type: ML
  has a `sharing` declaration for this; Sheldon's system does not, and
  the workaround is "awkward and entails extra subroutine calls which may
  be difficult for the compiler to open code" — parametrize both modules
  over the shared submodule explicitly and thread it through by hand,
  which is exactly FX-26's own "dictionary passing over specialization"
  discipline, arrived at for an unrelated reason. Transparent
  (non-abstract) description bindings are named as the single largest
  item of future work: "The next version of FX will have a module system
  allowing the export of abstraction, value, and transparent description
  bindings" (thesis §4.1.2, p. 44) — and FX-91 built exactly that:
  `(moduleof (abs id k) … (desc id dx) … (val id tx) …)`, with
  `define-description` inside a `module` (FX-91 report §2.2.6 p. 10, read
  directly, grammar lines confirmed at `fx91-report.pdf`). **So "Sheldon's
  design" properly means two different systems**: the LFP90/thesis SDT
  system (fully opaque, no sharing) and FX-91's superset of it (adds
  transparent descriptions, i.e. manifest types). Anything FX-26 borrows
  should be named against FX-91, which is the version with a sharing
  story, not the 1990 paper alone.
- **An `up`/`down` conversion is free only when the compiler can see it is
  one.** The thesis's run-time section says the identity-function
  conversions are elided "when programs are alpha-renamed" and the
  compiler can detect that a call refers to the coercion supplied by a
  particular `mod` (thesis §3.5, p. 41). When it cannot — the module came
  in as an opaque parameter, say — "the identity function really needs to
  exist," i.e. it is a real call. FX-26's `define-generative` already
  gets this for free at the point of definition (its conversions are
  literally compiled as identity lambdas, inlinable like any other known
  procedure, `docs/research/generative-types.md`), but the same caveat
  will apply the moment a generative type's conversions travel through an
  *unknown* first-class module value rather than a name the checker knows
  statically — worth remembering if first-class modules are ever built
  (§4.5, below).

**On the "functor-shaped" intuition:** confirmed, and independently
reconfirmed by unrelated later work. Sheldon's own dependent-subroutine
pattern — `(lambda ((m SIG) (p (m.field …))) …)` — is a functor,
parametrizing code over an unknown module of a known signature, with the
later parameter's *type* depending on the earlier parameter's *value*.
What makes it a restricted functor rather than an unrestricted one is
exactly the effect-purity-on-selects restriction (Design Constraint 1).
The striking finding from the ML-module-theory research (Agent B, full
report in §8) is that the *identical* restriction — "a module expression
may take part in type identity only if it is effect-pure" — was
independently rediscovered three separate times, decades later, by a
completely different research lineage chasing a completely different
goal (decidable applicative functors, not first-class modules): Leroy's
applicative functors (POPL 1995, where a functor application is only
sound to reuse as a path when the functor body is pure, and Leroy states
outright that the applicative scheme, as he builds it, "precludes modules
as first-class values," p. 12); F-ing Modules (Rossberg, Russo and
Dreyer, JFP 2014, "applicative iff pure"); and 1ML (Rossberg, JFP 2018,
which gates type identity on its `⇒`/`→` purity distinction throughout,
and whose effect-polymorphic extension, "1ML with Special Effects," gives
the same rule *effect-polymorphically* — a module expression's type
identity behaves differently depending on what effect variable it is
instantiated at, which is close in spirit to FX-26's own effect
polymorphism already used to hide a module's private region,
`separate-compilation.md` Example 7). That three independent efforts,
separated by decades and pursuing different goals, converged on
"purity gates identity" is strong evidence the rule is not an
idiosyncrasy of Sheldon's particular design — it is close to the only
sound way to let a syntactic, non-inferential notion of module-type
identity survive in the presence of effects, in *any* module system.
1ML in particular is the closest living relative: its modules are
dependent records with type-valued fields — essentially Sheldon's `mod`
restated — but its type-identity rule is *structural* rather than
*textual* (matching `pair int int` to `{fst: int; snd: int}`, say), kept
decidable by a small/large split on which types may be substituted away,
rather than by forbidding evaluation outright. That buys real type
sharing (the LEX/SYMBOLTABLE diamond Sheldon's own thesis admits it
cannot express cleanly) at the cost of a genuine matching algorithm in
place of a string comparison. Neither 1ML paper discusses macros or a
syntax-extension phase at all (confirmed by direct reading of both, §8) —
the silence is itself informative: the module-theory tradition that
solved "first-class and decidable" never had to reconcile it with a
macro phase, because none of these languages have Racket-style macros.

## 3. What the user's other half-remembered claim turns out to be

The working hypothesis recalled, unverified, that "Racket's unit system
allows macros in unit signatures (Owens and Flatt, ICFP 2006)." Checked
directly: **the ICFP 2006 paper itself does not say this** — it was read
in full (6 pages, §§1–4.3) and only gestures at a future "signature
facility for abstracting common import/export patterns" without
detailing it. The feature exists, but it was built into `racket/unit`
afterward and is documented only in the current Racket Reference, not
the 2006 paper: `define-signature` accepts `define-syntaxes` forms (§7.1,
quoted in §1 above), and there is a second, independent point of
attachment above that — `define-signature-form` lets a macro operate on
the *syntax of a signature declaration itself*, to build reusable DSLs
for writing signatures (§7.7). So the recollection was correct in
substance, wrong about where to find it: it is a Reference-level feature
of the implementation, not a claim in the paper that introduced units.
It is also, per the Guide's own tutorial (which shows no macro examples
at all), a lightly-exercised corner of the design — real and documented,
not a headline feature.

A second correction, found while chasing this down and worth recording
because it bears directly on how FX-26's own "unit" should be named and
scoped (§4): **Racket units are not acyclic.** The working hypothesis, and
`separate-compilation.md`'s own citation of Racket for "no cycles," is
about Racket *modules* — "Module requires cannot form cycles" (Racket
Reference §1.1.9) is a true statement about `module`, confirmed correct.
But Racket's `unit` construct is a *different* thing, deliberately built
to support what modules cannot: "unit linking is analogous to function
application" and units support genuinely cyclic linking — a
self-referential factorial unit, recursive datatypes split across units,
and a worked "Cyclic Linking Dependencies" example including Russo's
`NatFun`/`BoolFun` mutual recursion and a bootstrapped heap (Owens and
Flatt, §4.3, read in full). The mechanism is exactly the one FX-26
already has for a knot across files: "unit compounding does not create
directly accessible bindings" — imports are satisfied by backpatching
suspended, uninitialized slots, not by eager evaluation, so a cycle is
fine as long as nothing is *read* before it is filled; a premature read
is a run-time error, not a static one. **This is, mechanism for
mechanism, FX-26's I-cell**: "A read waits for the write … A program runs
sequentially, so a read of an empty cell could only wait forever. It is
an error instead" (`docs/fx26.md`, "I-cells: recursion's knot, made
explicit"), used today exactly for a knot across files
(`hook-icell.fx`, `separate-compilation.md` Example 10). The identical
mechanism appears a third time, independently, in MixML (Dreyer and
Rossberg, ICFP 2008): recursive linking of separately-elaborated modules
through "lazy reference cells: exports start as uninitialized cells, and
a deref before patching is a run-time error" (MixML, p. 11, read
directly). Three systems — Racket units, MixML, and FX-26's own I-cells —
independently landed on the same answer to "how do you let two
separately-compiled things call each other": a write-once cell,
backpatched, checked dynamically rather than statically. This is
worth taking as confirmation that FX-26's existing choice was the right
one, not a stopgap.

## 4. A layered design for FX-26

### 4.1 Vocabulary across three systems

The terminology collides in an unhelpful way and is worth pinning down
before anything else, because "unit" means different things in the three
systems this note compares:

| Layer                                                             | Racket                                                                             | Sheldon / FX-91                     | FX-26 (this note's recommendation)                               |
| ----------------------------------------------------------------- | ---------------------------------------------------------------------------------- | ----------------------------------- | ---------------------------------------------------------------- |
| static, textual, acyclic, resolved before anything runs           | `module` (+ `#lang`, phases, `require-for-syntax`)                                 | `(input "file")`                    | `(unit …)` (`separate-compilation.md` §2.1, unchanged name)      |
| where macros / a surface language live                            | `module`'s reader + expander; signatures (`define-syntaxes` in `define-signature`) | none (FX had no macros)             | the unit header, read before the unit's body is checked (§4.2)   |
| first-class, run-time value, signature-typed, may link cyclically | `unit` (confusingly named the same as FX-26's static layer above)                  | `mod` / `modof` / `select` / `with` | a later, optional module-value layer (§4.5), never called "unit" |

FX-26's existing proposal already calls its static layer `unit`, which
this note keeps — it predates this research and changing it would touch
`separate-compilation.md`, `TODO.md` §22 and `PLAN.md`'s Q9 for no
benefit. But it means FX-26's "unit" corresponds to Racket's *module*,
not Racket's *unit*; if FX-26 ever builds the first-class layer of §4.5,
it needs a different name (this note uses "module value" throughout,
provisionally).

### 4.2 What a unit is, and what its interface records

Unchanged from `separate-compilation.md` §2.1–§2.2, which this note
endorses without modification for the parts it already covers: a unit is
a file, with an optional `(unit NAME (import …) (export …))` header; a
`.fxi` interface, written by the checker (never by hand), holding
`(name type)` per export, type/effect/family abbreviations, generative
types with their representations and variance, lemmas, known-lambda and
conversion flags, exported private regions, a content-hash stamp of
everything the unit was checked against, and optionally inlinable
unfoldings.

**New, from this note's macro research:** a unit's header gains, before
its `import`/`export` lines, an optional **language line** and a set of
**macro exports**:

```
(unit parser
  (language fx26)                        ; the default; omit it for fx26
  (import eager-reader table)
  (export parse-program syn top
          (macro with-checkpoint)         ; a syntax-rules-shaped export
          (effect parses)
          (region @p)))
```

The language line is the FX-26 analogue of `#lang`: which reader profile
and which base set of forms this unit's text is read with. It is read by
the *reader*, before the unit's body is parsed at all — exactly where
Racket's own language choice is resolved ("a module declaring `#lang lam`
may only write `lm` functions; using any other form results in an
error," Chang, Knauth and Greenman, POPL 2017, describing their own
toy `#lang`). FX-26 already has reader profiles (`SyntaxProfile::FX26`,
`docs/fx26.md`, "Surface"), chosen per *session* today; a unit's
`(language …)` line would let it be chosen per *unit* instead, the one
piece of genuine new reader work this design needs (§7, open question).

Macro exports are a `.fxi` concern, not a unit-header concern, once the
unit is checked — they are listed in the header only as a declaration of
intent (what is expected to be there), the way `export` already lists
value and type names before the checker confirms them.

### 4.3 Where macros live, and how they are checked

FX-26 today already has a narrow, unadvertised version of exactly this
split. `define-type`, `define-effect` and `define-generative` are
**checker-only forms**, expanded at read time into ordinary definitions
before the effect checker ever runs on them (`docs/fx26.md`,
"Generative types": "Expanded as it is read into the checker-only form
and two ordinary definitions, so nothing downstream changes"), and a
whole program is read in **two passes**: "`define-type`, `define-effect`
and every signature come first, then the definitions in order"
(`docs/fx26.md`, describing the eager reader's own port, step 6). That
two-pass structure — type-level names available everywhere before any
value is checked — is already a phase separation, just not named as one
and not open to user-written extension.

The design this note proposes makes that separation a genuine, three-pass
structure per unit, and opens the middle pass to macros:

1. **Read pass.** The unit's `(language …)` line picks the reader
   profile and the base macro environment (its imports' macro exports).
   The unit's own text is read, expanding macros as it goes — exactly
   today's Scheme-level expander (`docs/macros.md`), run before the FX-26
   checker sees anything. Output is plain FX-26 syntax: macros leave no
   trace downstream, the same property `docs/macros.md` already commits
   to for the Scheme level ("Output stays plain Scheme … That keeps the
   property the metadata work relied on: every stage is a legal Scheme
   expression").
2. **Declare-ahead pass.** Types, effects and generative-type headers,
   exactly as today, now including imports' exported types.
3. **Value-check pass.** Definitions checked in order against imports'
   exported values, exactly as today.

Nothing about the effect checker changes. What changes is *where the
expander gets its bindings from* when it is expanding a unit's own body:
today, in one flat program, it is one global scope; across units, it
must resolve a macro's free identifiers (both the macro's own name, and
anything its templates insert) against **the macro's home unit's
environment**, which may be a different, separately-checked unit than
the one doing the expanding. This is new engineering, detailed in §5.

### 4.4 Importing, and its effect

A unit import is an edge in the unit DAG, checked once at read time
(which units exist, in what order) and not an effect in FX-26's own
sense: unlike naming a global, which is `(read (globals g))`, naming an
imported unit's export is exactly as free as naming a same-unit global
is today — the cost already lives in the exported value's own type and
effect. No cycles: this matches Sheldon's `input` (files have no free
variables beyond a fixed standard library, so no file can see a file
that has not been fully elaborated), FX-26's own prior choice
(`separate-compilation.md` §2.6, "A cycle between units is an error"),
Chez Scheme's libraries ("once invoked, the library is not invoked
again," CSUG §10.5), SML's build order (Leroy 1994, "build linearly in
strict bottom-up order"), and Racket's *modules* specifically (not
units). Five independent systems agree on "the static layer is acyclic";
a knot that must cross unit boundaries anyway is an I-cell, as it already
is today (§3, above) — and as Racket units, MixML and (within one
recursive binder) the Harper/Crary/Dreyer and Russo tradition all
independently confirm is the right *dynamic*-layer answer when true
recursion between separately-elaborated things is wanted.

### 4.5 Exports immutable

Already the shape of today's design: a unit's exports are not globals an
importer can redefine (`separate-compilation.md`'s redefinition-at-unit-
grain design, S4, reuses the existing `fits_old` subtype check rather
than making imported names writable at all). This is what `TODO.md` §22
was written to depend on — "exports that cannot be reassigned (so that
using `map` is a constant, adding no `(read (globals map))` to a caller's
effect, as a global would)." Nothing in the macro extension changes
this: a macro export is, if anything, *more* immutable than a value
export, since Scheme-level macros are resolved entirely before the
effect checker runs and have no run-time representation to redefine.

### 4.6 Where first-class module values would fit later

Not now — this note agrees with `separate-compilation.md`'s existing
"skip first-class modules for now" (its adopt/adapt/skip table) and adds
one more reason on top of the ones already given there: a first-class
module-value layer is exactly where Sheldon's `mod`/`modof`/`select`/
`with` and dependent subroutines would live, entirely *inside* a unit's
value language, available to ordinary FX-26 code the way products and
polymorphic procedures already are — because `separate-compilation.md`'s
own Examples 1 and 3 show FX-26 can already write something
module-shaped (a product of procedures as a structure, a `poly`
procedure between two products as a functor) without any new forms at
all. What would be new, if ever built:

- **A `modof` type former**, closer to a dependent product type than
  anything FX-26 has (a labelled product whose later fields' types may
  mention earlier fields' *values*, not just their types) — genuinely new
  in both checkers, since today's `(productof (l T) …)` has no such
  dependency.
- **A `select` expression form** carrying Sheldon's effect-purity
  restriction when it appears inside a type: exactly FX-26's own
  precise-globals-effects discipline, generalized from "naming a global
  is `(read (globals g))`" to "a module expression inside a type must
  have no `read` in its masked effect" — the same shape of rule FX-26
  already enforces for other reasons (`docs/fx26.md`, "Globals as a
  region"), so the effect system does not need new atoms, only a new
  place the existing purity check is asked.
- **Textual (not structural) equality of selects**, as a new comparison
  rule beside the existing structural/equi-recursive one, restricted to
  types built from `select`. 1ML's structural alternative (§2) is more
  expressive but needs a real matching algorithm; recommend starting with
  Sheldon's textual rule, which is a string comparison, and only moving
  toward 1ML's if the diamond-sharing case (§2, the LEX/SYMBOLTABLE
  example) is actually hit in practice.
- **Opaque `let`**, i.e. a `let`-bound value of module type must not have
  its selects treated as interchangeable with the binding expression's —
  the one place FX-26's existing "redefinition sees only the newest
  value" discipline would need a carve-out, since a `let` is not a
  `define`.
- **A run-time representation.** The natural one, given FX-26's own
  design, is a frozen product (a module value *is* a dependent product,
  erased); `up-`/`down-` erase to identity exactly as `define-generative`
  conversions already do (`docs/research/generative-types.md`), with the
  caveat from §2 above: the identity erasure is only free when the
  checker can see through to a statically-known conversion, and a
  first-class module value, by construction, sometimes hides that.
- **Both checkers** would need the new type former, the new expression
  form, the purity-in-types check, and the textual-equality comparison
  rule — each rule-for-rule in Rust and in `check.fx`, as every other
  FX-26 feature has been. Nothing here needs run-time support beyond
  "a product," which is the one piece of good news: unlike a real ML
  functor system, Sheldon's design needs no new closure-conversion or
  existential-packing machinery at run time, because nothing is ever
  generative at the value level — every module value is exactly the
  product it was built from.

No client is in view for this today, which is the same open question
`separate-compilation.md` already asked (§7 below carries it forward).

### 4.7 What happens at the REPL

Unchanged from `separate-compilation.md` §2.1: "the REPL is the
anonymous last unit." A `define-syntax` typed at the REPL is local to the
session, exactly as it is today (`docs/macros.md`); importing a unit that
exports macros brings them into the REPL's scope the same way importing
a unit that exports values does. Nothing about speculative checking
changes for syntax-rules-shaped macros, since they run with no evaluation
at all (`docs/macros.md`, step 1 of the recommendation). If FX-26 later
hosts its own expander (already planned independently of modules,
`TODO.md` §11, "Speculative analysis as you type") and wants *procedural*
macros to run speculatively as the user types, a macro transformer's
effect would need to be licensed exactly the way the eager reader's is
today — "no read or write on any region the REPL shares with the user's
program" (`docs/fx26.md`, "What licence to speculate means") — and a
macro exported from a unit that closes over private state would need a
licensed effect before it could run early. This is not new machinery to
build; it is the existing `licence.rs`/`private-regions` mechanism,
applied to one more kind of code that might run before the user presses
Enter.

## 5. Hygiene, and whether macros can live in interfaces

**What hygiene must record, once macros cross a unit boundary.** FX-26's
existing mechanism: "An alias is an uninterned symbol with its original's
name … Resolving an alias that nothing in the expansion rebound means
looking the original up in the environment of the macro's definition"
(`docs/macros.md`). Today that environment is one flat program's global
scope. The moment a macro is exported from one unit and used in another,
"the macro's definition environment" must be able to name a binding that
lives in a *different*, separately checked and compiled unit — which is
precisely the identity problem `separate-compilation.md`'s own table
already raised for ordinary globals ("two units' private `helper`s
collide … a global is (unit, name); a private name never appears
unqualified outside its unit") and for generative types ("two runs
number differently … (unit, name), with `rep` in the interface"). Macro
hygiene is a third consumer of exactly the same fix, not a new one: once
globals and generative types are `(unit, name)`-keyed for separate
compilation's own sake, an alias's "where it was introduced" can be
`(unit, name)` too, at no extra design cost.

**A sharper problem, not covered by that fix alone.** A macro very often
needs to expand into a reference to a helper its home unit does *not*
export — this is completely ordinary in Racket (a macro may reference any
binding visible at its own definition site, exported or not) and it is
exactly how a `syntax-rules` or `er-macro-transformer` template avoids
re-deriving logic inline at every use. But FX-26's export list is meant
to say what an *importer may write*: `client.fx` typing `down-counter`
directly, when `counter` did not export it, is refused today
(`separate-compilation.md` Example 4, "proposed error: `down-counter` is
not exported by `counter`"). A macro-expanded reference to the same name
must still be *allowed* — the export list governs surface text, not what
an expansion may produce. FX-26's current implementation cannot make this
distinction: by the time the checker sees anything, aliases have already
been stripped back to plain symbols ("Output stays plain Scheme … `quote`
strips aliases back to their originals," `docs/macros.md`), so a
macro-introduced global reference and a user-typed one are
indistinguishable by the time the export check would need to run. **This
is genuinely new checker work**, not a reuse of anything that exists: the
checker (or a pass between expansion and checking) needs to know, per
reference, whether it came from surface text or from an unexported
macro's template, and apply the export-list rule only to the former.

**Can macros live in interfaces?** Split by kind:

- **`syntax-rules`-shaped macros are pure data** — a set of
  pattern/template pairs, trees with no attached code — and can be
  printed into a unit's `.fxi` exactly the way a type or an effect
  abbreviation already is: readable back by the same checker that wrote
  it, byte-for-byte between the two checkers, no new carrier needed. This
  is the same shape of "pure data survives as text" argument
  `separate-compilation.md` already makes for lemmas ("a lemma is a
  proof, so exporting one is coherent").
- **Procedural macros (ER/IR, `er-macro-transformer`/`ir-macro-transformer`)
  are Scheme closures** — they need `%host` and the expansion-time engine
  to run at all (`docs/macros.md`, "Interfaces, in order," step 3). A
  closure cannot be printed as `.fxi` text the way a type can; it has to
  ride the same carrier `separate-compilation.md` already proposes for
  cross-unit inlining (the fragment/unfolding track, stages S5–S6:
  "a unit's compiled cellular words, with an import table"). So
  **`syntax-rules` exports are an `.fxi`-text-only feature, available as
  soon as units exist (S3); procedural macro exports wait for the
  fragment carrier (S5/S6)**, the same staged dependency
  `separate-compilation.md` already has for unfoldings, now with one more
  consumer.
- Racket's own precedent for "macros as pure interface data" is exactly
  the `define-syntaxes`-in-`define-signature` case (§1, §3): the macro's
  implementation is part of the signature's own source, recompiled
  whenever the signature is, not something the linking step has to carry
  separately — which only works because a Racket signature is itself
  always recompiled as source, never cached as a stamped binary interface
  the way FX-26's `.fxi` is meant to be. FX-26's stamped, checker-written
  `.fxi` is a stronger caching story than Racket's signatures have, which
  is exactly why the syntax-rules/procedural split above matters for
  FX-26 in a way it does not for Racket.

**A further technique worth banking, not building yet:** if FX-26 ever
wants *type-and-effect-directed* macros — the Klister-style idea
`docs/macros.md` already names as "the experiment worth doing there
later," where a macro can ask what effect is permitted where it expands —
the concrete, load-bearing technique for combining a macro-expansion pass
with a genuine static checker was read directly in two papers: Typed
Racket "expand[s] macros before typechecking … integrat[ing] the type
checker with the macro expander" (Tobin-Hochstadt and Felleisen, POPL
2008, read in full), and Chang, Knauth and Greenman's *Type Systems as
Macros* (POPL 2017, read in full) implement a whole bidirectional type
system *as* macro-expansion-time computation, carrying types as syntax
properties attached to expanded syntax objects and fully erasing them
before any phase-0 code runs. Both papers flag the same unsolved edge:
macros whose invariants the type system does not understand (Typed
Racket's own words: "cannot be specified ahead of time"). This is not
something to build for FX-26 now; it is the concrete prior art to reread
if and when a type-effect-directed macro is actually wanted.

## 6. What Swift's resilience work suggests for FX-26's cached units

Swift's library-evolution model answers exactly the question
`separate-compilation.md`'s guarded-unfolding design (S5) was built to
answer, from the opposite direction: not "how do we let a client inline
a callee's body without forcing recompilation," but "what, structurally,
can a library change without breaking any client that never saw the
change coming." Read directly from `apple/swift`'s
`docs/LibraryEvolution.rst` and the Swift.org "Library Evolution in
Swift" post (full findings, and the sources actually fetched, in the
report filed under this note's sources table, §8):

| Change                                                          | Safe without recompiling clients?                    | Why                                                                                                                 |
| --------------------------------------------------------------- | ---------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------- |
| Add/reorder a stored property on a non-`@frozen` struct/enum    | yes                                                  | layout is opaque across the boundary; clients go through type metadata and accessor functions, never a fixed offset |
| Add an enum case to a non-`@frozen` enum                        | yes (clients must already `switch` non-exhaustively) | same: no fixed case-dispatch table baked into client code                                                           |
| Change a function's body (not `@inlinable`)                     | yes                                                  | clients call through a stable entry point and never see the body at all                                             |
| Add a protocol requirement with a default implementation        | yes                                                  | witness tables are instantiated at run time and filled from the default when an old conformance lacks the slot      |
| Add/reorder a stored property on a `@frozen` struct             | **no**                                               | `@frozen` publishes exact layout; clients access fields by offset directly                                          |
| Remove any ABI-public declaration, even a "private-looking" one | **no**                                               | `@inlinable` client code may already reference it directly                                                          |
| Change a function's signature at all                            | **no**                                               | the entry point itself is part of the contract                                                                      |

The organizing idea — "opaque by default, fast-but-fixed only by explicit
opt-in" — maps onto FX-26's generative types almost exactly, and the
mapping is good news: **FX-26's generative types are already resilient
in Swift's sense, for free, today.** A generative type's representation
is never visible outside its `up-`/`down-` conversions ("Only its
conversions see inside it," `docs/fx26.md`); at run time those
conversions are identity lambdas, and a client only ever reaches a
generative value through exported operations, never by unpacking a
representation directly (there is no "unpack" at all — `down-name` is the
*only* way in, and it is not exported unless the unit's author chooses
to). That is exactly Swift's non-`@frozen` story — opaque, accessed
through named operations, safe to change — and FX-26 gets it with no
extra mechanism because nothing in the compiler currently bakes a
generative type's representation *size* into a caller's code: products
and sums are frozen bloblets, uniformly, and "whether products and sums
of flat data may be flattened too (unboxed data types, as Rust has them)
is a question for later" (`docs/research/shapes.md`, "Flat arrays").
**The day FX-26 adds that — an opt-in unboxed/inline representation for a
generative type, the FX-26 analogue of `@frozen` — is the day a
representation change stops being free**, and it should be gated at link
time by exactly the compatibility check `separate-compilation.md`
already proposes for everything else (`fits_old`, S4): a `@frozen`-like
generative type's representation becoming part of its exported interface,
checked for exact match (not mere subtyping) on relink, the same way
`@frozen` is a one-way commitment in Swift.

Two smaller points, from the same research, worth folding into the
existing design rather than treated as new stages:

- **GHC's per-declaration fingerprinting, not Rust's whole-crate hash, is
  the right precedent to keep following.** `separate-compilation.md`
  already cites GHC's fingerprint scheme for the `.fxi` stamp design; the
  Swift/Rust/Backpack research independently surfaces the same
  conclusion by showing the failure mode of the coarser alternative:
  "current rustc/Cargo has no per-declaration early cutoff across the
  crate boundary — when a crate's metadata hash changes at all, every
  transitive dependent's rustc invocation reruns, even if the parts of
  the interface a given dependent actually used are unchanged." FX-26's
  own `fits_old`-per-export design (S4) already avoids this failure mode
  by construction; this is confirmation to keep it that way, not a change.
- **Backpack's separate-typechecking-before-linking result is the
  closest academic precedent to what a `.fxi`-without-unfoldings already
  is**: a signature-only fragment (types and effects, no implementation)
  that can be fully checked on its own and linked against any later
  implementation that structurally matches it (Kilpatrick, Dreyer, Peyton
  Jones and Marlow, *Backpack: Retrofitting Haskell with Interfaces*,
  POPL 2014, read in full, downloaded to
  `docs/research/papers/backpack-kilpatrick-popl14.pdf`). Backpack's
  harder problem — module *identity* tracked as an infinite regular tree
  of identity-constructors and -variables, so two separately-obtained
  instantiations of the same hole can be recognized as "the same" module
  — is more machinery than FX-26 needs today, because FX-26 units do not
  (and this note does not propose they should) support one unit being
  linked against a choice of several different implementations of a
  shared hole; `(unit, name)` identity is enough as long as each unit
  names its imports directly rather than through a parametrized
  signature. Worth remembering only if that changes. One honest caveat
  in the same source: Backpack's own paper states that full separate
  *object-code* compilation of an incomplete package "would require
  sweeping changes to GHC's existing infrastructure" and was not built —
  what is proven is separate *typechecking* soundness, which is the part
  actually relevant to FX-26's `.fxi`, not a working claim about
  compiled, linkable fragments.

## 7. Open questions for the user

1. **Macros now, or wait for units?** Independent axis from the
   first-class-modules question. Recommend: wait for S3 (the `unit`
   header itself), then add `syntax-rules`-shaped macro exports as part
   of the same stage — they cost nothing new in the `.fxi` carrier (§5)
   and the hygiene fix they need ((unit, name) identity) is required for
   separate compilation anyway. Procedural macro exports should wait for
   the fragment carrier (S5/S6), already a later stage for an unrelated
   reason (cross-unit inlining).
2. **`syntax-rules` only, or procedural (ER/IR) too, from the start?**
   Recommend `syntax-rules` only at first: it is the one that needs no
   new carrier, no `%host` reachability across units, and no answer yet
   to "what does a licence mean for a macro transformer that closes over
   another unit's private state" (§4.7). Revisit once a real macro that
   needs ER/IR power is actually wanted.
3. **Does a unit's `(language …)` line mean only "plain FX-26 plus these
   imported macros," or should FX-26 ever want a genuinely different
   *reader* per unit, the way Racket's `#lang` can swap the whole
   surface syntax?** FX-26 already has reader profiles
   (`SyntaxProfile::FX26`/`FX87`/`FX91`), chosen per session today, not
   per unit. Recommend: start with "same reader, different macro
   environment" (cheap, matches what units actually need right now,
   i.e. the front end's own twelve files sharing one profile); leave
   per-unit reader-profile switching as a later, separate question — it
   is a real engineering project (the reader would need to be re-entrant
   per unit) with no client in view yet, exactly like first-class
   modules.
4. **Export-list semantics for macro-introduced references — build the
   distinction now, or defer macros-in-units until this is needed?** §5
   identified this as genuinely new checker work (telling a
   macro-expanded reference apart from user-typed surface text, for the
   purpose of the export check alone). It is small in isolation but
   touches the boundary between the expander and the checker that
   `docs/macros.md`'s current design keeps deliberately separate ("Output
   stays plain Scheme"). Recommend deciding this before building macro
   exports at all, since the alternative — forbidding a macro from ever
   referencing an unexported helper of its own unit — would make
   exported macros nearly useless for anything beyond trivial
   `syntax-rules` sugar.
5. **Transparent (manifest) type exports — does FX-26 want FX-91's
   `define-description`/`desc`, or Sheldon's fully-opaque original?**
   Raised directly by rereading the thesis (§2, above): Sheldon's own
   system cannot express the "two modules must agree on one shared
   abstract type" case cleanly, and calls the workaround "awkward."
   FX-91 fixed this with transparent descriptions. FX-26 already has an
   answer *within* one unit (`define-type` abbreviations, visible to
   every later definition); the open question is only whether a unit
   should be able to *export* a transparent type abbreviation the same
   way it exports an opaque generative one — this is cheap (a `.fxi`
   entry that is a type synonym rather than a generative header) and
   does not require first-class modules at all. Recommend: add it
   alongside S3, it is nearly free and Sheldon's own thesis names its
   absence as the single largest wart in the original design.
6. **First-class modules: any client in view yet?** Carried forward
   unanswered from `separate-compilation.md`'s own open question 8. This
   note adds nothing that changes the answer, only confirms that if a
   client does appear, §4.6's sketch is where to start, and that nothing
   about macros should be allowed to motivate building it prematurely —
   macros belong to the static layer regardless of whether the dynamic,
   first-class layer is ever built at all.

## 8. Sources

Read directly for this note (not delegated):

| Source                                                                                                                                                                     | Where                                                  | Depth                                                                                                                                          |
| -------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| Sheldon and Gifford, *Static Dependent Types for First Class Modules*, LFP 1990                                                                                            | `~/Dev/LangPlay/GiffordHistory/papers/lfp90.pdf`       | read in full                                                                                                                                   |
| Sheldon, *Static Dependent Types for First-Class Modules*, MIT S.M. thesis, 1990                                                                                           | `~/Dev/LangPlay/GiffordHistory/papers/mthesis.pdf`     | read in full                                                                                                                                   |
| Gifford, Jouvelot, Sheldon, O'Toole, *Report on the FX Programming Language* (FX-91)                                                                                       | `~/Dev/LangPlay/GiffordHistory/papers/fx91-report.pdf` | introduction and module grammar (§2.2.6) read directly; rest previously read for `separate-compilation.md`, reused with its own page citations |
| `docs/fx26.md`, `docs/macros.md`, `docs/research/separate-compilation.md`, `docs/research/generative-types.md`, `docs/research/shapes.md`, `TODO.md` §22, `PLAN.md` Q9/Q11 | this repository                                        | read in full                                                                                                                                   |

Read directly by the Racket-macros research agent (full report filed in
this session; papers downloaded to `docs/research/papers/`):

| Source                                                                                    | Where                                                                           | Depth                                                                     |
| ----------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------- | ------------------------------------------------------------------------- |
| Flatt, *Composable and Compilable Macros: You Want It When?*, ICFP 2002                   | `docs/research/papers/flatt-icfp02-composable-compilable-macros.pdf`            | read in full (10 pp.)                                                     |
| Owens and Flatt, *From Structures and Functors to Modules and Units*, ICFP 2006           | `docs/research/papers/owens-flatt-icfp06-structures-functors-modules-units.pdf` | read in full (6 pp.)                                                      |
| Flatt, *Binding as Sets of Scopes*, POPL 2016                                             | `docs/research/papers/flatt-popl16-binding-sets-of-scopes.pdf`                  | §1–4.3 read (6 of 13 pp.)                                                 |
| Chang, Knauth, Greenman, *Type Systems as Macros*, POPL 2017                              | `docs/research/papers/chang-knauth-greenman-popl17-type-systems-as-macros.pdf`  | §1–5.3 read (6 of 12 pp.)                                                 |
| Tobin-Hochstadt and Felleisen, *The Design and Implementation of Typed Scheme*, POPL 2008 | `docs/research/papers/tobin-hochstadt-felleisen-popl08-typed-scheme.pdf`        | §1–4.1 read (6 of 12 pp.)                                                 |
| Racket Reference §7.1, *Creating Units* (`define-signature`)                              | <https://docs.racket-lang.org/reference/creatingunits.html>                     | read                                                                      |
| Racket Reference §7.7, *Extending the Syntax of Signatures* (`define-signature-form`)     | <https://docs.racket-lang.org/reference/define-sig-form.html>                   | read                                                                      |
| Racket Guide §14.1, *Signatures and Units*                                                | <https://docs.racket-lang.org/guide/Signatures_and_Units.html>                  | read                                                                      |
| Racket Guide §17.1, *Module Languages*                                                    | <https://docs.racket-lang.org/guide/module-languages.html>                      | read                                                                      |
| Racket Reference §1.2, *Syntax Model*                                                     | <https://docs.racket-lang.org/reference/syntax-model.html>                      | read                                                                      |
| Typed Racket Reference §5, *Typed Units*                                                  | <https://docs.racket-lang.org/ts-reference/Typed_Units.html>                    | abstract only (search snippet)                                            |
| Culpepper and Felleisen, *Fortifying Macros*, ICFP 2010 / JFP 2012                        | <https://www2.ccs.neu.edu/racket/pubs/icfp10-cf.pdf>                            | abstract only                                                             |
| Sheldon and Gifford, LFP 1990 (attempted independently by this agent)                     | dl.acm.org                                                                      | not obtained (paywalled); superseded by this note's own direct read above |

Read directly by the ML-module-theory research agent:

| Source                                                                                              | Where                                                                                                 | Depth                                                               |
| --------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------- |
| MacQueen, Harper, Reppy, *History of Standard ML*, HOPL 2020 (§5, Modules)                          | `docs/research/papers/macqueen-2020-history-of-standard-ml.pdf`                                       | §5 read in full                                                     |
| MacQueen, *Reflections on Standard ML*                                                              | `docs/research/papers/macqueen-reflections-on-standard-ml.pdf`                                        | pp. 1–2 only                                                        |
| Harper and Lillibridge, *A Type-Theoretic Approach to Higher-Order Modules with Sharing*, POPL 1994 | `docs/research/papers/harper-lillibridge-popl94-higher-order-modules-sharing.pdf`                     | read in full                                                        |
| Lillibridge, PhD thesis (translucent sums), CMU-CS-97-122                                           | `docs/research/papers/lillibridge-1997-thesis-translucent-sums.pdf`                                   | abstract and table of contents only                                 |
| Leroy, *Manifest Types, Modules, and Separate Compilation*, POPL 1994                               | `docs/research/papers/leroy-popl94-manifest-types.pdf`                                                | read in full                                                        |
| Leroy, *Applicative Functors and Fully Transparent Higher-Order Modules*, POPL 1995                 | `docs/research/papers/leroy-popl95-applicative-functors.pdf`                                          | read in full; p. 12 quote verified                                  |
| Crary, Harper, Puri, *What is a Recursive Module?*, PLDI 1999                                       | `docs/research/papers/crary-harper-puri-pldi99-recursive-module.pdf`                                  | read, key quotes verified                                           |
| Dreyer, *Understanding and Evolving the ML Module System*, PhD thesis, CMU 2005                     | `docs/research/papers/dreyer-2005-thesis-ml-module-system.pdf`                                        | table of contents plus recursive-modules chapter (pp. 87–102)       |
| Russo, *Recursive Structures for Standard ML*, ICFP 2001                                            | `docs/research/papers/russo-icfp01-recursive-structures-sml.pdf`                                      | abstract and §5–6                                                   |
| Dreyer and Rossberg, *Mixin' Up the ML Module System* (MixML), ICFP 2008, extended version          | `docs/research/papers/dreyer-rossberg-icfp08-mixml-extended.pdf`                                      | abstract, introduction, dynamic semantics, appendix IL              |
| Rossberg, Russo, Dreyer, *F-ing Modules*, JFP 2014                                                  | `docs/research/papers/rossberg-russo-dreyer-fing-modules-jfp14.pdf`                                   | pp. 1–4 read; pp. 7, 35 quotes verified                             |
| Rossberg, *1ML — Core and Modules United*, JFP version                                              | `docs/research/papers/rossberg-1ml-jfp.pdf`                                                           | pp. 1–9, 55–61 read; §§2–7 technical body not read                  |
| Rossberg, *1ML with Special Effects*, 2016                                                          | `docs/research/papers/rossberg-2016-1ml-with-special-effects.pdf`                                     | pp. 1–3 read                                                        |
| Garrigue and Frisch, *First-Class Modules in OCaml*, ML Workshop 2010 (slides)                      | `docs/research/papers/garrigue-frisch-ml2010-first-class-modules.pdf`                                 | read in full                                                        |
| OCaml manual 5.x, first-class modules, `module type of`, module types                               | <https://ocaml.org/manual/5.5/firstclassmodules.html>, `/5.3/moduletypeof.html`, `/5.3/modtypes.html` | fetched and read                                                    |
| MacQueen, *Modules for Standard ML*, LFP 1984                                                       | dl.acm.org / ResearchGate                                                                             | not obtained (paywalled); superseded by the HOPL 2020 retrospective |

Read directly by the Swift/Rust/Scala/Backpack research agent:

| Source                                                                                                | Where                                                                                        | Depth                                                                                     |
| ----------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| Swift.org, *Library Evolution in Swift* (blog, S. Pestov)                                             | <https://www.swift.org/blog/library-evolution/>                                              | read in full                                                                              |
| `apple/swift`, `docs/LibraryEvolution.rst`                                                            | <https://github.com/apple/swift/blob/main/docs/LibraryEvolution.rst>                         | read in full; primary source for §6's table                                               |
| swift-evolution SE-0260, *Library Evolution for Stable ABIs*                                          | <https://github.com/swiftlang/swift-evolution/blob/main/proposals/0260-library-evolution.md> | not independently verified (search snippet only)                                          |
| `.swiftinterface` mechanics                                                                           | three independent secondary sources, cross-confirmed                                         | skimmed; no swift.org primary doc fetched directly                                        |
| Rust Edition Guide                                                                                    | <https://doc.rust-lang.org/edition-guide/editions/index.html>                                | read in full                                                                              |
| Rust RFC 1566 (procedural macros)                                                                     | <https://rust-lang.github.io/rfcs/1566-proc-macros.html>                                     | read in full                                                                              |
| Rust Reference, *Macros By Example*                                                                   | <https://doc.rust-lang.org/reference/macros-by-example.html>                                 | read in full                                                                              |
| Rust Reference, `#[non_exhaustive]`                                                                   | <https://doc.rust-lang.org/reference/attributes/type_system.html>                            | read in full                                                                              |
| Cargo Book, *SemVer Compatibility*                                                                    | <https://doc.rust-lang.org/cargo/reference/semver.html>                                      | read in full                                                                              |
| rustc-dev-guide, *Libs and metadata* / incremental compilation                                        | rustc-dev-guide.rust-lang.org (via search)                                                   | skimmed, not fetched page-by-page                                                         |
| Scala Language Specification 2.13, §3, *Types*                                                        | <https://scala-lang.org/files/archive/spec/2.13/03-types.html>                               | read in full; source of the `p.type ≡ q.type` rules                                       |
| Odersky and Zenger, *Scalable Component Abstractions*, OOPSLA 2005                                    | <https://chara.epfl.ch/~odersky/papers/ScalableComponent.pdf>                                | not independently verified (PDF text extraction failed); relied on the Scala spec instead |
| Kilpatrick, Dreyer, Peyton Jones, Marlow, *Backpack: Retrofitting Haskell with Interfaces*, POPL 2014 | `docs/research/papers/backpack-kilpatrick-popl14.pdf`                                        | read in full                                                                              |
| GHC User's Guide, *Separate compilation*                                                              | <https://downloads.haskell.org/ghc/latest/docs/users_guide/separate_compilation.html>        | read in full; per-declaration fingerprinting confirmed verbatim                           |
| GHC `-fomit-interface-pragmas`                                                                        | older GHC users-guide mirror, via search                                                     | skimmed, substance consistent with current docs but not refetched                         |

Everything in §§1–7 above not directly attributed to one of the three
agents' reports, and not marked "read directly" above, traces to this
repository's own prior notes (`separate-compilation.md`, `macros.md`,
`generative-types.md`, `shapes.md`, `fx26.md`), each already citing its
own sources; nothing in this note is presented from memory without a
citation to one of the two tiers above.
