# Combining modules that have abstract types: what Sheldon and FX-91 say

Research note, 2026-10-09, for lifting the "no abstract types" refusal on
FX-26's `(extend e0 e1)` and `(include m)`. Nothing here is implemented.

## Sources, and what was and was not obtained

Read in full or in the relevant parts, all local:

- **Thesis**: Mark A. Sheldon, *Static Dependent Types for First-Class
  Modules*, **S.M. (master's) thesis**, MIT EECS, 22 May 1989 (title page;
  advisor D. K. Gifford), 68 pp. It is not a PhD thesis, and its date is
  June 1989, not 1990. Cited "Thesis p. N" with N the printed page (the PDF
  page number is the same). Copy:
  `docs/research/papers/sheldon-mit-1989-thesis-static-dependent-types-first-class-modules.pdf`.
- **LFP90**: Sheldon and Gifford, *Static Dependent Types for First Class
  Modules*, LFP 1990 (Nice), pp. 20-29 (dblp:
  <https://dblp1.uni-trier.de/db/conf/lfp/lfp1990.html>). Cited "LFP90 §n".
  Copy: `docs/research/papers/sheldon-gifford-lfp90-static-dependent-types-first-class-modules.pdf`.
- **FX-91 report**: `docs/research/papers/gifford-jouvelot-sheldon-otoole-fx91-report.pdf`,
  §2.2.6 (`moduleof`), §2.2.9 (`select`), §2.3.5 (`extend`, p. 15), §2.3.19
  (`with`, p. 23). Cited "FX-91 §n".

Both Sheldon documents came from the user's local archive
`~/Dev/LangPlay/GiffordHistory/papers/` (`mthesis.pdf`, `lfp90.pdf`; its
`README.md` records that they were fetched from
<https://groups.csail.mit.edu/cgs/pubs/>). Nothing was downloaded for this
note. The "thesis" the question mentions is this S.M. thesis; no later
PhD thesis by Sheldon was found by a web search (the searches returned only
unrelated module work: Russo, Lillibridge, Rossberg). The LFP90 paper
refers to a fuller treatment as "[Sheldon 90]" (LFP90 §2.1.1, §2.3, §4),
which appears to be this thesis under its published year.

Repo context read: `docs/research/first-class-modules.md` (the FX-26 design:
modules as values; `select` on paths only; opaque `let`; M4 subtyping) and
`docs/research/modules.md` §2 (earlier reading of the same sources).

Legend: **[src]** is what a source says; **[inf]** is my inference.

## Summary

- **Sheldon's 1989/1990 system has neither `include` nor a working
  `extend`.** The thesis lists "opening" and "merging" modules as an open
  problem and floats `(extend a b)` as a possible solution, adding only that
  its fields' types would be changed "to reflect the re-exported
  abstractions" and that "problems of name clashes and renaming remain"
  (Thesis §4.1.4, p. 47). What it actually does to combine modules is
  *repackage*: write a new `mod` whose abstractions have the old modules'
  selected types as their *representations*, with every operation wrapped in
  `up`/`down` conversions (the `fx` module, Thesis §3.6, pp. 41-43).
  That is re-binding as a new, distinct abstraction, which the thesis calls
  "unnecessary work" and error-prone.
- **FX-91's `extend`** (§2.3.5, p. 15) is typed by listing both modules'
  `abs`, `desc` and `val` components, e1's winning; it types e1 inside
  `(with e0 ...)`, so e1 sees e0's abstract types as `(select e0 t)`. The
  printed rule does not say how e0's own `abs t` entries in the result relate
  to those selects. [inf] the rule as printed is a sketch on this point.
- **`select` is allowed on any expression with no `read` effect** (thesis,
  LFP90) or on a *pure* expression (FX-91), compared by textual identity;
  names are the easy case, not the only one. Impure (reading) expressions are
  refused because the module they name could change between two evaluations.
- **The candidate direction is what Sheldon's own later design
  (transparent descriptions, Thesis §4.1.2, p. 45) and FX-91's `with`
  already do:** a transparent alias `(select m t)` of the original. Names
  only, with non-name expressions refused or spliced, is a sound
  restriction of Sheldon's rule, not a departure from it. Main caveats are in
  §4.

## 1. Abstract types when two modules are combined

**[src] No combination operator exists in the 1989/1990 system.** The kernel
has `mod`, `with`, `input`, `dselect`/`select` and nothing that merges two
modules (Thesis §2.1, pp. 17-18; LFP90 Fig. 1). The thesis says so
(§4.1.4, p. 47): "One problem, illustrated clearly by the `fx` module
itself, is the way fields inherited from a module must be repackaged into a
new module. An `open` form which makes all the names of a module available in
some scope would be most useful." Design questions it lists: do the names
shadow, and is there "an elegant way to do systematic renaming".
Then: "There may be a way to solve the above problem together with the
problem of merging modules (a common operation). The form `(extend a b)`
might [verb missing in the printed text, checked on the page image] the
fields of the modules `a` and `b`, changing the types of the fields to
reflect the re-exported abstractions. Problems of name clashes and renaming
remain."

**[src] What the thesis does instead: re-bind.** The `fx` library module
loads one module per library type and builds a new `mod` whose
abstractions are defined *as* the old modules' selected types, and whose
operations are wrappers (Thesis §3.6, pp. 41-43):

```scheme
(mod ((unit type refof-mod.unit)
      (refof (dfunc (type region) type) refof-mod.refof) ...)
     ((new ... (up-refof ((proj (proj refof-mod.new r) t) v))) ...
      (set ... (up-unit ((proj ... refof-mod.set r t) (down-refof x) v))) ...))
```

The new `unit` is a new abstraction (opaque outside `fx`) whose
representation is `refof-mod.unit`; each operation converts with `down-`
and `up-`. Types are *not* the same as the originals' outside. The thesis
calls the cost out: "Instead ... the arguments (description and value) must
be collected and converted to the representation type, the subroutine must be
called on the converted values, and the result must be converted to the
abstract type. This is unnecessary work. In addition, such convoluted code is
error prone and adds extra subroutine calls which may be difficult for the
compiler to open code" (Thesis §4.1.4, p. 47). `up`/`down` compile to
identity functions, and calls to a module's own coercions can be removed
after alpha-renaming (Thesis §3.5, p. 41).

**[src] Sharing was not expressible.** No way for two modules to agree on a
type without parameterizing both over a common submodule: "The system
presented in this thesis has no concise way to express sharing constraints
... This is awkward and entails extra subroutine calls" (Thesis §4.1.5,
pp. 47-48; LEX/SYMBOLTABLE example from MacQueen 88).

**[src] The planned fix is transparent descriptions.** "The next version of
FX will have a module system allowing the export of abstraction, value, and
transparent description bindings. These bindings appear in the module and in
the type" with the example `(modof ((a type)) ((t (pairof a a @red))) ((x a)
(f (subr pure ((y t)) a))))` (Thesis §4.1.2, p. 45); the design "has not yet
been implemented" (Thesis §2, p. 16). FX-91 has it: `(moduleof (abs ..)
(desc ..) (val ..))` (FX-91 §2.2.6). A transparent description may be defined
as any description, so `(desc d (select m t))` is expressible there
[inf; the §2.2.6 kind rule only requires `dx` to have a kind in a context
with the module's `abs` names].

**[src] FX-91 `extend` (§2.3.5, p. 15).** "The expression e0 is evaluated
to a module v0 and the value of module e1, extended with all the bindings
introduced by v0, is returned. The expression e1 has access to the bindings
of e0. In the case of conflict, the bindings of v1 take precedence. An
extend expression is a binding construct." Static rule: `e0 : (moduleof
abs0 desc0 val0) ! ei0`; `(with e0 e1) : tx ! ei` with `tx ~ (moduleof abs1
desc1 val1)`; the result is `(moduleof abs2 abs1 desc2 desc1 val2 val1)`
where `abs2 = abs0 - abs1` (set difference by name), likewise `desc2`,
`val2`; effect `(maxeff ei0 ei)`. Dynamic: the values' union, e1's winning.
Nothing in the section mentions abstract types specially: abs components
simply appear in the result's `moduleof`. The e0 side is a plain `abs` entry;
the e1 side was typed under `with`, whose rule substitutes `(select e0 id)`
for e0's abs names and `(with e0 id)` for its value names (FX-91 §2.3.19,
p. 23).

[inf] Consequences of reading the printed rule literally:
(a) e0's abstract types come out as the result's *own* `abs` entries
(re-bound, same names) while the types inside e1's components mention
`(select e0 t)`; the report does not say these are the same type, so a value
of e1's `(select e0 t)` need not fit a result operation expecting the
result's `t`. (b) The names-only difference does not rewrite e0's remaining
component types; if e1 redefines `t`, e0's surviving components would
capture it. Neither is stated or ruled out in the report. Aliasing e0's
abstract types as `(select m t)` (the candidate) removes both.

| Mechanism                    | Abstract type of the original in the result                       | Source                      |
| ---------------------------- | ----------------------------------------------------------------- | --------------------------- |
| `fx` module (repackaging)    | new abstraction, original as representation, `up`/`down` wrappers | Thesis §3.6, pp. 41-43      |
| `(extend a b)` as proposed   | "re-exported abstractions"; undeveloped                           | Thesis §4.1.4, p. 47        |
| FX-91 `extend`               | listed as the result's `abs`; e1's side sees `(select e0 t)`      | FX-91 §2.3.5, §2.3.19       |
| FX-91/thesis `with`          | body sees names; result type has `(select e0 t)` in their place   | FX-91 §2.3.19; Thesis p. 31 |
| transparent `desc` (planned) | alias by definition, visible outside                              | Thesis §4.1.2, p. 45        |

## 2. The rule for `select`

**[src] Kind rule.** `(select e t)` (thesis `dselect`) is well-kinded only if
`e` has a `modof`/`moduleof` type with `t` among its abstractions (or, in
FX-91, descriptions) and the *effect of `e`* satisfies:

- Thesis §2.2.1, `Dselect`, pp. 20-21: the effect is `v (maxeff (write ..)
  ... (alloc ..) ...)`, i.e. zero or more writes and allocations. "An earlier
  proposal ... required that the module expression in a dselect be pure. But
  this is too restrictive. If the module expression only allocates and
  writes, there is no problem. Only if it reads mutable storage which another
  expression may alter is it possible for an implementation to change
  dynamically." Design Constraint 1: "Value expressions occurring in
  descriptions must not have read effects."
- LFP90 §2.1.3: same ("by requiring that the static effect of the module
  expression not contain read effects. (Quest is much more restrictive,
  requiring that the module expression be an identifier.)").
- FX-91 §2.2.9: stricter, `! fx..pure`: "The effect of e must be pure to
  prevent type abstraction violation."

So *expressions* are allowed, not just names; the rule is on effects.
(Quest, which has no effect system, allows only identifiers, Thesis §1.4.1,
p. 14.)

**[src] Identity.** "Two select forms are equivalent iff they are textually
identical" (LFP90 §2.1.3; Thesis §2.3, p. 34, "The simplest equivalence
relation is textual equality"). The checker never evaluates the module
expression. Soundness story (LFP90 §2.1.3): if module expressions in types
are store-independent, "two expressions with the same abstract type must have
come from the implementation of the same module (or from syntactically
identical implementations in the same file)". An abstraction selected from a
module is *not* convertible to its representation (LFP90 §2.1.3).

**[src] Substitution on leaving a scope.** `with`, application and `let`
substitute the module *expression* for the bound name in the result type
(Thesis §2.2.2, pp. 23-25, 31; LFP90 §2.2): applying a dependent subroutine
`(pair-example pair-impl ...)` yields `(pair-impl.pairof int char)`; a
non-name argument yields `((select (mk-pair-impl "lambda-based") pairof) int
char)` in the type. "Descriptions never contain liberated local
identifiers" (Thesis p. 34).

**[src] Non-name / impure expressions.**
- Reading expression in a select: illegal. The motivating example is
  `(mk-pair-impl (read-string-from-keyboard))` used twice: the types would
  match textually but the modules could differ (LFP90 §2.2).
- `let` is opaque: "Even if two identifiers are bound to textually
  identical expressions, select descriptions from the two variables are not
  interconvertible" (LFP90 §2.2; Thesis §2.2.2, p. 25). A `let` whose
  initializer reads can be used locally, but its result type may not mention
  the variable, since substituting the definition would put a read into a
  select; "the system enforces the same constraints as weak existential types
  in the presence of reads" (Thesis p. 25).
- `input "file"`: allowed, a pure expression, identical text means identical
  module; this needs the file system treated as immutable (LFP90 §2.3;
  Thesis §3.4, pp. 40-41).

**[src] Non-termination guard.** The select kind rule calls the type checker,
so Design Constraint 2 (a variable's type may not depend on itself) and the
`mod` scope rule (field types do not see field names, Thesis p. 26 and n. 3;
LFP90 §2.1.2) keep it terminating.

## 3. `include`, concatenation, inheritance; pitfalls

**[src] No `include` as such.** The nearest items are the `open` form
wish and `(extend a b)` (Thesis §4.1.4, p. 47); the Thesis also floats
`local`/`exports` for hiding items (Thesis §4.1.3, pp. 45-46), noting "one
must be careful that a local name does not appear free in a transparent
definition or in a field type" (p. 46). FX-91 `with` is the nearest
shipping form: it brings a module's names into scope, not into a new
module (FX-91 §2.3.19). FX-91's `include` is only file inclusion for `input`
(the `input` form, FX-91 report p. 17, `(with fx (include literal))`), unrelated.
No discussion of OCaml's `include`, ML `open`/`include` or inheritance of
abstract types exists in either document (grep of the thesis and LFP90 for
inherit/include/concatenat found nothing relevant; "inherited" appears once,
in the "fields inherited from a module" sentence quoted above).

**[src] Pitfalls the sources raise.**
1. *Name clashes and renaming*: unresolved (Thesis p. 47).
2. *Hidden dependence through abstraction*: a file importing another
   "merely places the input inside an abstraction", so stamping the outer
   file is not enough (Thesis §3.4, p. 40).
3. *Escape*: SOL and Quest "may not return a value of abstract type from a
   scope in which the abstraction is opened"; SDT lifts this by substituting
   the module expression into the type, except when it has read effects
   (LFP90 §2.2; Thesis §1.2.2, pp. 10-12).
4. *Effect loophole via abstraction*: "Abstraction boundaries must not hide
   side effects" (Design Constraint 3; Thesis pp. 27-28): a `mod` abstraction
   may not mention a mutable region constant, so mutable abstractions are
   parameterized over regions. [inf] relevant to FX-26 only if an included
   module's abstractions could be re-bound over a region the includer owns.
5. *No recursion through select*: types in `mod` representation are
   recursive only through abstraction names, not substituted away (Thesis
   p. 27). [inf] aliasing by `(select m t)` does not touch this.
6. *Alpha-renaming of `with`-bound names* is why the parser cannot parse a
   `with` body before the module's type is known (Thesis §3.1, pp. 37-38).
   [inf] `include`/`extend` of a typed module has the same property: item
   names come from m's type.
7. *Generativity*: Sheldon's abstractions are *not* generative per
   evaluation. They are named by the select expression, so textually
   identical module expressions give identical types (LFP90 §2.1.3).
   `first-class-modules.md` (the two-loads decision) already departs from
   this deliberately; that departure matters here because an
   expression-based `include` would inherit the textual rule.

## 4. Assessment of the candidate direction

Candidate: for `(include m)` or `(extend m e1)` with `m` a variable, each
abstract type `t` of `m` appears in the combined module's type as a
transparent alias of `(select m t)`; for a non-name module expression, refuse
or (for literal inline module text) splice its items.

**What it gets right.**
- **[src+inf]** It is exactly the "transparent description" feature the thesis
  names as the fix for the repackaging/sharing problem (Thesis §4.1.2, p. 45;
  §4.1.4-4.1.5) and FX-91 realizes (§2.2.6). It avoids the `fx`-module
  pattern's cost: no new abstraction, so no `up`/`down` wrapping, and values
  stay interchangeable with the original's (the combined module's values
  are m's values; `up`/`down` are identities either way, Thesis p. 41).
- **[inf]** Aliasing through `(select m t)` fixes the two gaps in FX-91's
  printed `extend` rule noted in §1: the combined module's component types
  mention `(select m t)` consistently, and e1 shadowing the name `t` cannot
  capture m's remaining components.
- **[src+inf]** Names only is a sound subset of Sheldon's rule (textual
  identity of select expressions; Quest-style identifier-only is the
  conservative end, LFP90 §2.1.3) and matches the repo's paths-only
  first stage (`first-class-modules.md`, "Selection and opening"), so no
  purity analysis of the module expression is needed and `let` opacity is
  respected for free (the path is the binding). Refusing calls and loads
  matches Sheldon's own treatment of impure expressions and the repo's
  "every load is one value / `load-module` is a global" decision.
- **[inf]** Splicing literal inline module text defines *fresh* abstractions
  in the enclosing module, which is ordinary ML `include`-of-a-body behavior
  and needs nothing from `select`. It is consistent with Sheldon only in the
  trivial sense that the abstractions are the enclosing `mod`'s own.

**What the sources suggest differently.**
- Sheldon's rule admits *any expression* without reads (thesis: writes and
  allocs fine; FX-91: pure). Refusing calls is stricter than the sources
  require; it is the first-stage choice the repo already made for `select`,
  not a soundness need. A pure call `((f 2) ..t)` would be allowed by
  FX-91 §2.2.9 with textual equality. [inf] If `include` of a non-name were
  later wanted, the evaluation-once point matters: `extend` evaluates e0
  once (FX-91 §2.3.5 dynamic rule), but the alias `(select (f 2) t)`
  identifies by *text*, so a second `(f 2)` elsewhere would be the same type.
  That is Sheldon's design, and sound only under his purity and immutability
  conditions; the repo has chosen not to take it.
- The 1989 thesis's own answer for re-exporting an abstract type was a *new*
  abstraction, to keep abstraction control (the includer can then change the
  representation without changing the type's identity). A transparent alias
  gives that up: the includer's interface publicly says its `t` *is* m's
  `t`. [inf] This is the point of the feature, but it is a commitment: the
  combined module's type is meaningful only where `m` is in scope.
- FX-91 `extend` is binary and e1-wins. Thesis §4.1.4 flags name clashes as
  unresolved; `include` as "a name given twice an error" is a deliberate
  tightening, not something the sources decide. For `extend`, an e1
  component that shadows an *abstract or aliased* type that e0's surviving
  values mention is the interesting case: with select-aliasing the e0
  values keep `(select m t)` and stay well typed; with FX-91's rule they
  may not (§1).

**Open questions.**
1. **Is the alias a `desc` or a re-bound `abs`?** If the combined module
   exports `(desc t (select m t))`, outside users see through to `m`'s
   abstract type; if it exports `(abs t)` re-bound as an alias, `up-t` and
   `down-t` do not exist for it (the includer cannot make `t` values except
   via m's operations). [inf] The former matches Thesis §4.1.2.
2. **Escape of the combined module.** Its type mentions `m`. Returned from a
   scope where `m` is a `lambda` parameter or `let` variable, the type
   becomes a dependent-subroutine type (needs M5), or, for `let`, the
   definition is substituted in (LFP90 §2.2): for a variable bound by a
   module-producing call with reads, this is the case Sheldon makes illegal.
   Checking this at every `include`/`extend` site is the place a hole could
   hide. [inf]
3. **Globals.** A global `m` redefined later: `(select m t)` of the old and
   new `m` differ (`first-class-modules.md`, "Globals and the REPL"); the
   combined module made from the old `m` then has a stale alias. Same
   treatment as other uses of a redefined global is the repo's stated rule.
4. **Abstract regions and effects.** FX-91 allows `(abs e effect)`/`(abs r
   region)`; the thesis restricts abstractions to types and type constructors
   and says "There is no way to get a region or effect out of a dselect"
   (Thesis p. 23, p. 19 `FinallyType`), because of the effect-loophole
   concern (Design Constraint 3). [inf] Aliasing region/effect abstractions
   via `select` is therefore outside what the 1989 system justified; FX-91
   permits it (§2.2.6), but the soundness argument is not in these sources.
5. **Subtyping interaction (M4).** Inclusion on `dselect` is equivalence
   only (Thesis p. 34); a transparent alias made abstract again is the
   M4 "transparent where abstract expected" case. Not discussed in the
   thesis (no transparent descriptions yet); FX-91 inclusion rules for
   `desc`/`abs` are at §2.2.6.
6. **`(extend e0 e1)` with e1 referring to e0's names.** FX-91 makes e1 a
   binding-construct scope over e0's bindings. If FX-26's `extend` keeps
   that, e1's types see e0's abstract types as `(select e0 t)` already
   (FX-91 §2.3.19); that should then agree with the alias in the result,
   which is the consistency FX-91's printed rule leaves implicit.

## 5. FX-91's `extend`, re-read against the report (Claude, 2026-10-09)

Checked against `fx91-report.txt` (§2.3.5 `extend`, p. 15; §2.3.19 `with`,
p. 23; §2.2.9 `select`, p. 11), at the user's request: does "the bindings of
`v1` take precedence" say anything about the semantics *inside* the modules,
or only about how the result looks from outside?

- **Dynamic:** only the outside. `(extend e0 e1)` steps to
  `(*extend* v0 (with v0 e1))`, and the last step concatenates: `v0`'s
  bindings not named in `v1`, then `v1`'s. `v0`'s values are already closed
  over `v0`'s own bindings (`*rec*`, §2.3.11), so overriding `x` does not
  change what `v0`'s `f` calls `x`. There is no late binding.
  `e1` sees `e0`'s bindings through `with`. Its own definitions shadow them
  inside `e1`, because `with` substitutes `v0`'s values into `e1` and
  `e1`'s `module` binds its own names.
- **Static:** `e1` is typed as `(with e0 e1)`. The `with` rule's `θ` turns
  `e0`'s abstract `t` into `(select e0 t)`, its descs into their
  definitions, and its values into `(with e0 x)`. So `e1`'s types speak of
  `e0`'s abstractions as `(select e0 t)`. The result is
  `(moduleof (abs ida2…) (abs ida1…) (desc idd2…) (desc idd1…) (val idv2…) (val idv1…))`,
  where the `2` names are `e0`'s minus `e1`'s.
  The surviving `e0` items keep their types *as written in `e0`'s
  moduleof*. Two consequences follow from the printed rule; the report states neither:
  1. **Capture.** If `e1` also has an abstract `t`, `e0`'s `t` is dropped,
     but `e0`'s surviving `val`s still say `t`, which now names `e1`'s `t`.
     That is unsound when the two representations differ.
  2. **No interconversion.** `e0`'s surviving `t` is re-bound as the
     result's own `abs`, so through `r = (extend e0 e1)` `e0`'s values are
     at `(select r t)`. `e1`'s values that use it are at `(select e0 t)`.
     The two are distinct abstract types, so an `e1` value cannot be passed
     to an `e0` operation through `r`.
  Since `(with e0 e1)` requires a pure `e0`, `extend` does too.

The alias design (`desc t (select m t)` for a module included by name)
avoids both problems. `e0`'s values keep `(select m t)`, so nothing is
captured. Everything is at one type, so values convert both ways.

Our `extend` matches FX-91 dynamically: `e0`'s `f` keeps its own `x`, and
the probe gives `f` 1, `g` 110 and `x` 10. It differs statically in that
`e1` does *not* see `e0`'s bindings: `(extend a (module (define y int (+ x 1))))`
is `unbound variable x` in both checkers.

## Citation index

| Cite                             | Location                                                                                                                                       |
| -------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| Thesis                           | `docs/research/papers/sheldon-mit-1989-thesis-static-dependent-types-first-class-modules.pdf`                                                  |
| LFP90                            | `docs/research/papers/sheldon-gifford-lfp90-static-dependent-types-first-class-modules.pdf`                                                    |
| FX-91                            | `docs/research/papers/gifford-jouvelot-sheldon-otoole-fx91-report.pdf`                                                                         |
| Origin of the two Sheldon copies | `~/Dev/LangPlay/GiffordHistory/papers/{mthesis,lfp90}.pdf`, listed in its `README.md` as fetched from <https://groups.csail.mit.edu/cgs/pubs/> |
