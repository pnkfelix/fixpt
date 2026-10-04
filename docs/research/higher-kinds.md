# Higher-kinded type parameters for FX-26: two paths, and what they cost

Research note, 2026-10-02, answering the user's question: how feasible is it
for FX-26 to gain type parameters of kind `type -> type` (and deeper, e.g.
`(type -> type) -> type`), by extending the core's kinds (arrow kinds,
`poly`/`plambda`/`proj` generalized, type-level application `(f a)`), or by
letting a module's abstract component carry such a kind, with functors
(FX-26's dependent procedures) doing the abstracting, ML's way. Sources are
listed in full at the end, with where each was read and how much; a claim
marked *(from memory)* was not checked against a source during this note.
Every FX-26 program shown as "today" is a file under
`docs/research/examples/higher-kinds/`, checked with
`target/release/fixpt check` (both checkers agree) and run with
`target/release/fixpt eval`; syntax marked `; PROPOSED` exists nowhere.

## Status (2026-10-04): both paths built

Built in both checkers, which agree on every program in
`crates/fixpt-fx26/tests/programs/higher-kinds/`: Path 1 (arrow kinds in
the core, §5) and Path 2 (a module's abstract component of an arrow kind,
§6), together, and past FX-91 in one direction: a description function may
give an effect (`(=> region effect)`), applied inside effects as an atom
of its own. Inference is first-order, as §5.3 recommends. The rules that
keep it sound (§5.4 to §5.7) are in `docs/fx26.md`, "Higher kinds". What
this note says below about the code is as it was on 2026-10-02. The syntax
taken differs from the proposal below: an arrow kind is written `(=> (k1 …
kn) k)`, its parameters' kinds in a list, as a `lambda`'s are, not
`(=> k1 … kn k)`.

## 0. The answer, up front

- **Both paths are buildable; neither is free, and they are not the same
  size.** Path 2 (modules) is small and almost entirely already built: FX-26
  already has dependent procedures as functors (M5), modules already erase
  to products at run time regardless of a component's kind
  (`docs/research/first-class-modules.md`, "Run time"), and the one thing
  stopping an abstract component from carrying kind `(=> type type)` today is
  a single hard-coded `Kind::Type` in `name_module`
  (`crates/fixpt-fx26/src/modules.rs:149`) plus the test that documents the
  restriction on purpose
  (`crates/fixpt-fx26/tests/programs/modules/abs-kind.fx:1`). Path 1 (arrow
  kinds in the core: `poly`/`plambda`/`proj` over a function kind, type-level
  application `(f a)` inside ordinary types) is the more general feature —
  it would also make a `define-type`/`define-generative` parameter
  higher-kinded, and a `data`-kinded binder, and let a `define-generative`
  whose structure depends on a container parameter exist outside a module —
  but it touches `infer.rs`'s unification, `check.rs`'s subtyping (already at
  a documented divergence risk for cycles through `poly`,
  `docs/research/recursive-subtyping.md` §1, "Why `poly` diverges"), and the
  FX-26 mirrors of both, several of which are already within 10–40 lines of
  the 1000-line cap (`check-subtype.fx` 990/1000, `check-synth.fx` 977/1000,
  `check-resolve.fx` 973/1000, `check-infer.fx` 964/1000 — §6 below).
- **FX-26's own predecessor already built Path 1, in full, in 1991, and
  already used it for Path 2.** FX-91's kind language is `type | effect |
  (->> k1 ... kn)` (`fx91-report.pdf` §2.1.3 p.6, read directly); its
  `dlambda`/description-application give exactly a `poly`/`plambda`/`proj`
  over arrow kinds, kept decidable by excluding abstraction from the
  *unification* algebra, never attempting to solve a flexible higher-kinded
  variable against an arbitrary type (`crates/fixpt-fx91/src/kind.rs:44-55`,
  `unify.rs:228-242`, `subtype.rs:37,55-73`); and its module system already
  allows `(abs id k)` for any `k`, `DFunc` included
  (`crates/fixpt-fx91/src/modules.rs:149-150`, `finally_type`). FX-91's own
  subtyping of two different higher-kinded abstractions is a documented,
  preserved *bug* from the 1991 reference implementation
  (`crates/fixpt-fx91/src/subtype.rs:55-59`, `docs/divergences.md:120`) —
  worth knowing before repeating the shape of that code.
- **Neither path is on `PLAN.md`'s queue today.** "Soundness first" (`PLAN.md`
  line 132) puts S4–S5 ahead of any feature; GADTs (N4) are plan item 7, and
  this note's own motivating examples (`docs/research/gadts.md` lines 39,
  222, 260) already flag the missing kind as *why* two GADT encodings fall
  short, without asking for it to be built. Q8, "generic operations by
  dictionary" (`PLAN.md:2193-2200`), wants exactly a container-generic
  `map`/`fold`, and is the nearest real client.
- **A lighter interim exists and checks today, with no new syntax.**
  Tagless-final (`docs/research/examples/higher-kinds/tagless-final.fx`,
  already present as `docs/research/examples/gadts/eval-closures.fx`) sidesteps
  the missing kind by making every operation of an interpreter a *subroutine
  taking no further type argument*, at the cost of one interpreter per use.
  A closed, tag-dispatched union
  (`docs/research/examples/higher-kinds/closed-dictionary.fx`) gives a
  `map`-like function over a *fixed, enumerated* set of containers. Neither
  is open the way a real `Functor` class is. Yallop and White's
  defunctionalised "brands" (§8.3) do **not** port cleanly: their `app` type
  needs one representation shared, unsafely, across every brand, and FX-26
  deliberately has no unsafe cast to play that role (§8.3 is my own analysis,
  not from a source).
- **Recommendation: build Path 2 first, if and when a client needs it, and
  treat Path 1 as something to revisit only if Path 2's reach turns out too
  narrow.** §9 gives the reasoning and the open questions.

## 1. What FX-26 has today

**Kinds are seven flat constants, no arrows.** `enum Kind { Region, Place,
Effect, Type, Data, Size, Conv }` (`crates/fixpt-fx26/src/ast.rs:16-33`);
`Kind::fits` (`ast.rs:55-61`) relates `Place ≤ Region` and `Data ≤ Type` and
nothing else. There is no `KFun`/arrow/higher-kind variant anywhere in the
crate (grepped; none found), confirming the task's premise directly in code.

**Types already take a flat list of descriptions, never a partial one.**
`Ty::Named { which: u32, args: Vec<D> }` is a generative type applied to its
descriptions (`ast.rs:233-236`); `D` unifies the four non-kind description
domains, `Region(Region) | Effect(Effect) | Type(TyId) | Size(Size) |
Conv(Conv)` (`ast.rs:352-358`). A `Named` node's `args` is always exactly as
long as the `define-generative`'s own parameter list — there is no notion of
a type constructor *value* that can be applied to fewer arguments than it
declares, carried around, and applied later. `Ty::Poly { binders:
Vec<(DVar, Kind)>, body: TyId }` (`ast.rs:190`) and `Exp::PLambda { binders,
body }` / `Exp::Proj { body, args: Vec<D> }` (`ast.rs:379-380`) are
value-level polymorphism and its instantiation (`proj` applies a `poly`
*value* to its description arguments) — not a type-level function or type-level
application. Nothing plays the role of FX-91's `dlambda`/`(dx0 dx1 ... dxn)`
inside the *type* grammar.

**Parametric types are abbreviations and nominal families, both at kind
`type` (or a base kind) per parameter.** `define-type` with parameters is a
substitution-expanded abbreviation (`docs/fx26.md:1210-1213`); `define-datatype`
with parameters is a family that may mention itself non-expansively
(`docs/fx26.md:1179-1194`); `define-generative` with parameters makes a new,
opaque-to-comparison type, each parameter `(param kind [+|-])`, invariant
unless marked, a region or place parameter always invariant
(`docs/fx26.md:1034-1047`). Every one of these parameter lists is a flat list
of *base*-kinded binders (`type`, `region`, `effect`, `size`, `data`); none
can itself be `type -> type`.

**`poly`/`plambda`/`proj` generalize over base kinds only**, matching `Ty::Poly`
and `Exp::PLambda`/`Exp::Proj` above; `region-parameter.fx`
(`crates/fixpt-fx26/tests/programs/modules/region-parameter.fx`) is today's
working example of a `plambda ((k region))` producing a module, which is the
base case Path 2's functors generalize.

**Modules exist (M1–M5, M7, `docs/fx26.md:864-923`), and their abstract
component is kind `type` only, enforced in one place.** A module's abstract
components come only from `define-generative`
(`ModItem::Abs { name, var, rep: TyId, ... }`, `ast.rs:429-433`), whose `rep`
is a `TyId`: a type, never an effect or region (contrast FX-91's
`define-abstraction`, any kind, below). When a module value is bound to a
name, each abstract binder is freshly renamed **at a hard-coded
`Kind::Type`**: `let w = self.arena.dvar_of(named, Kind::Type);`
(`crates/fixpt-fx26/src/modules.rs:149`). The restriction is deliberate and
tested: `tests/programs/modules/abs-kind.fx` is one line, `(define-type bad
(moduleof (abs t region) (val zero t)))`, with the comment `; ! an abstract
component is a type, for now` — i.e. it is expected to be *refused*. Dependent
procedures (M5, "functors, of which ML's are a restricted form",
`docs/fx26.md:897-899`) are ordinary `subr`s whose later parameters' types
name an earlier module parameter by `(select $k t)`
(`Ty::ParamSel(usize, Sym)`, `ast.rs:246`), resolved at a call site by
`Checker::dependent_args` (`modules.rs:324-352`), which requires the argument
be a bound variable (a `let`-bound module is opaque, Sheldon's rule,
`docs/fx26.md:886-888`). A module is erased to a product of its values at run
time; abstract, transparent, region and effect components carry nothing at
run time (`docs/research/first-class-modules.md`, "Run time", confirmed by
`modules.rs` having no run-time-facing code at all — the whole 358-line file
is checker-side).

**Two checkers, by design, must agree word for word.** The Rust checker
(`check.rs` 2643 lines, `infer.rs` 1449, `parse.rs` 1792, `modules.rs` 358)
has a mirror written in FX-26 itself, split across files because of the
1000-line/100-column cap on hand-written `.fx`
(`fx-size-limits-by-extraction`, confirmed live at `PLAN.md:124-130`: "every
hand-written `.fx` file is within both ... the debt list is empty"). The
files nearest the cap are exactly the ones a new kind-checking or
kind-directed-unification pass would touch:

| file (`crates/fixpt-fx26/src/`) | lines | of 1000 | what it does                                                 |
| ------------------------------- | ----- | ------- | ------------------------------------------------------------ |
| `check-subtype.fx`              | 990   | 99%     | subtyping, errors, calls that may not end                    |
| `check-syntax.fx`               | 993   | 99%     | the parser's description half                                |
| `check-terminate.fx`            | 992   | 99%     | size-change termination                                      |
| `check-synth.fx`                | 977   | 98%     | each expression's type and effect                            |
| `check-resolve.fx`              | 973   | 97%     | resolving descriptions, masking, **substitution**            |
| `check-infer.fx`                | 964   | 96%     | **instantiation**, `tagcase`, what synthesis needs           |
| `parser.fx`                     | 939   | 94%     | the parser                                                   |
| `check-program.fx`              | 922   | 92%     | top-level definitions and redefinition                       |
| `check-types.fx`                | 835   | 84%     | the Rust checker's rules, rule for rule                      |
| `check-print.fx`                | 834   | 83%     | printing types and effects                                   |
| `check-modules.fx`              | 406   | 41%     | modules' descriptions (M2)                                   |
| `check-module-rules.fx`         | 386   | 39%     | modules' rules: `module`, `with`, module types compared (M2) |
| `check-dependent.fx`            | 234   | 23%     | dependent procedures (M5)                                    |

(line counts from `wc -l`, 2026-10-02.) A new kind form touches `check-types.fx`
(rules), `check-infer.fx` (instantiation of a new binder shape), `check-resolve.fx`
(substitution through a new application node) and `check-subtype.fx`
(a new comparison case) at minimum — four files, three of them past 96% of
the cap already. The module files have headroom; see §6.

**Regions and effects are kinds of parameter too, and a type operator would
have to answer to them.** A generative type's parameter list already mixes
kinds freely, e.g. `(nlist T size)`, `(arrayof T R)`; `docs/fx26.md:1196`
treats `arrayof`/`make-array` as "ordinary polymorphic constants", and
`vsubr`'s declared variance is `(vsubr (e effect +) (t type -) (r type +))`
(`docs/fx26.md:945-947`) — three different kinds in one parameter list,
already. So a container of kind `type -> type` in FX-26 is really asking "can
`f` in `(f a)` also need a region or an effect to make sense of `a`?" — e.g.
`(f a r)` for a container that must know where its payload lives. §5.5 and
§6.5 take this up per path.

**Equi-recursive structural types are graphs; `define-generative`'s
recursion is iso-recursive through the name.** FX-26 kept FX-87's
equi-recursive `dletrec`/cyclic types for ordinary structural recursion, and
added `define-generative` as a second, nominal route whose own recursion is
never unfolded to compare (`docs/fx26.md:1055-1056`;
`docs/research/recursive-subtyping.md` §2(b), "Recommendation: stay
equi-recursive"). Subtyping over a cycle through `poly` **already
diverges** today without special handling (prototype fix in `d260522`, not
yet ported to the FX-26 mirror, `recursive-subtyping.md` §1, "Why `poly`
diverges" and the `polycycle2`/`polyvar`/`polyonly` probes) — a new binder
shape inside `poly` inherits that open risk before it adds any of its own.

## 2. Why this already bites, in this repository's own notes

`docs/research/gadts.md`, written 2026-09-27 while surveying GADTs, already
names the missing kind three times, independently of this note:

- "GADT refinement needs evidence FX-26 cannot state today: no existentials,
  no refinement in `tagcase` arms, **no kinds like `type → type`**"
  (`gadts.md:39`).
- The tagless-final evaluator, `eval-closures.fx`: "an expression can no
  longer be inspected, printed or optimized; **abstracting over the
  interpreter needs a kind `type → type`**" (`gadts.md:222`).
- The type-equality witness, `eq-coercions.fx`: "proves nothing ... **Leibniz
  equality (`forall f. f a -> f b`) would be a proof, but needs a kind `type
  → type`**" (`gadts.md:260`).

Both motivating examples already exist as checked FX-26 programs
(`docs/research/examples/gadts/eval-closures.fx`,
`docs/research/examples/gadts/eq-coercions.fx`) and are reused as this note's
own "lighter interim" in §8.1. `PLAN.md`'s Q8, "Generic operations by
dictionary" (`polytypic.md`, revised by decision 4): "generic `equal`,
`hash`, `->datum`, `compare`, `map`/`fold` as one definition each over a type
representation or a dictionary" (`PLAN.md:2193-2200`) is the plan item this
note is closest to serving — a container-generic `map` is exactly a `Functor
f ⇒ map :: (a -> b) -> f a -> f b`.

## 3. FX-91's precedent: `Kind::DFunc` and `dlambda`, read directly

FX-91's kernel already has Path 1, built and tested, in `crates/fixpt-fx91`.
Read directly from the FX-91 report (`~/Dev/LangPlay/GiffordHistory/papers/
fx91-report.txt`, §§2.1–2.2.6, the formal grammar and semantics, pp. 6–10,
read in full) and the Rust reimplementation (`kind.rs` full, 214 lines;
`ast.rs`, `modules.rs`, `unify.rs`, `subtype.rs`, `evaluate.rs`, the relevant
functions read in full).

**The grammar** (`fx91-report.txt` lines 272, 343; §2.1, §2.2 pp. 6–8):

```
k  ::= type | effect | (->> k1 ...kn)
dx ::= tx | (dlambda ((id1 k1)...(idn kn)) tx) | di
ti ::= ... | (di di1 ...din) | ...
```

A `(->> k1 ... kn)` is the kind of an n-ary description-level function to a
type (not curried — FX-91 flattens application and abstraction to lists, the
same choice as its `maxeff` and `productof`); `dlambda` is the constructor,
`(dx0 dx1 ... dxn)` the application. Both **static and inclusion** semantics
are given (`fx91-report.txt:377-434`):

```
TK ⊢ dx0 :: (->> k1 ...kn)      TK ⊢ dxi :: ki (1 ≤ i ≤ n)
----------------------------------------------------------
TK ⊢ (dx0 dx1 ...dxn) :: type

((dlambda ((id1 k1)...(idn kn)) tx) dx1 ...dxn) ~ [dxi/idi]tx      -- beta
(dlambda ((id1 k1)...) (tx id1 ...idn)) ~ tx,  idi ∉ FV(tx)         -- eta
```

**The Rust port matches this exactly**, and is where the decidability answer
lives in code, not just in a 1993 report:

- `Kind::DFunc(Vec<Kind>)` (`crates/fixpt-fx91/src/ast.rs:51`), kind-checked
  by `kind_of_dexp_1` (`kind.rs:44-55` for `DLambda`, requiring the body have
  kind `Type`; `kind.rs:149-168` for `DApp`, requiring the **already-known**
  kind of the operator be `DFunc`, and each argument's kind to match
  positionally). **Kind-checking is purely declarative here: nothing is
  inferred, only checked against what a `dlambda` or a module's `abs`
  declared.**
- **Normalization, not unification, resolves most of the work.**
  `Checker::evaluate` performs beta and eta reduction on descriptions before
  comparing them (`evaluate.rs:1-16`, doc comment: "Descriptions are a little
  lambda calculus of their own, so comparing two of them means reducing both
  first"); eta turns `(dlambda (x...) (f x...))` back into `f`
  (`evaluate.rs:182-200`, `eta_reduce`). This terminates because the
  description calculus is simply-kinded with no fixed-point former at the
  kind level — there is nothing in `k ::= type | effect | (->> k...)` for a
  `dlambda`'s body to loop through.
- **Unification of a `DApp` node is first-order congruence, never
  higher-order solving.** `unify_dapplication`
  (`crates/fixpt-fx91/src/unify.rs:432-452`) requires **both** sides already
  be `DApp` nodes, unifies rator with rator and each rand with each rand
  positionally, and otherwise fails — it never attempts to solve a flexible
  (unification) variable of kind `DFunc` applied to an argument against an
  arbitrary type. A `DFunc`-kinded unification variable can only be *bound
  outright* by `unify_on_unification`'s occurs-check-then-forward
  (`unify.rs:163-179`), i.e. treated as a first-order metavariable over whole
  dlambda terms — exactly the restriction the task description names: `f` is
  a rigid head, matched, never decomposed through higher-order unification.
  This is the FX-91-native version of Jones's and Miller's restriction (§4.1,
  §4.4).
- **Subtyping of two different `dlambda`s is a documented, preserved bug.**
  `dlambda_leq` (`crates/fixpt-fx91/src/subtype.rs:55-73`) recurses on itself
  over the bodies instead of calling the general `description_leq`; since a
  `dlambda`'s *body* has kind `type`, not `(->> ...)`, the recursive call's
  pattern match fails immediately, so **two dlambdas essentially never
  compare** by this path. The comment says why it is kept: "reproduces a
  second bug in the 1991 source ... preserved for the same reason as
  `unify_poly`'s bug: the reference defines what FX-91 accepts," cross-
  referenced at `docs/divergences.md:120`. This is a cautionary, primary-
  source data point: even the *original* 1991 implementation of exactly this
  feature shipped with a subtyping gap around two distinct higher-kinded
  abstractions, not caught for decades, because it never mattered to its own
  conformance suite.
- **The module system already allows any kind for `abs`, `DFunc` included.**
  `finally_type` (`crates/fixpt-fx91/src/modules.rs:149-150`): `matches!(k,
  Kind::Type | Kind::DFunc(_))` — "a kind that ultimately classifies types,
  so a coercion can be built." `make_ups` (`modules.rs:152-192`) builds the
  `up-`/`down-` coercions: for `Kind::Type`, an ordinary `(rep -> id)`
  subroutine; for `Kind::DFunc(kinds)`, it introduces fresh description
  parameters of those kinds, applies both `rep` and `id` to them via `DApp`,
  recurses at `Kind::Type` for the applied form, and wraps the result in a
  `Poly` over the fresh parameters — i.e. `up-id : (poly ((a k1) (b k2) ...)
  (-> pure ((rep a b ...)) (id a b ...)))`, exactly
  `docs/research/generative-types.md:25`'s own paraphrase of the report ("At
  higher kinds they are polymorphic"). **This is Path 2, already built, in
  1991, as a side effect of Path 1 already existing.**

The report's own words on why this stays decidable, from the kind-checking
rule's shape alone (not stated as a theorem in the report; my own reading of
the rule): kind-checking an application never needs to *guess* the operator's
kind — `TK ⊢ dx0 :: (->> k1...kn)` is a premise, found by looking `dx0` up
or kind-checking it structurally, never solved for. The report's "Kinds have
neither static nor dynamic semantics" (`fx91-report.txt`, §2.1 header, p.6)
undersells this a little: kinds *are* checked (every description expression
has one, found compositionally), just never *inferred* by unification the
way types are.

## 4. The theory, independent of FX-26

### 4.1 Jones's constructor classes: decidable by excluding abstraction from unification

Mark P. Jones, *A System of Constructor Classes: Overloading and Implicit
Higher-Order Polymorphism* (FPCA 1993; `docs/research/papers/
jones-fpca93-constructor-classes.pdf`, read in full, 10 pages). Jones
extends Haskell's type classes to classes of *type constructors* (`class
Functor f where map :: (a -> b) -> (f a -> f b)`), with a kind system `κ ::=
∗ | κ1 → κ2` (§1.3) and, crucially, **excludes lambda-abstraction from the
language of constructors**: `C ::= χ (constants) | α (variables) | C C′
(applications)` (§3.1) — no binder. The paper states the consequence
explicitly, twice:

> "The decision to exclude any form of abstraction from the language of
> constructors is essential to ensure the tractability of the whole system."
> (§5, p.10)

> "This property would be lost if we had included abstractions over
> constructor variables in the language of constructors requiring the use of
> higher-order unification and ultimately leading to undecidability in the
> type system." (§3.4.1, p.8, after Theorem 1)

With no binder, "unification" of constructors is ordinary first-order term
unification extended to check kinds at each `bindVar` step (Figure 2, p.8),
with a most-general-unifier theorem (Theorem 1). **Kind inference**, applied
to the *surface* syntax (where the programmer writes no kind annotations at
all), is a second, separate, simple constraint-propagation pass over the
same combinator structure (§4): find each constant's kind, each class's
arity, each quantified variable's kind, by unifying kind variables — no
polymorphic kinds are inferred (`Fork a = Prong | Split (Fork a) (Fork a)`
could have kind `κ → ∗` for any `κ`; "the current implementation ... replaces
any unknown part of an inferred kind with `∗`", §4.1, i.e. **defaulting**,
the same move GHC's Haskell98 mode makes, §4.2 below). This is the complete
template both FX-91's `DFunc`/`dlambda` (declared kinds, no kind inference at
all, since every binder is explicitly kinded) and this note's Path 1 (§5)
would need to match for decidability: **keep kind-level application
unification first-order by never putting a binder in the kind-indexed
language types range over.**

### 4.2 Haskell's kind system and its own first-order unification of constructor application

Modern GHC's kind language is dependently-typed and much richer than Jones's
`κ ::= ∗ | κ1 → κ2` (kind polymorphism, `Type :: Type`, promoted data kinds),
but the *application* discipline at its base is the same: a kind like
`AppInt :: (★ → ★) → ★` is checked, and `AppInt Bool` is ill-kinded because
`Bool` does not have the arrow kind `AppInt`'s parameter needs
(`docs/research/papers/xie-eisenberg-oliveira-popl20-kind-inference.pdf`,
Ningning Xie, Richard A. Eisenberg, Bruno C. d. S. Oliveira, *Kind Inference
for Datatypes*, POPL 2020, read pp. 1–3: abstract, introduction, §2.1
directly). Two facts from that paper bear directly on Path 1's inference
story:

- **Haskell98's kind inference, like Jones's, is sound but not complete, and
  the gap is closed by defaulting, not by solving harder equations.**
  "Haskell98 solves this problem by using a defaulting strategy: if the kind
  of a type variable cannot be inferred, then it is defaulted to ★ ... we
  believe ours is the first formalization of this historically important
  aspect of Haskell98" (p.2, §2.1). The paper is, by its own account, the
  first rigorous study of something every Haskell implementation has done
  informally since 1998 — a sign the question is genuinely subtle even in a
  mature, widely-used system, not merely unexplored.
- **Adding dependent kinds (kind-indexed unification, `kind-directed
  unification`) risks non-termination, and only a "subtle proof" rules it
  out**: "our kind-directed unification appears to risk divergence, yet we
  provide a subtle proof that it is indeed terminating" (p.3, §2.2). This is
  the same shape of risk `recursive-subtyping.md` already found in FX-26's
  *existing* `poly` subtyping (cycles through `poly` diverge today, §1
  above) — a new binder inside `poly` is exactly where Haskell's own kind
  system needed a non-obvious termination argument.

GHC's kind-checking of an applied type constructor (`Maybe Int`, `f a`) is,
at base, exactly Jones's first-order constructor unification: the head's
kind must already be (or be inferred to be) an arrow whose domain the
argument's kind matches — I did not re-derive GHC's unifier from a primary
source beyond this paper, so the general claim that GHC's *constructor
application* unification is first-order in the same sense as Jones's is
*(from memory)*, though consistent with everything the POPL20 paper's
introduction says about the lineage ("Haskell98 accepts higher-kinded
polymorphism... Jones [1995] presents one of the few extensions of HM that
deals with a non-trivial language of kinds," p.2). This is independently
corroborated, in more formal terms, by Rémy's course notes (§4.3 below):
Haskell's type-operator application is literally modelled as an
*uninterpreted first-order symbol*, not a reducible redex, which is exactly
what buys it first-order-unification-compatible inference at the cost of
falling short of full Fω.

### 4.3 System F-omega: the checking ceiling, and what breaks it

Didier Rémy, *Type systems for programming languages* (MPRI course notes,
2020–2021; `docs/research/papers/remy-mpri-system-fomega.pdf`, a 39-page
extract — Ch. 7, "System Fω: higher-kinds and higher-order types" — read
directly, pp. 121, 124–126, 133–134: the introduction, Figure 7.1's full
kinding/typing rules, §7.2.1 "Properties", §7.3.2 "Abstracting over type
operators", and §7.4.3 "Recursion"). Fω (Girard) gives the full theory of
arrow-kinded, explicitly-typed type operators: `κ ::= ⋆ | κ⇒κ`, `τ ::= α |
τ→τ | ∀α::κ.τ | λα::κ.τ | τ τ`, with a `KApp` rule exactly matching this
note's proposed `Ty::App` (Figure 7.1, p.124). §7.2.1 states the decidability
argument precisely, as three separate properties, not one:

> "Termination of reduction. This holds in the absence of other constructs
> that can be used to introduce recursion, such as recursive types, recursive
> definitions or side effects... Typechecking is decidable. This requires
> reduction at the level of types to check type equality. Checking type
> equality can be performed by putting types in normal forms... Normal forms
> for types exists as the language of type is a simply-typed λ-calculus
> (where kinds plays the role of types)." (p.125)

So **type-checking is decidable because the type-level calculus, kinds and
all, is itself simply-typed and strongly normalizing — not merely because
binders are annotated**, a sharper statement than this note's first draft
made. §7.3.2 then states, independently and in more formal terms, exactly
the restriction §4.1–4.2 attribute to Jones and to GHC's constructor-application
unification:

> "In fact type abstraction over type operators is already available in
> Haskell, but does not handle β-reduction. In this case, type application
> `φ α` behaves as a first-order type `App(φ,α)` where App is a binary
> (application) symbol of kind `(κ1⇒κ2)⇒κ1⇒κ2`. That is: `φ α = ψ β ⟺ φ=ψ ∧
> α=β`. The expressiveness is then closer to System F than to System Fω. As a
> counterpart of this limitation, this approach is compatible with type
> inference, based on first-order unification." (p.126)

This is the same move FX-91 made (§3) and this note's Path 1 §5.3 recommends:
treat type-level application as an *uninterpreted, injective, first-order
constructor* rather than a reducible redex, trading Fω's full expressiveness
for first-order-unification-compatible inference. (The same section's
`monad ≜ λφ.{ret:..; bind:..} : (⋆⇒⋆)⇒⋆` example (p.126) is a published,
independent confirmation that a monad/container abstraction genuinely needs
higher-order *kinds*, corroborating §5.1's `(=> (=> type type) type)`
example.)

**§7.4.3, "Recursion," answers this note's own open question (§5.7, §9 Q4)
directly — equi-recursive types combined with higher-order kinds is a known,
separately-studied hard case, not a detail this note had to work out alone:**

> "Checking equality of equirecursive types in System F is already non
> obvious, since unfolding may require α-conversion to avoid variable
> capture... **With higher-order types, it is even trickier, since unfolding
> at functional kinds could expose new type redexes.** Besides, the language
> of types would be the simply typed λ-calculus with a fix-point operator:
> type reduction would not terminate. Therefore type equality would be
> undecidable, as well as type checking. **A solution is to restrict to
> recursion at the base kind ⋆. This allows to define recursive types but not
> recursive type functions.** Such an extension has been proven sound and
> decidable, but only for the weak form of equirecursive types (with the
> unfolding but not the uniqueness rule) — see Cai et al. (2016)." (p.134,
> citing Cai, Giarrusso, Ostermann et al. 2016, not independently read for
> this note)

This resolves §5.7's open question with a citable answer, not just an
analogy to `structural-adts.md`'s unbuilt "whnf on demand" design: **FX-26's
`Ty::App` should never itself be the thing a `dletrec`/`mu`-cycle recurses
through — only its fully-reduced, base-kinded (`type`) result may. A
recursive type family parametrized by a higher-kinded variable `f` (`(define-
type (wrap (f (=> type type))) (f (wrap f)))`, say) is exactly the case Rémy
shows is undecidable in general and should be refused**, while an ordinary
recursive type that merely *contains* a `Ty::App` at base kind (`(define-type
t (sumof (leaf int) (node (f t))))` for a already-resolved `f`) is the "weak
equirecursive" case Cai et al. show decidable — which is already FX-26's
existing equi-recursive machinery, untouched. §9's open question 4 is updated
accordingly below.

Every remaining difficulty this note surveys (Jones's restriction, Miller's
pattern fragment, Haskell's defaulting, Rossberg's warning in §4.5) is
specifically about *inference* — recovering kinds and type arguments the
programmer did not write — not about checking fully-annotated programs,
which FX-26 already does well (its whole design is bidirectional checking
over inference, `docs/fx26.md` decision 3, `docs/research/modules.md:747`).
This matters for scoping: if FX-26 requires declared parameter kinds and
declared signatures wherever a higher kind appears (as FX-91's
`dlambda`/`abs` already do, and as `poly`/`plambda` already require today for
every binder), the *checking* story is close to free; the *inference* story
is where all of §4.1–4.2, §4.4–4.5's cited restrictions earn their keep.

### 4.4 Higher-order unification, and the Miller-pattern restriction FX-91 already takes

Dale Miller, *A Logic Programming Language with Lambda-Abstraction, Function
Variables, and Simple Unification* (expanded version of the paper that
introduced the decidable "Miller pattern" fragment, `L_λ`;
`docs/research/papers/miller1991-pattern-unification.pdf`, read pp. 1–2,
abstract and introduction, directly). The paper states the dividing line the
task description asks about exactly:

> "Huet and Lang described how such an approach, when restricted to
> second-order matching, can be used to analyze and manipulate simple
> functional and imperative programs... The general problem of the
> unification of simply typed λ-terms of order 2 and higher is undecidable."
> (p.2, citing Huet 1976/Goldfarb 1981 for the undecidability result, Huet
> and Lang 1978 for decidable second-order *matching*)

> "`L_λ`... term language... is the simply typed λ-calculus with equality
> modulo α, β, and η-conversion. The 'β-aspects' of `L_λ` are, however,
> greatly restricted and, as a result, unification in this language
> resembles first-order unification — the main difference being that
> λ-abstractions are handled directly." (p.2)

The restriction that buys decidability (Miller's own later papers name it
the *pattern* condition, not stated in the pages read here but well known
*(from memory)*) is: **a flexible (unification) variable may only be applied
to a list of distinct, universally-bound variables** — never to an arbitrary
term, and never to a repeated variable. Under that restriction a unification
problem has at most one solution (up to equivalence) and finding it is a
first-order-style algorithm; outside it, general higher-order unification is
undecidable and may have infinitely many incomparable solutions. **This is
exactly the task's own example**: solving `(f a)` against `(listof int r)`
for a flexible `f` of kind `(=> type type)` is a pattern (`a` is a single,
distinct bound/rigid variable) only if `a` is literally the *only* way `int`
and `r` occur, and even then the solution `f := (plambda (x) (listof x r))`
vs. `f := (plambda (x) (listof int r))` (ignoring `x`, i.e. a constant
function) are both unifiers unless something (the pattern condition's usual
side-clause, or an explicit annotation) picks one. FX-91 does not attempt
this at all (§3 above): a `DFunc`-kinded unification variable is only ever
*bound outright*, never pattern-unified against an application. This is the
cheaper, blunter version of the Miller restriction, and the one this note
recommends FX-26 copy if it ever builds Path 1 (§9).

### 4.5 ML modules, functors, and 1ML: higher-kinded polymorphism without touching the core

Standard ML and OCaml give higher-kinded abstraction *for free*, at the
module level, because a signature may say `type 'a t` (a genuine type
constructor, parametric in a core-language sense) and a functor may abstract
over a structure matching that signature — e.g. `functor
MakeFunctor(F : sig type 'a t val map : ('a -> 'b) -> 'a t -> 'b t end)`.
This is exactly Jones's `Functor f` reborn as a module signature, and is
Path 2's entire premise, independently confirmed by a system that has
shipped in production compilers since the 1990s *(from memory — the ML
module literature on this point is large; not independently re-verified
against a primary source for this note beyond what Rossberg's 1ML paper
says about it directly, below)*.

Andreas Rossberg, *1ML — Core and Modules United* (JFP;
`docs/research/papers/rossberg-1ml-jfp.pdf`, read directly: pp. 2–3
(motivation), pp. 12–13 (applicative functors), pp. 15–16 (predicativity),
pp. 24–25 (elaboration of higher kinds)). 1ML's own motivation section
states, as a *reason not to add higher-kinded polymorphism to ML's core*,
exactly the risk this note's Path 1 carries:

> "Worse, because core-level polymorphism is first-order, this approach
> cannot express type sharing between type constructors — a complaint that
> has come up several times on the OCaml mailing list. For example, if one
> were to abstract over a monad: `val map : (module MONAD with type 'a t =
> ?) -> ('a -> 'b) -> ? -> ?` ... it would require a type variable of higher
> kind, which is not supported in ML... One could imagine addressing this
> particular limitation by introducing higher-kinded polymorphism into the
> ML core. **But with such an extension type inference would require
> higher-order unification and hence become undecidable** — unless
> accompanied by significant restrictions that are likely to defeat this
> example (or others)." (p.3)

1ML's own answer is Path 2, taken further than FX-26 would need to: it
unifies the core and module languages so that **"pure functions over `type`
readily subsume abstract type constructors"** (p.24) — a type constructor
*is* a (1ML) functor, and "all semantic types are Fω types of kind Ω, even
those that are the equivalent of higher kinds, such as `type ⇒ type`" (p.24).
Decidability is bought not by restricting kinds but by a **predicativity**
restriction orthogonal to kind structure: during subtyping/signature
matching, an abstract-type slot can only be filled by a *small* type, one
that itself contains no further `type` component — "small types thus exclude
first-class abstract types, actual functors ..., and type constructors
(which are just functors)" (p.15–16). Applicative-functor semantics (sealing
a fully transparent functor gives a type constructor usable as a path, so
`map int` compares equal to itself across uses, Leroy 1995/Rossberg, Russo
and Dreyer 2014) is needed to make the resulting "type constructor" behave
like one (p.12–13). **None of this needs higher-order unification anywhere**
— module-level application is checked (a functor's parameter signature is
declared), and the identity question ("is this applied functor the same
type as that one") is settled by Sheldon's own textual/path equality
(`docs/research/modules.md` §2, already FX-26's chosen rule,
`docs/fx26.md:885-888`), not by solving for an unknown functor. This is the
central argument for Path 2 over Path 1 in FX-26 specifically: **FX-26
already has exactly 1ML's "functors instead of higher-kinded core
polymorphism" shape (dependent procedures, M5), already compares module
paths textually/by binding rather than by unification, and already erases
modules to products at run time** — the missing piece really is the one
line at `modules.rs:149`, not a new inference algorithm.

### 4.6 Scala's higher-kinded types *(from memory)*

Scala has supported native higher-kinded type parameters since early
versions: `trait Functor[F[_]] { def map[A, B](fa: F[A])(f: A => B): F[B] }`,
with `F[_]` a kind annotation (kind `* -> *`) checked, not inferred from
scratch, the same discipline as Jones's constructor classes and Haskell's
`class Functor f`. Scala's `implicit`/`given` mechanism is dictionary
passing for exactly this shape of class, compiled by the usual
dictionary-passing translation (Wadler and Blott 1989, cited by Jones
directly, §3.5) — the same mechanism FX-26's own "dictionaries and tags over
specialization" decision already commits to (`PLAN.md:1899-1905`). I did not
fetch a primary source on Scala's kind-checking algorithm for this note;
this paragraph is from memory and should be treated as orientation, not a
citation-grade claim.

### 4.7 Rust's GATs: a deliberate, narrower alternative

Rust RFC 1598, "Generic Associated Types" (`rust-lang.github.io/rfcs/1598-
generic_associated_types.html`, fetched and read directly). GATs let a
trait's *associated type* take its own generic parameters — the RFC's own
framing is "Allow type constructors to be associated with traits" — e.g. a
`StreamingIterator` whose `type Item<'a>;` makes `next`'s returned item
borrow from the iterator call itself, rather than from the iterator's whole
lifetime. The RFC is explicit that this is **not** full higher-kinded
polymorphism and says so directly:

> "This does not add all of the features people want when they talk about
> higher-kinded types. For example, it does not enable traits like `Monad`."

GATs give a trait author a type *indexed by* a parameter (closer to a
dependent family than to a quantified type constructor); they do not give
Rust a `trait Functor<F<_>>`-shaped way to quantify a trait or a function
over an unknown type constructor the way Jones's constructor classes,
Haskell's `class Functor f`, or Scala's `Functor[F[_]]` do (§4.1, §4.6). This
is useful orientation for FX-26 by contrast: GATs are closer in spirit to
FX-26's own parametric `define-datatype` (`docs/fx26.md:1179-1194`, which
already lets a family's variant mention itself at *other* descriptions,
non-expansively) than to either path this note evaluates — neither Path 1
nor Path 2 as scoped here is "just GATs," and a GAT-shaped narrower feature
was not separately explored for this note. Rust's own motivation for the
narrower feature (implementation/inference cost of full HKT) was not found
stated explicitly in the RFC text fetched; that specific claim remains
*(from memory)*.

### 4.8 Yallop and White: lightweight higher-kinded polymorphism by defunctionalisation

Jeremy Yallop and Leo White, *Lightweight Higher-Kinded Polymorphism*
(FLOPS 2014; `docs/research/papers/
yallop-white-flops14-lightweight-higher-kinded-polymorphism.pdf`, read
directly via local text extraction, pp. 4–6, §1.3 and the start of §2).
OCaml, like FX-26, has no kind `type -> type` for core-language type
variables. Their technique is literally *defunctionalisation applied to
types*: introduce one abstract carrier type

```
type ('a, 'f) app
```

and, per container, an opaque phantom **brand** type `t` plus a pair of
conversions:

```
module List : sig
  type t
  val inj : 'a list -> ('a, t) app
  val prj : ('a, t) app -> 'a list
end
```

so that `(a, List.t) app` *stands for* `a list` without `app` itself ever
being kind-polymorphic; generic code is written once, abstracting over the
brand: `val when : 'm #monad -> bool -> (unit, 'm) app -> (unit, 'm) app`
(p.5). A `Newtype1`/`Newtype2` functor family (p.6) generates a brand plus
`inj`/`prj` for a 1-parameter or 2-parameter concrete type constructor,
currying the second parameter so it can still be partially applied. The
paper's own framing: "we can change a program with [higher-kinded types]
into a program [without them]... much as the `apply` function makes it
possible to embed the application of a higher-order function in a
first-order defunctionalized program" (p.5). *(I read this via local text
extraction rather than the rendered PDF; §8.3 below works out, as my own
analysis rather than the paper's, whether and how this ports to FX-26.)*

## 5. Path 1: arrow kinds in the core

### 5.1 Syntax and kinds

Add one `Kind` variant, following FX-91's own choice of a flat, n-ary (not
curried) arrow to keep deeper towers (`(type -> type) -> type`, needed for a
monad-transformer-shaped container) expressible without a separate currying
step:

```
Kind::Arrow(Vec<Kind>)   // "(=> k1 ... kn type)"; FX-91's DFunc is the precedent
```

Surface syntax, following the task's own suggestion and FX-91's `(->> k1
... kn)`:

```scheme
; PROPOSED
(poly ((f (=> type type))) ...)             ; f ranges over type -> type
(poly ((f (=> type type type))) ...)        ; f ranges over type -> type -> type
(poly ((f (=> (=> type type) type))) ...)   ; f ranges over (type -> type) -> type
```

A new binder form in `poly`/`plambda` (today's `binders: Vec<(DVar, Kind)>`,
`ast.rs:190,379`, already accepts any `Kind`, so **the AST needs no change
here** — only the parser's binder-kind grammar and the new `Kind::Arrow`
case) and a new type-level application node:

```
Ty::App { fun: TyId, args: Vec<TyId> }   // "(f a)", "(f a b)"
```

(today's closest cousin, `Ty::Named { which, args }`, is a *fully applied,
fixed-arity* generative type — `Ty::App` is new because `fun` may be a
*variable* of arrow kind, not a known `define-generative`.)

### 5.2 Checking

A kind-checking pass, following §3's FX-91 model directly: every type
expression synthesizes a `Kind` compositionally (`Ty::App`'s rule: `fun ::
(=> k1 ... kn type)`, each `argi :: ki`, result `:: type`, exactly
`fx91-report.txt:377-379`'s rule transliterated); a `poly`/`plambda` binder's
kind is declared, never inferred (matching today's binders, which already
carry an explicit `Kind`). This is new logic in `check.rs`'s type-checking
core and its FX-26 mirror — most naturally in `check-types.fx` (835/1000,
room) and wherever `check-resolve.fx` (973/1000, nearly full) does
substitution, since a new node needs a new substitution case.

### 5.3 Inference: the restriction to take, worked

The task's own example: solving `(f a)` against `(listof int r)` for a
flexible `f`. §4.1 and §4.4 give the two established exits, and §3 shows
FX-91 already picked the cheaper one:

- **Jones's exit: never let `f` be a *unification* variable applied to an
  argument in the first place.** Constructor-class-style systems only ever
  unify `(f a)` against `(f a')` (both sides already applications with the
  *same* head) or `(f a)` against `(g b)` where `f`/`g` are both rigid —
  congruence, never "solve for `f`." A program that needs to *infer* which
  container `f` is from a call site like `(the-generic-map inc xs)` with
  `xs : (listof int r)` must instead have `f` determined by `xs`'s already-
  known type directly (ordinary first-order unification of `xs`'s type
  against the *expected* parameter shape, with `f` read off, not solved for)
  — which only works if the expected parameter shape already names `f`
  applied to a bound/rigid variable in exactly the pattern `(f a)`, `a` not
  otherwise occurring; FX-26's own `unify.rs` (today, no higher kinds)
  already works this way for `Ty::Named`'s arguments (matched positionally,
  `infer.rs`'s `unify`, confirmed by `docs/research/recursive-subtyping.md`
  §1, "Matching (`infer.rs`)": "one-sided matching ... matches cyclic
  patterns against cyclic actuals").
- **Miller's exit (not taken by FX-91, and not recommended here): the
  pattern restriction**, flexible-variable-applied-only-to-distinct-bound-
  variables, decidable with principal unifiers (§4.4). This is strictly more
  permissive than Jones's "never solve for `f`" rule, but it is new
  algorithmic machinery (occurs-check-with-pruning, raising) that neither
  FX-91 nor Jones's constructor classes needed to build, because both of
  them instead restricted *where* a flexible higher-kinded variable could
  appear at all (never as an unresolved unification target, only as a
  checked binder or a rigid name).

**Recommendation for Path 1, if built: copy FX-91's choice exactly — a
`DFunc`/`Arrow`-kinded unification variable is bound outright (occurs-check,
then forward) or left for the caller to supply explicitly (as `poly`/
`plambda` binders already require callers to supply description arguments
today via `proj`, or let the expected type drive instantiation); never
attempt to decompose `(f a)` against an arbitrary type when `f` is
unresolved.** This is strictly first-order, matches `infer.rs`'s existing
unifier shape (congruence on `Ty::App` the same way it already does on
`Ty::Named`), and inherits none of Miller's or full higher-order
unification's complexity. The cost is exactly Jones's own, named
explicitly: some programs a human would consider obviously well-typed (where
the *right* `f` is "obvious" from context but not syntactically a pattern)
will need an explicit `the`/annotation. FX-26 already asks for this
constantly (`docs/fx26.md`, "bidirectional checking over inference," and "A
list with nothing to say what it is a list of ... still needs a `the`,"
`docs/fx26.md:1218-1219`) — the same discipline, one level up.

### 5.4 Subtyping and variance

**New risk: cycles through `poly` already diverge (§1); a new binder kind
inside `poly` inherits this before adding anything of its own.** The
existing fix (`BinderEnv`, comparing `poly` binders by position through an
environment rather than by substitution, `recursive-subtyping.md` §1, "The
prototype fix for `poly`") is a prerequisite, not optional, for Path 1 — and
is itself only a *prototype*, not yet ported to the FX-26 mirror checker
(`recursive-subtyping.md`: "The FX-26 twin, `check.fx`, is not ported").

**Variance of a `(=> type type)`-kinded parameter must be *derived*, not
declared the way a `type`-kinded `define-generative` parameter's `+`/`-` is
today** (`docs/fx26.md:1046`, "checked once"), because the parameter is
itself a function from types to types, and "is `f` covariant" is really "is
`(f a) ≤ (f b)` whenever `a ≤ b`" — a property of `f`'s *body*, computed, not
annotated by the binder site the way a plain type parameter's variance is.
`docs/research/structural-adts.md` §3.5.2, "Derived variance," already
designs almost exactly this computation for a different (non-expansive
family) feature, citing GHC's own role inference directly: "start with the
role information of the built-in constants ... and propagate ... until it
finds a fixpoint" (Breitner, Eisenberg, Peyton Jones and Weirich, JFP 2016,
cited at `structural-adts.md:666`). The same fixpoint computation is the
right model for "is this `(=> type type)` parameter covariant" — re-derive
it, do not ask the binder site to declare it, and reuse the
already-researched mechanism rather than inventing a second one. FX-91's own
`dlambda_leq` bug (§3) is a direct warning that subtyping of two distinct
applications of (possibly different) higher-kinded names is the one place
this has gone wrong before, silently, in a real implementation.

### 5.5 Regions and effects

A container that needs to know *where* its payload lives (`(f a r)` for a
region-parametric container `f`) asks whether `f`'s own kind should be `(=>
type region type)` — i.e. **arrow kinds need to range over FX-26's other
kinds too, not just `type -> type`**, which the `Kind::Arrow(Vec<Kind>)`
design in §5.1 already allows for free (each `ki` in the vector is any
`Kind`, matching FX-91's own `(->> k1 ... kn)`, which already allows `region`
and `effect` components, `fx91-report.txt` §2.1.3). What is genuinely new
work, not free: every safety analysis that currently looks *through* a
generative name's arguments by substituting them into `rep`
(`docs/research/generative-types.md`, "Opaque to comparison, transparent to
safety": `regions_in`, `no_knot`, `writes_in`, `cyclic`) would, for a
*variable* `f` of arrow kind applied to arguments, have **no `rep` to
substitute into** — `f` is abstract, its body unknown at the point `(f a r)`
is analyzed inside a polymorphic definition. This is not a new problem Path
1 invents; it is the same problem any analysis already faces for an
*abstract* `define-generative` type reached only through its `up`/`down`
(handled today by being conservative, "for what the name was given,
cautiously," `docs/fx26.md:1050`) — but Path 1 makes it the *common* case
(every use of a polymorphic `f` inside a `poly ((f (=> type type))) ...)`
body) rather than the rare one, which raises the practical cost even though
it raises no new soundness question.

### 5.6 The `data` kind

A `data`-kinded binder `(t data)` (`docs/fx26.md:1090-1105`) demands its
argument be built from data base types, products, sums and frozen
pairs/bloblets of `data` — a *structural* property the checker currently
computes for a *concrete* type (`docs/fx26.md:1095`, "the checker works out
whether a type is data"). For `(f a)` with `f` of arrow kind, "`is (f a)
data`" cannot be computed without unfolding `f`'s definition — which, for an
abstract/variable `f`, does not exist locally — so a `data`-kinded quantified
`a` under a higher-kinded `f` is either refused outright (the conservative,
sound default: a `poly ((f (=> type type)) (a data)) ...)` cannot assume `(f
a)` is `data` unless `f` itself is constrained to preserve `data`-ness,
which is a second, unbuilt piece of machinery — a `data`-preserving-functor
constraint, with no precedent in this codebase or in the papers surveyed) or
left for a future "`f` preserves `data`" bound, out of scope for an initial
Path 1.

### 5.7 Equi-recursion

FX-26's equi-recursive comparison already normalizes nothing before walking
a type graph (`recursive-subtyping.md` §1, "Representation: ... Nothing is
hash-consed"). FX-91's own description calculus needs beta/eta
*normalization* before two descriptions can even be compared structurally
(§3 above, `evaluate.rs`). Combining the two means deciding **when** a
`Ty::App` node is reduced: eagerly (every `(f a)` with `f` a known `dlambda`-
equivalent reduces to a plain structural type immediately, folded into
today's graph the same way `define-type` abbreviations already are,
`docs/fx26.md:1210-1213`, "expanded by substitution where used") or lazily
(kept as a node, unfolded only on demand at `tagcase`, `extract`, or a
subtype question, the same "whnf on demand" design
`docs/research/structural-adts.md` §3.5.2 already works out in detail for
expansive families, "family node ... unfolding on demand ... whnf at
`tagcase`, `extract` ..."). **Lazy unfolding is the right model to copy** —
it is already designed, in this repository, for a structurally similar
problem (a type-level application node whose head may or may not be
expandable), and reusing it means Path 1 shares machinery with that
not-yet-built feature rather than inventing a second "when do I unfold a
type-level redex" policy.

**The remaining question — whether unfolding a `Ty::App` commutes with
unfolding an equi-recursive `mu` cycle through the *same* node — now has a
citable answer, not just an open flag: no, not in general, and the known fix
is to forbid it.** Rémy's course notes (§4.3 above, p.134, citing Cai et al.
2016) show that combining unrestricted type-level recursion with higher-order
kinds makes type reduction (and hence type equality and type-checking)
undecidable, and that the decidable fix is **restricting recursion to the
base kind**: a `mu`/`dletrec` cycle may pass through an ordinary (`type`-
kinded) `Ty::App` result, but a `Ty::App` node whose own *operator* position
sits inside the cycle — a recursive type FUNCTION, like `(define-type (wrap
(f (=> type type))) (f (wrap f)))` — must be refused. This is a concrete,
checkable rule (closely analogous to `grounded`'s existing refusal of a cycle
made only of `poly` nodes, `recursive-subtyping.md` §1, "Why `polyonly`
diverges"), not a new research question; §9's open question 4 is updated to
reflect this.

### 5.8 Printing

`Ty::Poly`'s binders already print their `Kind` (`docs/fx26.md`'s printed
types show `(poly ((t type) (r region)) ...)` throughout); a `Kind::Arrow`
would print `(=> k1 ... kn)` the same way, and `Ty::App { fun, args }` would
print `(f a)` the same way `Ty::Named` already prints `(name d ...)`
(`docs/fx26.md:1095`, "`name` or `(name d ...)`, which reads back"). No new
printing *design* is needed, only new match arms — in both `check-print.fx`
(834/1000, headroom) and the Rust printer.

### 5.9 Both checkers: the cost, concretely

A new `Kind` variant, a new `Ty`/`Exp` node, a kind-checking pass, a new
substitution case, a new unification congruence case, a new subtyping case
(with the `poly`-cycle prerequisite from §5.4), a new printing case, derived
variance (§5.4, reusing `structural-adts.md`'s GHC-role-inference design),
and the `data`/region/effect interactions of §5.5–5.6 — each written twice,
Rust and FX-26, matching word for word (`docs/fx26.md`: "Both checkers have
all of it, agreeing on every program," the house standard). The FX-26 side
lands mostly in `check-types.fx` (835/1000), `check-infer.fx` (964/1000,
**nearly full**), `check-resolve.fx` (973/1000, **nearly full**) and
`check-subtype.fx` (990/1000, **nearly full**) — three of the four busiest
files in the checker, meaning this feature cannot be added to them without
first extracting material out to stay under the 1000-line cap
(`fx-size-limits-by-extraction`), which is itself real, if mechanical, work
not counted in a naive line-count estimate.

### 5.10 Lowering and run time

**Nothing changes.** Kinds, like types, are erased before lowering
(`docs/fx26.md`: types carry no run-time representation anywhere in this
codebase; `define-generative`'s `up`/`down` are literally `(lambda (x) x)`
at run time, `docs/fx26.md:1037`, and FX-91's higher-kinded `up`/`down`
coercions are the identity too, `generative-types.md:26`, "At run time both
are `(lambda (x) x)`"). A `Ty::App` node, fully resolved by the time a
program reaches `lower.rs`/`cellular.rs`, contributes nothing new to the
compiled output — the *checker's* cost (§5.9) is the whole cost.

### 5.11 Worked example

The tagless-final limitation from `gadts.md:222` (§2), with Path 1's syntax:

```scheme
; PROPOSED — needs Kind::Arrow and Ty::App (§5.1)
(define-type (exp (f (=> type type)) (a type)) (f a))
; "an exp is whatever shape its interpretation f gives a"

(define-type (closure-interp (a type)) (subr pure () a))   ; today's interpreter
(define-generative (tree-interp (a type))                   ; a second interpretation,
  (sumof (int-node int) (bool-node bool) (add-node (productof (l (exp tree-interp int)) (r (exp tree-interp int))))))
; both are now `(exp closure-interp a)` and `(exp tree-interp a)` of the SAME `exp` family;
; `eval`, `pretty-print` and `optimize` each take a `(poly ((f (=> type type)) (a type)) (subr ... ((exp f a)) ...))`
; written once, abstracting over which interpretation `f` is -- the capability `gadts.md:222`
; says is missing.
```

## 6. Path 2: through modules

### 6.1 Syntax

No new core syntax at all — only lifting the one restriction at
`modules.rs:149` and its tested counterpart (`abs-kind.fx`), and extending
`abs`'s grammar (already `(abs id kind)` generically in the AST,
`ModItem::Abs` is produced only by `define-generative` today, §1) to accept
a `define-generative` whose own parameter list makes it `(=> type type)`-
kinded directly — i.e. **Path 2's syntax is exactly Path 1's `Kind::Arrow`
plus `define-generative`'s existing parameterization**, reused, not
duplicated:

```scheme
; PROPOSED — needs Kind::Arrow (§5.1) for define-generative's own parameter list,
; but needs NO Ty::App, no type-level application syntax inside ordinary types,
; and no change to poly/plambda/proj.
(define-type container
  (moduleof (abs f (=> type type))
            (val empty (poly ((a type)) (f a)))
            (val map (poly ((a type) (b type)) (subr pure ((subr pure (a) b) (f a)) (f b))))))

(define list-container container
  (module
    (define-generative (f (a type)) (listof a @heap))    ; f is itself the abstract component
    (define empty (poly ((a type)) (f a)) (plambda ((a type)) (up-f nil)))
    (define map (poly ((a type) (b type)) (subr pure ((subr pure (a) b) (f a)) (f b)))
      (plambda ((a type) (b type)) (lambda (g xs) (up-f (map-list g (down-f xs))))))))
```

This matches FX-91's own grammar directly (`fx91-report.txt` §2.2.6, p.9-10,
read): `(moduleof (abs ida1 k1) ... (desc ...) (val ...))`, any `ki`,
`DFunc` included (§3 above) — FX-26's `(abs f (=> type type))` is the same
rule with FX-26's own spelling.

### 6.2 Checking, in both checkers — the one-line gate and its blast radius

The core change is `modules.rs:149`: `self.arena.dvar_of(named, Kind::Type)`
would need to become `self.arena.dvar_of(named, <the abs component's own
declared kind>)`, reading the kind off the `ModItem::Abs`'s binder (already
carried: `Abs { name, var, rep, ... }`, where `var: DVar` already has a
`Kind` recorded by `dvar_of` at the point `define-generative` created it,
§1). The restriction's *test*, `abs-kind.fx`, would need to flip from
"refused" to "accepted" (and a new refusal test written for whatever is
*still* refused, e.g. `(abs t region)` directly as a module component, which
FX-91 allowed but which §1 found FX-26's `ModItem::Abs` structurally cannot
produce today, since it is wired to `define-generative`'s `rep: TyId`
specifically — extending *that* is a second, smaller piece of work, needed
only if the user also wants `(abs e effect)`/`(abs r region)` module
components directly, which `first-class-modules.md`'s own stage table
already defers ("later: abstract regions and effects," line 171) and which
is not required for a `type -> type` container). The FX-26 mirror's module
files have real headroom for this: `check-modules.fx` 406/1000,
`check-module-rules.fx` 386/1000, `check-dependent.fx` 234/1000 — none
within even 60% of the cap, unlike §5.9's core-checker files.

**The one genuinely new piece of module-side checking**: `module_types`
(`modules.rs:282-291`), which turns an abstract component into `(Sym,
TyId)` pairs for `(select m t)` resolution, assumes every abstract
component names a plain type variable (`Ty::Var(*v)`, line 285) — for an
arrow-kinded component, `(select m f)` would need to name a type-level
*function* variable, which only matters once something tries to *apply* it,
i.e. `(select m f) a` — **and that application is exactly Path 1's
`Ty::App`, needed here too**, the moment a client of `container` wants to
write `((select m f) int)` outside the module rather than only inside it (as
the worked example in §6.10 needs). This is the one place the two paths are
not actually independent: **a module whose abstract component has an arrow
kind still needs `Ty::App` wherever a *client* applies that component to a
concrete type**, even though the module system itself needs nothing else
new. Scoped narrowly (allow `(select m f)` to appear only in a functor's own
`(select $k (f ...))`-shaped parameter/result positions, where the
application is written once by the functor's author and never needs
inference) this is small; scoped generally (let any client write `((select
m f) int)` anywhere a type is expected) it is Path 1's `Ty::App` in full,
with all of §5's cost.

### 6.3 Inference: close to none needed

This is Path 2's strongest advantage over Path 1. **Modules are checked, not
inferred, already**: every `module` expression's abstract components come
from explicit `define-generative` forms (no inference of *which* type a
module abstracts over — the programmer writes it); every `moduleof`
ascription is explicit; a dependent procedure's `(select $k t)` is resolved
by *name*, not by unification, at a call site that must already name its
module argument by a bound variable (`dependent_args`, `modules.rs:324-352`,
§1). **None of §4.4's higher-order unification question arises for Path 2
at all**, because nothing is ever asked to *solve for* which functor/module
a flexible variable stands for — exactly 1ML's own observation, §4.5,
("module-level application is checked... not solved for"). The only
inference-shaped work is ordinary: instantiating a `poly` inside a module's
`val` the same way `poly` is instantiated everywhere else today.

### 6.4 Subtyping and variance

Module subtyping (M4, `docs/fx26.md:889-895`) relates module *types* by
width (fewer values) and by an abstract component standing in for a
transparent one — it does not, and under Sheldon's path-identity rule
(`docs/research/modules.md` §2, "textual identity") should not, ask whether
one abstract component's *representation* is a subtype of another's: two
different modules' abstract types are simply incomparable, generative,
unrelated, by design (`docs/fx26.md:885-888`). **This means an arrow-kinded
abstract component needs no variance computation of its own at the module-
subtyping level** — unlike §5.4's Path 1, where `(f a) ≤ (f b)` genuinely
asks "is `f` covariant." The variance question only resurfaces *inside* the
module body, at the `define-generative (f (a type)) rep` that implements
`f` — and that is squarely `define-generative`'s *existing* `+`/-`
mechanism (`docs/fx26.md:1046`, "checked once," already built), not a new
derived-variance computation. **This is a second, independent reason Path 2
is cheaper than Path 1: it inherits an already-built variance story instead
of needing §5.4's new one.**

### 6.5 Regions and effects

`first-class-modules.md`'s own stage table already plans this, deferred:
"later | abstract regions and effects; `plambda` over regions making
modules" (line 171), and FX-91's `abs` already allows it for any kind
(`fx91-report.pdf` §2.2.6, quoted in `first-class-modules.md:39-42`: "`abs`
takes any kind: `(abs e effect)`, `(abs r region)` are as legal as `(abs t
type)`"). An arrow-kinded `abs` whose *domain* includes a region or effect
(`(abs f (=> type region type))`, a container that needs to know where its
payload lives, mirroring §5.5's Path 1 question) is the same `Kind::Arrow`
extension in both paths — the module system itself adds nothing extra here
beyond what §5.5 already costs.

### 6.6 The `data` kind

Same shape of open question as §5.6 — `module_types`/`select` resolution
would need to answer "is `(select m f) a` a `data` type" without access to
`f`'s hidden representation (that is the entire point of `abs`), so the same
conservative default (refuse unless `f` carries an explicit `data`-
preserving bound, unbuilt) applies, inherited rather than independently
re-derived, since it is really Path 1's `Ty::App` question (§5.6) reached
through a `select` instead of a bare variable.

### 6.7 Equi-recursion

Modules do not interact with `mu`/equi-recursion directly — a module's
abstract component is already nominal (generative, iso-recursive through its
own name if its `rep` is self-referential, `docs/research/generative-types.md`
§2: "a generative name is never unfolded to compare... [so] a generative
representation may be non-regular"). An arrow-kinded abstract component
inherits this for free: `(f a)` for `f` abstract is never unfolded by module
subtyping (§6.4) regardless of kind, so there is nothing for equi-recursion
to interact with *inside the module system* — the interaction only exists at
the `Ty::App` boundary (§6.2's "client applies the component"), which is
Path 1's question, not a new one Path 2 raises.

### 6.8 Printing

`moduleof` already prints each `abs` component's kind implicitly (today
always `type`, so never shown); printing `(abs f (=> type type))` is the
same new `Kind::Arrow` printing case §5.8 already needs, reached from one
more place. No separate module-printing design is needed.

### 6.9 Lowering and run time

**Already unchanged, today, regardless of kind** — `first-class-modules.md`,
"Run time": "Abstract, transparent, region and effect components are
erased... up-t/down-t are identities... So the compilers and the native
code see only products and lets, if the checker gives them those." This
sentence was written (2026-10-01) before this note and already covers an
arrow-kinded abstract component: `up-f`/`down-f` for a `Kind::Arrow`
component are still identity functions at run time (the value they coerce
is whatever concrete container value flows through them, never a type), and
FX-91's own `make_ups` (§3) already builds exactly this coercion shape for
`DFunc`-kinded abstractions, confirming the claim in code, not just in the
design note's prose.

### 6.10 Worked example: a functor over containers

The container-abstraction motivation directly, using M5's dependent
procedures as the functor (`docs/fx26.md:897-899`, "ML's functors are a
restricted form" of exactly this):

```scheme
; PROPOSED — needs only the modules.rs:149 kind restriction lifted (§6.2),
; plus Ty::App (§5.1) at the one `((select c f) a)` use site below.
(define-type container
  (moduleof (abs f (=> type type))
            (val map (poly ((a type) (b type)) (subr pure ((subr pure (a) b) (f a)) (f b))))))

(define pair-up                                           ; a functor: a dependent procedure
  (subr pure ((c container) ((select c f) int)) ((select c f) (productof (l int) (r int))))
  (lambda (c xs) (with c (map (lambda ((x int)) (product (l x) (r x))) xs))))
```

Contrast with today's working, kind-`type`-only functor
(`crates/fixpt-fx26/tests/programs/modules/functor-max.fx`, checked, both
checkers agree): `max-of`'s module parameter `o`'s abstract `t` names *one*
type, fixed for the whole call; `pair-up` above needs `f` to be re-applied
at two *different* types (`int`, then `(productof (l int) (r int))`) within
one call — the exact gap `functor-max.fx` cannot express today, and the
reason `(select $k (f ...))`, not just `(select $k t)`, is the piece this
path is missing.

## 7. Comparing the two paths, stage by stage

Sizing follows the house convention (`generative-types.md` §4,
`first-class-modules.md` "Stages"): **S** a day or less, **M** a few days,
**L** a week or more, each a guess, not a measurement — nothing here is
built.

| path   | stage | size | what                                                                                                                                                                             |
| ------ | ----- | ---- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Path 1 | A1    | M    | `Kind::Arrow`, parser, printing (§5.1, §5.8); both checkers                                                                                                                      |
| Path 1 | A2    | M    | `Ty::App`, kind-checking (§5.2); substitution case in `check-resolve.fx` (973/1000)                                                                                              |
| Path 1 | A3    | S    | unification congruence only, no higher-order solving (§5.3); `check-infer.fx` (964/1000)                                                                                         |
| Path 1 | A4    | L    | subtyping (§5.4): port the `poly`-cycle `BinderEnv` fix first (prerequisite, not yet in `check.fx`), then derived variance, reusing `structural-adts.md`'s role-inference design |
| Path 1 | A5    | M    | regions/effects in arrow-kind domains (§5.5); safety analyses through an abstract applied `f`                                                                                    |
| Path 1 | A6    | S    | `data` kind: refuse under an unconstrained higher-kinded `f` (§5.6), conservative, no new theory                                                                                 |
| Path 1 | A7    | M    | lazy unfolding of `Ty::App`, reusing the expansive-family "whnf on demand" design (§5.7, `structural-adts.md` §3.5.2)                                                            |
| Path 2 | B1    | S    | lift `Kind::Type` at `modules.rs:149`; flip `abs-kind.fx`'s expectation; new refusal tests for what stays refused (§6.2)                                                         |
| Path 2 | B2    | S    | `module_types`/`select` for an arrow-kinded component (§6.2), **needs A1 and a narrow A2** (`(select $k (f ...))` only)                                                          |
| Path 2 | B3    | —    | inference: none beyond what A3 already gives the narrow `select`-application case (§6.3)                                                                                         |
| Path 2 | B4    | —    | subtyping/variance: none new — module subtyping is generativity, not substitutability (§6.4)                                                                                     |
| Path 2 | B5    | S    | regions/effects in `abs`'s kind (§6.5), reusing A5 if full `Ty::App` is wanted, else free                                                                                        |
| Path 2 | B6    | —    | `data` kind: same open question as A6, inherited, not independent (§6.6)                                                                                                         |
| Path 2 | B7    | —    | equi-recursion: no interaction inside the module system (§6.7)                                                                                                                   |
| Path 2 | B8    | —    | run time: already correct today, confirmed in code (§6.9)                                                                                                                        |

**Path 2 alone (B1–B2, narrow `select`-application only, no general `(f a)`
anywhere a type is expected) is roughly S+S: a two-line kind change, a test
flip, and a scoped `select`-of-an-applied-component rule touching only
`check-dependent.fx` (234/1000) and `check-modules.fx` (406/1000), both with
headroom.** This buys exactly §6.10's worked example — functors over
containers, named by path, resolved at call sites that already name their
module argument — without touching `infer.rs`'s unifier, `check.rs`'s
subtyping, or any file within reach of the 1000-line cap. **Path 1 in full
is A1–A7, roughly M+M+S+L+M+S+M — materially larger, and the one place it is
genuinely needed on top of Path 2 is a client that wants to apply a
higher-kinded type *outside* any module's `select`-scoped functor
parameters** (an ordinary `poly ((f (=> type type))) ...)` definition with
no module in sight, e.g. a standalone generic `map` over an open set of
containers passed as plain dictionary values, not module values).

## 8. A lighter interim

### 8.1 Tagless-final: checked today, the primary recommendation

`docs/research/examples/higher-kinds/tagless-final.fx` (identical to
`docs/research/examples/gadts/eval-closures.fx`, kept in both places: the
former for this note, the latter for `gadts.md`), checked:

```
$ target/release/fixpt check docs/research/examples/higher-kinds/tagless-final.fx
define int-x : (subr pure (int) (subr pure () int)) ! pure
define bool-x : (subr pure (bool) (subr pure () bool)) ! pure
define add-x : (subr pure ((subr pure () int) (subr pure () int)) (subr pure () int)) ! pure
define if-x : (poly ((a type)) (subr pure ((subr pure () bool) (subr pure () a) (subr pure () a)) (subr pure () a))) ! pure
define eval : (poly ((a type)) (subr pure ((subr pure () a)) a)) ! pure
int ! (read (globals add-x bool-x eval if-x int-x))
; both checkers agree
$ target/release/fixpt eval docs/research/examples/higher-kinds/tagless-final.fx
...
3 : int ! (read (globals add-x bool-x eval if-x int-x))
```

This is Carette, Kiselyov and Shan's "finally tagless" style *(from
memory — not independently re-fetched for this note; cited already, by
name, in this repository's own prior reasoning about `eval-closures.fx`,
`gadts.md:219-222`)*: represent each syntactic form as a subroutine
directly, so "the interpreter" *is* the representation, with no `exp` data
type and no `eval` function to write separately. The cost, stated plainly in
the file's own comment: a **second** interpretation (print the expression,
count its nodes, optimize it) needs a **second**, parallel family of
`int-x`/`bool-x`/`add-x`/`if-x`, because nothing abstracts over "which
interpretation" — exactly the `type -> type` gap, sidestepped rather than
closed. For a program that only ever needs *one* interpretation (a
compiler's own expression-building code, say, where "evaluate" is the only
operation that ever runs), this is not a workaround at all — it is simply
the right representation, at zero extra cost, and is this note's strongest
"you may not need Path 1 or Path 2 yet" data point.

### 8.2 A closed, tag-dispatched union: checked today, narrower

`docs/research/examples/higher-kinds/closed-dictionary.fx`, checked and run
(both checkers agree, result `#<sum as-pair>`, i.e. `(pair 2 3)`):

```scheme
(define-type (maybe (a type)) (sumof (none unit) (some a)))
(define-type (pair (a type)) (productof (fst a) (snd a)))
(define-type (box (a type)) (sumof (as-maybe (maybe a)) (as-pair (pair a))))
(define map-box
  (poly ((a type) (b type)) (subr pure ((subr pure (a) b) (box a)) (box b)))
  (lambda (f bx) (tagcase bx
    (as-maybe m (sum as-maybe (tagcase m (none u (sum none u)) (some x (sum some (f x))))))
    (as-pair p (sum as-pair (product (fst (f (extract p fst))) (snd (f (extract p snd)))))))))
```

`map-box` is written **once** and works on either shape — a genuine `map`
over more than one container, with no new kind, no type-level application,
and no inference beyond what FX-26 already does: `box`'s width-subtyped sum
(`docs/research/structural-adts.md` §1.1, "width subtyping on sums ...
inclusion of ... unions") already gives "more than one shape, one type" for
free. The limitation is exactly the task's own framing of "dictionary
passing over modules" taken to its most literal extreme: this is **closed**
— adding a third container means editing `box` and `map-box` together, not
writing an independent `instance` elsewhere the way Jones's `class Functor
f` or an ML `FUNCTOR`-signed structure would let a client do without
touching the class/signature itself. It is a legitimate, cheap answer for a
program with a small, known, stable set of containers (which is most of
what `PLAN.md`'s Q8 asks for: `equal`, `hash`, `->datum`, `compare` over
FX-26's *own*, closed set of base shapes) and not an answer for an
open-ended user-extensible `Functor` class.

### 8.3 Why Yallop and White's brand encoding does not port cleanly (my own analysis)

The `app`/brand technique (§4.8) needs **one** carrier type, `('a, 'f) app`,
whose true runtime representation differs per brand `'f`, related to each
brand's own concrete type only through that brand's `inj`/`prj`. In OCaml
this works because `app`'s actual implementation is permitted to be an
unsafe, representation-erasing identity (OCaml's `Obj.magic`, or an
equivalent single hidden representation shared by every brand) — the type
system's soundness argument is entirely *parametricity-after-sealing*, never
mechanically checked against each brand's real structure. FX-26 has no such
escape hatch, by design: `define-generative`'s `up-name`/`down-name` are
*checked* identity coercions against **one fixed `rep`**
(`docs/fx26.md:1036-1037`), and there is no primitive anywhere in this
codebase that reinterprets a value's representation without the checker
proving the reinterpretation sound first. Concretely: a single
`(define-generative (app (a type) (f type)) ???)` cannot have its `???`
depend on which `f` is supplied — `rep` is one fixed expression, the same
for every instantiation of the family, so there is nothing for a
container-specific `inj-List`/`inj-Option` pair to attach *to* inside one
shared `app`. The only FX-26-native ways to recover a shared carrier are:
(a) a closed, tag-dispatched union (§8.2 — effectively "the brands are a
finite `sumof`, known in advance"), which is open-world *within* the sum but
not extensible beyond it, or (b) actually adding an arrow kind somewhere
(Path 1 or Path 2), at which point the brand encoding is no longer needed at
all — a real `(f a)` already says what `app`+brand was faking. **Verdict:
Yallop and White's technique is specific to a language (OCaml) that already
has an unsafe-cast primitive FX-26 deliberately lacks; it does not transfer
as a free lunch, and §8.1/§8.2 are the right "lighter than Path 1/2"
answers for FX-26 specifically.**

### 8.4 Dictionary passing over first-class modules, at kind `type`: already real, already narrower than a true `Functor`

`functor-max.fx`/`functor-abstract.fx`
(`crates/fixpt-fx26/tests/programs/modules/`, both checked today, both
checkers agree, §1) already demonstrate genuine dictionary passing — a
module value carries an abstract type plus the operations that work on it,
and a dependent procedure (functor) abstracts over "which module." This is
exactly `PLAN.md`'s decision 4 ("dictionaries and tags over specialization,"
`PLAN.md:1899-1905`) and exactly what Q8 asks for (`PLAN.md:2193-2200`), for
any operation whose signature needs only *one* fixed instantiation of the
abstract type per dictionary — `equal`, `hash`, `compare`, `->datum` all fit
this shape (one dictionary, one type, operations that consume or produce
values of that one type, never *change* which type is involved). It does
**not** give `map`'s shape (`f a -> f b`, two different instantiations of
the same `f` in one signature) without `(select $k (f ...))`, i.e. without
at least §6's narrow Path 2 slice. **This is the honest boundary**:
dictionary passing over today's kind-`type`-only modules already covers
most of Q8's list; `map`/`fold`-shaped operations are the one item on that
list that needs this note's Path 2 (narrowly, §6.2's B1–B2) to express
cleanly.

## 9. Recommendation and open questions

**Recommendation: do not build either path speculatively. If and when a
concrete client needs container-generic code (Q8's `map`/`fold`, or a second
interpreter for the tagless-final pattern outgrowing §8.1), build Path 2's
narrow slice first (§7, B1–B2: lift `modules.rs:149`'s `Kind::Type`, flip
`abs-kind.fx`, add the scoped `(select $k (f ...))` application rule) —
it is roughly two days of work, touches only the module files (all with
headroom), needs no new inference, no new subtyping, and no change to a file
within reach of the 1000-line cap.** Revisit full Path 1 (§7, A1–A7) only if
that slice turns out too narrow in practice — specifically, only if a real
program wants a standalone `poly ((f (=> type type))) ...)` with no module
anywhere in sight, which is a materially larger, multi-week undertaking
whose riskiest piece (subtyping through `poly`, §5.4/A4) is a prerequisite
bug-fix FX-26 does not strictly need higher kinds to justify fixing on its
own (`recursive-subtyping.md`'s `poly`-cycle divergence is a real, already-
known gap, kinds or no kinds).

Open questions, for the user:

1. **Is there a concrete client yet, or is this still speculative?** Q8
   (`PLAN.md:2193-2200`) is the nearest; §8.4 argues most of it does not
   actually need either path. Worth asking directly: does anything on the
   front end's own roadmap want a container-generic `map`/`fold` across more
   than the fixed shapes §8.2's closed union could cover?
2. **If Path 2's narrow slice is built, should `(select $k (f ...))` stay
   scoped to a functor's own declared parameter/result positions (§6.2's
   small reading), or should any client be allowed to write `((select m f)
   int)` wherever a type is expected (which is Path 1's `Ty::App` in full,
   reached through a `select`)?** This note recommends the narrow reading
   first, matching "soundness first" and the smallest-slice-that-answers-
   the-motivating-example discipline this repository already follows
   elsewhere (e.g. M1 before M4 before M5 in `first-class-modules.md`'s own
   stages).
3. **Should FX-26 ever allow `(abs e effect)`/`(abs r region)` module
   components directly** (not arrow-kinded, just a bare effect or region
   abstracted over), as FX-91 already does and `first-class-modules.md`
   already defers ("later")? This is independent of both paths in this note
   but shares `Kind::Arrow`'s eventual domain-kind generality (§5.5/§6.5) if
   built at the same time.
4. **Is `Ty::App`'s unfolding policy (§5.7) meant to share machinery with the
   not-yet-built expansive-family work (`structural-adts.md` §3.5)?** This
   note recommends yes — reusing one "when do I unfold a type-level redex"
   policy for both, rather than building two — but that is a design call for
   whoever builds either feature first, since neither is built yet. The
   deeper soundness question this was originally paired with — whether
   `Ty::App` unfolding commutes with equi-recursive `mu`-unfolding — is no
   longer fully open: Rémy's course notes, citing Cai et al. (2016), show the
   decidable fix is to forbid a `mu`/`dletrec` cycle from passing through a
   `Ty::App`'s *operator* position (recursion stays at base kind only, §5.7).
   What remains a genuine implementation question is only *where* in
   `grounded`/`k-grounded` to add that check, not *whether* one is needed.
5. **Does a `data`-kinded binder under an abstract higher-kinded `f` need a
   first-class "`f` preserves `data`-ness" bound** (§5.6/§6.6), or is
   refusing it outright (the conservative default this note assumes
   throughout) acceptable indefinitely? No motivating example in this
   repository currently needs the permissive answer.

## What I could not verify

- Whether GHC's actual constructor-application *unification* algorithm is
  literally first-order in Jones's exact sense, beyond what the POPL20 kind-
  inference paper's introduction says about the lineage (§4.2) — not
  independently re-derived from a primary source on GHC's unifier itself,
  though Rémy's course notes (§4.3) independently corroborate the same shape
  of restriction in more formal terms.
- Scala's kind-checking algorithm (§4.6) is from memory; no primary source
  was fetched (the web-search budget for this session was exhausted before
  it could be looked up, and no local PDF was already present in
  `docs/research/papers/`; two direct `WebFetch` attempts at specific URLs —
  a PDF mirror and a dblp bibliography page — were both denied by this
  session's own sandbox policy on an unrelated, apparently non-deterministic
  "irreversible local destruction" classifier, not a content or budget
  issue).
- Rust's own stated *motivation* for choosing GATs over full higher-kinded
  types (implementation/inference cost) was not found in the RFC text
  actually fetched (§4.7 now has a verified primary citation for what GATs
  *are*, via `WebFetch` on the RFC itself; only the "why not full HKT"
  rationale remains from memory).
- Cai, Giarrusso, Ostermann et al. (2016), cited by Rémy's course notes for
  the "recursion restricted to base kind" decidability result (§4.3, §5.7),
  was not independently located or read — the claim is at one remove, via
  Rémy's citation of it, not a direct read of that paper.
- `docs/research/modules.md`'s own ML-functor background (§4.5's opening
  paragraph) was read only through lines 1–819 of 1033 in a prior pass this
  note reused; the remaining ~215 lines (Swift resilience and sources
  tables) were not re-read for this note and are not cited here.
- `docs/research/structural-adts.md` was read through line 816 of 1298;
  §3.5.3's worked lemma examples past that point (parts (b)/(c) in detail,
  and §4 onward) were read in the portion quoted above but the file's tail
  beyond what is cited was not independently re-verified line by line.

## Sources

| source                                                                                                     | where                                                                                  | how much                                                                                                                       |
| ---------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| `crates/fixpt-fx26/src/ast.rs`                                                                             | this repository                                                                        | read in full for `Kind`, `Ty`, `D`, `Exp`, `ModItem`, `Variance` (lines 1-465)                                                 |
| `crates/fixpt-fx26/src/modules.rs`                                                                         | this repository                                                                        | read in full, 358/358 lines                                                                                                    |
| `crates/fixpt-fx26/tests/programs/modules/*.fx`                                                            | this repository                                                                        | 7 programs read in full (`abs-kind`, `functor-abstract`, `functor-max`, `param-select`, `region-parameter`, `dependent-later`) |
| `docs/fx26.md`                                                                                             | this repository                                                                        | read in full, 1024-1260 and 864-923 closely; headings scanned elsewhere                                                        |
| `docs/research/first-class-modules.md`                                                                     | this repository                                                                        | read in full, 228/228 lines                                                                                                    |
| `docs/research/generative-types.md`                                                                        | this repository                                                                        | read in full, 292/292 lines                                                                                                    |
| `docs/research/structural-adts.md`                                                                         | this repository                                                                        | read lines 1-816 of 1298 (partial; see "What I could not verify")                                                              |
| `docs/research/gadts.md`                                                                                   | this repository                                                                        | read lines 1-100, 195-284 of 525 (summary, decisions, toy examples E1-E3)                                                      |
| `docs/research/recursive-subtyping.md`                                                                     | this repository                                                                        | read in full, 550/550 lines                                                                                                    |
| `docs/research/modules.md`                                                                                 | this repository                                                                        | read lines 1-819 of 1033 (partial)                                                                                             |
| `PLAN.md`                                                                                                  | this repository                                                                        | read lines 1-240, 1885-1910, 2190-2213                                                                                         |
| `crates/fixpt-fx91/src/kind.rs`                                                                            | this repository                                                                        | read in full, 214/214 lines                                                                                                    |
| `crates/fixpt-fx91/src/ast.rs`, `modules.rs`, `unify.rs`, `subtype.rs`, `evaluate.rs`                      | this repository                                                                        | relevant functions read in full (grep-located, then read with context)                                                         |
| `docs/divergences.md`                                                                                      | this repository                                                                        | line 120 (the `dlambda<=?` entry) read with surrounding table                                                                  |
| Gifford, Jouvelot, Sheldon, O'Toole, *Report on the FX-91 Programming Language*                            | `~/Dev/LangPlay/GiffordHistory/papers/fx91-report.txt`                                 | §§2.1-2.2.6 (pp. 6-10) read in full, directly, as plain text                                                                   |
| Jones, *A System of Constructor Classes* (FPCA 1993)                                                       | `docs/research/papers/jones-fpca93-constructor-classes.pdf`                            | read in full, 10 pages                                                                                                         |
| Miller, *A Logic Programming Language with Lambda-Abstraction, Function Variables, and Simple Unification* | `docs/research/papers/miller1991-pattern-unification.pdf`                              | read pp. 1-2 (abstract, introduction) directly                                                                                 |
| Xie, Eisenberg, Oliveira, *Kind Inference for Datatypes* (POPL 2020)                                       | `docs/research/papers/xie-eisenberg-oliveira-popl20-kind-inference.pdf`                | read pp. 1-3 (abstract, introduction, §2.1) directly                                                                           |
| Rossberg, *1ML — Core and Modules United* (JFP)                                                            | `docs/research/papers/rossberg-1ml-jfp.pdf`                                            | read pp. 2-3, 12-13, 15-16, 24-25 directly (via local text extraction)                                                         |
| Yallop, White, *Lightweight Higher-Kinded Polymorphism* (FLOPS 2014)                                       | `docs/research/papers/yallop-white-flops14-lightweight-higher-kinded-polymorphism.pdf` | read pp. 4-6 (§1.3, start of §2) directly (via local text extraction)                                                          |
| Rémy, *Type systems for programming languages* (MPRI course notes, 2020-21), Ch. 7 "System Fω"             | `docs/research/papers/remy-mpri-system-fomega.pdf`                                     | read pp. 121, 124-126, 133-134 directly (intro, Fig. 7.1, §7.2.1, §7.3.1-7.3.2, §7.4.1-7.4.3)                                  |
| Scala higher-kinded types                                                                                  | *(from memory)*                                                                        | from memory only; two `WebFetch` attempts at specific URLs were denied by this session's sandbox policy, not a content issue   |
| Rust RFC 1598, *Generic Associated Types*                                                                  | `rust-lang.github.io/rfcs/1598-generic_associated_types.html`                          | fetched and read directly                                                                                                      |
| Carette, Kiselyov, Shan, "finally tagless" style                                                           | *(from memory)*, named already in `docs/research/gadts.md:219`                         | from memory only, no source fetched for this note                                                                              |
