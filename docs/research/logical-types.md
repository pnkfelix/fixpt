# Logical type constructors: union, intersection, difference

Design note, 2026-09-29. Research only: no code was changed. The
question: what intersection, union and negation (or set-difference) types
would mean in FX-26, which of them are sound with its refs, regions and
effects, what they cost the two checkers and the compilers, and whether to
add any.

Sources were read online on 2026-09-29 and are listed at the end, with
URL and version; a claim marked *(from memory)* was not checked against a
source. FX-26 facts cite files in this repository; FX-87 and FX-91 facts
cite `~/Dev/LangPlay/GiffordHistory`.

## 0. The recommendation, in brief

- **Add unions, restricted to members of disjoint run-time shapes.** A
  *shape* is what a word's tag and, for a bloblet, its header's kind tell
  apart: fixnum, pair, `nil`, boolean, character, unit, string, symbol,
  sum, product, box, bloblet or array, closure. A union of disjoint shapes
  costs nothing at run time (no box, no tag word), and a membership test
  is one or two instructions. This is Ceylon's "disjoint cases" rule
  pushed down to the representation, and the case Typed Racket and
  Elixir exploit with their data-type predicates.
- **Eliminate unions only by narrowing a variable**: `typecase`, and `if`
  on a shape predicate (`null?`, `pair?`, `int?`, …) applied to a
  variable. FX-26 has no assignable variables, so narrowing by binding is
  always sound: Typed Racket's one hard case (a mutated variable or a
  mutable field) cannot arise. The `else` branch sees the *difference*:
  that is the only negation FX-26 needs, and it is already how
  `tagcase`'s `else` works.
- **First step, separately useful: a non-`nil` pair type.** FX-26's
  `(pairof A B r)` is already the union `nil ∪ pair` (FX-87's `null ≤
  pairof`). A type for the pair alone, which `null?` narrows to, makes
  native `car` provably safe where it is used unchecked today (`car` of
  `nil` crashes native code: `PLAN.md`, "Bugs the benchmark ports found").
- **Add intersections only of subroutine types (overloading), later**,
  with Davies and Pfenning's restrictions: introduced only by checking a
  `lambda` against each arm, and no distributivity rule. In FX-26 the
  interesting use is not ad-hoc overloading but **refining latent effects
  and sizes by argument type**: `pure` on an `acyclic` list, `spin` on a
  writable one.
- **Do not add** general negation, a top type, semantic subtyping,
  unions inferred at joins, unions of overlapping shapes (two lists at
  different regions, `int` and a generative type over `int`), or
  intersections of non-procedure types.

Section 8 has the proposed syntax (marked as proposed), the soundness
additions, the checker changes and the stages; section 9 the questions for
you.

## 1. What FX-26 already has that is logical

FX-26 has more set-theoretic structure than its grammar shows:

| Existing feature                                     | Logical reading                                                 | Where                                                          |
| ---------------------------------------------------- | --------------------------------------------------------------- | -------------------------------------------------------------- |
| `void`, a subtype of every type                      | the empty union, ⊥                                              | `docs/fx26.md`, "The kernel"                                   |
| `(sumof (l T) …)` with width subtyping               | a union of tagged singletons: `(sum l e)` fits any sum with `l` | `check.rs:1686–1688`                                           |
| `tagcase`'s `else` sees only the tags not named      | difference over tags: `S ∖ {l₁ … lₙ}`                           | `check.rs:1952–1967`; `check.fx:3840` (`k-variants-not-named`) |
| effects as sets: `maxeff`, `within`, masking         | union, inclusion, difference (`φ ∖ r`)                          | `docs/research/soundness.md` §2.4                              |
| convention `fx`, with `cellular ≤ fx`, `native ≤ fx` | the union of two closure kinds, split at run time by the kind   | `docs/research/native-conventions.md`, "Conventions in types"  |
| `nil` inhabits every pair type                       | `(pairof A B r)` is `nil ∪ pair`; `null?` is its test           | `standard.rs:10`, `:46`; `soundness.md` §1.4                   |
| `datum`, opaque, with `datum-int?` and the rest      | a closed union of Scheme data with checked projections          | `standard.rs:87–131`                                           |
| `certify-acyclic`, `certify-nat`, `certify-length`   | occurrence typing in miniature: a test refines *this binding*   | `infer.rs:340–470`; `check.rs:521–545`                         |
| `nat_join` of naturals of unequal sizes              | a join computed where no member is the larger                   | `check.rs:551–557`                                             |

So the proposal is less a new idea than a generalisation of three that
exist: `fx` (union split by kind), `tagcase` (difference in `else`) and
certification (refining a binding in a branch).

## 2. The friction in the ports

What the benchmark ports did for want of a union, and whether a
disjoint-shape union would relieve it:

| Port                                                  | What it did                                                                                   | Union that fits                                               | Relieved?                                             |
| ----------------------------------------------------- | --------------------------------------------------------------------------------------------- | ------------------------------------------------------------- | ----------------------------------------------------- |
| `scheme-bench/destruc.fx`                             | `(define-datatype item (null-item) (num int))`: a box per number Larceny keeps raw            | `(union nil int)`                                             | yes: no allocation per element                        |
| `scheme-bench/lseq.fx`                                | an lseq's cdr, a list or a generator, as a sum `(seq …)` / `(gen …)`                          | `(union lseq gen)`: pair or `nil`, and a closure              | yes: `procedure?` is the original's test              |
| `scheme-bench/browse.fx`                              | `(define-datatype item (sym symbol) (lst (listof item @heap)))`                               | `(union symbol (listof item @heap))`                          | yes                                                   |
| `scheme-bench/gcbench.fx`                             | a record whose children may be `0`: three pairs instead                                       | `(union bool node)`, `node` a bloblet                         | yes: one object, as Larceny's                         |
| `scheme-bench/earley.fx`                              | "vector or `#f`" as an empty array; "int or `#f`" as `-2`                                     | `(union bool (arrayof int r))`, `(union bool int)`            | yes; sentinels go                                     |
| `scheme-bench/mazefun.fx`                             | a cell "`#f` or a pair" as a nullable `(pairof int int @heap)`                                | already a union (`nil ∪ pair`)                                | already works; the non-`nil` pair type makes it exact |
| `scheme-bench/conform.fx`                             | `nil` for `#f` in lookups                                                                     | `(union bool (pairof …))`                                     | yes, or keep `nil`                                    |
| `scheme-bench/deriv.fx` etc.                          | heterogeneous S-expressions as `datum`                                                        | `datum` itself as a recursive union                           | partly: typed walks instead of checked projections    |
| `mllang-bench/fx/mlton/logic.fx`                      | `term option` as a sum, plus a `PROBE` sentinel for identity                                  | `(union nil term)` if `term` is not a list                    | the option, yes; identity no (needs `eq?`)            |
| `mllang-bench/fx/ocaml/kb.fx`, `boyer.fx`, `zebra.fx` | one prompt tag per exception, answer type fixed, so an `outcome` sum wraps every `try` result | `(union term bool …)`: but `terms` and `subst` are both lists | **no**: see below                                     |

The exceptions case is not a union problem. A prompt tag fixes its answer
type `A` (`docs/fx26.md`, "Control, typed") because a composable
continuation returns an `A`. An exception tag is never captured
composably; its handler maps the payload to whatever its own prompt
returns. The fix is a tag whose prompts each choose their answer type,
checked only when no `call-with-composable-continuation` can reach it:
worth its own note, and independent of unions. A union answer type would
only move the wrapping from injection to narrowing, and fails outright
where two answer types share a shape (`terms` and `subst`, both lists).

## 3. The survey

### 3.1 Intersection types

- **Origin.** Coppo and Dezani-Ciancaglini (1980) add `A ∧ B` to
  Curry's functionality theory: a term has an intersection when it has
  both types. In pure λ-calculus it characterises normalisation; for a
  language it is the type of a value that serves several uses at once.
- **Forsythe** (Reynolds, CMU-CS-96-146, 1996) uses intersections for
  Algol's overloaded operators, for records (a record is the intersection
  of its one-field types) and for the distinction between phrases that
  can be assigned and those that cannot. It is the first language built
  on them.
- **Pierce's thesis** (CMU-CS-91-205, 1991; MSCS 7(2), 1997) combines
  intersections with bounded quantification and gives the subtyping and
  checking algorithms; overloading is written as an intersection of
  arrows.
- **Refinement intersections.** Freeman and Pfenning (PLDI 1991) refine
  ML datatypes by regular-tree subsorts and need intersections so a
  function can have several refined types (`double : (nat → nat) ∧ (pos
  → pos)`). Davies' thesis (CMU-CS-05-110) makes it practical for SML
  with bidirectional checking. Dunfield and Pfenning (FoSSaCS 2003;
  "tridirectional", POPL 2004) add unions, and Dunfield (ICFP 2012)
  elaborates intersections and unions to products and sums.
- **The value restriction for intersections.** Davies and Pfenning
  (ICFP 2000, p. 199) show general intersections unsound with references:
  `let x = ref(1) : nat ref ∧ pos ref` lets one alias store a `nat`
  (zero) and another read it as a `pos`. Their fix: introduce `∧` only on
  values, and **drop distributivity**, `(A → B) ∧ (A → C) ≤ A → (B ∧ C)`,
  since `(λx. ref(1)) ()` would otherwise get `nat ref ∧ pos ref` (p. 200).
  They keep a bidirectional algorithm.
- **Overloading in practice.** TypeScript and Flow write overloads as
  intersections of function types, resolved by trying the arms in order;
  Luau types built-ins so but "still does not support user-defined
  overloaded functions", and forbids intersections of primitives
  (`string & number`). Scala 3's `A & B` is on classes and traits
  (records by another name) and is commutative. MLstruct (Parreaux and
  Chau, OOPSLA 2022) deliberately posits `(τ₁ → τ₂) ∧ (τ₃ → τ₄) ≤ (τ₁ ∨
  τ₃) → (τ₂ ∧ τ₄)` so that it keeps principal inference, and so "we do
  not permit the use of intersection types to encode inclusive function
  overloading" (extended version, §2.3.4, p. 9).

### 3.2 Union types

- **Typed Racket** (Tobin-Hochstadt and Felleisen, POPL 2008; ICFP 2010)
  has "true" untagged unions over Racket's tagged values, and *occurrence
  typing*: a predicate's type carries latent propositions (`number?`
  proves `N_x` in the then branch, `¬N_x` in the else), and the checker
  refines by `restrict` and `remove`, the latter set difference on unions
  (ICFP 2010, Fig. on PDF p. 8). §7.1 (PDF p. 10) is the pitfall: a test
  on `(unbox b)` says nothing after `(set-box! b* 'no)` through an alias,
  so mutable fields' selectors get no propositions, and a variable that is
  ever `set!` gets no refinement.
- **TypeScript and Flow** narrow unions by `typeof`, truthiness,
  equality, `in`, `instanceof`, user predicates (`x is T`) and discriminant
  fields, with `never` for exhaustiveness (TypeScript Handbook,
  "Narrowing"; Flow docs, "Type Refinements", "Unions"). Both are unsound
  by design in places (narrowing survives calls that could mutate).
- **Ceylon** requires the cases of a `switch` to be disjoint, and lets an
  exhausted union drop its `else` (Ceylon 1.0 spec, ch. 3). Muehlboeck and
  Tate (OOPSLA 2018) formalise the integration of unions and
  intersections with the rest of Ceylon's subtyping, keeping it decidable.
- **Scala 3** (DOT) has `A | B`, but infers a union only when one is
  written or asked for: a "soft" union inferred for a definition is
  widened to its *join*, "the smallest intersection type of base class
  instances" (Scala 3 reference, "Union Types – More Details"). Matches
  on a union are exhaustive when each part is covered.
- **Luau** narrows by `type(x) == "number"` and by equality to singleton
  types; tagged unions of tables are discriminated by a field.
- **Python** has `Union`/`X | Y`, narrowing by `isinstance` and by
  user functions returning `TypeIs[T]` (PEP 742), which narrow in both
  branches and require `T` to be a subtype of the input, unlike the older
  `TypeGuard`.
- **Dialyzer** (Lindahl and Sagonas, PPDP 2006) infers *success typings*
  for Erlang: over-approximations, with unions of singleton atoms and
  tuples, that flag only code sure to fail. It is a bug finder, not a
  sound type system: the opposite contract from FX-26's.
- **XDuce and CDuce** (Hosoya and Pierce, TOIT 2003; Benzaken, Castagna
  and Frisch, ICFP 2003) type XML with regular-expression types, unions
  of tree shapes, where subtyping is language inclusion. Inclusion of tree
  automata is EXPTIME-complete (Hosoya, Vouillon and Pierce, TOPLAS 2005).
- **Julia** keeps unions at run time with a type tag: an "isbits Union"
  field is stored inline with a one-byte tag (Julia dev docs, "isbits
  Union Optimizations"), and the compiler *splits* code on a small union
  (Julia blog, "Union-splitting", 2018). This is the precedent for
  unboxed unions, which section 7 declines for now.

### 3.3 Negation and difference

- **Semantic subtyping** (Frisch, Castagna and Benzaken, JACM 55(4),
  2008) interprets types as sets of values and gives `∨`, `∧`, `¬` their
  set meaning; the hard part is arrows, done through an auxiliary model.
  Subtyping is decidable: `t₁ ≤ t₂` iff `t₁ ∧ ¬t₂` is empty (Castagna,
  "Programming with union, intersection, and negation types", arXiv
  2111.03354v4, p. 16).
- **Castagna's essay** is the best map. Its practical conclusions, for
  FX-26:
  - a type-case must be decidable *without the type checker at run time*,
    so the implicitly-typed system restricts test types to ground types
    with no arrow but `0 → 1`, "the type of all functions": functions can
    be told from non-functions, not `int → int` from others (p. 33);
  - the polymorphic system needs a value restriction for mutation (p. 33,
    fn. 22);
  - "constraint solving is a potential source of computational explosion
    that we do not master well, yet", and error messages suffer (p. 56);
  - side effects are "swept under the carpet", and some of the occurrence
    typing "is sound only for pure expressions" (p. 56).
- **Occurrence typing with negation**: "Revisiting occurrence typing"
  (Castagna, Lanvin, Laurent and Nguyen, SCP 217, 2022) and "On
  type-cases, union elimination, and occurrence typing" (Castagna,
  Laurent, Nguyen and Lutze, POPL 2022) type the else branch by `t ∖ s`
  and reconstruct intersections of arrows. Pearce (VMCAI 2013) gives a
  sound and complete subtype test for flow typing with all three
  connectives, for Whiley: "intersections for the true-branch of a type
  test, negations for the false-branch, and unions … at meet points".
- **MLstruct** (OOPSLA 2022) makes unions, intersections and negations a
  Boolean algebra over *nominal class tags* and structural records, with
  principal ML-style inference and no backtracking; negation of a class
  is set-like, negation of functions and records "essentially algebraic"
  (extended version, p. 19). It needs a value restriction with mutation
  (p. 13). Chau and Parreaux (POPL 2026) prove its subtyping sound
  semantically, and **NP-hard**.
- **Algebraic subtyping** (Dolan and Mycroft's MLsub, POPL 2017;
  Parreaux's Simple-sub, ICFP 2020) has unions and intersections only as
  the joins and meets of inferred types, in positive and negative
  positions respectively: principal types, but not types a programmer
  writes to state a disjoint union.
- **Elixir** (Castagna, Duboc and Valim, ‹Programming› 8(2), 2024) is the
  closest precedent: set-theoretic types over a VM whose values are all
  tagged, narrowing from guards (`is_integer`, pp. 4:12 and on), negated
  type variables in signatures (`(a -> a) when a: not(integer() or
  boolean())`, p. 4:8), and "strong arrows", functions whose own guards
  check their domain at run time (p. 4:17–18).

### 3.4 Effects, regions and cost

- **Effects are already a Boolean lattice of atoms**, with variables. A
  union of effects is `maxeff`; inclusion is `within`; masking is
  difference. Intersection of effects has no user yet; an effect variable
  makes it symbolic, which is a reason not to need it (section 5).
- **Union of types is not union of effects.** Reading a `(union (ref A
  r₁) (ref B r₂))` would have effect `(read r₁) ∪ (read r₂)`; but the
  disjoint-shape rule refuses that union anyway (two boxes), and
  section 5 shows why that is the right call.
- **Cost.** Full semantic subtyping is EXPTIME in general (the tree
  automata bound above); Boolean-algebraic subtyping is NP-hard. What
  FX-26 would add is far smaller: a union node whose members have
  distinct shapes compares by matching members shape by shape, which is
  linear in the members and needs no search on the left; only a union on
  the right and an intersection on the left are disjunctive. Those need
  the trail rolled back on failure, which the lemma rule already does
  (`check.rs:1538–1566`) and `recursive-subtyping.md` ("The hazard for
  the future") prescribes.
- **Recursive types.** A union is not a constructor, so a cycle must
  still pass through one (as through `poly`: `fx26.md`, "Recursive types,
  named or not"); `(mu d (union nil int (pairof d d const)))` is fine,
  `(mu d (union d int))` is not.

## 4. What FX-87 and FX-91 had

- **FX-87's `oneof`** was a *tagged*, region-allocated, mutable variant:
  `(oneof ((tag T) …) R)`, made by `one`, taken apart by `tagcase`,
  changed in place by `one-set!` (`mit-psrg-fx/fx87/old-impl/standard.lisp:590–663`;
  `library/polynm.fx:120` uses one). Its width subtyping was unsound when
  mutable, and the implementation corrected the reference manual: "The
  subtyping rule for oneofs is incorrect in the FX-RM -- when they are
  mutable, the sets of tags must be equal" (`standard.lisp:1596–1597`,
  the rule at `:1670–1696`; `init.lisp:62–63`). That is the "unions with
  mutable cells" pitfall, met in 1987. FX-26's sums are immutable, so
  their width subtyping is sound.
- **FX-87's `null` type** is a subtype of every `pairof`
  (`standard.lisp:1614–1616`): the one singleton type, and the reason
  `nil` inhabits FX-26's pair types.
- **FX-91** has `sumof` with an inclusion rule (width and depth,
  covariant) and `tagcase`, and no union, intersection or negation
  (*Report on the FX-91 Programming Language*, `papers/fx91-report.pdf`,
  p. 12, §2.2.10, and p. 22, §2.3.17; its reserved words, p. 4, have no
  union former). FX-91's Scheme conflated `NIL` and false (the
  `compatlisp-nil` shim, `GiffordHistory/README.md`); FX-26's `#f` and
  `nil` are distinct immediates (`crates/fixpt-heap/src/value.rs`,
  `IMM_FALSE`, `IMM_NULL`), which is what makes `(union bool (pairof …))`
  disjoint.
- The FX-87 Reference Manual (MIT/LCS/TR-407) is not available
  (`papers/README.md`), so the manual's own `oneof` rule is known only
  through that correction.

## 5. The constructors over FX-26's types

Read each constructor as sets of run-time values of the types it
combines.

| Constructor, over                     | Meaning                                                           | Sound?                                                                                  |
| ------------------------------------- | ----------------------------------------------------------------- | --------------------------------------------------------------------------------------- |
| union of base types, sums, products   | a value of one of them                                            | yes; immutable                                                                          |
| union with `(ref T r)`, arrays, cells | a value of one; the cell's contents stay invariant                | yes if at most one box and one array: otherwise refused (same shape)                    |
| union with `(pairof A B r)` writable  | as above; `nil ∪ pair` already                                    | yes; narrowing is of the variable, never of a path into the pair                        |
| union of `subr` types                 | a procedure of one of them                                        | callable only if parameters agree: then it *is* `(subr (maxeff e₁ e₂) …)`. Refuse       |
| union with a generative type `N`      | a value of `N` or another                                         | only if `N`'s representation's shape is disjoint from the others' (safety sees through) |
| union with `(nat s)`, `nlist` sizes   | naturals are fixnums: same shape as `int`                         | refused; `nat_join` and size facts stay as they are                                     |
| union with a type variable `t`        | depends on what `t` becomes                                       | not in stage 1; section 9, question 3                                                   |
| union with `void`                     | `(union T void)` = `T`                                            | yes                                                                                     |
| intersection of `subr` types          | one procedure with each type                                      | yes, with the value restriction and without distributivity                              |
| intersection of `(ref A r)` types     | one box holding both                                              | **no** (Davies–Pfenning); refused                                                       |
| intersection of other types           | products: positional, no width, so rarely inhabited; bases: empty | not needed; refused                                                                     |
| negation `¬T`                         | every value not a `T`                                             | needs a top type FX-26 does not have; refused                                           |
| difference `S ∖ T`, `S` a union       | the members of `S` whose shapes `T` excludes                      | yes, as a narrowing result only                                                         |

Notes on the pitfalls:

- **Intersections and mutation.** An intersection is introduced only by
  checking a `lambda` (or a `plambda` over one) against each arm. That is
  the value restriction, and FX-26 already has its twin: `(TLam)` allows
  only a closure former under a `poly` (`soundness.md` §2.4). Without
  distributivity, `(λx. new 1)` cannot be given `(and (ref nat r) (ref pos
  r))` through its arrows.
- **Intersections and effects.** Each arm has its own latent effect.
  Calling at an argument that fits arm `i` has arm `i`'s effect. That is
  what makes them useful here: `(overload (subr pure ((listof T acyclic))
  int) (subr spin ((listof T r)) int))` for one `length`. Size-change
  termination is then per arm: the `acyclic` arm is shown to end, the
  other says `spin`.
- **Intersections and conventions.** One closure has one kind, so every
  arm must have the same convention (or `fx`).
- **Unions and mutable cells.** FX-87's `oneof` failed because a
  *mutable tagged* variant was given width subtyping. A union of cell
  types is different: each member cell stays invariant, and nothing
  relates `(union (ref A r) (ref B r))` to `(ref (union A B) r)`. The
  disjoint-shape rule refuses the former anyway, and the latter is an
  ordinary cell whose contents are a union: writing needs an `A` or a
  `B`, reading gives either.
- **Unions and narrowing through the store.** Typed Racket §7.1 is the
  pitfall: narrow `(get c)`, then write `c` through an alias. FX-26
  narrows only variables, and a variable's value never changes; `(let ((x
  (get c))) (typecase x …))` narrows the value read, which stays true.
  Narrowing *paths* (`(car p)` without binding) could be sound too, and
  FX-26 could do what Typed Racket cannot: keep a narrowed path into
  region `r` valid across code whose effect has no `(write r)`. That is a
  later refinement, not needed for the ports.
- **Negation and polymorphism.** `t ∖ nil` for a type variable `t` is
  exactly where set-theoretic systems need `α ∧ ¬nil` (Elixir's `a: not
  (…)`), and where an untagged option loses information when `t` is
  itself `(union nil …)`. FX-26 keeps tagged sums for polymorphic
  options.
- **Negation and generative types.** Generative types are "opaque to
  comparison, transparent to safety" (`fx26.md`). A run-time test cannot
  tell a `ty-id` from an `int`, so the shape of a generative type is its
  representation's, and `(union int ty-id)` is refused as overlapping.
  Giving generative bloblets a type identity would lift this
  (`recursion-and-initialization.md`, option 3, "Disjointness has a
  limit").
- **Regions under unions.** `(union (listof T r₁) (listof T r₂))` is two
  pair shapes, so it is refused; the message should suggest a region
  variable. Masking reads a union's regions as the union of its members'
  (`regions_in`), which needs no new idea.

## 6. Checking

### 6.1 Bidirectional, in both checkers

- **Introduction only by subsumption in checking mode.** `T ≤ (union T
  U)`. A union is never *synthesized*: an `if` or `tagcase` whose arms
  have unrelated types is still an error unless a type is expected
  (`check.rs:551–557` picks the larger arm today, and keeps doing so). A
  binder solved twice keeps the larger, as now, not a union. Scala 3
  widens inferred unions for the same reason: a union found by inference
  turns a local error into a distant one.
- **Elimination only by narrowing a variable.** Not MacQueen's general
  union elimination on any subterm: in call by value it must follow
  evaluation order (Dunfield and Pfenning, FoSSaCS 2003), and it would
  need a third direction in the checker.
- **Intersection introduction**: check the `lambda` once per arm, with
  that arm's parameter types, result and latent effect; errors name the
  arm. **Elimination**: at a call, try the arms in order and take the
  first whose parameters accept the arguments (TypeScript's and Flow's
  rule), rolling back inference state between tries.
- **Subtyping**: union on the left and intersection on the right are
  conjunctions; union on the right and intersection on the left are
  disjunctions, so the trail is restored on a failed branch, as the lemma
  rule does (`check.rs:1538–1566`). With disjoint shapes, a non-union
  left side matches at most one member of a right-side union by shape,
  so there is no real search. The rules are not semantically complete
  (for example `(pairof (union A B) C const)` versus `(union (pairof A C
  const) (pairof B C const))`); Typed Racket and TypeScript accept the
  same incompleteness, and a lemma can state a missing case.
- **Normal form**: a union node is kept flattened, `void` dropped,
  members sorted by shape; two sums merge into one sum (their tags'
  union), which keeps `(union (sumof (a A)) (sumof (b B)))` a sum and
  `tagcase` working on it.
- **Both checkers**: a `Ty::Union` and a `Ty::Overload` node in
  `check.rs`'s arena, the same in `check.fx`'s index arena; a `shape`
  function in each (with generative types through their representation);
  the new rules in `sub` and `k-sub-rules`; `typecase` in the synth and
  check halves; the narrowing of `if`; printing. The agreement tests
  (`checker.rs`, the 80/90 accepted/rejected programs, the front end's
  738 forms) carry over unchanged.

### 6.2 Narrowing: what `tagcase` becomes

- **`typecase`**, proposed: `(typecase e (T x body) … (else y body))`
  where each `T` is a *test type*, a union of whole shapes (`int`, `nil`,
  `(pairof A B r)` with its parts as the static type says, `string`, a
  sum, …), never a type a run-time test cannot decide (a `subr` type, a
  region, a size). Each arm's `x` has the static type's members of that
  shape; `else` has the rest, the difference. Without `else`, the arms
  must cover the union, as `tagcase`'s must cover the sum.
- **`if` on a predicate of a variable**: `(null? x)`, `(pair? x)`,
  `(int? x)`, `(bool? x)`, `(char? x)`, `(string? x)`, `(symbol? x)`,
  `(procedure? x)`, and `(sum? x)` narrow `x` in both branches, by
  binding not by name (as `certify-acyclic` already does, so shadowing
  cannot fool it). `and`, `or` and `not` of such tests combine as
  Typed Racket's propositions do, but only for this fixed set of
  predicates: no latent propositions on user procedures in stage 1
  (question 5).
- **`tagcase` stays** for sums, now also accepting a union that contains
  a sum, its `else` seeing the other tags *and* the other shapes.
- **Datum predicates**: if `datum` becomes a union (stage 3), `datum-int?`
  and the rest are the shape predicates above and `datum-int-value` is
  the identity after narrowing.

### 6.3 Termination, lemmas, confirmation

- **Size-change** (`terminate.rs`, `k-terminates?`): a variable bound by
  a `typecase` arm or narrowed by `if` is the same value as the one
  tested, so it relates to the caller's parameter as that did (the
  certifications already do this). `cdr` of a narrowed pair at `acyclic`
  is a part, as now. Per-arm checking of an intersection makes `spin` a
  property of the arm.
- **Sizes**: unchanged. `(null? xs)` on a `(nlist T n)` already teaches
  `n = 0` or `n ≥ 1`; the non-`nil` pair type is the `n ≥ 1` case's type.
- **Lemmas** (`lemma.rs`): the lemma rule is already a disjunctive
  alternative with rollback, so unions add alternatives, not a new
  mechanism. A lemma body that takes apart a union by `typecase` and
  returns each member rebuilt is still a guarded structural identity, but
  should wait until someone needs it.
- **Confirmation** (`confirmation.md`): `confirm e T` *is* a
  `typecase` whose test type is checked by a walk (CF2). With unions its
  `else` gets `S ∖ T` where `T` is shape-decidable at the top, and the
  walk's per-node test is the shape test of section 7.

## 7. Run-time representation

A value is a tagged word; a bloblet's header carries a kind
(`crates/fixpt-heap/src/value.rs`; `layout.rs:118–159`). The shapes, and
the test for each:

| Type                       | Shape                                      | Test                                |
| -------------------------- | ------------------------------------------ | ----------------------------------- |
| `int`, `nat`, `(nat s)`    | fixnum, tag `000`                          | low 3 bits                          |
| non-`nil` pair             | tag `001`                                  | low 3 bits                          |
| `nil`                      | immediate, subtag 2                        | one compare                         |
| `bool`                     | immediates `#f` (0), `#t` (1)              | one or two compares                 |
| `unit`                     | immediate, subtag 3                        | one compare                         |
| `char`                     | immediate, subtag 8                        | low 8 bits                          |
| `string`, `symbol`         | bloblet, kinds 1 and 2                     | low bits, then the header's kind    |
| `(sumof …)`                | bloblet, kind 36 (`runtime.scm:33`)        | kind; then the tag symbol           |
| `(productof …)`            | bloblet, kind 37: every product alike      | kind                                |
| `(ref T r)`                | box, kind 10 (`runtime.scm:17`)            | kind                                |
| arrays and `bloblet` types | generic bloblets (`runtime.scm:39`)        | kind; one shape for both today      |
| `subr` of any convention   | closure kinds 8, 38, 41                    | kind; `fx` already dispatches on it |
| `float` (planned)          | flonum, kind 5 (`docs/research/floats.md`) | kind                                |
| a generative type          | its representation's                       | its representation's                |
| `datum`                    | several: it *is* Scheme data               | overlaps all of the above           |

- **Free unions.** Any union of distinct rows above costs nothing: the
  value is stored as it is, and a test is a tag check or a tag check and a
  kind load. This is the case for every port in section 2.
- **Unions needing a tag.** Two members of one shape (two products, two
  lists, `int` and a generative `int`) would need a tag the value does
  not have: that is a sum, which FX-26 already has. So the rule "one
  member per shape" is exactly "no hidden tags".
- **The compilers' use of types.** Native code omits checks where types
  prove them: `pair-car` is one `ldur` (`native.fx:541–546`,
  `crates/fixpt-native/src/direct.rs:1205`). That is unsound today for
  `nil`, which the pair types admit. With a non-`nil` pair type, the
  compilers emit the bare load for it and a checked `car` for the
  nullable one; after `(null? x)` the checker has already narrowed `x`,
  so most loops keep the bare load. A union-typed value itself needs no
  check: no operation but a test applies to it until it is narrowed.
- **`typecase` lowers** to the Scheme predicates in the lowering, and in
  the compilers to one new routine (a low-tag test, and a kind test for
  bloblets), both of which the `fx` dispatch already needs.
- **Floats** (`docs/research/floats.md`): raw `d` registers are only for
  the monomorphic `float` and a procedure's second entry. A `(union float
  int)` is uniform (a flonum bloblet or a fixnum) and uses the uniform
  entry, as polymorphic code does; floats.md's "no type ever has two
  layouts" is kept. An unboxed union layout (Julia's inline tag byte)
  is possible later for `f64array`-like containers, not now.
- **Conventions**: a union holds at most one `subr` (by the rule above),
  so it adds no conversion cases; an intersection's arms share one
  convention, so the checker's inserted conversions apply to it whole.

## 8. The recommendation

### 8.1 What, and in what form

1. **A non-`nil` pair type**, proposed spelling `(consof A B r)`, with
   `(consof A B r) ≤ (pairof A B r)` and `nil`'s own type `nil ≤ (pairof
   A B r)`. `null?` narrows a variable's `pairof` to `consof` in its
   `else`; `pair?` the reverse. `car`, `cdr` and `set-car!` accept both;
   on `pairof` the compilers check. Nothing existing breaks.
2. **Unions of disjoint shapes**, `(union T …)`, introduced by
   subsumption where a type is expected, eliminated by `typecase` or by
   narrowing `if`s on a variable. `(listof T r)` stays `(pairof T
   (listof T r) r)`, which is now also `(union nil (consof T (listof T r)
   r))`, and the two are equal.
3. **Difference only as narrowing**, never written. A message prints it
   as the remaining union, as `tagcase`'s `else` prints the remaining sum.
4. **Intersections of `subr` types only**, `(overload (subr …) …)`:
   value restriction, no distributivity, ordered selection at calls,
   one convention.

Proposed syntax, for review (none of it exists):

```
(define-type cell (union bool (consof int int @heap)))      ; mazefun: #f or a pair
(define-type item (union nil int))                            ; destruc: no box per number

(define* count-nil (subr (maxeff (read @heap) spin) ((listof item @heap)) int)
  (lambda (xs)
    (if (null? xs)
        0
        (+ (typecase (car xs) (nil n 1) (else i 0))           ; else: i : int
           (count-nil (cdr xs))))))                           ; xs : (consof …) here

(define-type len-type (overload (subr pure ((listof int acyclic)) int)
                                (subr spin ((listof int @heap)) int)))
(define len len-type                 ; local recursion, so no global read
  (letrec ((len len-type (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs)))))))
    len))
```

The name `union` over `or` because `or` is an expression form and form
names are reserved (`fx26.md`, "Names"); `overload` over `and` or
`inter` because only arrows may be intersected, and the name should say
so. `oneof` is taken by history: FX-87's was tagged.

### 8.2 Additions to the soundness note

For `docs/research/soundness.md`, when stage 2 lands:

- **§1.4 types**: `τ ::= … | (consof τ τ ρ) | nil | ∪(τ₁ … τₙ) | ∧(σ₁ … σₙ)`
  with each `σᵢ` a `subr`; a function `sh(τ) ⊆ Shapes` and `sh(v)` on
  values; well-formedness: the members of a union have pairwise disjoint
  shapes, and each shape is a single set of run-time words.
- **§2.3 subtyping**: the four connective rules; Lemma 2.1 (transitivity,
  inversion) must be redone, since "every rule but `void` and the lemma
  rule relates a former only to the same former" stops being true. The
  inversion that survives: `∪τ̄ ≤ σ` iff each `τᵢ ≤ σ`; `τ ≤ ∪σ̄`, with
  `τ` not a union, only if `τ ≤ σⱼ` for the `j` with `sh(τ) ⊆ sh(σⱼ)`.
  Disjointness is what makes that `j` unique and the proof ordinary.
- **§2.4 typing**: (Typecase), whose arm `i` binds `x : ∪{τ ∈ members(e)
  | sh(τ) ⊆ Tᵢ}` and whose `else` binds the rest; (Narrow) for `if` on a
  shape predicate of a variable; (Overload-I) by value restriction,
  checking the value at each arm; (Overload-E) by subsumption `∧σ̄ ≤ σᵢ`.
- **§3 reductions**: `typecase v …` steps by `sh(v)`; that `sh` is
  decidable on values from the word alone is the lemma the compilers rely
  on.
- **§4 cases**: canonical forms for unions (a value of `∪τ̄` is a value
  of the unique `τᵢ` with its shape); progress for `car` on `consof`
  (never `nil`: the checked error disappears there); preservation of
  narrowing (variables are immutable, so the branch assumption stays
  true); effect soundness per arm (T3), and termination per arm (T5).

### 8.3 Stages

| Stage | Size | What                                                                                                          | Test                                                                                                   |
| ----- | ---- | ------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------ |
| L0    | S–M  | `consof` and `nil` types; `null?`/`pair?` narrow a variable; checked `car` on `pairof` in both compilers      | a native `car` of `nil` is an error, not a crash; the front end's `car`s mostly stay bare (count them) |
| L1    | M    | `shape` in both checkers; `(union …)` of disjoint shapes; `typecase`; shape predicates narrow; both compilers | `destruc`, `lseq`, `browse`, `gcbench`, `earley` without their wrappers; overlapping unions refused    |
| L2    | S    | `tagcase` on a union holding a sum; sums merged in unions                                                     | a union of a sum and `nil`; exhaustiveness errors                                                      |
| L3    | M    | `datum` as a recursive union; `confirm` (CF2) as a `typecase` with a walk                                     | the reader's and parser's datum code, both checkers agreeing                                           |
| L4    | M    | `(overload …)` of `subr` types; per-arm effects and termination                                               | the `len` example: `pure` on `acyclic`, `spin` on `@heap`; a `ref` intersection refused                |
| L5    | L    | research: unions with type variables under a shape bound; latent propositions on user predicates              | only if a program needs it                                                                             |

Before L0: measure how many `car`/`cdr` sites in the front end and the
ports are dominated by a `null?` of the same variable (they will stay
bare) against those that are not (they gain a check), since native speed
is what counts.

**L0, as built (2026-10-07).** The user's answers (section 9): `pairof`
itself non-`nil`, not a new `consof`; the pair that may be `nil` spelled
`(union nil (pairof …))`, the one union so far; type variables in unions
refused; a singleton `false` wanted (L1's stage 3). Both checkers carry
the distinction as a flag on the pair type; `null?` narrows a variable's
`else` (through `not`, `and`, `or`); the pair operations take the pair
that may be `nil`. Not yet: `pair?` (there is none yet for lists), and the
compilers' use of a `pairof` to leave out `car`'s check, which waits on
counting the sites (above). One inference rule changed: inside a pair's
contents, which are invariant, a binder solved already from the context
takes what an argument says, where the two are related (`car` of a list's
element where the context expects a pair that may be `nil`).

**L1's stage 3, as built (2026-10-07).** `false`, the type of `#f` alone,
below `bool` and of its shape: a member of unions (`(union false int)`),
which `bool?` narrows like any shape. `#f` synthesizes `bool`, as before
(so a `ref` made with `#f` still takes `#t`), and checks as `false`
where `false`, or a union with it, is expected.

**L1, as built (2026-10-07).** `(union T …)` of two members or more, of
fourteen shapes (`check.rs`'s `SHAPES`: the tag, and for a bloblet its
kind), normalized (flattened; `nil` beside a pair makes the pair that may
be `nil`); a member of no known shape, or two sharing one, refused. A
recursive type may run through a union: one read with a member not yet
defined is checked once its knot is tied (both checkers, at `grounded`).
Subtyping: a union is below what each member is below, a type below a
union if below a member (a pair that may be `nil`, if `nil` and the pair
are each below one). Inference: a union expected of a call's result
solves it from the member whose shapes hold the result's; `nil` where a
pair that may be `nil` is expected whose tail is no list is of the type
`nil`. The shape predicates (`int?`, `char?`, `bool?`, `null?`, `pair?`,
`string?`, `symbol?`, `procedure?`, `array?`) narrow a variable, as their
types' latent propositions say (a result `(bool (then (shape 0 int))
(else (not (shape 0 int))))`; the checkers read them from the callee's
type, not its name; a call's own type is `bool`), splitting
a union by its members' shapes, a pair that may be `nil` into `nil` and
the pair; `typecase` is sugar over them, `else` required. Shapes are bit
masks in both checkers (the FX-26 one's since `int` has bit operations,
`DONE.md` §55). The shape tests are in line natively (`DONE.md` §56), and
`lseq` is converted: 2.0 s with its union against 4.0 s with its sum
(`--calling-convention native`). The other ports L1 named (2026-10-07,
back to back, natively and in register code): `destruc`'s elements are
`(union nil int)`, as Larceny's, 22.4 → 8.1 s and 8.6 → 7.8 s, no `(num i)`
allocated per element; `browse`'s `item` is `(union symbol (listof item
@heap))`, level (about 11 s and 8.9 s); `gcbench`'s node as Larceny's one
record, a bloblet with children `(union int node)`, was slower, 1.3 → 3.0 s,
`make-bloblet` a call-out natively; made in line (`DONE.md` §57), 1.18 →
0.60 s, so converted; `earley` keeps its sentinels by design, since its configuration
sets' slots 1 to 4 always hold ints, which an `(arrayof (union false
int))` would have to test at every read where Scheme tests none. Not yet: predicates for `f64`, `f32`, `ref`, sums and products (their shapes
are disjoint, but nothing tests for them); a `lambda` checked against a
type proving something (`TODO.md` §54). Paths narrow too since
2026-10-08 (`docs/fx26.md`, "A test narrows a path too"): a fact of
`(car x)` lasts until an effect may write a region the path reads through
or transfers control, as the language's concurrency rule makes sound. Size facts and
certifications are propositions too since 2026-10-08 (`(< a b)`, `(=
(length 0) (lit 0))`, `(acyclic i)`, `(length i j)` …): no test's facts
are read from its name any more, only from its type.

### 8.4 What not to do, and why

- **General negation and a top type**: FX-26 values need not be
  classifiable by one universal test, and a top type would make every
  signature that forgets a type legal. Difference as narrowing is all the
  ports need.
- **Semantic subtyping**: the cost (EXPTIME in general; NP-hard even for
  MLstruct's algebra) buys completeness FX-26's programs do not ask for,
  and both checkers would have to implement it identically.
- **Inferred unions**: errors move away from their cause, and the
  checkers' messages are their product.
- **Unions of overlapping shapes**: they are hidden tags; write a sum.
- **Intersections of non-procedure types**: with refs they are unsound,
  and products are positional, so nothing gains.

## 9. Open questions for you

1. **Is the disjoint-shape rule the right line?** It forbids `(union
   (listof A r) (listof B r))` and `(union int ty-id)`, and makes every
   union free at run time. The alternative, unions with hidden tags, is
   sums by another name.
2. **`consof` first, and should `pairof` stay nullable?** Making `pairof`
   non-`nil` and writing lists as `(union nil (consof …))` is cleaner but
   touches every signature in the front end; a separate `consof` breaks
   nothing. Which way, and is fixing native `car` of `nil` this way (a
   check only where the type is nullable) what you want?
3. **Type variables in unions.** `(union t nil)` needs either a bound on
   `t` ("not `nil`", as Kotlin's `T : Any` or Elixir's `not`), or to stay
   refused. Refused until a program needs it?
4. **`overload` at all?** Its best use found is per-argument effects and
   `spin` (and nat arithmetic, which the checker special-cases for `+`
   and `-` today). Is that worth a second arrow-like former in both
   checkers, or should it wait for a program that asks?
5. **Latent propositions on user procedures** (Typed Racket's filters,
   Python's `TypeIs`): a user-defined `item-null?` could narrow its
   argument. Stage 1 narrows only by the built-in predicates; is that
   enough?
6. **Singleton `false`?** Scheme's "X or `#f`" wants `#f` alone; `(union
   bool X)` also admits `#t`. A `false` type below `bool` (FX-87 had a
   singleton, `null`) is cheap; wanted?
7. **Exceptions.** The `outcome` sums in the OCaml ports are a
   prompt-tag answer-type problem, not a union problem (section 2). Shall
   I write that up separately: tags whose prompts each choose an answer
   type, when no composable capture can reach them?
8. **`datum` as a union (L3)**: its operations would become `car`,
   `cdr` and narrowing, and `datum-car` of a non-pair, a checked error
   today, would be a type error. Is changing `datum`'s operations in the
   front end acceptable?

## Sources

Read 2026-09-29 unless noted. Page numbers are the PDF's own printed
pages where it has them.

On disk:
- `~/Dev/LangPlay/GiffordHistory/mit-psrg-fx/fx87/old-impl/standard.lisp`
  (lines 590–663 `oneof`; 1596–1597 the correction; 1614–1616 `null`;
  1670–1696 the `oneof` subtyping rule), `init.lisp:62–63`,
  `mit-psrg-fx/fx87/library/polynm.fx:120`.
- Gifford, Jouvelot, Sheldon, O'Toole, *Report on the FX-91 Programming
  Language*, `~/Dev/LangPlay/GiffordHistory/papers/fx91-report.pdf`,
  pp. 4, 12, 22.
- `~/Dev/LangPlay/GiffordHistory/papers/README.md` (TR-407 not found);
  `README.md` (`compatlisp-nil`).

Online:
1. G. Castagna, "Programming with union, intersection, and negation
   types", arXiv:2111.03354**v4** (27 Mar 2024),
   https://arxiv.org/pdf/2111.03354, pp. 16, 18, 33, 56; also in *The
   French School of Programming*, Springer, 2023.
2. A. Frisch, G. Castagna, V. Benzaken, "Semantic subtyping: dealing
   set-theoretically with function, union, intersection, and negation
   types", JACM 55(4), 2008, https://www.irif.fr/~gc/papers/semantic_subtyping.pdf
   (cited through [1]; not read in full).
3. R. Davies, F. Pfenning, "Intersection types and computational
   effects", ICFP 2000, pp. 198–208, https://www.cs.cmu.edu/~fp/papers/icfp00.pdf,
   pp. 198–200.
4. S. Tobin-Hochstadt, M. Felleisen, "Logical types for untyped
   languages", ICFP 2010, https://www2.ccs.neu.edu/racket/pubs/icfp10-thf.pdf,
   PDF pp. 3–4, 8, 10 (§7.1).
5. S. Tobin-Hochstadt, M. Felleisen, "The design and implementation of
   Typed Scheme", POPL 2008, https://www2.ccs.neu.edu/racket/pubs/popl08-thf.pdf
   (not read in full).
6. L. Parreaux, C. Y. Chau, "MLstruct: principal type inference in a
   Boolean algebra of structural types", OOPSLA 2022,
   https://doi.org/10.1145/3563304; extended version v8.0,
   https://lptk.github.io/files/[v8.0]%20mlstruct.pdf, pp. 6, 9, 13, 19, 21;
   code https://github.com/hkust-taco/mlstruct (branch `mlstruct`, not
   pinned).
7. C. Y. Chau, L. Parreaux, "The simple essence of Boolean-algebraic
   subtyping", POPL 2026, https://doi.org/10.1145/3776689 (abstract, from
   https://cse.hkust.edu.hk/~parreaux/publication/popl26/).
8. S. Dolan, A. Mycroft, "Polymorphism, subtyping, and type inference in
   MLsub", POPL 2017, https://doi.org/10.1145/3093333.3009882 (abstract).
9. L. Parreaux, "The simple essence of algebraic subtyping", ICFP 2020,
   https://infoscience.epfl.ch/record/278576 (abstract).
10. G. Castagna, G. Duboc, J. Valim, "The design principles of the Elixir
    type system", ‹Programming› 8(2), 2024, article 4,
    https://arxiv.org/pdf/2306.06391 (latest version on the date read),
    pp. 4:7–4:8, 4:12, 4:17–4:18.
11. G. Castagna, V. Lanvin, M. Laurent, K. Nguyen, "Revisiting occurrence
    typing", SCP 217, 2022, https://arxiv.org/abs/1907.05590 (abstract).
12. G. Castagna, M. Laurent, K. Nguyen, M. Lutze, "On type-cases, union
    elimination, and occurrence typing", POPL 2022,
    https://doi.org/10.1145/3498674 (abstract).
13. D. J. Pearce, "Sound and complete flow typing with unions,
    intersections and negations", VMCAI 2013, LNCS 7737,
    https://whileydave.com/publications/Pea13_VMCAI_preprint.pdf (abstract).
14. M. Coppo, M. Dezani-Ciancaglini, "An extension of the basic
    functionality theory for the λ-calculus", Notre Dame J. Formal Logic
    21(4):685–693, 1980, https://dblp.org/rec/journals/ndjfl/CoppoD80.html
    (bibliographic record only).
15. J. C. Reynolds, "Design of the programming language Forsythe",
    CMU-CS-96-146, 1996, https://apps.dtic.mil/sti/pdfs/ADA311094.pdf
    (download refused, 403; content *from memory*).
16. B. C. Pierce, *Programming with Intersection Types and Bounded
    Polymorphism*, PhD thesis, CMU-CS-91-205, 1991,
    https://www.cis.upenn.edu/~bcpierce/papers/chronological.html
    (bibliographic entry; content *from memory*).
17. T. Freeman, F. Pfenning, "Refinement types for ML", PLDI 1991,
    https://dl.acm.org/doi/10.1145/113446.113468; R. Davies, *Practical
    Refinement-Type Checking*, CMU-CS-05-110, 2005 (abstracts).
18. J. Dunfield, F. Pfenning, "Type assignment for intersections and
    unions in call-by-value languages", FoSSaCS 2003,
    https://research.cs.queensu.ca/home/jana/papers/union-assignment/Dunfield03_union-assignment.pdf;
    "Tridirectional typechecking", POPL 2004; J. Dunfield, "Elaborating
    intersection and union types", ICFP 2012, https://arxiv.org/pdf/1206.5386
    (abstracts).
19. H. Hosoya, B. C. Pierce, "XDuce: a statically typed XML processing
    language", ACM TOIT 3(2), 2003, https://www.cis.upenn.edu/~bcpierce/papers/xduce-toit.pdf;
    H. Hosoya, J. Vouillon, B. C. Pierce, "Regular expression types for
    XML", TOPLAS 27(1):46–90, 2005, https://www.cis.upenn.edu/~bcpierce/papers/regsub-toplas.pdf
    (EXPTIME-completeness of inclusion, from its abstract).
20. V. Benzaken, G. Castagna, A. Frisch, "CDuce: an XML-centric
    general-purpose language", ICFP 2003, https://www.irif.fr/~gc/papers/icfp03.pdf
    (abstract).
21. F. Muehlboeck, R. Tate, "Empowering union and intersection types with
    integrated subtyping", OOPSLA 2018, https://doi.org/10.1145/3276482
    (abstract).
22. Ceylon 1.0 specification, ch. 3, "Type system",
    https://ceylon-lang.org/documentation/1.0/spec/html/typesystem.html
    (via search summary).
23. Scala 3 reference, "Union Types – More Details",
    https://docs.scala-lang.org/scala3/reference/new-types/union-types-spec.html
    (current on the date read).
24. TypeScript Handbook, "Narrowing",
    https://www.typescriptlang.org/docs/handbook/2/narrowing.html
    (current on the date read).
25. Flow documentation, "Unions", "Intersections", "Type Refinements",
    https://flow.org/en/docs/types/unions/,
    https://flow.org/en/docs/types/intersections/,
    https://flow.org/en/docs/lang/refinements/ (via search summary).
26. Luau, "Union and Intersection Types",
    https://luau.org/types/unions-and-intersections/, and "Type
    Refinements", https://luau.org/types/type-refinements/.
27. Python typing specification, "Type narrowing",
    https://typing.python.org/en/latest/spec/narrowing.html; PEP 742,
    https://peps.python.org/pep-0742/ (via search summary).
28. T. Lindahl, K. Sagonas, "Practical type inference based on success
    typings", PPDP 2006, pp. 167–178, https://doi.org/10.1145/1140335.1140356
    (abstract).
29. Julia developer documentation, "isbits Union Optimizations",
    https://docs.julialang.org/en/v1/devdocs/isbitsunionarrays/; "Union-splitting:
    what it is, and why you should care", https://julialang.org/blog/2018/08/union-splitting/
    (via search summary).
