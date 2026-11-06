# Logical type constructors: union, intersection, difference

Design note, 2026-09-29; revised 2026-11-04 (sections 0, 8.4, 8.5 to
8.7, 9). Research only: no code was changed. The question: what intersection, union and negation (or set-difference) types
would mean in FX-26, which of them are sound with its refs, regions and
effects, what they cost the two checkers and the compilers, and whether to
add any.

Sources were read online on 2026-09-29 and are listed at the end, with
URL and version; a claim marked *(from memory)* was not checked against a
source. FX-26 facts cite files in this repository; FX-87 and FX-91 facts
cite `~/Dev/LangPlay/GiffordHistory`.

## 0. The recommendation, in brief

**Revised 2026-11-04, the user's direction.** Proper intersection *and*
union types, before macros (`TODO.md` §79, §182). What drove it: Herman
and Wand's swap, `(sym sym D) → D` for every syntactic sort D of λm,
over sorts encoded as sub-sums of one another, wants one body with
several types, and its callers the sort kept (section 8.5). Two rules of
the first recommendation (below; §8.4) are lifted, each under a
condition: unions of overlapping members (a *true* union, beside today's
disjoint one, renamed), and intersections beyond procedure types, as the
meets a call's result takes. Sections 8.5 to 8.7 are the revised design,
section 9.2 its questions. The first recommendation follows as it was;
its stages L0 to L3 are built.

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
  intersections of non-procedure types. (The last two lifted 2026-11-04,
  with conditions: section 8.5.)

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
- **Liquori and Stolze** (Inria hal-01488428, 2017): see section 8.5.
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
  the identity after narrowing. (Done 2026-10-08, `TODO.md` §51: the
  predicates and accessors are gone, `datum-int?`, the fixnum test, narrows
  to `int`.)

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
  *Lifted 2026-11-04* (section 8.5): a true union is not a hidden tag,
  since nothing at run time is asked to tell its members apart; what
  holds of it is only what holds of every member. The disjoint union,
  which a shape test does split, stays, under another name.
- **Intersections of non-procedure types**: with refs they are unsound,
  and products are positional, so nothing gains. *Lifted 2026-11-04 for
  meets that are computed, never written* (section 8.5): sums and
  products have exact structural meets, and the refs that make them
  unsound are refused a meet unless equal.

### 8.5 Revision (2026-11-04, settled 2026-11-05): `anyof`, `oneof`, `allof`

Three formers, the user's names (question 9): `(anyof T …)` a true
union, `(oneof T …)` a union whose members a run-time test separates
(today's `union`, renamed), `(allof (subr …) …)` an intersection of
procedure types (designed as `overload`). The name `union` goes. What
follows is the design as the user settled it in section 9.2.

**The case.** The user encoded λm (Herman and Wand, "A Theory of
Hygienic Macros", ESOP 2008) with structural types, each syntactic sort a
sub-sum of the next: `expr`'s variants are among `sexp`'s under the same
tags, as `s ::= e | op | (s̄)` reads, and a variable is an `expr` and an
`op` alike. The paper's α-equivalence (its §3) is Gabbay and Pitts'
swapping, one definition over every sort. Proposed syntax:

```
(define-type expr (sumof (var symbol) (lam (productof (1 symbol) (2 expr)))
                         (app (productof (1 expr) (2 expr)))))
(define-type op (sumof (var symbol) (mac macro)))
(define-type sexp (sumof (var symbol) (lam (productof (1 symbol) (2 expr)))
                         (app (productof (1 expr) (2 expr)))
                         (mac macro) (seq (listof sexp acyclic))))

(define-type swapper (allof (subr pure (symbol symbol expr) expr)
                            (subr pure (symbol symbol op) op)
                            (subr pure (symbol symbol sexp) sexp)))
(define* swap swapper
  (lambda (a b s)
    (tagcase s
      (var x (sum var (swap-name a b x)))
      (lam p (sum lam (product (1 (swap-name a b (extract p 1)))
                               (2 (swap a b (extract p 2))))))  ; the expr member
      (app p (sum app (product (1 (swap a b (extract p 1)))
                               (2 (swap a b (extract p 2))))))
      (mac m (sum mac (swap-macro a b m)))        ; not an expr's: skipped there
      (seq l (sum seq (swap-each a b l))))))      ; only an sexp's
```

Defined at `sexp` alone, `swap` loses for its callers that an `expr`
swapped is an `expr`. As a `poly` over D it cannot be written:
parametricity forbids taking a D apart, and a bound `D ≤ sexp` still
gives no way to build one, unless D's constructors are passed in. One
body with several typings is an intersection: Davies and Pfenning's
refinement types (section 3.1), Liquori and Stolze's strong conjunction
(below). Every member shares one representation; nothing here asks for
code per member (that is `case-lambda`, `TODO.md` §111).

**Liquori and Stolze** ("A Decidable Subtyping Logic for Intersection
and Union Types", Inria hal-01488428, 2017; the user's): ∩ as one term's
several typings (their typed calculus' ∩I asks the two derivations'
erasures β-equal: one program), ∪ its dual, and a sound decision
procedure for subtyping in BCD's theory Ξ, the first, they say, with
unions. Ξ has distributivity, `σ ∩ (τ ∪ ρ) ≤ (σ∩τ) ∪ (σ∩ρ)`, `(σ→τ) ∩
(σ→ρ) ≤ σ → (τ∩ρ)` and `(σ→ρ) ∩ (τ→ρ) ≤ (σ∪τ) → ρ`, over pure λ-terms.
FX-26 takes from Ξ only what the rules below need, each where its
condition holds: section 3.1's reason for dropping distributivity is
refs, and the conditions are what keep refs out.

**Five rules**, as the user settled them (questions 10 to 13).

1. **Intersection introduction, per member** (as section 6.1): the
   `lambda` is checked once per member, each with that member's
   parameters, result and latent effect; a recursive reference sees the
   whole intersection. Errors name the member.
2. **Dead arms** (question 12). Only while checking an `allof`'s
   members: checked against one member, a `tagcase` arm whose tag
   that member's subject type lacks cannot run: it is skipped, neither
   checked nor refused (today: "has no tag", `k-tagcase-arms`). An arm
   skipped under *every* member is refused as now, so a misspelt tag is
   still an error. Davies' refinement checking has the same rule. With
   it, the swap above checks: under `expr`, `mac` and `seq` are skipped,
   and a `lam` rebuilt from a symbol and a swapped `expr` is an `expr`.
   - *Shape tests* (2026-11-05, the user's, from their λm `swap` written
     with `cond`). An `if`'s branch (so a `cond`'s clause, and a
     `typecase`'s arm, which are `if`s of shape tests) is skipped under a
     member where its test narrows a variable to `void`: a shape test the
     variable's type cannot pass, or cannot fail (`null?` of a `symbol`,
     `symbol?` of a sum), narrows it to `void` while an `allof` is checked
     (outside one, nothing changes). One skipped under every member is
     checked under the last, as it would be outside an `allof`, so that its
     code has facts and its errors are said; not refused, as an `if` with
     a branch no value takes is not refused elsewhere. A skipped branch's
     facts are not compared (rule 3): its place is the whole of the chain
     a `cond` or `typecase` makes (`Checker::extent`, `k-extent`), each
     `typecase` arm's parts at the arm, as a `cond` clause's are. Tests
     `allof/cond-dead*.fx`, `allof/typecase-dead.fx`.
3. **One body, one code.** The compilers read facts the checker records
   per node (conversions, reshapes, standard operators, operand types,
   sizes). Checked once per member, a node gets them once per member;
   where they differ, the one body cannot be compiled for all, and the
   `allof` is refused at that node (question 13; taking the more general
   of two ordered facts, a checked `car`, is a later relaxation by an
   explicit list) ("uniform representation", made
   precise: not a property of the types but of the facts). Re-checking a
   node is a hazard already: a module reshaped twice over composed its
   reshape with itself until `8616f2fe`; each fact must be recorded so
   that a second check replaces, never compounds, the first.
4. **Intersection elimination: every member a call fits; the result their
   meet.** With sub-sums several members fit, and none need be best: an
   `expr` fits `expr`'s and `sexp`'s; a variable fits all three, `expr`
   and `op` apart. Ordered selection (section 6.1, TypeScript's) is
   fragile there. Each fitting member is a typing of the one call (∩E),
   so the call has them all: its result the meet of their results, its
   effect the *intersection* of their latent effects (the body runs once,
   inside each), the `length` case's `pure` where the list is
   `acyclic`. Swapping in a `(sum var x)` gives `expr ⊓ op ⊓ sexp`, which
   is `(sumof (var symbol))`.
   - *This is distributivity*, `(A→B) ∩ (A→C) ≤ A → (B ∩ C)`, which
     Davies and Pfenning drop because `(λx. ref 1)` would have `(ref nat)
     ∩ (ref pos)`. So the meet is defined only where it is exact and
     sound: base types (a type with itself; `nat` and `int` give `nat`;
     sizes by `nat_join`'s dual), sums (the tags in common, their
     payloads' meets; none in common, `void`), products (field by field),
     immutable pairs and lists (`acyclic`, `const`: part by part),
     `subr` types (an intersection: their `allof`). A cell, an array, a
     writable pair, a region, a type variable or a generative type meets
     another only if equal. Where the results of the fitting members have
     no meet, the call is refused, naming them (the caller `proj`s or
     annotates).
   - *Fresh regions* (2026-11-05, the user's question; soundness finding
     F18). Two `subr` types do not meet where they name a region the call
     allocates in (a fitting member's latent `alloc`, not of frozen data).
     The body is checked under each member, so a cell it makes may be typed
     by each member's parameter, `(ref ab)` under one and `(ref ac)` under
     the other; a closure kept in the result may hold it, and their
     `allof` would be one cell with both views: write a `b` as an `ab`,
     read it as an `ac` (`allof/fresh-closure.fx`, which ran and took the
     wrong arm). It is the distributivity above, at a call that allocates.
     The call's own effect is looked at, before masking hides it
     (`fresh-closure-masked.fx`). What a call makes is in a region a view
     of it names (a `ref`'s, or a reader's or writer's latent effect); a
     cell that existed before the call has one type, which every member
     agrees on, as cells are invariant; and every maker of mutable storage
     says `alloc` (`every_maker_of_mutable_storage_allocates`), no cell
     being polymorphic (`allof/poly-cell.fx`). Frozen data, `acyclic` or
     `const` (a `letfreeze`'s, cyclic or not), is made with no `alloc` in
     a region it names, and is one value of both types
     (`frozen-results.fx`, `frozen-ring.fx`); so is what a call allocates
     where its results do not look (`fresh-elsewhere.fx`). Where two
     results are related, the lesser is one member's typing, sound alone.
5. **Union elimination at a call's arguments** (question 11: at U3). A
   call's argument is
   evaluated once, before the call: Dunfield and Pfenning's condition for
   ∪E in call by value (section 3.1). So where an argument's type is a
   union and the call does not fit it whole, it is checked per member,
   and its type is the union over the members of what rule 4 gives:
   `swap` of an `(anyof expr op)` is an `(anyof expr op)`. One argument
   split at a time, only when the whole fails, so the cost is the
   members', not their product. This is Ξ's `(σ→ρ) ∩ (τ→ρ) ≤ (σ∪τ) →
   ρ` at calls only, not between procedure types (passing `swap` where a
   `(subr pure (symbol symbol (anyof expr op)) …)` is expected stays
   refused: later, if a program needs it).

**True unions.** `(anyof T …)`: a value of one of them, no test
required to tell which. At U2 its members are immutable: two that are
cells, arrays or writable pairs are refused (question 14; lifting it
later breaks nothing).
- *Introduction* by subsumption, as now; never synthesized (section 6.1).
- *Elimination*: by subsumption to a type above every member; by rule 5
  at calls (which takes `car`, `extract`, `with` and the rest, since
  they are calls); by narrowing on a shape test, which keeps the
  members of that shape, a union still if several share it.
- *Normal form*: flattened; `void` dropped; a member below another
  dropped (as built, only one the same as another: the rest is §8.8's,
  on demand); **sums merged** (as built since U3, on demand: kept as
  written, made one where one sum is needed), `(anyof (sumof (a A) (b B)) (sumof (a C) (c
  D)))` is `(sumof (a (anyof A C)) (b B) (c D))`, exactly the same set of
  values, since a sum's representation names its tag, not its type's
  tags. So `(anyof expr op)` is a sub-sum of `sexp` as written. Products
  are not merged: `(anyof (productof A B) (productof C D))` keeps the
  correlation that `(productof (anyof A C) (anyof B D))` loses.
- *Subtyping*: as section 6.1, but `τ ≤ ∪σ̄` may now hold through
  several members, so it tries each with the trail rolled back, as the
  lemma rule does (`check.rs`, the lemma rule). Not complete (section
  6.1's example stands); a lemma states a missing case.
- *Cells* (refused at U2, question 14; what lifting it would mean): a
  union of cells is not a cell of a union (section 5). Reading
  through `(anyof (ref A r₁) (ref B r₂))` gives `(anyof A B)` with effect
  `(read r₁) ∪ (read r₂)`; writing needs a value of `A ⊓ B` (rule 4's
  meet, so equal cells' contents, or immutable ones that meet), effect
  both writes. Regions: `(anyof (listof T r₁) (listof T r₂))` would be a
  type; section 5's message suggesting a region variable stays as a hint.
- *Representation*: none; a union is what its members are. A compiler
  may not assume a member it was not told by a narrowing.

**Disjoint unions: `oneof`.** Today's `union` is the disjoint kind by
construction (L1): members of pairwise distinct shapes, so a shape test
splits it, and `typecase` without `else` is exhaustive. Renamed `oneof`
(U0), with two settlements (question 9):
- *Well-formed* when a run-time test separates every two members: by
  shape (the word's tag, a bloblet's kind) or, for two sums, by tag, their
  tag sets disjoint. `(oneof (sumof (a A) (b B)) (sumof (c C)))` is
  well-formed; `(oneof (sumof (a A)) (sumof (a B)))` is not. A
  `typecase` arm for a sum member tests the shape, then the tag.
- *The same type as `anyof`* of its members: the same values, each
  below the other. `oneof` is an `anyof` whose members are checked where
  it is written: one node in each checker, printed `oneof` when its
  members are disjoint. Type variables stay out of `oneof` (question 3).

The renaming is mechanical: both checkers, the front end, the ports, the
docs; every `(union nil (pairof …))` becomes `(oneof nil (pairof …))`.
Further tests, singleton types and discriminants at a path, are future
work (question 9's notes).

**Intersections, written.** Only `(allof (subr …) …)` is written.
The meets of rule 4 are computed and print as the sum or product they
normalize to; one that does not normalize (two type variables) is not
formed (no meet: refused). No `inter` of data types is proposed.

**Effects, sizes, termination.** Per member, as section 5 says; a
`spin` judged per member (`len`'s `acyclic` member ends, its `@heap` one
spins). Size facts from a narrowing are per member check, and rule 3
compares them like any fact.

### 8.6 Additions to the soundness note, for the revision

- **§1.4 types**: `∪` without the disjointness side condition; the
  disjoint former (`oneof`) as `∪` with it, its side condition the
  separating tests; `∧(σ₁ … σₙ)` of `subr`s (`allof`); a partial
  `⊓` on types, defined as rule 4 lists, undefined at every invariant
  position whose two sides differ.
- **§2.3 subtyping**: Lemma 2.1's inversion becomes disjunctive for
  `τ ≤ ∪σ̄`; transitivity must be re-proved with it (Muehlboeck and Tate,
  OOPSLA 2018, is the model for a syntactic, decidable version).
- **§2.4 typing**: (Overload-I) per member, with the dead-arm rule as
  (Tagcase) whose arm for an absent tag is unconstrained when the
  subject's type rules the tag out (the arm cannot be reached: the
  progress case for `tagcase` needs only the arms of the tags the type
  has); (Overload-E) by ∩E at each fitting member and the meet,
  sound because `⊓` is defined only where `⟦A ⊓ B⟧ = ⟦A⟧ ∩ ⟦B⟧`
  holds of immutable values (the lemma to prove; refs excluded
  by construction); (Union-E-arg), ∪E in argument position.
- **§3, §4**: preservation through ∪E-arg (the argument is a value of
  one member when the call steps); canonical forms for `∪`
  without disjointness (a value of `∪τ̄` is a value of *some* `τᵢ`);
  rule 3's obligation for the compilers: the code made from a body's
  facts is the same under every member's check.

### 8.7 Stages, for the revision

| Stage | Size | What                                                                                                          | Test                                                                                     |
| ----- | ---- | ------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------- |
| U0    | S–M  | `union` renamed `oneof`; sums with disjoint tags well-formed members                                          | every existing program, renamed; two sums of disjoint tags; both checkers agree          |
| U1    | M–L  | `allof` of monomorphic `subr` members: rules 1 to 4, `⊓` on base types, sums, products, immutable lists        | the user's λm swap over `expr`, `op`, `sexp`; `len`'s `pure`/`spin`; cells refused (`allof/cell-*.fx`, `fresh-*.fx`, from 2026-11-05) |
| U2    | M    | `anyof`: overlapping immutable members, sums merged, disjunctive subtyping with rollback, narrowing that leaves unions | `(anyof expr op)` a sub-sum of `sexp`; two cells, or two writable lists, refused          |
| U2b   | M–L  | lazy normalization (§8.8): head forms by shape, greatest members, splits on failure with a budget, caches     | `car` of an `anyof` of `nat` and `int` lists; a pair of a union below a union of pairs; a mixed list refused    |
| U3    | M    | rule 5, ∪E at arguments                                                                                       | `swap` of an `(anyof expr op)`; `car` of an `anyof` of two `acyclic` lists               |
| U4    | M    | members that are `poly` (`TODO.md` §79's `length` over `nlist` and `listof`)                                 | `length` of an `nlist` gives its size, of a `@heap` list `(read r)`                      |
| U5    | L    | research: Ξ's arrow rules between procedure types; shape-directed conversion's σ-indexed arms                  | only if a program needs it                                                               |

**U0, as built (2026-11-05).** `oneof` in both checkers (`union` still
read as it, for Heist's and kayak's programs); two sums with no tag in
common well-formed members, made one sum where written (not where a
member is a recursive type's own name, not yet defined: refused); every
`(union …)` in the sources, tests, ports and `fx26.md` renamed; messages
and type representations say `oneof`. Tests: `unions/oneof-sums.fx`,
`oneof-sums-share.fx`, `union-still-read.fx`.

**U1, as built (2026-11-05).** `(allof (subr …) …)` in both checkers
(Rust's `Ty::AllOf`, `check_allof_lambda`, `synth_allof_call`, `meet`;
FX-26's `ty-allof` and `check-allof.fx`), rules 1 to 4 as above, with
these choices (CLAUDES_CHOICES.md, "U1"): a call's arguments are
synthesized once and a member fits by subtyping alone (no conversion or
reshape at an `allof` call); two members' facts are compared only where
both checked (outside the arms either skipped), and kept together; each
expression's effect summary is the greatest under any member; a call's
latent effect is the least of the fitting members' if one is, else the
first's; recursion ends if it does at each member's types.

**The verifier of typed cellular code (2026-11-05)**, in part. A call of
an `allof` takes every member the arguments' types fit, the meet of their
results and the least latent effect, as the checkers do; with none fitting
whole, rule 5 at an argument of a union. An `allof`'s lambda, and each
inside it, is certified at each member's signature (`Cert::variants`, from
`NodeFacts::lambda_variants`, which each member's check records): its word
must verify at each, and a closure of it is of the `allof` of those its
free values fit (a lambda inside an `allof`'s body, made under one member,
of that member's). A shape test a value's type cannot pass (or fail) makes
its way unreachable (a `void` value), in any word. Each variant's type
notes and operations are made of its own member's check (2026-11-06):
each member's check records what it found inside the body, each
expression's type and instantiations (`check::MemberFacts`), and the
compiler, which knows which fact each note and operation was made of
(`Compiler::fact_of`), makes them again of that member's (a join's type,
an instantiation, a `sum` made, at each member its own). A call that
fits an `allof` whole, and by rule 5 too at a result within the whole's,
has the closer, as the checkers take it where the whole's is not what
is expected; and `car` of an `anyof` of pairs is the `anyof` of their
parts. No `allof` or `anyof` word is a known gap now.

**Arguments at an `allof` call (2026-11-05).** A `lambda` with a
parameter of no type has no type of its own: it fits a member whose
parameter there is a procedure of its arity, and is checked, once the
members are known, against what they take there, their `allof` where they
differ (rule 3 then holds of its body). An argument a member takes only
converted (its procedure to another convention) or reshaped (a module)
fits it, the adaptation made once: only where every member the call fits
takes the same type there, else one value would be made two ways
(refused). Integer literals beyond a member's range are not taken so: a
literal synthesizes as an `int`. Tests: `allof/lambda-argument*.fx`,
`converted-argument.fx`, `converted-twice.fx`.

**Rule 5 at any argument (2026-11-05, U3's leftover).** An argument that
is no variable, of a union, is taken apart as a variable is: the call is
checked with it taken as each member in turn (`pinned`, `k-pinned`),
wherever it is synthesized or checked as a call; its value is made once.
An argument checked against a type it is given in some other way (an `if`
checked against a parameter) is not pinned, and the call is refused as
before. Test: `anyof/split-call.fx`.

**Over products (2026-11-05, the user's reading of the paper).** An
`allof` of products of the same labels, in order, is the product whose
field is what every member's is, where they are the same (by structure,
`same_ty`, `k-same-type?`), and the `allof` of the members' fields where
they differ: in procedure types, or products of them, distributed in turn.
A field that differs otherwise has no meet written (two cells of different
types, F18's reason, among them) and is refused, naming the field; so is a
product among `subr` members. Both checkers (`Checker::allof_of`;
`k-allof-of`, `check-read-allof.fx`). Tests: `allof/product*.fx`.

**Termination per member (2026-11-05).** Each binding of a recursive
group is a node at each member of its `allof` (one at its type for a
binding of no `allof`), its body walked at that member's parameter types,
passing over the `if` branches (a standard shape predicate, or its `not`,
of a value whose type is known) and the `tagcase` arms (a tag the sum
lacks) those types rule out, as checking it against that member does
(rule 2). Each call goes to every member its arguments' types fit, by
subtyping where the walk knows them, to every member where it does not. A
node ends if size-change holds for the calls reachable from it; a call
says `spin` only where a member it fits may not end; naming the callee as
its operator says none of its own. So `len` of the table checks: `pure` on
`acyclic` lists, `spin` on lists at `@heap` (`allof/len-by-member.fx`).
Calls that alternate between members are one graph, so a loop through
both that grows is refused though each member's calls alone shrink
(`members-alternate.fx`). Both checkers (`termination_by_member`,
`member_spins`; `k-termination-by-member`, `k-member-spins`). Tests:
`tests/programs/allof/` (swap, the meet, and four refusals).

**U2, as built (2026-11-05).** `(anyof T …)` in both checkers, one node
with `oneof`'s (`Ty::Union`, `ty-union`), printed `oneof` where no two
members share a shape, else `anyof`. Normal form as above, but for a
member below another: only one the same as one before it is dropped
(CLAUDES_CHOICES.md, "U2": FX-26 reads types before it has subtyping).
Members that may be written (cells, arrays, bloblets, pairs and lists not
frozen) must be told apart by shape from the rest. Subtyping needed
nothing new: both checkers already tried each member with the trail
rolled back. Where inference took a union's first member of a shape, it
now takes one only if it alone has it. Tests: `tests/programs/anyof/`
(`(anyof expr op)` a sub-sum of `sexp`, overlapping lists narrowed, a
`oneof` and an `anyof` as one type, a recursive one, and three refusals:
two cells, two writable lists; the sums' shared tag shown).

**U3, as built (2026-11-05).** Rule 5 in both checkers
(`synth_app_split` in `infer.rs`, `k-split-app` in `check-allof.fx`):
where a call fails whole, an argument that is a variable whose type is a
union is narrowed to each member in turn and the call checked again; if
every member checks, the call's type is the `anyof` of theirs, its effect
theirs together, and the facts the compilers read must be alike under
every member, as an `allof`'s body's (CLAUDES_CHOICES.md, "U3"). The
first such argument that works is taken; one argument at a time, so the
cost is the members', never their product. Not tried where the error is
inside an argument that is not a variable (a nested call's, a `lambda`'s
body's): no member of another argument changes it. Not covered: an
argument that is not a variable (bind it with `let`); and `extract`, which
is a form, not a call. Tests: `anyof/car-split.fx`, `car-split-misfit.fx`,
`allof-split.fx`.

*Then, the same day, the user's*: `swap` of an `(anyof expr op)` gave an
`sexp`, since U2 made the two sums one where the union was written and
left nothing to take apart ("normalizing the type there causes the
subsequent application to fail … not my intention nor expectation"). So an
`anyof`'s sums are kept as written (`logical-types.md` §8.8's direction),
their one sum a head form made where one is needed: `tagcase` of the union
(`sum_head`, `k-sum-head`), and a sum shown below the union when no member
takes it whole (`sums_joined_raw`, `k-sums-joined-raw`: each payload the
union of the distinct ones, unchecked, since a subtype test may not fail).
Writing one still checks that its sums can be made one. A recursive
`anyof` of sums, refused before, is taken. And rule 5 applies also where a
call checks but not as what is expected: taken apart, it is kept if its
union is; else the whole call as it was, for the expectation to refuse. So
`swap` of an `(anyof expr op)` is an `(anyof expr op)`
(`anyof/swap-anyof.fx`). A `oneof`'s sums are still made one where it is
written (U0).

Each stage in both checkers, agreeing, as L0 to L3 were. U1 before U2
because swap needs only it: `sexp` is written as the sum it is. U0 to U3
before macros (`TODO.md` §182), U4 and U5 after (question 15).

### 8.8 Lazy normalization (U2b, proposed 2026-11-05)

The user's concern (2026-11-05): without normalizing, the checker either
refuses programs it should take, or makes their authors write
boilerplate to get past it, or blows up while checking. U2 drops only a
member the same as one before it (CLAUDES_CHOICES.md, "U2"); both
failures are real today:

```
(define-type ns (anyof (listof nat acyclic) (listof int acyclic)))
(define f (subr pure (ns) int) (lambda (l) (if (null? l) 0 (car l))))
;; refused: argument 1 is a (anyof (pairof nat …) (pairof int …)), where a
;; (oneof nil (pairof int ? r)) is expected

(define p (pairof (oneof int bool) nil acyclic) (cons 1 nil))
(define q (anyof (pairof int nil acyclic) (pairof bool nil acyclic)) p)
;; refused, though every value of p's type is one of q's
```

The first is a missing normal form: `(listof nat acyclic)` is below
`(listof int acyclic)`, so the union is that list, and `car` would take
it apart. The second is missing distributivity: an immutable pair of a
union is the union of the pairs. Section 6.1 left the second to lemmas;
a lemma cannot take a union apart yet (section 6.3), so the boilerplate
is a `typecase` rebuilding the pair in each arm.

**Not eager.** Distribution as a normal form multiplies out: a product
of n fields, each a union of k, is a union of kⁿ products, and products
of such products multiply again. Nothing is stored that way. Deciding
it is hard in general (a product of unions covered by a union of
products is box covering; with recursion, subtyping of this kind is
inclusion of regular tree languages, EXPTIME-complete, as Hosoya and
Pierce note for XDuce), so the work must follow the question asked, not
the size of the types. The user's direction: normalize lazily, on
demand, only as far as a comparison needs.

**The proposal.** Types stay as written (and print so). Four pieces:

1. **A union's head form, on demand.** Its members grouped by run-time
   shape, sums made one (as U0 and U2 already do where it is written),
   each group in a fixed order. Linear in its members, computed when a
   comparison or an inference first needs it, kept on the node. Its
   fields are not looked into.
2. **A shape's greatest member, on demand.** Where inference needs one
   member of a shape (`cons` where a union is expected, `car` of a union
   with pairs, the termination walk, the verifier), it asks whether one
   member of that shape is above every other member of it, by
   subtyping, and takes that one; with none, nothing is inferred, as
   now. The first program above checks: `(listof int acyclic)` is the
   greatest pair member. Kept on the node.
3. **`τ ≤ σ₁ ∪ … ∪ σₘ`, split only on failure.**
   - The candidates are the members of `τ`'s own shapes (the head form);
     a `τ` of several shapes (a pair that may be `nil`, a union) is
     taken shape by shape. Today's `nil` and pair rule is the case of
     two shapes.
   - Each candidate is tried whole, in order, the trail rolled back
     after a failure, as now. Most questions end here, at today's cost.
   - If none takes `τ` whole, and `τ` is an immutable product, sum or
     frozen pair, it is split at one field: the first, in field order,
     whose type has a union in its head form and on which the
     candidates left differ. A candidate whose field shares no shape
     with `τ`'s is dropped first. `τ` with that field put to each member
     in turn must each be below the union. A field that may be written
     is never split (its types are invariant, as section 5 says).
   - This is distribution, one field at a time and only where a
     candidate is told from another by it. Exact for immutable fields:
     a value of `(pairof (anyof A B) C acyclic)` is a value of
     `(pairof A C acyclic)` or of `(pairof B C acyclic)`. The second
     program above checks by one split.
4. **A budget on splits.** Each top-level question may split at most a
   fixed number of times (counted in the proof, not in the work done:
   see the caches below). Past it, the question fails with a message
   that says so and names the two types: "deciding whether a … is a …
   needs more than N case splits: take it apart with `typecase`, or
   state it as a lemma".

**Termination with recursion.** Splitting along a recursive type makes
new pieces; the coinductive trail stops the search only if a piece met
again is known as the same. So a piece is named by where it came from
(the node, and the member chosen at each field split), never by a fresh
node, and the trail compares those names. Finitely many: a regular type
has finitely many subterms, and a union finitely many members. It
remains exactly the antichain setting: building only the subsets of
members a proof needs, skipping one covered by another already seen (De
Wulf, Doyen, Henzinger and Raskin, CAV 2006, for word automata;
Bouajjani, Habermehl, Holík, Touili and Vojnar, CIAA 2008, for tree
automata). A recursive list is not split along its tail: `(listof
(oneof int bool) acyclic)` is not below `(anyof (listof int acyclic)
(listof bool acyclic))`, and splitting the first pair leaves its tail,
of mixed elements, to fail, correctly.

**Caches.** A cached answer must be the answer recomputing gives, so
that dropping it is always safe and the two checkers agree whatever
their caches hold.
- *Head forms and greatest members*: on the node, kept. Linear in the
  union's own members, no more than the type itself.
- *Answers to subtype questions*: only of questions with no unsolved
  inference variables. A failure at any time (if it fails assuming
  more, it fails assuming less); a success only when its whole question
  ends, since until then it may rest on the trail's assumptions.
  Bounded by a count, then dropped and begun again, in both checkers,
  as FX-26's interning already is (`k-intern-budget`), and invalidated
  with it, as `k-proven` is. Not a weak table: when entries go would
  depend on the collector, a case would be hard to reproduce, and the
  Rust checker has no collector to match.
- *The budget counts splits in the proof*, so a cached answer is
  charged what it cost when found (kept with it): a cache hit never
  changes whether a question runs out.
- *Measured first*: the front end checking itself (some 200 modules)
  says whether the answer cache earns its keep, or the head forms are
  enough.

**Built first (2026-11-05): greatest members, piece 2**, which needs no
answer to questions 16 to 20. In both checkers (`greatest_of`,
`k-greatest-of` and `k-upper-bound`): where inference matched a union's
member of a shape, it takes the greatest of those, if one is. Not yet
kept on the node (to measure); the termination walk still takes a pair
member only if one alone is a pair, having no subtyping there, which
costs a descent it might have seen, never an answer. Tests:
`anyof/greatest-pair.fx`, `anyof/no-greatest.fx`.

**Built (2026-11-05): splitting, pieces 1, 3 and 4**, on the user's
answer to question 18 (products, sums and frozen pairs only) and,
provisionally, the proposals for 16 (by the checker), 17 (64 splits, a
plain refusal past them) and 19 (no answer cache yet). In both checkers
(`shaped_like`, `split_below` in `check.rs`; `k-shaped-like`,
`k-split-below` in `check-subtype.fx`):
- *Candidates by shape*: `τ ≤ ∪σ` tries only the members sharing a
  shape with `τ` (or of a shape not known), computed each time, not
  kept on the node (a union is small; to measure).
- *The split*: as piece 3, the field the first, in order, whose type is
  a union and on which two candidates of `τ`'s kind (a product of the
  same labels, a sum with each of its tags, a pair) differ; with fewer
  than two such candidates no split can help, and none is made.
- *The budget*: 64 splits per top-level question, counted as they are
  made (failed tries included), set again for a question asked inside
  one. Past it, `τ` is not shown below: the usual "is expected here"
  refusal, without a message of its own yet (question 17).
- *Termination*: a piece is a new node only at the top of a split; its
  fields are the original type's, so recursion reaches original pairs,
  which the trail already knows, and the budget bounds the rest. Naming
  pieces by origin waits for a case that needs it.
- *Not split*: a nullable pair's tail as `nil` and a pair (only at the
  top, as before), `nlist`s, bloblets, anything that may be written.
- Tests: `anyof/distribute.fx`, `distribute-product.fx`,
  `distribute-missing.fx`, `mixed-list.fx`, `budget-within.fx` (6
  fields, 63 splits), `budget-past.fx` (7 fields, 127: refused alike).
  Taking such a union apart (`car`, `extract` of it) is U3's.

**Inference variables.** A question with unsolved variables is not
split (a split would solve them per piece, and the pieces disagree);
it is decided as now, and refused if that fails.

**Both checkers alike.** The order of candidates, of fields, of members,
the budget and the caches' bound are part of the rule: with a budget, a
different order can give a different answer.

**What this changes.** Distribution over immutable fields becomes the
checker's, where section 6.1 left it to lemmas. Lemmas stay for what is
not structural (non-regular and generative families, `gadts.md`) and
for invariant positions; a union's lemma (a `typecase` in a lemma's
body, members matched as a set rather than in order) still waits for a
program to need it. Rule 5 (U3) is the same idea on terms: an
argument's union split only when the whole fails, one member at a time.

**Soundness note.** §2.3 gains the split as a derived rule, its premise
that the field split is immutable, with the lemma `⟦P[f ↦ A ∪ B]⟧ =
⟦P[f ↦ A]⟧ ∪ ⟦P[f ↦ B]⟧` for immutable `P`; coinductive soundness with
pieces named by their origin; the greatest-member rule is subsumption.

**Tests.** The two programs above, accepted; the recursive list above,
refused; a product of four fields of two-member unions against a union
of fifteen of the sixteen products, refused by the budget or by the
missing piece, whichever the budget allows, the same in both checkers;
every program checked once with the answer cache off and once on, the
verdicts compared.

## 9. Open questions for you

### 9.1 For the first recommendation (2026-09-29)

Answers recorded where known: questions 2, 3 and 6 in "L0, as built" and
"L1's stage 3, as built" (section 8.3), 8 below; question 1 revisited
by the revision (9.2), question 4 answered yes by it.

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
   front end acceptable? (Done 2026-10-08, the user's go-ahead. `car` of a
   union with a pair member stays a checked error, as `car` of a pair
   that may be `nil` is: Scheme ports take apart data they never test.)

### 9.2 For the revision (2026-11-04)

9. **The disjoint former's name.** A true `union` and a disjoint one
   (the user's direction). Candidates: `parts`, `partition` (the user's),
   `disjoint`; not `oneof` (FX-87's, tagged) nor `either` (two only).
   Or one former, `union`, with disjointness checked only where a program
   relies on it (a `typecase` without `else`): fewer formers, but the
   promise "a test splits it" no longer written in the type.
   *Answered 2026-11-04: `parts`; changed 2026-11-05 to `cases`, then
   the same day to the user's `oneof`, with `anyof` for the true union
   and `allof` for the intersection (for `overload`, which the user did
   not like).* The three read as FX-26's `-of` formers do (`listof`,
   `sumof`, `productof`), and as JSON Schema's `oneOf`, `anyOf` and
   `allOf`, with the same meanings: exactly one, any, all. FX-87's
   `oneof` (section 4) was a disjoint union too, by tags; this one is by
   shapes. The name `union` goes: today's becomes `oneof` (U0), the
   true one is `anyof` (U2), `overload` is `allof` (U1). Free as names:
   nothing is called any of the three today.
   *Also settled 2026-11-05, in discussing the names:*
   - **`oneof` and `anyof` of the same members are one type** whenever
     the `oneof` is well-formed: the same values, each below the other.
     `oneof` is a true union whose members are checked where it is
     written. One node in each checker; the former only decides the
     check. Printed as `oneof` when its members are disjoint, `anyof`
     when not. Type variables stay out of `oneof` (question 3), where
     the equivalence would need a bound.
   - **`oneof`'s well-formedness is a run-time test separating every two
     members**, not distinct shapes alone: by shape (the word's tag, a
     bloblet's kind), or, for two sums, by tag, their tag sets disjoint
     (the user's). `(oneof (sumof (a A) (b B)) (sumof (c C)))` is
     well-formed, the same type as the sum merged; `(oneof (sumof (a A))
     (sumof (a B)))` is refused, and `anyof` of the two is `(sumof (a
     (anyof A B)))`. A `typecase` arm for a sum member tests the shape,
     then the tag among the member's. At U0, with the renaming.
   - **Future** (not in U0 to U5): further tests, as programs ask.
     Singleton types (the user's: `'a` is told from `'b` by `eq?`; as
     `false` is today, and `nil` and `unit` in effect): `(oneof 'a 'b
     'c)` an enumeration free at run time, `(oneof 'a symbol)` refused.
     Then a discriminant at a path (TypeScript's discriminated unions):
     `(pairof 'lambda …)` from `(pairof 'app …)` by their `car`s, the
     test on a part, narrowing following the path (`docs/fx26.md`, "A
     test narrows a path too"); what would let λm be written as plain
     S-expressions rather than sums. Products of different lengths, by
     the header's length, likewise if wanted.
10. **Rule 4, the meet at calls.** Every fitting member and the meet of
    their results, refused where there is none (proposed); or ordered
    selection (the design of 2026-09-29), or the most precise member,
    refused where none is. The meet is distributivity under conditions:
    is excluding invariant positions enough for you, before the
    soundness note's lemma is written?
    *Answered 2026-11-04: the meet of results, as rule 4 has it
    ("sounds plausible"); the lemma still to be written.*
11. **Rule 5, union elimination at arguments**: wanted at U3, or later?
    Without it, a `(union expr op)` given to `swap` takes the `sexp`
    member, and its result is an `sexp`.
    *Answered 2026-11-05: at U3.*
12. **Rule 2's scope.** Dead arms skipped only while checking an
    overload's member (proposed), or wherever a subject's type rules a
    tag out (with "has no tag" kept as an error only for a tag no type
    reachable there has)?
    *Answered 2026-11-05: only while checking an overload's members; an
    arm skipped under every member refused, as today's "has no tag".*
13. **Rule 3's strictness.** Refuse an overload whose members' checks
    record different facts at a node (proposed), or let the compilers
    take the most general fact (a checked `car` where one member needs
    it)? The second compiles more programs, slower for the precise
    members.
    *Answered 2026-11-05: refuse (at U1); taking the more general of
    two ordered facts, such as a checked `car`, a later relaxation by an
    explicit list.*
14. **True unions of cells and regions.** Reading through a union of
    cells, writing only a meet: wanted now (U2), or refused until a
    program needs it?
    *Answered 2026-11-05: refused until a program needs it.* At U2 a true
    union of two members that are cells, arrays or writable pairs is
    refused; immutable members (base types, sums, products, `acyclic` and
    `const` lists) are allowed. Lifting it later breaks nothing.
15. **Order**: U0 to U3 before macros (`TODO.md` §182), U4 and U5 after
    (proposed)?
    *Answered 2026-11-05: yes.*

16. **Distribution over immutable fields, by the checker** (§8.8)? It
    reverses section 6.1's line for these (a lemma for each missing case)
    and makes the second program of §8.8 check. Or keep it to lemmas,
    with §8.8's head forms and greatest members only (which fix the
    first)?
17. **The budget**: how many splits per question (proposed: 64, which no
    program in the tests comes near; to measure), and is refusing past
    it, naming `typecase` and lemmas, the message you want?
18. **What may be split**: products, sums and frozen pairs (proposed); also
    frozen bloblets? An `nlist`'s first pair, as a pair's?
19. **The answer cache**: measured before it is built (proposed), or
    built with the head forms? Its bound, if built: as the interning
    table's, 400,000 entries?
20. **Messages**: types as written (proposed, which laziness keeps), or a
    union's head form where it differs?

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
