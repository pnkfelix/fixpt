# Non-regular type families, checked structurally: a prototype

An experiment, 2026-09-27, in the Rust checker only (`check.fx` is
untouched). The question: can a structural, equi-recursive type language
take non-regular families — nested datatypes, GADT-like indexed types —
by unfolding them lazily within a budget, and are its failures
understandable? Programs: `crates/fixpt-fx26/tests/programs/nonregular/`
(not in `tests/checker.rs`'s list, since the FX checker has none of this).

## What was built

- **`Ty::App { family, args }`** (`ast.rs`): a family applied to
  descriptions, not unfolded. A family that mentions itself with the *same*
  descriptions is still a knot (`parse.rs`, `expand_abbrev`); one that
  mentions itself with *other* descriptions gets an application there,
  interned so the same application is one node (`Checker::app`).
- **Unfolding on demand** (`Checker::unfold`, memoized, and `whnf`): by
  `tagcase`, `extract`, checking against an expected type, and unification
  (which first matches two applications of one family by their
  descriptions).
- **Subtyping** (`check.rs` `sub`, `nonregular.rs` `sub_app`): congruence
  first — two applications of one family compare their descriptions, each
  invariant (no variance is computed) — then both sides unfolded. A budget
  of 200 unfoldings per question (`BUDGET`).
- **Lemmas**: when the budget runs out, the pairs of applications on the
  way down are grouped by their two families; the largest group is
  generalized by first-order anti-unification (least general
  generalization, structural, cycles tied) into `∀x. F[x] ≤ G[x]`. The
  lemma is proved with itself as a hypothesis, usable only under a
  constructor (a guarded, cyclic proof); if it holds, the question is asked
  again with it. Up to two lemmas are sought (`MOST_LEMMAS`).
- **Three outcomes** (`Outcome`), in the error for `expect`:
  - proved (with `FX26_LEMMAS=1`, a note names any lemma found);
  - refuted: the path of tags and fields to where the types differ;
  - unknown: the chain, compressed to its first pair and its growth `X ↦
    C[X]`, the lemmas tried, and why they did not close.

## The examples

| program           | what                                        | outcome                         | time     |
| ----------------- | ------------------------------------------- | ------------------------------- | -------- |
| `nest-same.fx`    | nested datatype and its twin                | proved, with a found lemma      | 0.31 s   |
| `nest-other.fx`   | nested datatype against a different one     | refuted, with a path            | < 0.01 s |
| `exp-gadt.fx`     | GADT-like `(exp t)` and its evaluator       | checks and runs                 | < 0.01 s |
| `exp-wrong.fx`    | an `int` literal claimed an `(exp bool)`    | refuted (ordinary error)        | < 0.01 s |
| `exp-same.fx`     | `exp` against its twin, at `t` and at `int` | proved, no lemma (trail)        | < 0.01 s |
| `vec-phantom.fx`  | a Peano-indexed list, phantom index         | proved, with a lemma: see below | 0.01 s   |
| `three-lemmas.fx` | three twin pairs, needing three lemmas      | unknown, with the chains        | 0.01 s   |

Timings are wall-clock for the whole `fixpt run` under
`/private/tmp/claude-501/m12/t 20`. (`nest-same` first hung, before the
lemma search compared types structurally: unfolding builds equal types
afresh, so a table keyed by node identity never recognized a repeat.)

**Proved, with a lemma** (`nest-same.fx`, `FX26_LEMMAS=1`):

```
note: (sumof (none unit) (more (productof (hd int) (tl (nest (productof (l int) (r int))))))) ≤ (sumof (none unit) (more (productof (hd int) (tl (nest2 (productof (l int) (r int))))))): proved with the lemma ∀x1. (nest (productof (l x1) (r x1))) ≤ (nest2 (productof (l x1) (r x1)))
```

**Refuted, with a witness** (`nest-other.fx`):

```
a (sumof (none unit) (more (productof (hd int) (tl (nest3 (productof (l int) (r bool))))))) is expected here, and this is a (sumof (none unit) (more (productof (hd int) (tl (nest (productof (l int) (r int))))))) — they differ: at tag `more` → field `tl` → tag `more` → field `hd` → field `r`, a int against a bool
```

**Unknown** (`three-lemmas.fx`, the types elided):

```
— undecided, not refuted: 201 unfoldings without an answer. The pairs of applications on the way down grew:
    (p1 (productof (l int) (r int))) ≤ (p2 (productof (l int) (r int)))
      then 200 more, each step X ↦ (productof (l X) (r X)) ≤ X ↦ (productof (l X) (r X))
  Generalized, they gave the lemma ∀x1. (p1 (productof (l x1) (r x1))) ≤ (p2 (productof (l x1) (r x1))) and the lemma ∀x1. (q1 (productof (l x1) (r x1))) ≤ (q2 (productof (l x1) (r x1))); with 2 lemmas, the budget still ran out, on the way down to:
      (r1 (productof (l int) (r int))) ≤ (r2 (productof (l int) (r int)))
        then 200 more, each step X ↦ (productof (l X) (r X)) ≤ X ↦ (productof (l X) (r X)).
  State a lemma, or name the family where the two meet.
```

The first version printed 200 truncated pairs; showing the growth
instead, `X ↦ (productof (l X) (r X))`, is what made it readable: it names
the family and exactly how its index grows.

## What could not be expressed

- **Refinement.** A `tagcase` arm learns nothing about `t`. `exp-gadt.fx`
  stands in with a coercion per variant (`as : int → t`), which the
  evaluator applies; the constructor checks the coercion's type
  (`exp-wrong.fx`). Real equality evidence (Leibniz, `∀f. f a → f b`)
  needs quantification over type constructors (kind `type → type`), which
  FX-26 lacks.
- **Existentials** in variants (`pair : exp a → exp b → exp (a×b)`): no
  `exists` in the type language.
- **Size arithmetic.** No type-level functions, so `(vec t n)` can only
  count *up* from where a list starts; `pred` cannot be written.
- **Phantom indices mean nothing structurally.** `vec-phantom.fx` proves a
  list starting at 0 is a list starting at 1 — correctly, since nothing in
  a cell depends on the index. A structural system can make an index mean
  something only if the family declares it invariant (a variance
  annotation, checked once) or is nominal. This is the sharpest finding
  for size-indexed types: they need declared variance or generativity,
  not only lazy unfolding.
- **Variance** is not computed: descriptions of the same family are
  compared invariantly, which is sound but refuses `(nest int) ≤ (nest
  top)`-style questions that unfolding would prove (only after the budget,
  via a lemma).
- **Lemmas are only found, never written**: no syntax for stating one.

## Verdict

- **Feasibility: good, on these cases.** Every example decides in well
  under a second with a budget of 200. Congruence settles most questions
  with no unfolding; ground-index GADTs (`exp`) close on the trail;
  nested datatypes, the genuinely non-regular case, close with one lemma
  found by anti-unification. The machinery is small (`nonregular.rs`,
  about 600 lines, plus a dozen match arms elsewhere).
- **Soundness caveats** of the prototype, to settle before building on it:
  lemmas are used only under a constructor while being proved (guarded),
  but the guard is "some pair of constructors above", not a checked
  productivity condition per use; regions inside a family's body other
  than its descriptions are assumed absent (`regions_walk`).
- **Error quality: promising, with work.** Refutation gives a precise path.
  The unknown case is useful once the chain is shown as a growth `X ↦
  C[X]`; it points at the family and its index. What it lacks: a way for
  the programmer to *write* the lemma it proposes, and a budget reported in
  terms a programmer controls.
- **The deeper limit is not decidability but meaning:** structurally,
  phantom indices collapse, and refinement needs evidence the type
  language cannot state. So lazy unfolding makes non-regular families
  *checkable*; GADTs and sizes still need declared variance (or nominal
  families) and equality evidence or a refinement rule.

The fx26 tests all pass with the prototype in place
(`cargo test --release --offline -p fixpt-fx26`).
