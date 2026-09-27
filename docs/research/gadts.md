# GADTs, non-regular families and generative types: a plan

Design note, 2026-09-27, drawing together three pieces of work done for the
user's question "should we think about GADTs now, before building more on
plain datatypes?":

- `nonregular-subtyping-survey.md`: the literature (citations marked sure or
  from memory);
- `nonregular-prototype.md`: a Rust-only prototype of structural checking
  of non-regular families (branch `worktree-agent-a2bb056cff956c295`,
  commit `11bb8fa`, not merged);
- `generative-types.md`: generativity on its own, and a kind for
  serializable data.

## What we learned

- **Regular families stay structural.** `(rose t r)` and the rest, tied as
  knots, with equi-recursive subtyping: decidable and cheap, and what
  `finite`, size-change descent and recursive subtyping already rely on.
- **Non-regular families (GADTs, nested datatypes) cannot be compared
  structurally in general.** Equality is decidable but impractical;
  subtyping is inclusion, which is undecidable, and its "yes" is not even
  semi-decidable. A structural checker for them must sometimes say
  "unknown".
- **In practice the structural check did well.** The prototype decided
  every example in under a second with a budget of 200 unfoldings;
  congruence settled most questions; nested datatypes closed with one lemma
  found by anti-unification. Its messages were good: a path for "no", the
  growth `X ↦ C[X]` and the lemma tried for "unknown".
- **But the deeper limit is meaning, not decidability.** Structurally, a
  phantom index means nothing: the prototype proved, correctly, that a list
  "starting at 0" is one "starting at 1". Indices mean something only if a
  family's variance is declared (invariant) or the family is nominal. And
  GADT refinement needs evidence FX-26 cannot state today: no existentials,
  no refinement in `tagcase` arms, no kinds like `type → type`.
- **Generativity is cheap to add on its own.** FX-91 tied it to modules;
  FX-26 need not. Its rule: opaque to comparison, transparent to safety
  (region analyses, `no_knot` and the `spin` rules look through a
  generative name).

## Decisions proposed

1. **Non-regular families are nominal.** A family application is a node,
   compared with itself by the family's variance and never unfolded in
   comparison; values enter and leave by constructors and matching. This
   is the survey's recommendation and the generative note's G1, one
   mechanism.
2. **Variance is declared or inferred, and checked once** against the
   body; indices are invariant by default. A GADT index may be covariant
   only under Scherer and Rémy's upward-closure condition (few FX-26 types
   qualify, given width sums and region and effect subsumption).
3. **Lemmas are erased identity coercions.** An ordinary `define` whose
   declared type is a proposition, `(proves (<= A B))` or with hypotheses
   `(proves (<= (nest a) (nest b)) given (<= a b))`. The checker verifies
   the body: its type, that each arm rebuilds the same tag from coerced
   fields (mutable fields passed through unchanged), and that recursion is
   guarded (productive, as `cofix` requires: termination is not needed).
   Its existence in scope is the proof; nothing calls it, and it is dead
   code unless run on purpose, for debugging, where it is an ordinary
   function (a `trace` effect, ignored by the purity condition, gives
   println). A harness can run each on samples and check the result
   `equal?` to the input: a free test of the checker. Lemmas relate
   *different* nominal families too (`nest` and `nest'`), so they are not
   tied to structural checking. Precedents: coercion semantics of
   subtyping (Mitchell; Breazu-Tannen, Coquand, Gunter and Scedrov), erasable
   coercions (Cretin and Rémy, LICS 2014), Haskell's `Coercible` (all from
   memory).
4. **GADTs proper** add three things: constructors with their own result
   types, existentials in variants, and refinement: a `tagcase` arm checks
   with the equalities its constructor states. The bidirectional checker is
   the base for it.
5. **Size indices are their own sort**, with a decision procedure of their
   own (Dependent ML; sized types), not types to unfold. `confirm`'s sizes
   (CF1, CF3) use it.
6. **A kind `data ≤ type`** for structural, non-generative types: what
   `read` returns, what `acyclic` walks exactly, what `confirm` checks, and
   what an actor may send between machines (one definition with the actor
   notes' "transmissible"). Deserializing is `up`, so a generative type is
   `data` only if its owner supplies a validator. It arrives with its first
   consumer, and the checker works out `data`-ness of concrete types, so
   only binders say `(t data)`.
7. **Structural checking of non-regular families stays optional**, as the
   prototype has it, and never treats "unknown" as "yes". Its best use may
   be as a suggester: its growing chain gives the skeleton of the coercion
   (decision 3) a programmer would write.

## Stages

| Stage | Size | What                                                                                         |
| ----- | ---- | -------------------------------------------------------------------------------------------- |
| N1    | M    | nominal families: a type node, in both checkers; safety analyses look through (G1, G2), done |
| N2    | S    | variance declared, checked once; invariant by default, done                                  |
| N3    | M    | lemmas: `proves` types, checked as erased identity coercions, done                           |
| N4    | L    | GADTs: constructor result types, existentials, refinement in `tagcase`                       |
| N5    | L    | size indices as their own sort, for `confirm` (CF1, CF3)                                     |
| N6    | M    | the `data` kind, with `read` and `acyclic` (CF0)                                             |

`define-datatype` stays transparent by default; a generative variant is
`generative-types.md`'s G3, and hiding (G4) comes when wanted.
