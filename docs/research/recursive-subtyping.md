> **Where this stands (2026-09-27).** The report's first three tasks are
> done, in both checkers:
> - `sub` compares `poly` bodies under binder environments, not by
>   substitution, so a cycle through a `poly` terminates; bounded region
>   binders must have the same bounds;
> - `grounded` counts a `poly` as no constructor, so a cycle through `poly`s
>   alone is refused;
> - frozen pairs (`(const p)`) are covariant.
>
> The probes are `crates/fixpt-fx26/tests/programs/recursive/`, which both
> checkers must agree on (`tests/checker.rs`). The prototype branch and its
> instrumentation were not merged.

# Recursive subtyping in FX-26: what we have, and where to use it more

Research note, 2026-09-27. Worktree branch `worktree-agent-ad6bfd1a877c9a1c6`, commits
`d260522` and `570f1fd`. Both are prototypes, not for merging as they stand.

**Citations are from memory unless they name a file.** No papers were fetched.
FX-91 is quoted from `~/Dev/LangPlay/GiffordHistory/papers/fx91-report.pdf`.

## Summary

- **Algorithm.** Both checkers use the same one. It is the term-graph form of
  Amadio–Cardelli's assumption-set algorithm, with one trail threaded through
  the whole question. In effect it is the algorithm of Kozen, Palsberg and
  Schwartzbach (MSCS 1995), or TAPL ch. 21's `gfp^t`. It is sound. It is
  complete for the monomorphic types, and fast: under 1% of checking time.
- **Divergence.** The algorithm diverges whenever a recursive type's cycle
  passes through a `poly`. The Rust checker overflows its stack. The FX-26
  checker hits its step limit. This happens even with the same `define-type`
  name on both sides (`polyvar` below).
- **Contractiveness.** A cycle made only of `poly` nodes passes `grounded` and
  then sends `check` into unbounded recursion.
- **A missing covariance.** Frozen pairs (`(listof T const)`) are still
  invariant, though frozen bloblets are covariant.
- **Prototype fixes.** In the Rust checker, `poly` binders are now compared
  through an environment instead of by substitution, and frozen pairs are
  covariant. The whole `fixpt-fx26` suite passes with both changes. The
  FX-26 twin, `check.fx`, is not ported.
- **Most useful leverage:** canonical forms and fingerprints for recursive
  types, `confirm`'s value walk, duality and subtyping of session types, and
  a polarity analysis for `spin`.

## 1. The current algorithm

### Rust

`Checker::subtype` / `Checker::sub` are in `crates/fixpt-fx26/src/check.rs`,
around line 742 at `9651bea`.

- **Representation.** Types are nodes in an arena. A recursive type is a real
  cycle through `Ty::Link` slots. There are three ways to make one:
  - `dletrec` (`parse.rs` `parse_dletrec`);
  - `define-type` (`parse.rs` `define_type`);
  - `listof` (`parse.rs`, "a pair whose tail is the list itself").

  `resolve` follows links. Nothing is hash-consed: two spellings of one type
  are different graphs.
- **Algorithm.** `sub(a, b, trail)`:
  - returns true if `a == b`, or if `(a, b)` is already on the trail;
  - otherwise inserts `(a, b)`, then applies one structural rule.

  The trail is a `HashSet` shared by the whole question and never shrunk.
  Since every node is a constructor after `resolve`, an assumption is only
  ever used under at least one constructor. That is Brandt–Henglein's
  contractive FIX rule (from memory: "from A ≤ B ⊢ A' ≤ B', where the step
  goes through a type constructor, conclude A ≤ B"). So the rule structure
  is Brandt–Henglein's, run as an algorithm.
- **Size.** Each ordered pair of nodes is visited at most once. The work is
  therefore bounded by O(|A|·|B|) pairs.

### FX-26

`k-sub`, `k-trail`, `k-sub-fields`, `k-sub-sum` in
`crates/fixpt-fx26/src/check.fx`, around line 1335.

- It follows the Rust rules one for one.
- The trail is an association list in a `ref`, so each lookup is linear.
  Total cost is quadratic in the number of pairs.
- A synthetic sum of 1600 recursive variants still checks in about 1.5 s,
  about 0.6 s of which is starting the session. That is not a problem.

### Matching (infer.rs)

`unify` (`crates/fixpt-fx26/src/infer.rs`, around line 613) is one-sided
matching with its own `HashSet` trail.

- It matches cyclic patterns against cyclic actuals at different unfoldings.
- When a type binder is solved twice, it keeps the larger of the two by
  `subtype`, and each of those calls has its own trail. There is no
  least-upper-bound computation.

### Soundness of keeping assumptions after a failure

Assumptions that failed stay on the trail. This is harmless today, because
`sub` has no disjunctive rule:

- every rule is a conjunction, so the first `false` short-circuits all the
  way to the top;
- a `sumof` label is found by `find`, which makes no choice;
- the `composable`-as-`subr` case returns directly;
- `(or frozen …)` in `k-sub-fields` is a test of a flag, not a choice
  between subgoals.

**The hazard for the future:** an untagged union, an intersection, or a
`confirm` rule that tries alternatives would make a threaded trail unsound.
A failed branch would leave false assumptions that a later branch relies on.
The standard remedy:

- roll the trail back on `false`;
- memoize failures globally. A failure is unconditional: assumptions only
  prune refutations, never create them.
- memoize successes only when the top-level question succeeds. The final
  trail is then a simulation, so every pair in it holds.

### Completeness, rule by rule

| Feature                                      | Rule in `sub`                            | Status                                                                                     |
| -------------------------------------------- | ---------------------------------------- | ------------------------------------------------------------------------------------------ |
| Different unfoldings (μt.T vs T[μt.T/t])     | graph simulation                         | complete (probe `unfold`)                                                                  |
| `sumof` width + depth, recursive             | label lookup, covariant                  | complete (REPL: `w ≤ n`, and `n ≰ w` refused)                                              |
| `productof`                                  | same labels, same order, covariant       | no width subtyping; deliberate (the layout is positional)                                  |
| `pairof`/`listof`, `ref`, `arrayof`, `icell` | invariant, same region                   | sound; **incomplete at `const`** (probe `constcov`)                                        |
| frozen bloblet                               | covariant fields                         | complete, recursive too (probe `frozenblob`)                                               |
| unfrozen ≤ frozen                            | never                                    | correct: freezing is a change of type (comment in `sub`)                                   |
| `subr`, `composable`                         | contra/co, effect `within`               | complete for effects as sets of atoms                                                      |
| regions                                      | `r == s`                                 | no outlives order yet (places-and-regions.md step 2); `(const p)` unrelated to `(const q)` |
| `poly`                                       | rename `b`'s binders to `a`'s by `subst` | **diverges in cycles**; the renaming ignores shadowing                                     |
| `void`                                       | bottom                                   | fine                                                                                       |

### Probes

The probes are in `crates/fixpt-fx26/tests/recsub_probe.rs`, with programs in
`scratch/probes/*.fx`. Run one with
`PROBE=name SIDE=rust|fx26 cargo test --release --offline -p fixpt-fx26 --test recsub_probe probe -- --nocapture`.
The programs were moved out of string literals, because `checker.rs`
`every_program_in_the_tests_compiled` checks every literal it finds in
`tests/*.rs`.

| Probe        | Program (abridged)                                                      | Rust at `9651bea`      | FX-26 checker  | Rust prototype              |
| ------------ | ----------------------------------------------------------------------- | ---------------------- | -------------- | --------------------------- |
| `unfold`     | `s1 = () → {hd, tl: s1}` vs the same unrolled twice, as `s2`            | ok                     | ok             | ok                          |
| `polycycle`  | `p1 = (poly ((a type)) (subr pure (a) p1))` in a `productof`, same name | ok (`a == b` shortcut) | ok             | ok                          |
| `polycycle2` | `p1` against an α-equivalent `p2`, inside `productof`                   | **stack overflow**     | **step limit** | ok                          |
| `polyvar`    | `(f x)` with `f : (subr pure (p1) int)` and `x : p1`: the *same* type   | **stack overflow**     | **step limit** | ok                          |
| `polyonly`   | `(define-type t (poly ((a type)) t))`, then `(f x)`                     | **stack overflow**     | **step limit** | still overflows (see below) |
| `constcov`   | `(listof n1 const) ≤ (listof n2 const)`, where `n1 ≤ n2`                | refused                | refused        | ok                          |
| `frozenlist` | `(listof int @r)` where `(listof int const)` is expected                | refused (correct)      | refused        | refused                     |
| `frozenblob` | `(bloblet (frozen n1 b1) @r) ≤ (bloblet (frozen n2 b2) @r)`             | ok                     | not run        | ok                          |

### Why `poly` diverges

In the `poly` case, `sub` substitutes `b`'s binders by `a`'s with `subst`.
`subst` copies the cycle, and the copy has fresh `TyId`s. The copy's `poly`
node is compared the same way again, which makes another fresh copy. No pair
ever repeats, so the trail never stops the walk.

With the same name on both sides (`polyvar`), the cause is different.
`infer.rs` `check`, around line 62, checks a variable of `poly` type against
the `poly`'s body. `instantiate_against` then `subst`s, so the two sides are
no longer the same node.

`subst_memo` also descends into a nested `poly` without removing the
binder it rebinds. When a cycle re-enters the same `poly` node, the inner
binding is therefore substituted as though it were free. Today that only
shows up as divergence. A naive fix that memoized the substitution would
expose it as capture.

### Why `polyonly` diverges

`grounded` (`parse.rs` around line 360, and `k-grounded` in `check.fx`) only
rejects cycles made of names. A cycle made only of `poly` nodes passes it.
Then two loops never end:

- the `poly`-expected case of `check` (`infer.rs:62`) recurses forever;
- `binders_of` (`infer.rs:314`) loops forever.

In Brandt–Henglein terms, `∀` should not count as contractive.

### The prototype fix for `poly` (`d260522`)

`sub` carries a `BinderEnv`, with one map per side from `DVar` to a
synthetic name.

- **Entering a `poly` pair (A, B).** Binder *i* of both sides is bound to the
  label (A, B, i).
- **Re-entering the same pair.** The same labels are bound again. That is
  exactly shadowing, so there are finitely many environments.
- **Other rules.** Variables, regions and effect atoms are compared after
  renaming each side through its map.
- **The trail.** Its key is `(a, b, env)`. With an empty environment,
  behaviour is unchanged.
- **Soundness of the labels.** Two labels can only be equal when the latest
  entries of both binders were the same entry. Entering a pair rebinds both
  sides at once.
- **Kernel Fun.** Colazzo and Ghelli (from memory: "Subtyping recursion and
  parametric polymorphism in Kernel Fun", I&C 2005) needed a subtler
  argument for *bounded* quantification. FX-26's binders are unbounded and
  have to match kind for kind, which is the easy case.

### Cost today

I instrumented the prototype, whose counters are still in `check.rs`. Over a
check and compile of the whole front end:

- 24,480 `subtype` calls, 6 of them false;
- 6,931 trail pairs in all, and at most 177 in one call;
- 0.9 ms in `subtype` out of about 99 ms.

A cache of subtype results would buy nothing now. Canonical forms are worth
having for other reasons (§2c).

## 2. Where the machinery could be used

### (a) `confirm` against a recursive type

(`docs/research/confirmation.md`, "Cycles", CF2.)

**The key observation.** FX-87's `listof` is a *coinductive* type already.
It is a pair whose tail is itself, `nil` is in every `pairof`, and
`set-cdr!` can build a cycle that checks statically. So:

- `confirm` against a type in the static language should use the
  coinductive reading. That is what the static type already promises.
  Anything else would make `confirm` refuse values that the checker admits.
- The inductive reading belongs only to refinements the static language
  cannot express: sizes, and a "proper list" predicate.

**The walk.** It is the checker's `sub`, with the left side a heap object
instead of a type node:

- the visited set holds `(address, type node)` pairs;
- a revisit succeeds (the greatest fixpoint);
- nodes marked inductive fail on a *gray* revisit: a pair still on the DFS
  stack means a cycle;
- *black* pairs are memoized both ways, so sharing (DAGs) costs nothing
  extra;
- tags make every choice deterministic, so the threaded set is sound, as in
  §1;
- the bound is O(objects × type nodes).

**Pruning with static subtyping.** Before the walk, compute the product of
the static type S and the target T. For each pair `(s, t)` of nodes, if
`sub(s, t)` holds statically, that subgraph needs no walk. `confirm` then
compiles to a residual checker over only the pairs where the types differ,
and the walk stops at the first proven pair. The idea is the same as
space-efficient casts in gradual typing (Herman, Tomb and Flanagan; Siek and
Wadler's threesomes; both from memory). This check is also the static
precondition that confirmation.md states: "T must be a subtype of `e`'s
static type with its checkable parts strengthened".

**If `confirm` ever gains untagged alternatives** (for example over `datum`
shapes), roll the trail back as in §1.

### (b) Equi-recursive or iso-recursive

FX-26 is equi-recursive: types are graphs, and there are no fold or unfold
terms. That follows FX-87's circular types and trail. FX-91 went the other
way. In its module expressions, abstract descriptions may be mutually
recursive, and each gets `up-id`/`down-id` coercions (fx91-report.pdf,
module-expression section). That is iso-recursive and nominal.

**Recommendation: stay equi-recursive.**

- `define-datatype` already expands to a structural `define-type` of
  `sumof`/`productof` (`top.rs` `expand_datatype`).
- `unify` already handles cyclic matching.
- Iso-recursive subtyping needs the Amber rule, "μa.S ≤ μb.T if a ≤ b ⊢
  S ≤ T". It is incomplete with respect to the equi-recursive reading and
  awkward with invariance (Ligatti, Blackburn and Nachtigal, TOPLAS 2017;
  Zhou, Oliveira and others, "Revisiting iso-recursive subtyping", OOPSLA
  2020 and TOPLAS 2022; all from memory).
- Its only real benefit is cheap nominal identity, and fingerprints (c) give
  that structurally.

**The consequence for `infer.rs`.** If FX-26 ever does two-sided inference
(unknowns on both sides, say for unannotated `lambda`s), the natural
extension is unification of regular trees. That is union-find over graph
nodes with no occurs check (Huet 1976, from memory), and it is near-linear.
Subtype *inference* over recursive types is much harder
(Kozen–Palsberg–Schwartzbach; Pottier; from memory), so FX-26 should keep
local inference plus a subtype check.

### (c) Canonical forms, hash-consing and fingerprints

A type graph is a deterministic automaton over labelled nodes. Equality in
the equi-recursive reading is equivalence of those automata, so a canonical
form is the minimized automaton with a canonical numbering.

**Algorithm:**

1. Resolve links and collect the nodes reachable from the root.
2. Make an initial partition by shallow label:
   - the constructor and its arity;
   - base names;
   - `sumof` labels *sorted by name*, and `productof` labels in order;
   - region constants and effect atoms, *sorted by name*. The two checkers
     already order atoms differently, which is why `checker.rs` has
     `canonical()`.
   - a `Var` as an edge to the `poly` node that binds it, plus its index.
     This handles cycles through `poly`, provided binding is resolved to the
     innermost binder.
3. Refine the partition by the vectors of the children's blocks (Moore; or
   Hopcroft in O(n log n)).
4. Number the blocks in DFS order from the root.
5. Serialize, with symbols by name, and hash to 128 bits.

**What it gives:**

- *Fingerprints for messages and registries.* These are
  actors-and-distribution.md N1 and N4: "`M`'s fingerprint". A type is
  transmissible only if it mentions no region but `const` and no place but
  `heap`, so the fingerprint never sees a region variable.
- *Types in heap images.* A fingerprint at word granularity serves C3/C10's
  "imports by name and type" fast path: equal fingerprints need no check at
  all.
- *Hash-consing in the arena.* `subst` copies at every instantiation, so the
  arena grows. Canonical ids make copies share, and make the `a == b`
  shortcut in `sub` hit more often.
- *A subtype cache keyed on canonical ids.* Not needed now (§1, "Cost
  today").

**The invariant to test:** `canon(a) == canon(b)` if and only if `sub(a, b)`
and `sub(b, a)`, over random regular types. Frozen covariance does not break
this, since equivalence is subtyping in both directions.

### (d) Session types

(type-and-effect-directions.md P10; actors-and-distribution.md.)

**Representation.** Protocols can be arena nodes like any type: `end`,
`(! T S)`, `(? T S)`, `choose` and `offer`. Recursion comes from
`define-protocol` names, which gives cycles as `define-type` does.

**Duality.** Compute it as a memoized graph copy, like `subst_memo`:
dualize the continuation edges and *share* the payload edges. The naive
syntactic dual of `μX.!X.X` is `μX.?X.X`, which is wrong. The payload `X`
must stay the original protocol, not its dual (Bernardi and Hennessy;
Bernardi, Dardha, Gay and Kouzapas, "On duality relations for session
types", TGC 2014; both from memory). With graphs, the payload edge points at
the original node, so the copy is right by construction. Checking that S
and T are duals is a coinductive relation, with the same trail.

**Subtyping** (Gay and Hole, Acta Informatica 2005, from memory) adds a few
cases to `sub`:

| Construct | Payload       | Choice                                                           | Continuation |
| --------- | ------------- | ---------------------------------------------------------------- | ------------ |
| `!`       | contravariant | —                                                                | covariant    |
| `?`       | covariant     | —                                                                | covariant    |
| `offer`   | —             | covariant in the label set, as receiving a `sumof`: fewer ≤ more | covariant    |
| `choose`  | —             | the reverse                                                      | covariant    |

**Caveats:**

- Some later papers use the opposite convention, "process-oriented" rather
  than "channel-oriented". Fix one and write it down.
- Asynchronous session subtyping is undecidable (Bravetti, Carbone and
  Zavattaro; Lange and Yoshida; both 2017, from memory). Keep it
  synchronous.

### (e) The verifier for closures that carry their types

(type-and-effect-directions.md §4; C5–C11.) The loader has two subtype
questions:

1. each import's host type ≤ the fragment's assumed type;
2. each cell's stack state ≤ the stack map at branch targets and loop heads.

Both involve recursive types, such as a slot holding `(listof T r)`.
Carrying a stack map at every loop head keeps the verifier a *check* rather
than a fixpoint.

**Two concrete uses:**

- *Cross-arena comparison.* Import the fragment's types as data, then run
  `sub`. Use equal fingerprints (c) as the fast path.
- *Brandt–Henglein certificates.* A successful `sub` leaves its trail, which
  is a simulation: a set of pairs, each of which follows locally from pairs
  in the set. The fragment can ship that relation. The verifier then checks
  each pair's one rule, with no search, no trail, and no coinductive loop
  logic.

  This makes the trusted base smaller, which is the point of §4(b). It is
  also easy to write in FX-26 or in the runtime. The saving in time is
  small, since search is already polynomial. The gain is in simplicity.

### (f) Other uses

**Frozen data is covariant** (prototype `570f1fd`). `(pairof T U (const p))`
admits no `write` or `init`, so it is as safe to make covariant as a frozen
bloblet. That gives `(listof n1 const) ≤ (listof n2 const)` whenever
`n1 ≤ n2`: `constcov` passes, and `tests/regions.rs` and `tests/run.rs`
still pass.

- This matters for messages. A frozen `(listof (sumof (ok …)))` fits a
  mailbox for `(listof (sumof (ok …) (err …)) const)`.
- Once places-and-regions.md step 2 lands, the rule could also be
  `(const p) ≤ (const q)` when `p` outlives `q`. That is the first genuine
  region subtyping, and it fits naturally into `sub`'s region comparison.

**Polarity for `spin`** (type-and-effect-directions.md, "Recursive types",
and the Hazards item "one that occurs negatively in a `dletrec` cycle").

- Compute, per node, whether a cycle passes through it in a *negative*
  position: a `subr` parameter, or an invariant slot, which counts as both.
- The walk is over `(node, polarity)` pairs with a visited set, like `sub`.
- Only negative recursion allows self-application without recursive
  bindings. Recursion that stays positive (lists, streams of thunks) does
  not (Mendler 1987, from memory).
- So rule 3 need only fire for, say, C7's `k`, which takes a pair
  containing itself, and not for every type that mentions `listof`.

**Joins and meets.** Joins are taken at `if` (`check.rs:310`) and at
`tagcase` without an expected type (`check.rs:1035`). Today they take
whichever branch type is the larger, or fail.

- A real join of recursive sums is a memoized product construction over
  node pairs, as in the `sub` walk.
- Invariance makes the join partial: `ref` contents must be equal.
- For example, branches of `(sumof (a int) (b w))` and `(sumof (c unit))`
  would join to their union.

**Effect polymorphism.** It needs nothing new. Effects are compared as
atom sets after renaming. Rather than a Kleene closure, `unify_effect`
accumulates by union across unfoldings, and the trail stops it.

## 3. Tasks, smallest and most informative first

**R1 (S). Contractiveness counts `poly` as no constructor.**

- Changes: `parse.rs` `grounded` and `check.fx` `k-grounded` reject a cycle
  made only of links and `poly` nodes.
- First step: `polyonly` is refused with a message, and does not overflow.
- Tests: `tests/checker.rs` agreement on the refusal, under the timeout
  wrapper.
- Deps: none.

**R2 (S). The `poly` rule by binder environment, in both checkers.**

- Changes: port `d260522` (`BinderEnv`, `SubState`) to the Rust checker
  cleanly, without the stats, and to `check.fx` `k-sub` in place of
  `k-subst`/`k-rename`.
- First step: `polycycle2` and `polyvar` check, in both checkers, within
  time.
- Tests: the probes as `checker.rs` `both(…)` cases, plus the full suite.
  The prototype already passes it on the Rust side.
- Deps: R1.

**R3 (S). Frozen pairs covariant, in both checkers.**

- Changes: port `570f1fd`, and update places-and-regions.md.
- First step: `constcov` accepted by both checkers.
- Tests: a message-shaped example in `tests/regions.rs`. Also check that
  unfrozen pairs stay invariant.
- Deps: none.

**R4 (S). Make the trail discipline explicit.**

- Changes: add a comment in `sub`/`k-sub` that the rules are conjunctive,
  and a `debug_assert`-style test that fails if a disjunctive rule is added
  without rollback. Roll back on `false` when the first disjunction arrives.
- First step: document it.
- Tests: none until a disjunction exists.
- Deps: none.

**R5 (M). Canonical form and fingerprint.**

- Changes: `canon(t)` and `fingerprint(t) -> u128`, as §2c describes, in
  Rust first.
- First step: over a front-end check, count arena types and canonical
  classes, which is the hash-consing ratio.
- Tests: on random regular types, fingerprints are equal if and only if
  `sub` holds both ways; stable across two processes, since symbols go by
  name.
- Deps: R2, for `Var`-to-binder edges.

**R6 (M). The `confirm` walk, coinductive by default** (merges into CF2).

- Changes: a runtime walk over `(address, canonical node)` with gray and
  black marks, and inductive marking only for sizes and `proper`, pruned at
  compile time by static `sub` on node pairs.
- First step: confirm a cyclic frozen list against `(listof int const)`
  (accepted) and against a size (refused), without hanging.
- Tests: cyclic data of each shape, under the wrapper.
- Deps: CF1, R3; R5 helps.

**R7 (M). Polarity analysis for `spin` rule 3.**

- Changes: mark types with negative recursion.
- First step: list the front end's `define-type`s with negative recursion.
  The expectation is few, C7's `k` among them.
- Tests: C7 is `spin`, and a `listof` walker is not, once the spin effect
  exists.
- Deps: the spin task.

**R8 (M). Joins of recursive types** at `if` and `tagcase`.

- Changes: a memoized pairwise join, partial at invariant positions.
- First step: find the test and front-end programs that need a `the` today
  only because branch types are incomparable.
- Tests: `bidirectional.rs`.
- Deps: R2.

**R9 (M). Session types on the arena.**

- Changes: protocol nodes, dual by memoized copy with shared payloads, and
  Gay–Hole cases in `sub`.
- First step: `dual` of `μX.!X.X` is correct, and `S` is dual to `dual(S)`.
- Tests: a `recsub`-style probe set.
- Deps: P10.

**R10 (M). Subtyping certificates for the verifier.**

- Changes: `sub` returns its trail on success; a checker validates a
  relation locally.
- First step: for every successful front-end `subtype` call, the trail
  validates.
- Tests: mutated relations are refused.
- Deps: C5, R5.

**R11 (L, later). `(const p) ≤ (const q)` by outlives.**

- Changes: region subtyping in `sub`, using the order by nesting.
- First step: a frozen list at an inner place passed where the outer is
  expected.
- Deps: places-and-regions.md step 2, R3.

**Not recommended:** switching to iso-recursive types (§2b), and a subtype
cache (§1, "Cost today").

## Files

- `crates/fixpt-fx26/src/check.rs`: `subtype`/`sub` (prototype `BinderEnv`,
  `SubState`, `recsub_stats`), `subst_memo`, and the joins at lines 310 and
  1035.
- `crates/fixpt-fx26/src/check.fx`: `k-sub`, `k-trail`, `k-subst`,
  `k-rename`, `k-grounded`.
- `crates/fixpt-fx26/src/infer.rs`: `unify`, the `poly`-expected case in
  `check` (line 62), `binders_of` (line 314), `instantiate_against`.
- `crates/fixpt-fx26/src/parse.rs`: `parse_dletrec`, `grounded`,
  `define_type`, `listof`.
- Probes: `crates/fixpt-fx26/tests/recsub_probe.rs` and
  `scratch/probes/*.fx`, in the worktree.
