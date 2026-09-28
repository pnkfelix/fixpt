# Soundness for places: what `letrena` and its kin add

Research note, 2026-09-27. A companion to `docs/research/soundness.md`
(the core K26, its semantics and proof), answering the user's question:
what, if anything, must be generalised in Felleisen–Hieb type soundness to
cover `letrena`, `letreap`, `letfreeze` and places, and whether space
belongs in the theorem. Literature is from memory; no local copies of the
papers named here exist in `docs/research/papers/`. Labels as in
`soundness.md`: proved, sketched, conjectured.

## 1. What standard soundness does not say

Wright and Felleisen's syntactic soundness (progress and preservation over
a small-step semantics with evaluation contexts) says a well-typed program
never gets stuck. Whether that means anything about memory depends on the
semantics:
- In a semantics whose store only grows, as in the usual treatment of
  `ref`, soundness says nothing about freeing. Every program that never
  frees is trivially "safe".
- So the semantics must *free*. Then two new questions arise that
  progress and preservation do not settle on their own:
  1. **Safety of freeing**: is anything freed still used?
  2. **Space**: is anything *not* freed that the language promised to
     free, and is what is kept within a stated bound?

Question 1 is a stuck-state property and fits Felleisen–Hieb once the
semantics is changed. Question 2 is not a property of single steps; it is
about the size of states along a run, and needs Clinger's and Morrisett,
Felleisen and Harper's machinery.

## 2. Safety of freeing: what changes in the semantics and the proof

### 2.1 The semantics

`soundness.md` §3 makes these choices:
- A **place stack** `P` of live places, and tombstones for the locations
  of dead ones. Reading, writing or allocating in a dead place is stuck.
- Place **frames** `⟦π̂⟧E` in evaluation contexts, so that `abort` and
  `throw` end the places they leave, as `dynamic-wind` does in the
  lowering.
- Analysis-only regions have frames too (`letregion`, and the `priv` and
  `adopt` binders that stand for implicit masking), but free nothing.
- `letfreeze` has a frame that, when it ends, **retires** its region into
  `(const π)` or `(finite π)`: the name is dead, its locations keep their
  memory and are read at the frozen region from then on.

This is the Tofte–Talpin discipline in small steps, as Helsen and
Thiemann, and Calcagno, Helsen and Thiemann, gave it for the region
calculus. What FX-26 adds is the split of region and place, and freezing.

### 2.2 The generalisations the proof needs

Six things are not in a textbook Felleisen–Hieb proof:

1. **Dangling pointers are well typed.** A closure may capture a location
   in a place and never use it; the closure's type then says nothing of
   the place, and it may leave the place's scope. Tofte and Talpin allow
   this, and so does FX-26 (`letrena`'s rule looks only at the value's
   type). So the invariant cannot be "every reachable location is live".
   It is: *types may mention dead names; effects may not.* Formally,
   (I4) of `soundness.md`: every atom in the effect of the current term
   names a region whose places are live. The key step is Lemma 4.8: an
   access to a location has, in the redex's effect, an atom on the
   location's region, and that region won't outlive the location's place.
2. **Masking must be by binders.** FX-87 masks anywhere a region is
   invisible. That is not stable under reduction (a new location makes
   its region visible) nor under substitution of descriptions (a region
   variable instantiated to a visible region). The proof elaborates the
   checker's implicit masking into two binders, `priv` and `adopt`, and
   proves the elaboration sound (Lemma 2.2 of `soundness.md`, proved for
   `priv`, sketched for `adopt`).
3. **The order of lifetimes must be reflected in the frames.** A region
   `ρ` bounded by place `π` (`(r region p)`) must have its frame inside
   `π`'s at run time: invariant (I3). The checker's order by nesting
   (`Arena::outlived`, `ast.rs:503–512`) is what makes this so, and it
   refuses constants and fresh regions as `≤` a place variable.
4. **Freezing retypes the store.** No Tofte–Talpin rule changes a region
   of existing data. `letfreeze` does, safely, because the name being
   replaced is dead afterwards: every term that could write it is inside
   the frame. The proof needs a region-retargeting lemma (Lemma 4.5) and
   the notion of *junk*: stored objects whose types mention a retired name
   are unreachable by any live term, whatever their types say. For
   `finite`, a *write log* that masking never erases is needed, which is
   the checker's `written` flag.
5. **Continuations may not carry place frames out of their places.** A
   continuation that includes a place's frame must have a region bound
   inside that place (`soundness.md`, (I7), Lemma 4.9); the checker gets
   this from refusing `comefrom` at a place binder (`close_region`,
   `check.rs:564–578`). Composable continuations never carry a place frame.
6. **Frozen reads must keep their place.** Reading `(const π)` data is
   "pure" for the licence, but the atom `read (const π)` is the only
   thing tying a closure over frozen data to `π`'s lifetime. K26 keeps it
   (rule FrozenRead); the checkers drop it, and that is unsound (F2 in
   `soundness-findings.md`).

With these, **C1 (places are freed safely) is proved** for K26
(`soundness.md` §4.5).

## 3. Garbage collection alongside places

### 3.1 The problem

Dangling pointers are harmless to a program that never follows them, but a
*tracing collector* follows every pointer it finds. This is the classic
difficulty of combining Tofte–Talpin regions with a collector
(Hallenberg, Elsman and Tofte, PLDI 2002; Elsman, PLDI 2023, "garbage
collection safety for region-based type-polymorphic programs", both from
memory). Their answer is to strengthen typing so that no dangling pointer
exists (a closure's type must mention the regions of what it captures).

FX-26's runtime takes the other answer: it makes the collector tolerant
(`crates/fixpt-heap/src/heap/regions.rs`, module comment):
- it never follows a pointer into the arenas' address range; live
  arenas' chunks are scanned as roots instead;
- it follows pointers into a reap only when the chunk belongs to a live
  reap; an ended reap's chunks are quarantined until a collection finds
  no pointer into them.

### 3.2 A collection rule for the semantics

Morrisett, Felleisen and Harper ("Abstract models of memory management",
FPCA 1995, from memory) model collection as a rewriting rule on a
configuration `letrec H in e`: bindings of `H` not reachable from `e`
may be dropped. Their rule needs closed configurations. With tombstones
it is generalised thus:

```
(gc)   ⟨σ; P; e⟩ → ⟨σ|R; P; e⟩
       where R = the locations reachable from the roots, following
       pointers only into the heap and into live reaps, and
       roots = the locations in e ∪ every location in a live arena.
```

Pointers into dead places, and into locations not in `R`, become
tombstones. This is the runtime's policy stated as a rule.

**Theorem G1 (collection is invisible).** *Sketched.* If `C` is well
typed and `C →gc C′`, then `C` and `C′` reach the same answer (value up
to the locations it holds, `error`, or divergence). *Argument.* By T1–T2
and Lemma 4.8, the run from `C` only accesses live locations reachable
through the typed structure; those are in `R`, because each access path
starts in the term and descends through live objects. Tombstoning the
rest cannot change a step. The usual proof of the MFH rule (bisimulation
up to garbage) applies with "reachable" replaced by "reachable through
live places".

G1 is where FX-26's choice pays: soundness of collection needs no
stronger typing, only a collector that does not trace into dead places.

### 3.3 A caution: `no-escape`

The lowering emits a `(no-escape)` claim for an expression whose
allocations masking removed (`check.rs:711–714`, `lower.rs:400–401`). Its
comment reads "nothing they allocate outlives them". Under Tofte–Talpin
typing that is false: `(let ((x (cons 1 2))) (lambda () (begin x 1)))`
has its allocation masked, yet the pair is held by the closure it
returns. The claim is true as "nothing *uses* what they allocate after
them", which licenses nothing about where to put it: stack allocation on
its strength would leave the collector a pointer into a popped frame. No
optimisation consumes the claim yet (`Claim::NoEscape` is parsed in
`fixpt-scheme/src/expand.rs:987` and not acted on). Either the claim's
meaning is narrowed, or the typing is strengthened in the way Elsman's
work does before anything uses it.

## 4. Space: a cost semantics and space classes

### 4.1 Clinger's framework

Clinger ("Proper tail recursion and space efficiency", PLDI 1998, from
memory) defines the space an implementation uses for a program and input
as the supremum, over the configurations of a reference semantics, of the
size of the configuration after collection. Several reference machines
give a hierarchy of classes, asymptotically distinct:
`S_stack`, `S_gc`, `S_tail`, `S_evlis`, `S_free`, `S_sfs`, each at
least as space-efficient as the one before (`S_sfs ≤ S_free ≤ S_evlis ≤
S_tail ≤ S_gc ≤ S_stack`, as functions). "Properly tail recursive" means
in `O(S_tail)`. Morrisett, Felleisen and Harper's collection rules are
what makes "after collection" precise.

### 4.2 Why places need a class of their own

Places do not fit that hierarchy:
- An **arena** keeps everything allocated into it until it ends, garbage
  or not: its chunks are roots. A loop allocating into one arena uses
  space linear in its iterations where `S_gc` is constant. So FX-26 with
  arenas is *not* in `O(S_gc)`, by design.
- A **place frame is not a tail position** (`docs/fx26.md`; the body is
  followed by `%region-exit`). A procedure whose tail call is inside a
  `letrena` body grows the stack and the place stack. So FX-26 is not in
  `O(S_tail)` either, measured against Scheme with places erased.
- A **reap** is collected: within it, space is reachability's.
- `letfreeze` costs nothing: no frame at run time.

### 4.3 The measure `S_place`

Define, for a configuration `C = ⟨σ; P; e⟩` of the K26 semantics with
proper tail calls (a call in tail position does not grow the context, as
in Clinger's `S_tail` machine):

```
|C|_place = |e|                                   the term and its context, frames included
          + Σ_{π̂ ∈ P, π̂ an arena} words(π̂)       everything ever allocated in a live arena
          + Σ_{ℓ ∈ R(C), ℓ in heap or a live reap} |σ(ℓ)|
```

where `R(C)` is the reachable set of §3.2 (arena contents are roots).
`S_place(prog, input)` is the supremum of `|C|_place` over the run.

Relations:
- `S_gc ≤ S_place` always, when both are measured on the same run with
  places erased for `S_gc`: collection can only free more.
- If no `letrena` is used, `S_place` is `S_tail` (reaps are collected,
  `letregion` and `letfreeze` have no memory), up to the constant cost of
  place frames on the stack.

### 4.4 The theorems one would want

**S1 (implementation in class).** *Conjectured.* Both ways FX-26 runs
(lowered to Scheme on the bytecode engine, and the threaded engine) use
space `O(S_place)`.
Evidence for: allocation into a place goes into that place's chunks or to
the heap (`regions.rs:126–146`); reaps are copied; arenas end with their
frames, and on abort (`fixpt-engine/src/threaded.rs:939–947`); the lowering
uses `dynamic-wind`.
**The threaded-engine counterexample is now closed (F7 fix, d83face).**
It was: a full continuation thrown out of a place body did not end the
place (`reinstate` had no `region_exit`), so a loop that enters an arena
and escapes with `cwcc` each time kept every arena live, `Θ(n)` where
`S_place` is `O(1)`. It was space, not safety (the place was ended safely,
never while used). The fix is the one the abort path already had, now
applied to throw: a continuation records the live-region count when taken
(`CONT_REGIONS`), and reinstating a whole continuation ends those entered
since, in both the Rust threaded machine and fixpt-native. So S1 no longer
has this counterexample. (Verified only that the fix is present and matches
the abort path; the asymptotic claim S1 is still conjectured — no
space-measurement harness was run.)

**S2 (early release).** *Sketched.* If a `letrena π` body is
`E[f v̄]` with the call in tail position of the body, and `π` is in
neither the types of `f` and `v̄` nor the call's latent effect, then
ending `π` *before* the call preserves typing and (I4). *Argument.* The
exit-rena case of preservation needs only that the rest of the
computation's effect and the value's type avoid `π`; both hold for the
call's continuation (the frame's result type avoids `π`, by the
`(Arena)` rule) and for the call itself (hypothesis). With S2 the
compiler could make such calls proper tail calls, and FX-26 with places
would be in `O(S_place)` measured on a machine that drops place frames
at tail calls. This is the small-step counterpart of the MLKit's region
resetting for tail recursion (Birkedal, Tofte and Vejlstrup, POPL 1996,
from memory).

**S3 (reap quarantine is bounded).** *Conjectured.* Quarantine holds
address space, not memory: an ended reap's pages are given back
(`regions.rs:188–207`); a chunk stays quarantined while any dangling
pointer into it survives. The address area is finite; when it is used
up, allocation falls back to the heap (`regions.rs:95–124`), which is
safe. So quarantine never costs more than `S_place` in memory, and may
cost address space proportional to the number of reaps that ended while a
captured-but-unused pointer into them survived.

## 5. What to put in the soundness theorem

A proposal, in three parts:

1. **Type soundness (Felleisen–Hieb), over a semantics that frees**:
   progress and preservation for K26 with tombstoned places and frozen
   retirement. Proved in `soundness.md`, memory fragment in full, control
   sketched. It implies C1 (no use after free) and C2 (frozen is never
   written, `finite` is acyclic).
2. **Collection soundness**: G1, stated over the collection rule of §3.2.
   Sketched. It is what lets the runtime's tolerant collector coexist with
   Tofte–Talpin typing.
3. **Space**: S1 as a class statement, `O(S_place)`, with S2 as the
   refinement for tail calls. Conjectured; its one known counterexample
   (F7) is now fixed (both engines end a thrown-past place), so no
   counterexample stands, but the asymptotic claim is unproved and no
   space-measurement harness has been run. Space belongs *beside* the
   soundness theorem, not in it: it is a statement about implementations
   measured against the reference semantics, as Clinger's classes are.

Not needed: a region-level logical relation in the style of Tofte and
Talpin's consistency relation. The syntactic proof suffices once masking
is by binders. A logical relation *is* needed for termination (T5 in
`soundness.md`) and for the effect claim T3 in the presence of
continuations.

## 6. Open questions

- **Threads.** Each thread needs its own place stack before places can be
  ended out of order (`docs/research/actors-and-distribution.md`, Q1).
  The proof's (I2)–(I3) become per-thread, and a place shared by threads
  needs an outlives constraint that nesting cannot decide.
- **Messages between heaps.** A transmissible type mentions no place but
  `heap`; the proof of copying would be a lemma that a value of such a
  type reaches no location outside the heap, which (I4) gives only for
  *usable* reachability. A copying transmitter follows every pointer, so
  it needs the stronger, Elsman-style guarantee, or a copy that stops at
  pointers into places.
