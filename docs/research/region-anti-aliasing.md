# Region anti-aliasing: FX-87's rule, splits, and Rust's `&mut`

Status: a research note (the user's question, 2026-10-11). Nothing here is
built. A companion survey measures what re-introducing the rule would
break (`anti-aliasing-survey.md`, pending; see §8).

## 1. The question

FX-87 had a rule that distinct region identifiers never alias. FX-26 has
none: the PLDI '89 control-effects paper assumed the rule away, and
FX-26 followed it "until something needs it" (`docs/fx26.md`, the kernel's
departures). Two things now might need it:

- **Disjoint borrows, as Rust has them.** kayak transpiles a subset of
  FX-26 to Rust. A region that is written maps naturally to a `&mut`
  borrow, and two `&mut`s are never aliases. Without an anti-aliasing
  rule, two region variables may be one region, and a transpiler has to
  assume they are (a `RefCell`, a `Cell`, raw pointers).
- **Non-interference.** Effects on disjoint regions commute, which is what
  licenses evaluating two expressions in either order or at once
  (Lucassen's motivation; `docs/research/async.md`'s structured
  concurrency).

And the user's question: if a region and the data in it could be
*provably split* into disjoint parts, would that recover what the rule
costs: applying a procedure over `r1` and `r2` to data that is all in one
region?

## 2. What FX-87 had

Sources: John M. Lucassen, *Types and Effects: Towards the Integration
of Functional and Imperative Programming*, PhD thesis, MIT/LCS/TR-408,
August 1987 (a DTIC scan, accession ADA186930, mirrored at
`https://archive.org/download/DTIC_ADA186930/DTIC_ADA186930.pdf`; the
user's local copy in `GiffordHistory/papers/`). Pages are the thesis's own.

**Why regions need it** (§3.6.3, p. 46): region variables have two
properties of interest, convertibility and overlap. "If no additional
assumptions were made about region parameters, any conservative
syntactic effect analysis algorithm would have to assume that any two
region variables may correspond to overlapping regions. This would
discourage the use of procedural abstraction, which is contrary to our
philosophy." Constrained quantification (disjointness constraints on a
region parameter) was considered and set aside as beyond the thesis.

**The rule** (§3.6.3, p. 47), modelled on Euclid's [Lam77, Pop77]:

> Restriction. In a polymorphic application (PROJ e p), where e has type
> τ, no region constant or variable may appear free in both τ and p; in
> other words, FRC(τ) ∩ FRC(p) and FDV(τ) ∩ FDV(p) must be empty.

It touches only polymorphic applications whose operand is a region.
Since every region a value uses is free in its type, it "is sufficient to
maintain the invariant that effects on distinct region constants and/or
variables in any scope do not interfere." In FX-26's n-ary terms,
instantiating `(poly ((r1 region) … (rk region)) body)` at `p1 … pk` is
refused when (a) some `pi` is free in the `poly` type itself (a region a
closure captured, say), or (b) `pi` and `pj` are one region for `i ≠ j`
(after `r1 := p1`, `p1` is free in what remains).

**What it buys** (§8.2.2, p. 122): with aliasing permitted, "a WRITE
effect on a region variable would interfere with a READ or WRITE effect on
any region constant or variable". With it prohibited, region variables are
treated as constants for interference: `(write d)` interferes only with
`(read d)` and `(write d)`. Effect *variables* get no such guarantee: an
effect variable may interfere with anything, itself included (§3.6.2).

**Fresh regions are free of it** (§5.3.6, p. 70): a `PRIVATE` region
(FX-26's `letregion`) is "disjoint from all other regions past, present or
future", so it introduces no aliasing. `EXTEND`, whose bound variable
becomes an alias of a target region on return, is kept sound by a syntax
restriction making the target inaccessible in the body. This is exactly
the shape a split needs (§5).

**Its author's verdict**: the rule is "no more than a reasonable
compromise" (p. 47, after Reynolds [Rey78]), and by §9.2.3 (p. 144) it "has
proved to be rather restrictive in practice"; Lucassen wishes for "a means
of indicating explicitly whether or not certain region variables are
allowed to be aliases for certain other region variables or constants",
which "would eliminate the need for the current general anti-aliasing
rule".

**Then it was dropped.** Jouvelot and Gifford, "Reasoning about
continuations with control effects", PLDI '89, p. 4, footnote 2: "Without
loss of generality, we assume that the anti-aliasing rule of FX-87
[GJLS87] is eliminated." The FX-91 report (Gifford, Jouvelot, Sheldon,
O'Toole) does not mention aliasing at all. FX-26 started from the PLDI
'89 kernel.

## 3. What FX-26 does without it

It is sound by being conservative, and nothing relies on disjointness:

- **Kept test facts** (`TODO.md` §54, `Checker::kill_paths`,
  `crates/fixpt-fx26/src/check.rs`): a fact a test established about a
  path survives until an effect may change what the path reads. Its
  `may_alias` treats any region variable as possibly any region, so a
  write to `@r1` kills a fact that reads through `@r2`. Under the rule,
  that fact would survive.
- **Masking** (`letregion`, `letrena`, `letreap`) needs no anti-aliasing:
  the masked region is fresh, Lucassen's `PRIVATE` case.
- **The REPL's licence to speculate** (`docs/fx26.md`, "What 'licence to
  speculate' means") is a disjointness judgment, but about regions the
  driver made itself and owns (no `read` or `write` on a region it shares
  with the user's program), which are fresh: Lucassen's `PRIVATE` case
  again, needing no rule. Any future use of "these two effects commute"
  for two region *variables* would need the rule, or a constraint.

So the rule's absence costs precision, not soundness; and it costs any
mapping onto a target, like Rust, that wants to know two writable regions
are distinct.

## 4. The variants

| Variant                         | Rule                                                                                  | Rust analogue                     | What it refuses                                                    |
| ------------------------------- | ------------------------------------------------------------------------------------- | --------------------------------- | ------------------------------------------------------------------ |
| (L) Lucassen                    | a region operand of an instantiation may not be free in the polymorphic value's type   | every borrow is `&mut`            | a procedure over `r1`, `r2` at one region; at a region it captured |
| (A) distinct binders            | (L)'s case (b) alone: distinct region binders get distinct regions                     | (none exactly)                    | a procedure over `r1`, `r2` at one region                          |
| (B) write-exclusive             | binders may get one region unless the type writes at least one of them                 | aliasing XOR mutation             | one region given to a written binder and another binder            |
| (C) opt-in                      | only binders declared `(distinct r1 r2)` must differ                                   | `&mut` where written, by choice   | only what a signature asks for                                     |

(B) is the one Rust actually has: `&T` and `&T` may alias, `&mut T` aliases
nothing. A procedure that only reads two regions can still be given one;
`copy` from `r1` into `r2` cannot (Rust: `copy_from_slice` takes `&mut`
and `&`, which may not overlap; one region uses `copy_within`). (C) is
Lucassen's own wish (§9.2.3), and the gentlest change: existing code is
untouched, and a procedure that wants the guarantee says so. (B) and (C)
combine: distinctness inferred for written binders, declared for others.

Inference interacts with all of them: two fresh region unknowns unified
by a call today become one region silently; under (A), (B) or (L) that
unification is an error unless the regions are allowed to coincide. The
survey (§8) measures how often the code base does it.

## 5. Splits

A split is how a strict rule stays livable: Rust's `split_at_mut` and its
disjoint field borrows. Given data in `R`, a split yields pieces at fresh
regions `R1` and `R2`, provably disjoint, for a scope; within it, `R`
itself is not used; at its end the pieces are `R`'s again.

Typing, in the shape of Lucassen's `EXTEND` (§5.3.6):

```
(split e k (x1 x2 (r1 r2)) body)
```

`r1`, `r2` are fresh (like `letregion`'s), and the body's effect may not
mention `R`: holding references at `R` is harmless, using them is an effect
on `R`, which the condition catches. The body's effects on `r1` and `r2`
become effects on `R` outside (masking in reverse: the pieces' effects
are the whole's). The result's type may not mention `r1` or `r2`, as a
`letregion`'s may not mention its region.

The hard part is "provably disjoint". Rust can split by structure because
ownership makes data a tree. FX-26's regions do not: two fields of a pair
in `R` may reach one cons cell, so a structural split of heap data is not
sound without a uniqueness discipline FX-26 does not have. Three ways
remain.

### 5.1 Flat data: a split by offset

A bloblet's suffix holds no pointers and has one owner (`TODO.md` §77):
its bytes are Rust's value data. Splitting a blobref to a flat array at
an element is disjoint by arithmetic:

```
(blobref-split r k (left right (r1 r2)) body)
;; r : (blobref B (arrayof F n)), k a literal ≤ n (or checked at run time)
;; left  : (blobref (slice r1) (arrayof F k))
;; right : (blobref (slice r2) (arrayof F (- n k)))
```

Two things a blobref can do today would break the disjointness, and the
pieces' types must forbid them:

- **`blobref-owner`** gives the owning bloblet, through which the whole
  suffix is reachable (`blobref-at` anywhere, `bloblet-byte`). So a
  piece's owner is not a bloblet type but `(slice r1)`, an owner type
  with a region and no operations: `blobref-owner` of a piece gives a
  value nothing can be done with.
- **`blobref+`** steps any number of bytes, past the piece into the other
  one (the runtime checks only the owner's suffix bounds). So `blobref+`
  and `blobref-at` require a bloblet owner, and are refused on a piece;
  `blobref-index` (its range checked against the length the type says,
  already at run time) and `extract` stay within the piece's layout.

The run-time representation is unchanged: a piece is an ordinary suffix
ref (tag `010`); the restrictions are all in the types. This is
`split_at_mut` exactly, and it composes: a piece is split again.

### 5.2 By construction

Allocate the parts in distinct regions from the start, and say so in the
type: a product whose fields' types are at `r1` and `r2`, both binders of
the procedure that made it. Under (L), (A) or (C) those are distinct, so
the fields are disjoint borrows already, with no split at all; viewing
the whole as one region is region subtyping or a `poly` instantiated
twice. This is how Rust's struct field borrows look once regions are
explicit: each field its own region.

### 5.3 Heap data generally

Splitting arbitrary heap data needs to know it is a tree: a uniqueness or
linearity discipline, or a run-time check (a traversal proving no sharing,
as `acyclic?` proves no cycles; `docs/research/acyclic-regions.md`). Both
are large; deferred.

## 6. The mapping to Rust

| FX-26                                            | Rust                                          |
| ------------------------------------------------ | --------------------------------------------- |
| region variable `r`, written                     | lifetime `'r` of a `&'r mut` borrow            |
| region variable `r`, only read                   | lifetime `'r` of a `&'r` borrow                |
| anti-aliasing, variant (B)                       | `&mut` aliases nothing; `&` may alias `&`      |
| `letregion r`                                    | a local scope owning what it allocates        |
| `blobref-split` (§5.1)                           | `split_at_mut`                                 |
| the parent region unusable in a split's body     | the parent borrow suspended by the reborrows  |
| a split's effects on `r1`, `r2` charged to `R`   | the reborrows ending, the parent usable again |
| a product with fields at distinct regions (§5.2) | disjoint field borrows                        |
| a flat array, `(arrayof F n)` at a blobref       | `[F; n]`, `&mut [F]`                          |

Where it does not map: FX-26's regions group *objects*, which may share;
Rust's borrows are of *places* in an ownership tree. A region with no
written effect maps well to `&`; a written one maps to `&mut` only for
data that is a tree (flat data, or data built by construction as §5.2);
other heap data at a written region maps to `Rc<RefCell<…>>` or an arena
with indices, as kayak would have to today.

## 7. A proposed order

1. **(C), opt-in `distinct`**, in both checkers: no existing program
   changes, and a signature that needs disjointness (a transpiler's,
   kayak's) can ask for it. `kill_paths` uses declared distinctness.
2. **`blobref-split`** (§5.1), with `(slice r)` owners: the flat world's
   `split_at_mut`, the case kayak's flat code and the Rust-parity
   benchmarks want.
3. Then decide, with the survey's numbers, whether (B) should become the
   default for written binders.

## 8. What the survey found, and what was built

**The survey** (`anti-aliasing-survey.md`, measured at `4670769`, by a
diagnostic left on its own branch) asked: if the rule came back, how many
places in our code would stop checking?

| How strict                                                     | Places that would break |
| -------------------------------------------------------------- | ----------------------: |
| (L) Lucassen's rule as written                                 |                     274 |
| (A) different region binders always get different regions     |                      96 |
| (B) may share a region only if neither is written through      |                       9 |

In plain terms:

- Almost all of it is ordinary code like `(append xs ys)` or `(reverse
  xs)`. Those standard procedures are typed over two regions, one for the
  input and one for the result, and programs routinely use one region for
  both. That is harmless, since they only read their input, but a strict
  rule refuses it. Our own code almost never defines a procedure over two
  regions: the breakage is the standard library's types, not user code.
- (L)'s extra 178 are all the frozen `acyclic` region, which every
  variadic call (`list`) carries in its type: an artifact of that
  encoding, and harmless since frozen data is never written.
- (B), Rust's rule, breaks almost nothing. Its 9 are a real instance of
  what it forbids: one benchmark's hash tables (`scheme-bench/equal.fx`)
  write into the same region as their keys.
- No soundness hole: today's checker never assumes two region variables
  are distinct (§3).

So: the full rule (L or A) would be costly, needing `append`, `reverse`
and kin retyped or given one-region versions; (B) is nearly free and is
what a Rust transpiler wants, the candidate default for later.

**What was built** (2026-10-11, `31eebfb`): the opt-in, (C), per binder.
A region binder may be marked `distinct`:

```
(poly ((r1 region distinct) (r2 region)) …)
```

Each instantiation must then give `r1` a region provably different from
the other binders' regions and from any region the procedure's type
mentions (different constants, the heap, a fresh or `letregion` region,
or an enclosing procedure's own `distinct` binder); else it is refused.
Inside, the checker may rely on `r1` overlapping nothing else (facts
read through it survive writes elsewhere). A procedure needing a
`distinct` region is no procedure that does not. Nothing unmarked
changes, so nothing broke. Both checkers; `docs/fx26.md`, "Distinct
regions"; tests `regions/distinct-*.fx`. Not yet: module parameters and
signatures. It gives Rust-style `&mut` disjointness between parameters;
`&mut` into a linked heap structure needs a substructural discipline
(§9, "What opt-in distinctness can and cannot give `&mut`").

## 9. Questions for the user

1. Is (C), opt-in distinctness, enough to start with, or should written
   binders be distinct by default (B)?
2. A split's pieces: refuse `blobref+` on them (§5.1), or give pieces
   their own bounds at run time (a fatter ref) so stepping is checked?
3. Does kayak need heap data (pairs, lists) as `&mut`, or is flat data
   plus `&` for the rest enough? That decides whether §5.3 matters.

### Answers (the user's, 2026-10-11)

1. Prototype (C), opt-in distinctness, first.
2. No fatter refs: a piece refuses `blobref+` (§5.1). A substructural
   type system is the only further step imaginable, and not yet.
3. kayak does not know yet; it is early there.

### What opt-in distinctness can and cannot give `&mut`

The user doubts `&mut` can be built on it, and the doubt is right for
heap data. Distinctness says two *regions* do not overlap. It gives:
two parameters at declared-distinct regions are disjoint borrows
(`fn f(a: &mut i32, b: &mut i32)`); with `blobref-split`, flat data is
`&mut [T]` down to `split_at_mut`; and effects on distinct regions
commute (`kill_paths`). It does not give uniqueness *within* a region:
two arguments `(ref int r1)` may be one cell, and data in `r1` may share
internally, where Rust's `&mut Vec<T>` relies on ownership making it a
tree. Nor, declared pairwise, does it say `r1` is distinct from a region
the callee reaches otherwise (a global at `@heap`): that is Lucassen's
clause (a), which the opt-in would need too (`(distinct r1 *)`, say). So:
`&mut` for flat data and for separate parameters on distinctness and
splits; `&mut` to a general heap structure needs a single owning path to
a tree, a substructural property, and waits for that.

## References

- [GJLS87] Gifford, Jouvelot, Lucassen, Sheldon. *FX-87 Reference
  Manual*, MIT/LCS/TR-407, 1987.
- [Luc87] Lucassen. *Types and Effects*, MIT/LCS/TR-408, 1987: §2.6.2,
  §3.6 (pp. 45–47), §5.3.6 (p. 70), §8.2.2 (p. 122), §9.2.3 (p. 144).
- [LG88] Lucassen, Gifford. "Polymorphic effect systems", POPL '88,
  pp. 47–57, doi:10.1145/73560.73564.
- [JG89] Jouvelot, Gifford. "Reasoning about continuations with control
  effects", PLDI '89, pp. 218–226, doi:10.1145/73141.74837: p. 4,
  footnote 2.
- [FX91] Gifford, Jouvelot, Sheldon, O'Toole. *Report on the FX-91
  Programming Language*, MIT, 1992 (`docs/research/papers/`).
- [Rey78] Reynolds. "Syntactic control of interference", POPL '78.
- [Lam77, Pop77] Lampson et al., "Report on the programming language
  Euclid"; Popek et al., "Notes on the design of Euclid" (as cited by
  Lucassen).
