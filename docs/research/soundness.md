# Type soundness for FX-26: a core, its semantics, and a proof

Research note, 2026-09-27. Theoretical work only: no code was changed.
Companions:
- `docs/research/soundness-regions.md`: what Felleisen–Hieb soundness
  must be generalised to for `letrena`, `letreap`, `letfreeze` and places,
  with a space-cost semantics.
- `docs/research/soundness-findings.md`: places where the checkers'
  rules look unsound, or where the proof needs an assumption the code may
  not meet, with file and line.

Every result below carries one of three labels:
- **Proved**: a paper proof is given here, the key cases worked in full.
- **Sketched**: the shape of the argument is given, and some cases.
- **Conjectured**: stated, with what a proof would need.

Literature is cited from memory unless a local copy is named
(`docs/research/papers/`).

## 0. Results at a glance

| result                                                    | status                                             |
| --------------------------------------------------------- | -------------------------------------------------- |
| T0 elaboration of the checker's derivations into core K26 | sketched; rule-1 masking proved, rule-2 sketched   |
| T1 progress                                               | proved (memory fragment); control cases sketched   |
| T2 preservation                                           | proved (memory fragment); control cases sketched   |
| C1 no dead place is ever read, written or allocated into  | proved from T1–T2, given the fixes in §6           |
| C2 frozen data is never written; `finite` data is acyclic | proved from T1–T2                                  |
| C3 sizes and `nat` values are exact                       | proved for the core; false for the checker (§6)    |
| T3 effect soundness (masking hides only fresh state)      | sketched                                           |
| T4 lemmas are erasable                                    | sketched                                           |
| T5 termination of `spin`-free code                        | conjectured; false for the checker today (§5, §6)  |
| T6 space safety of places (in `soundness-regions.md`)     | conjectured; one counterexample in the threaded VM |

## 1. The core calculus K26

### 1.1 Why a core, and which

The checkers have no single typing judgment: they check bidirectionally,
infer instantiations locally, and mask effects at every expression that
combines them. A proof needs a declarative system. K26 is that system.
The checkers' derivations are *elaborated* into K26 (§2.6), and soundness
is proved for K26.

One design choice drives the rest: **in K26 masking happens only at
binders.** FX-87 masks implicitly, anywhere a region is invisible. Implicit
masking is not preserved by small-step reduction: after `(new 0)` steps to
a location `ℓ`, the location is part of the term, its region is now
"visible", and the effect grows. Tofte and Talpin avoid this with an
explicit `letregion`; so does K26. Two binders stand for the checker's two
masking rules (§2.4).

### 1.2 What is elaborated away

| surface form                                             | in K26                                                     |
| -------------------------------------------------------- | ---------------------------------------------------------- |
| a program's `define`, `define-rec`, redefinition         | nested `let` and `letrec`; a redefinition is a new binding |
| `define-type`, parametric abbreviations                  | types, with `μ` for knots                                  |
| `define-datatype`                                        | a sum of products and constructor functions                |
| `define-generative`                                      | a name `N` and constants `upN`, `downN`                    |
| `cond`, `and`, `or`, `let*`, `acyclic`, `confirm-length` | `if`, `let`, and the primitive tests and certifications    |
| omitted `proj`, omitted parameter types, `the`           | explicit `e[d̄]` and annotated `λ`; `the` is subsumption    |
| implicit masking (FX-87's `erase-effect`)                | the binders `priv` (rule 1) and `adopt` (rule 2)           |
| `private-regions`                                        | fresh region constants                                     |
| lemma definitions                                        | erased: a lemma is a new subtyping axiom (§4.8)            |
| arrays, I-cells, bloblets                                | store objects like `ref`, with their own checked errors    |
| `rlambda`                                                | a closure object allocated in a place                      |

### 1.3 What is left out, and why

- **The REPL licence.** It is a claim about observers, proved from effect
  soundness (T3), not from type safety.
- **Strings, characters, symbols, `datum`.** Immutable base values with
  total or checked operations; they add cases, not ideas.
- **Bloblet bytes.** As fields, with integer contents.
- **Inference and error messages.** Elaboration fixes every choice.
- **Threads.** FX-26 has none yet; the place stack would become one per
  thread (`docs/research/actors-and-distribution.md`, Q1).

### 1.4 Syntax

Descriptions and kinds:

```
κ ::= region | place | effect | type | data | size
π ::= p | heap | π̂                       place: variable, the heap, runtime name
ρ ::= r | @c | π | (const π) | (finite π) | ρ̂    region: every place is a region
s ::= n | k | s + s | s − k               size (no `finite` among sizes; §4.9)
φ ::= ∅ | ε | a | φ ∪ φ                   effect: a set of atoms and variables
a ::= read ρ | write ρ | alloc ρ | await ρ | goto ρ | comefrom ρ | spin
d ::= ρ | φ | τ | s                       descriptions
```

`finite` is kept as a *type* former only: `(nlist τ ∃ ρ)`, written
`(nlist τ finite ρ)` in the surface, means "some length", an existential
(§4.9).

Types:

```
τ ::= B | nat | (nat s) | void | α
    | (subr φ (τ…) τ) | (∀ (χ:κ ≤ ρ)… τ)          ≤ ρ: an optional bound
    | (ref τ ρ) | (pairof τ τ ρ) | (icell τ ρ) | (arrayof τ ρ)
    | (bloblet (fields τ…) ρ) | (bloblet (frozen τ…) ρ)
    | (place π)
    | (prompt-tag τ τ φ ρ) | (composable τ τ φ ρ) | (mark-key τ ρ)
    | (productof (l τ)…) | (sumof (l τ)…)
    | (nlist τ s ρ) | (nlist τ ∃ ρ)
    | N[d…]                                        a generative type
    | μα.τ                                         contractive (§4.7)
```

`nil` inhabits every pair type, as in FX-87; `(listof τ ρ)` is
`μl.(pairof τ l ρ)`.

Expressions:

```
e ::= x | c | λ(x:τ…).e | e e… | Λ(χ:κ ≤ ρ)….e | e[d…]
    | let x = e in e | letrec (f:τ = λ…)… in e | if e e e | begin e…
    | product (l e)… | extract e l | sum l e | tagcase e (l x e)… [else x e]
    | prompt e e e
    | letregion r e | letrena p e | letreap p e | letfreeze (r π) e
    | priv r ≤ π. e | adopt r ⇒ ρ. e                 elaboration only
    | rlambda e (x:τ…) e
```

Constants `c` are literals and the primitives of `standard.rs`, with the
types given there: `new`, `get`, `set`, `cons`, `rcons`, `car`, `cdr`,
`set-car!`, `null?`, `make-icell`, `icell-put!`, `icell-get`, `cwcc`,
`make-continuation-prompt-tag`, `abort-current-continuation`,
`call-with-composable-continuation`, the mark operations, `acyclic?`,
`certify-acyclic`, `length-is?`, `certify-length`, `upN`, `downN`.

## 2. Static semantics

### 2.1 Contexts

- `Δ`: descriptions in scope, each with its kind and, for a bounded
  region binder, its bound; for places and regions, the order of their
  binders (below). At run time `Δ` also holds runtime names, each marked
  *live* or *dead*.
- `Γ`: value variables and their types.
- `Σ`: store typing, `ℓ ↦ (τ, π, ρ)`: the object's type, its place (where
  its memory is) and its region (what the analysis calls it).
- `Φ`: size facts, linear equalities and inequalities over size variables.

The judgment is `Δ; Φ; Γ; Σ ⊢ e : τ ! φ`. Most rules leave `Φ` and `Σ`
unchanged; they are dropped when so.

### 2.2 The lifetime order

`ρ ≤ ρ′`, "ρ won't outlive ρ′", is the reflexive-transitive closure of:
- `ρ ≤ ρ′` when `ρ`'s binder is inside `ρ′`'s (`letregion`, `letrena`,
  `letreap`, `letfreeze`, `priv`, or a `Λ`'s binder around its body);
- `r ≤ π` when `r` is bound `(r region π)`;
- `ρ ≤ heap`, `ρ ≤ @c`, `ρ ≤ (const heap)`;
- `(const π) ≤ ρ′` and `(finite π) ≤ ρ′` when `π ≤ ρ′`.

This is `Arena::outlived` (`ast.rs:503–512`). Note what it refuses: a
constant, `heap` or a fresh inference region is never `≤` a place
variable. So data in a place that ends can only be at a region whose
binder is inside that place's (or at the place itself).

Let `places(ρ) = {π | ρ ≤ π}`.

### 2.3 Subtyping

`τ ≤ τ′` is the greatest relation closed under these rules (graphs,
compared coinductively: Amadio–Cardelli; `check.rs:1366–1552`):

| rule                       | condition                                                             |
| -------------------------- | --------------------------------------------------------------------- |
| `void ≤ τ`                 | always: no value has type `void`                                      |
| `(nat s) ≤ (nat s′) ≤ int` | `Φ ⊢ s = s′` (with `nat` = `(nat ∃)`)                                 |
| `subr`                     | effects `φ ⊆ φ′`, parameters contravariant, result covariant          |
| `ref`, `icell`, `arrayof`  | same region, contents invariant                                       |
| mutable `pairof`, bloblet  | same region, contents invariant                                       |
| frozen `pairof`, bloblet   | `(finite π) ≤ (const π)`; contents covariant                          |
| `nlist`                    | frozen region order, `Φ ⊢ s = s′` or target `∃`, elements covariant   |
| `productof`                | same labels in order, fields covariant                                |
| `sumof`                    | each tag of the left is on the right, covariant (width)               |
| `prompt-tag`, `mark-key`   | invariant                                                             |
| `composable`               | as a `subr` of effect `φ ∪ goto ρ ∪ comefrom ρ`; also `≤` that `subr` |
| `N[d…] ≤ N[d′…]`           | argument by argument, by declared variance; regions invariant         |
| `∀`                        | same kinds and bounds, bodies related under a renaming                |
| lemma                      | `A ≤ B` when a proved lemma's instance has all its hypotheses (§4.8)  |

**Lemma 2.1 (transitivity, inversion).** *Proved in outline.* On
contractive types the relation is a preorder, and inversion holds: if
`(subr φ (τ̄) τ) ≤ (subr φ′ (τ̄′) τ′)` then `φ ⊆ φ′`, `τ̄′ ≤ τ̄`,
`τ ≤ τ′`; if `(ref τ ρ) ≤ σ` then `σ = (ref τ′ ρ)` with `τ ≡ τ′`; and so
on for each former. The standard proof by coinduction (Amadio and
Cardelli; Brandt and Henglein) applies, because every rule but `void`
and the lemma rule relates a former only to the same former. `void`
appears only on the left. The lemma rule is handled in §4.8.

### 2.4 Typing rules

Values and variables have effect `∅`. Only the rules that differ from a
textbook effect system are written out.

```
(Var)     Γ(x) = τ                                  ⊢ x : τ ! ∅
(Loc)     Σ(ℓ) = (τ, π, ρ)                          ⊢ ℓ : τ ! ∅
(Sub)     ⊢ e : τ ! φ    τ ≤ τ′   φ ⊆ φ′            ⊢ e : τ′ ! φ′
(Lam)     Γ, x̄:τ̄ ⊢ e : τ ! φ                        ⊢ λ(x̄:τ̄).e : (subr φ (τ̄) τ) ! ∅
(App)     ⊢ e : (subr φ (τ̄) τ) ! φ₀   ⊢ eᵢ : τᵢ ! φᵢ
                                                    ⊢ e ē : τ ! φ₀ ∪ ⋃φᵢ ∪ φ
(TLam)    Δ, χ:κ≤ρ ⊢ e : τ ! φ    φ ⊆ alloc-only, e a closure former
                                                    ⊢ Λ(χ:κ≤ρ).e : ∀(χ:κ≤ρ).τ ! φ
(TApp)    ⊢ e : ∀(χ:κ≤ρ).τ ! φ   Δ ⊢ d : κ   d ≤ ρ[d/χ]   no knot in τ[d/χ]
                                                    ⊢ e[d] : τ[d/χ] ! φ
```

`(Lam)` has **no masking**: the latent effect is the body's effect,
exactly. Masking is only in the binders:

```
(Priv)    Δ, r≤π ⊢ e : τ ! φ    r ∉ fr(Γ, τ)      no comefrom r left in φ
                                                    ⊢ priv r≤π. e : τ ! φ∖r
(Adopt)   Δ, r≤places(ρ) ⊢ e : τ ! φ    r ∉ fr(Γ)
          ⊢ adopt r⇒ρ. e : τ[ρ/r] ! (φ∖r) ∪ {alloc/goto/comefrom ρ | the same atom on r ∈ φ}
(Region)  Δ, r ⊢ e : τ ! φ    r ∉ fr(τ)    no comefrom r ∈ φ     (letregion r e)
(Arena)   Δ, p:place; Γ, p:(place p) ⊢ e : τ ! φ    p ∉ fr(τ)    no comefrom p ∈ φ
                                                    ⊢ letrena p e : τ ! φ∖p      (and letreap)
(Freeze)  Δ, r≤π ⊢ e : τ ! φ    no latent write r in τ
          ⊢ letfreeze (r π) e : τ[F/r] ! φ∖r      F = (finite π) if r ∉ W(e), else (const π)
```

`φ∖r` removes every atom on `r`. `fr(τ)` is every region `τ` mentions,
latent effects and the places of frozen regions included
(`regions_in`, `check.rs:818–828`). `W(e)`, the **write log**, is the set
of regions some sub-derivation of `e` writes before any binder removes
the atom: the checker's `freezing`/`written` bookkeeping
(`check.rs:676–683`). Effects in K26 are pairs `(φ, W)`; `W` is removed
only by its region's own binder, and `adopt` renames it. Below `W` is
left implicit.

The **frozen-read rule** differs from the checkers deliberately:

```
(FrozenRead)   read (const π), read (finite π), alloc (const π) stay in φ
```

The checkers drop them (§6, F2). For the licence and for purity, an
atom on a frozen region is harmless and may be ignored; for safety it is
the only thing that ties a closure over frozen data to `π`'s lifetime.
K26 therefore keeps them in the effect, and a separate *erasure*
`pure(φ)` ignores them where the checkers' "pure" is meant.

Control:

```
(Prompt)  ⊢ t : (prompt-tag A H D ρ) ! φ₁    ⊢ e : A ! φ₂    ⊢ h : (subr φ₃ (H) A) ! φ₄
          φ₂ ⊆ D ∪ {goto ρ, comefrom ρ}      reach(e, t, ρ)
          ⊢ prompt t e h : A ! φ₁ ∪ φ₄ ∪ φ₃ ∪ (φ₂ ∖ {goto ρ, comefrom ρ})
```

`reach(e, t, ρ)`: no free variable of `e` other than `t` has a type
mentioning `ρ` (`reaches_only`, `check.rs:1946–1959`); without it the
atoms stay (`check.rs:1935–1939`).

Sizes: `if` over `(null? x)` with `x : (nlist τ s ρ)` checks the branches
under `Φ, s = 0` and `Φ, s ≥ 1`; `cdr` of such an `x` is
`(nlist τ (s − 1) ρ)` where `Φ ⊢ s ≥ 1`.

### 2.5 The standard environment

The constants have the types in `standard.rs`, with one change for the
proof: the allocators take the place and the region,
`rcons : ∀(p:place)(r:region≤p). ∀t₁t₂. (subr {alloc r, alloc p} ((place p) t₁ t₂) (pairof t₁ t₂ r))`
(`standard.rs:33–37`).

### 2.6 Elaboration (T0)

**Theorem T0 (elaboration).** If the Rust checker accepts a program, and
none of the conditions of §6 (F1–F5) arises in its derivation, there is
a K26 term, erasing to the lowered Scheme text, with a K26 derivation of
the same type and an effect `φ` such that `pure(φ)` is the checker's
effect.

*Status: sketched.* The derivation is followed node by node. Local
inference contributes the explicit instantiations. The two masking rules
are the only nontrivial steps.

**Rule 1** (`check.rs:699–708`): at `e`, an atom on `r` is dropped when
`r` is not in the type of any free variable of `e` and not in `e`'s type.
Elaborate `e` to `priv r̂≤π̄. e[r̂/r]` with `r̂` fresh and `π̄` the bounds
of `r`.

*Lemma 2.2 (rule-1 renaming). Proved.* If `Δ; Γ ⊢ e : τ ! φ` and
`r ∉ fr(Γ|fv(e)) ∪ fr(τ)`, then `Δ, r̂; Γ ⊢ e[r̂/r] : τ ! φ[r̂/r]`.
*Proof.* By strengthening, the derivation of `e` uses only `Γ|fv(e)`,
which does not mention `r`. An *injective* renaming of a name that no
assumption mentions preserves every equality and disequality among the
regions compared inside the derivation (subtyping, the side conditions
of `(Priv)`, `(Region)`, `(Arena)`, `(Prompt)`), because both sides of
each comparison are renamed alike. Bounds are kept: `r̂` gets `r`'s
bound, so every `(TApp)` bound check is preserved. ∎

The side condition of `(Priv)` that no `comefrom r` is left is *not*
checked by rule 1. When it fails, the analysis region is captured into a
continuation. For an analysis region with no memory that is harmless:
K26's `priv` therefore allows it (a `priv` frame may be captured and
reinstated, §3.4), and only the place binders keep the restriction. The
effect claim this weakens is discussed in §4.6.

**Rule 2** (`check.rs:704–706`): when `r` is in `e`'s type but not in
any free variable's, reads, writes and awaits on `r` are dropped and
allocation and control kept. Elaborate to `adopt r̂⇒r. e[r̂/r]`. The
proof obligation is at the exit of the frame (§4.4, case Adopt-exit): the
locations allocated at `r̂` become locations at `r`. This needs the
region-substitution lemma of K26 (Lemma 4.5), which holds because K26
masks only at binders.

## 3. Dynamic semantics

### 3.1 Runtime syntax

```
ℓ, κ                    locations (κ for tags and keys)
π̂, r̂                    runtime place and region names
v ::= c | λ(x̄:τ̄).e | Λ(χ̄).v | ℓ | π̂ | nil | product (l v)… | sum l v
    | cont E | comp E ρ                          full and composable continuations
```

A closure is a substitution instance (`e` closed but for locations and
runtime names). An `rlambda` closure is a location in its place holding a
`λ`.

A **store** `σ` maps each location to `(π̂, ρ, o)`: its place, its region,
and an object `o`:

```
o ::= cell v | pair v v | icell ⊥ | icell v | array v… | bloblet f v…
    | tag | key | clos v
```

where `f` is a frozen flag. A **place stack** `P` lists the live places,
oldest first, `heap` at the bottom; `D` is the set of dead places. The
store is never shrunk by reduction: a location in a dead place is a
*tombstone*, and any access to it is stuck. (The garbage collection rule
of `soundness-regions.md` §3 removes tombstones and garbage; it is not
needed here.)

### 3.2 Frames and evaluation contexts

```
E ::= [] | E ē | v… E ē… | e[d̄]-context | let x = E in e | if E e e | begin E e…
    | product (l v)… (l E) (l e)… | extract E l | sum l E | tagcase E …
    | [r̂] E                    an analysis region's frame (letregion, priv)
    | ⟦π̂⟧ E                    a place's frame (letrena, letreap)
    | ⟨r̂ ▹ F⟩ E               a freezing frame, F its target region
    | ⟨r̂ ⇒ ρ⟩ E               an adopting frame
    | #κ{E, h}                 a prompt for tag κ with handler h
    | μ(κ′, v) E               a continuation mark
    | Λχ.E                     a plambda body, evaluated once (erasure)
```

`Λχ.E` reflects the lowering: a `plambda` is its body, evaluated once
(`lower.rs:279`). Its body is pure but for closure allocation, so no
control frame can capture it.

### 3.3 Reductions

`⟨σ; P; e⟩ → ⟨σ′; P′; e′⟩` or `→ error`. The contextual closure is
`E[r] → E[r′]` for the rules marked "in E"; the control rules name the
context. The checked errors are the ones the implementation raises:
`car`/`cdr` of `nil`, reading an empty I-cell, a second `icell-put!`, an
array index out of bounds, writing a frozen bloblet through an old alias,
and an abort with no prompt for its tag.

| rule       | redex and result                                                                              | condition                                |
| ---------- | --------------------------------------------------------------------------------------------- | ---------------------------------------- |
| β          | `(λ(x̄).e) v̄ → e[v̄/x̄]`                                                                         |                                          |
| Tβ         | `(Λχ.v)[d] → v[d/χ]`                                                                          |                                          |
| alloc      | `rcons π̂ v w → ℓ`, `σ(ℓ) := (π̂, ρ, pair v w)`                                                 | `π̂ ∈ P`, `ℓ` fresh                       |
| read       | `car ℓ → v` where `σ(ℓ) = (π̂, _, pair v _)`                                                   | `π̂ ∈ P`, else stuck                      |
| write      | `set-car! ℓ w → unit`, contents updated                                                       | `π̂ ∈ P`                                  |
| enter-rena | `letrena p e → ⟦π̂⟧ e[π̂/p]`, `P := P·π̂`                                                        | `π̂` fresh                                |
| exit-rena  | `⟦π̂⟧ v → v`, `P := P ∖ π̂`, `D := D ∪ {π̂}`                                                     | `π̂` is the top of `P`                    |
| enter-reg  | `letregion r e → [r̂] e[r̂/r]`; `priv r≤π. e` likewise                                          | `r̂` fresh, bounds kept                   |
| exit-reg   | `[r̂] v → v`                                                                                   |                                          |
| freeze     | `letfreeze (r π̂) e → ⟨r̂ ▹ F⟩ e[r̂/r]`; `⟨r̂ ▹ F⟩ v → v`, and `r̂` is *retired into* `F`          |                                          |
| adopt      | `adopt r⇒ρ. e → ⟨r̂ ⇒ ρ⟩ e[r̂/r]`; `⟨r̂ ⇒ ρ⟩ v → v`, and every location at `r̂` gets region `ρ`   |                                          |
| prompt     | `prompt κ e h → #κ{e, h}`; `#κ{v, h} → v`                                                     |                                          |
| abort      | `E[#κ{E′[abort κ v], h}] → E[h v]`, places framed in `E′` ended                               | `E′` has no `#κ`                         |
| no prompt  | `E[abort κ v] → error`                                                                        | `E` has no `#κ`                          |
| callcomp   | `E[#κ{E′[callcomp f κ], h}] → E[#κ{E′[f (comp E′ ρ)], h}]`                                    | `E′` has no `#κ`                         |
| compose    | `E[(comp E′ ρ) v] → E[E′[v]]`                                                                 | `E′` has no live-place frame (Lemma 4.9) |
| cwcc       | `E[cwcc f] → E[f (cont E)]`                                                                   |                                          |
| throw      | `E[(cont E′) v] → E′[v]`, places framed in `E` but not `E′` ended                             | every place framed in `E′` is live       |
| marks      | `with-mark κ′ v f → μ(κ′, v) (f)`; `first-mark` reads the innermost `μ(κ′, _)` of the context |                                          |

A **stuck** state is one that is not a value, not `error`, and has no
step. By design these are stuck:
1. any read, write or allocation at a location or place in `D`;
2. `throw` into a context with a place frame for a dead place;
3. `compose` of a segment holding a place frame;
4. a write to a location at a frozen or retired region: the rules for
   `set-car!`, `set`, `icell-put!` and `array-set!` require the location's
   region to be neither `(const π)`, `(finite π)` nor retired.

Soundness therefore says, among other things, that no program frees a
place too soon, and none writes frozen data.

Two remarks on faithfulness:
- **Abort and throw end places.** The lowering wraps each place body in
  `dynamic-wind` (`lower.rs:286–295`), and the threaded engine's abort ends
  the regions entered inside the prompt (`fixpt-engine/src/threaded.rs:939–947`).
  The threaded engine's `throw` does not (§6, F7). That is a space
  question, not a safety one: a place left live longer is still safe.
- **Allocation into a dead place.** `Heap::in_region` allocates in the
  heap when the region is no longer live (`regions.rs:210–218`). K26 makes
  it stuck instead; the theorem shows it never happens in a well-typed
  program, so the difference is unobservable.

## 4. Soundness

### 4.1 Configuration typing

`Δ; Σ ⊢ ⟨σ; P; e⟩ : τ ! φ` holds when:

- **(I1) Store.** For every location `ℓ` whose place is live and whose
  region is neither retired nor dead, `σ(ℓ)`'s object has type `Σ(ℓ)`.
  Tombstones and locations at retired regions are unconstrained.
- **(I2) Places.** `P` lists exactly the place frames of `e`'s evaluation
  context, in nesting order, with `heap` first.
- **(I3) Order.** For each runtime region `r̂` that has a frame in `e`'s
  context, each place in `places(r̂)` has a frame outside `r̂`'s frame.
- **(I4) Live effects.** `Δ_live; Σ ⊢ e : τ ! φ`, where the typing of each
  frame adds its name to `Δ_live` for the part inside it, and every atom
  of `φ` on a region `ρ` has `places(ρ) ⊆ P`. Types may mention dead names.
- **(I5) Frozen.** No location at `(const π)`, `(finite π)` or a retired
  region is written after it gets that region; and the graph of locations
  at `(finite π)` is acyclic.
- **(I6) Sizes.** A value of type `(nlist τ k ρ)` with `k` a closed size
  has exactly `k` elements; a value of type `(nat k)` equals `k`; one of
  type `nat` is at least 0.
- **(I7) Continuations.** Every `cont E` or `comp E ρ` reachable from the
  term or a live location has, for each place frame `⟦π̂⟧` in `E`, its
  region `ρ` bound inside `π̂`'s frame (`ρ ≤ π̂`); a `comp` segment has no
  place frame at all.

### 4.2 Lemmas

**Lemma 4.1 (canonical forms). Proved.** If `⊢ v : τ ! φ` then: `τ` is not
`void`; if `τ` is a `subr`, `v` is a closure, a `cont`, a `comp`, or a
location holding a closure; if `(pairof …)`, `v` is `nil` or a location
of a pair; if `(place π)`, `v` is `π`; if a sum, `v` is `sum l w` with `l`
among its tags; if `(nat k)` with `k` closed, `v` is the integer `k` (by
I6); and so on. *Proof.* Inversion of the value rules, and Lemma 2.1 for
`(Sub)`: `void` is only on the left of `≤`, so no value rule gives it. ∎

**Lemma 4.2 (value substitution). Proved.** If `Γ, x:τ′ ⊢ e : τ ! φ` and
`⊢ v : τ′ ! ∅` then `Γ ⊢ e[v/x] : τ ! φ`. *Proof.* Induction on the
derivation. The only rules with side conditions on the context are the
binders' (`fr(Γ)`), `(Prompt)`'s `reach`, and `(Priv)`/`(Adopt)`'s. In each
the side condition speaks of `fr(τ′)` for `x`. After substitution `x` is
gone and `v` is typed at `τ′` by `(Sub)`; the conditions are stated over
the *types in the derivation*, not the syntax of `v`, so they are
unchanged. This is why the side conditions must be read that way: read
syntactically (the checker's `free_vars`), a closure that captures a
location without using it would make that location's region visible
after substitution and break the lemma. ∎

**Lemma 4.3 (description substitution). Proved for types, regions,
effects; sizes in §4.9.** If `Δ, χ:κ≤ρ ⊢ e : τ ! φ`, `Δ ⊢ d : κ` and
`d ≤ ρ[d/χ]` then `Δ ⊢ e[d/χ] : τ[d/χ] ! φ[d/χ]`. *Proof.* Induction. The
binders' conditions are about names they bind, which are renamed away
from `d` (capture-avoiding substitution); subtyping is closed under
substitution; `(TApp)`'s bound checks hold after substitution because
`≤` is closed under it. This lemma *fails* for implicit masking: that is
why K26 has none (see §1.1). ∎

**Lemma 4.4 (context replacement). Proved.** If `⊢ E[e] : τ ! φ` then
there are `τ′, φ′` with `⊢ e : τ′ ! φ′`, and for any `e′` with
`⊢ e′ : τ′ ! φ″`, `φ″ ⊆ φ′`, `⊢ E[e′] : τ ! φ‴` with `φ‴ ⊆ φ`, provided
no name bound by a frame of `E` escapes into `e′`'s new locations'
types except as `Σ` records. The standard Wright–Felleisen lemma; frames
add their names to `Δ` and remove their atoms, monotonically.

**Lemma 4.5 (region retargeting). Proved.** Let `r̂` be a runtime region
that no term outside a frame `F` mentions. Then renaming `r̂` to `ρ` in
`Σ`, in `F`'s body and in its value preserves typing, provided `ρ` is not
bound inside `F` and `places(ρ) ⊇ places(r̂)`. *Proof.* Lemma 4.3 applied
to a name rather than a variable; the proviso is what keeps (I3) and the
bound checks. ∎

**Lemma 4.6 (stable outside). Proved.** While a frame instance `F` is in
the evaluation context, the part of the context outside `F` does not
change. *Proof.* Every rule changes the context only inside the redex's
own frames, except `abort`, `throw` and `compose`. An `abort` to a prompt
outside `F` removes `F`. A `throw` replaces the whole context; if `F`
survives, the new context is `E′`, captured while `F` was in the context,
and by induction `E′` agrees with the current context outside `F`.
`compose` adds frames inside. ∎

**Lemma 4.7 (effects of the redex).** If `⊢ E[r] : τ ! φ` with (I4), the
redex `r`'s own effect `φ_r` satisfies: every atom on `ρ` has
`places(ρ)` live. *Proved.* Frames only remove atoms of the names they
bind, and those names are live (their frames are in the context); every
other atom of `φ_r` reaches `φ`, which is live by (I4). ∎

**Lemma 4.8 (no dangling read). Proved.** In a configuration satisfying
(I1)–(I4), if the redex reads, writes or allocates at location `ℓ` or
place `π̂`, then `ℓ`'s place, or `π̂`, is live. *Proof.* A read of `ℓ` at
region `ρ` has `read ρ` in the redex's effect (from the primitive's
type, instantiated at `Σ(ℓ)`'s region, invariant by Lemma 2.1). By Lemma
4.7, `places(ρ)` is live. `ℓ` was allocated by `rcons π̂′` at `ρ` with
`ρ ≤ π̂′` checked by `(TApp)`, so `π̂′ ∈ places(ρ)`. For a frozen region
`(const π)` the atom is kept by `(FrozenRead)`, and `places((const π)) ∋ π`.
For an adopted location, Lemma 4.5 kept `places` from shrinking. ∎

The last lemma is exactly where the checkers differ from K26: they drop
`read (const π)` (§6, F2), and then a closure over frozen data in a place
has a latent effect, and a type, that mention nothing of that place.

**Lemma 4.9 (continuations). Proved.** (I7) is preserved.
*Proof.* A `cont E` is created by `cwcc` at region `ρ` with effect
`comefrom ρ`. For each place frame `⟦π̂⟧` in `E`, the atom reaches the
body of `π̂`. `(Arena)` refuses a body whose effect keeps `comefrom`, so
the atom was removed inside: by a `priv`, `letregion` or other binder of
`ρ` inside `π̂`'s frame (so `ρ ≤ π̂`), or by a prompt (only for composable
continuations, which stop at the prompt). A `comp E′ ρ` stops at the
nearest prompt for its tag; if `E′` held a place frame, the capture's
`comefrom ρ` would reach that place's body with `ρ` visible there (the
tag, bound outside, is free in it), and `(Arena)` refuses it. ∎

### 4.3 Progress

**Theorem T1 (progress).** If `⊢ ⟨σ; P; e⟩ : τ ! φ` then `e` is a value,
or the configuration steps, or it steps to `error`.
*Status: proved for the memory fragment; control sketched.*

*Proof.* Decompose `e = E[r]` with `r` a redex or a value in a frame
(unique decomposition: the grammar of `E` is deterministic, left to
right). Cases on `r`:
- **Application `v v̄`.** By Lemma 4.1 `v` is a closure (β), a location
  holding a closure (read, then β: the location's place is live by Lemma
  4.8, since its `subr` type has `read π` for an `rlambda`), a primitive
  (below), a `cont` (throw) or a `comp` (compose).
- **Primitive on a location** (`car`, `set`, `icell-get`, …). By Lemma 4.1
  the argument is `nil` (error, for `car`/`cdr`) or a location. By Lemma 4.8
  its place is live. By (I1) the object has the right shape. A write's
  region is not frozen: its type says `write ρ`, and a frozen region is
  never given `write` (the checkers' `frozen`, `check.rs:312–321`, and
  `(Freeze)`'s latent-write check), and a retired one is dead (I4).
  I-cell and bounds errors step to `error`.
- **Allocation** `rcons π̂ v w`. `π̂` is live by Lemma 4.8 (`alloc π̂` is in
  the redex effect).
- **`⟦π̂⟧ v`.** By (I2) `π̂` is the top of `P`: frames inside it are gone,
  since `v` is a value; exit steps.
- **`#κ{v,h}`, `[r̂]v`, `⟨…⟩v`.** Step.
- **`abort κ v`.** Either the context has `#κ` (abort) or not (error).
- **`throw`.** By (I7), each place frame in the target `E′` is bound
  outside the continuation's region `ρ`; `ρ` is live by Lemma 4.7 (the
  throw's effect has `goto ρ`); by (I3) its places are live, and by Lemma
  4.6 they are the same frame instances as now. So the side condition
  holds.
- **`compose`.** `E′` has no place frame by (I7).
- **Tβ.** `(Λχ.v)[d]`: canonical forms. ∎

### 4.4 Preservation

**Theorem T2 (preservation).** If `Δ; Σ ⊢ ⟨σ; P; e⟩ : τ ! φ` and
`⟨σ; P; e⟩ → ⟨σ′; P′; e′⟩`, then there are `Δ′ ⊇ Δ` (up to liveness
changes) and `Σ′`, agreeing with `Σ` on locations still typed, such that
`Δ′; Σ′ ⊢ ⟨σ′; P′; e′⟩ : τ ! φ′` with `φ′ ⊆ φ`.
*Status: proved for the memory fragment; control cases sketched.*

*Proof.* By Lemma 4.4 it suffices to treat the redex, and then check the
global invariants. The key cases:

- **β.** Lemma 4.2. The latent effect of the closure is in the
  application's effect, so the body's effect is `⊆ φ`.
- **alloc.** `Σ′ = Σ, ℓ:((pairof τ₁ τ₂ ρ), π̂, ρ)`. (I1): the new object
  has its type. (I4): `alloc ρ` was already in `φ`; the location `ℓ` adds
  no atom. (I5): a new pair at `(finite π)` points only to older
  locations, so acyclicity is kept (allocation order is a topological
  order).
- **write.** (I1) by the primitive's type. (I5): the region is not frozen
  (progress case). For `(finite π)`, nothing is written at all; and a
  freezing frame whose target is `finite` saw no write of its region
  (the write log `W`), so while it runs its locations too are only built.
- **exit-rena** `⟦π̂⟧ v → v`. The frame's rule gave `π̂ ∉ fr(τ_v)`. Mark
  `π̂` dead. (I1): its locations become tombstones, unconstrained.
  (I4): the rest of the term is `E[v]`. `E` was typed before `π̂` existed,
  so its effect never mentions `π̂`; `v`'s type does not either. Atoms on
  regions `ρ ≤ π̂` are on names bound inside `π̂`'s frame, which have all
  exited (LIFO, Lemma 4.6), so none is in the effect of the new term
  either: each such frame's rule removed its own atoms, and its result
  type excluded its name. The value `v` may still *contain* locations in
  `π̂` (a closure that captured one without using it): that is allowed,
  since types may mention dead names and (I1) does not constrain
  tombstones. (I7): continuations with a `⟦π̂⟧` frame have `ρ ≤ π̂`, and
  `ρ` is now dead, so they can never be thrown to (their `goto ρ` would
  violate (I4)).
- **exit-reg** `[r̂] v → v`. As above, with no memory.
- **freeze exit** `⟨r̂ ▹ F⟩ v → v`. Retire `r̂` into `F`: every location at
  `r̂` keeps its memory, and its type is read with `r̂` replaced by `F`
  (Lemma 4.5 on the value, which is all that remains mentioning `r̂`).
  Stored objects at `r̂` not reachable through `v`'s type may have types
  that write `r̂` (a closure kept in a private ref): they become junk.
  (I4) guarantees no live term can reach them, since their types mention
  the retired `r̂`, which no live term mentions. (I5): for `F = (finite π)`
  the write log showed no write, so the locations at `r̂` form an acyclic
  graph built in allocation order; for `(const π)` nothing writes them
  from now on, because a write needs `write (const π)`, which is never
  well formed.
- **adopt exit** `⟨r̂ ⇒ ρ⟩ v → v`. Lemma 4.5, renaming `r̂` to `ρ` in `Σ` and
  `v`. The dropped `read`/`write` atoms of `r̂` concerned only locations
  allocated inside the frame, now at `ρ`. `φ′ ⊆ φ` because `(Adopt)` kept
  `alloc ρ`.
- **Tβ.** Lemma 4.3.
- **if on `null?`.** Taking the `then` branch on `nil` of type
  `(nlist τ k ρ)`: by (I6) `k = 0` holds, so the fact `k = 0` the branch was
  checked under is true and can be discharged (a closed true fact adds
  nothing to `Φ`). Likewise `k ≥ 1` in the `else` branch.
- **abort** *(sketched)*. The handler's type `(subr φ₃ (H) A)` and the
  abort's payload `H` give `h v : A`. Places framed in the discarded `E′`
  end, as in exit-rena; the dropped `goto ρ` atoms were removed by the
  prompt, and `φ₃ ∪ φ₄` were already in `φ`.
- **callcomp and compose** *(sketched)*. `comp E′ ρ : (composable T A D ρ)`
  because the prompt checked `E′`'s effect `⊆ D ∪ {goto ρ, comefrom ρ}`.
  Composing reinstates `E′`, whose frames are only `priv`, `letregion`,
  marks and prompts: `priv`/`letregion` frames may be duplicated, since
  their names carry no memory (a duplicated `[r̂]` frame shares `r̂`, which
  is sound because nothing is freed at its exit).
- **cwcc and throw** *(sketched)*. `cont E : (subr (goto ρ) (T) void)`.
  Throw: the new term `E′[v]` is typed as it was at capture, by Lemma 4.6
  and (I7); places framed in the abandoned context end, as in exit-rena.

The invariants (I2), (I3) follow from the frame rules (each push is
inside the current frames; each pop is of the innermost, or of a whole
discarded segment). ∎

### 4.5 What the two theorems give

**Corollary C1 (places are freed safely). Proved** from T1–T2: in a run
of a well-typed K26 program no step reads, writes or allocates in a place
after it ended. Stuck states of kind 1–3 (§3.3) are never reached.

**Corollary C2 (frozen and finite). Proved:** no location is written
after it becomes frozen; `(finite π)` data has no cycle through its
frozen pairs. Cycles through *mutable* objects that a finite pair points
to are possible (`(pairof (ref τ ρ′) … (finite π))`): `finite` promises
nothing about them, and size-change never descends through a mutable
object, so termination is not affected.

**Corollary C3 (sizes). Proved for K26:** by (I6). In the checkers it is
false, because they instantiate size binders with `finite` (§4.9, §6 F4).

### 4.6 Effect soundness

**Theorem T3 (masking hides only fresh state).** If `⊢ e : τ ! φ` and
`⟨σ; P; e⟩ →* ⟨σ′; P′; v⟩`, every location of `dom σ` that the run reads
(writes, awaits) is at a region `ρ` with `read ρ` (`write ρ`, `await ρ`)
in `φ`; every place allocated into has `alloc` in `φ`; and every control
transfer out of `e` is to a region with `goto` in `φ`.
*Status: sketched.* Instrument each frame with the domain of the store
when it was entered; an access to an older location inside `priv r̂` or
`adopt` is at a region other than `r̂`, since `r̂` is fresh, so its atom
reaches the frame's result. The obstacle is continuations: a `comp`
captured inside a prompt carries frames that hold private state, and
calling it again touches that state although `D` does not say so. The
theorem holds only if `comefrom ρ`/`goto ρ` on the continuation's region
are read as covering the state its frames hold. Every call of a
composable has those atoms (`ast.rs:249–253`), so what the REPL licence
and the compiler's reordering rely on still holds; but `D` alone is not a
complete description of what calling a continuation does.

### 4.7 Recursive and generative types

Equi-recursive types are graphs. K26 requires them **contractive**: every
cycle passes through a type former that is a constructor of *values*
(pair, `ref`, sum, product, `subr`, …). The checkers require a cycle to
pass through "a constructor", and count a generative name `N[d…]` as one
(`docs/fx26.md`, "Recursive types"). Semantically a generative type is
its representation (`upN`, `downN` are the identity), so a cycle through
`N` alone, with a representation that is just a parameter, is not
contractive: `μx.N[x]` with `N[a] = a`. No value of such a type can be
built (there is nothing to start from), so this is not unsound as far as
we can see; the proof assumes it (§6, A2).

Generative types in the proof: `N[d̄]` is a type former whose values are
the values of its representation; `upN`, `downN` are typed constants that
reduce to the identity; subtyping of `N` by declared variance is sound
when the variance is borne out by the representation, which the checker
verifies (`check_variance`, `check.rs:1068–1092`). The analyses that
"look through" `N` (regions, knots, writes) must see what the
representation holds: they do (`regions_walk`, `check.rs:884–899`).

### 4.8 Lemmas as erased coercions

**Theorem T4 (erasure of lemmas).** *Sketched.* A lemma of type
`(proves (∀χ̄. (<= A B) (<= X₁ Y₁) …))` whose body passes the guarded
structural identity check (`lemma.rs:131–279`) justifies the subtyping
axiom "if every `Xᵢ ≤ Yᵢ` then `A ≤ B`", with the identity as coercion.

*Argument.* Interpret types as sets of values (a unary model over the
store typing). The body only takes apart sums and products and rebuilds
the same tags and labels, in order; applies hypotheses only to what it
was given at the same place; and calls itself only under a rebuilt
constructor. Sums and products are immutable and finite (they are built
bottom-up). So by induction on the value, every value of `A` is a value of
`B`, using the hypotheses as inclusions. The coinductive use in
subtyping (the goal assumed while the hypotheses are compared,
`check.rs:1348–1360`) is justified by the same induction, since each use
of the goal is under a rebuilt constructor. The check never rebuilds a
mutable pair, a `ref` or a bloblet, which is what keeps the argument from
failing on invariant storage.

### 4.9 Sizes

A size binder ranges over naturals. `(nlist τ ∃ ρ)` is an existential,
`∃n.(nlist τ n ρ)`. **Instantiating a size binder with `finite` is not a
substitution**: `∀n.(nlist τ n) (nlist τ n) → …` at `finite` would admit
two lists of different lengths, and facts learned from one would be
applied to the other. The sound reading is to *open* the existential of
one argument: `∀n.(nlist τ n ρ) → B[n]` may be used at
`(nlist τ ∃ ρ) → ∃n.B[n]` when `n` occurs in exactly one parameter,
and not under another arrow. The checkers substitute instead (§6, F4).
With that restriction Lemma 4.3 holds for sizes: facts in `Φ` stay true
under substitution of a natural.

## 5. `spin` and termination

**What T1–T2 do not say.** Progress and preservation hold for looping
programs. They say nothing about `spin`. A `pure` effect means, by T3,
"touches no pre-existing state and jumps nowhere outside"; it does not
mean "ends".

**What the checkers claim.** A recursive group needs no `spin` when
size-change termination (Lee–Jones–Ben-Amram, POPL 2001; local copy
`docs/research/papers/lee-jones-benamram-popl01-size-change.pdf`) shows
that every run ends; other loops are ruled out by typing: self-application
through a recursive type says `spin` (`may_spin`, `infer.rs:469–488`), and
a procedure kept in a region whose latent effect reads that region must say
`spin` (`no_knot`, `check.rs:1190–1274`).

**Theorem T5 (termination).** *Conjectured*, and false for the checkers
today (§6, F1, F3, F4, F5). Statement: if `⊢ e : τ ! φ` with `spin ∉ φ`,
all fixes of §6 applied, and every `datum` from the host acyclic, then
every run of `e` from a well-typed store ends in a value or `error`.

*What a proof needs.*
1. **A unary logical relation**, indexed by types and by a *level* for
   each region: a closure is terminating at `(subr φ …)` if applying it to
   terminating arguments in a store whose contents at the regions `φ`
   reads are terminating yields a terminating result. The circularity
   through the store is broken by stratification (Boudol, "Typing
   termination in a higher-order concurrent imperative language",
   2007/2010, from memory): a procedure stored at level `n` may only read
   regions below `n`. FX-26's knot rule is a weaker, local version: it
   forbids reading one's own region. Because latent effects are
   transitively closed (a call includes the callee's latent effect), a
   cross-region knot `A → B → A` does show as a read of the storage's own
   region, so the local rule implies a stratification *if* the region
   graph of stored procedure types is acyclic. That graph is exactly what
   the knot rule's walk inspects; the proof would have to make this
   precise.
2. **Size-change soundness**: the Lee–Jones–Ben-Amram theorem, plus
   well-foundedness of each measure: parts of immutable finite data
   (corollary C2 and the acyclicity of sums and products), integers
   bounded by a test, and `nat` (by I6, which needs F4 fixed).
3. **Control.** A continuation re-entered from the store is a backward
   jump with no recursive call and no read of the continuation's own
   region. The relation must treat `comefrom ρ` as possible
   non-termination unless `ρ`'s continuations cannot be stored or called
   twice. Without that, T5 is false (§6, F3).
4. **Known procedures.** The exemption of calls to "known" procedures
   from the self-application test must refer to a binding, not a name
   (§6, F1).

A proof of T5 along these lines is a substantial piece of work: the
relation is not step-indexed (it must prove termination), and the store
makes it Kripke-style over worlds of region levels. Ahmed's and Boudol's
work are the nearest precedents we know of, from memory.

## 6. Where the proof and the checkers part

Details, with file and line and a short program where one was tried, are
in `docs/research/soundness-findings.md`. In short:

| id  | what                                                                             | kind                  |
| --- | -------------------------------------------------------------------------------- | --------------------- |
| F1  | calls of "known" procedures exempt from `spin` by name and type, not by binding  | `spin` unsound        |
| F2  | reads of frozen data dropped from effects, so a closure forgets its place        | memory unsafe         |
| F3  | a continuation stored and re-entered loops with no `spin`                        | `spin` unsound        |
| F4  | size binders instantiated with `finite`                                          | sizes and `nat` wrong |
| F5  | the self-application test gives up at depth 64 and answers "not cyclic"          | `spin` unsound        |
| F6  | the `no-escape` fact is claimed for data a returned closure still holds          | latent                |
| F7  | the threaded engine's throw does not end the places it leaves                    | space                 |
| A1  | K26 reads masking side conditions over derivation types, the checker over syntax | proof assumption      |
| A2  | cycles through a generative name count as contractive                            | proof assumption      |
| A3  | `datum` values from the host are acyclic                                         | proof assumption      |
