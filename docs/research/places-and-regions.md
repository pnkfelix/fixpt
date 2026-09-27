# Places and regions

Design note, 2026-09-27, from discussions with the user. It splits what
FX-26 called a region into two things:
- a **region** is for analysis: a name in types and effects, erased
  before anything runs;
- a **place** is for allocation: memory that data is put in, with a
  lifetime.

Its purpose is `letfreeze` (below), and after it `confirm`
(`docs/research/confirmation.md`).

## Where FX-26 stood

Most regions were already analysis only:
- `@l`, `@t`, the region variables of `poly`, and `private-regions` name
  sets of locations for effects and aliasing. They are FX-87's regions:
  Lucassen's are names for sets of locations and manage no memory.
- Plain `cons` at type `(listof int @l)` allocates in the collected heap,
  even inside a `letrena r` body at type `(listof int r)`.

Only one thing was dynamic: the value that `letrena` and `letreap` bind,
which `rcons`, `rnew`, `rmake-array`, `rmake-icell`, `rmake-bloblet` and
`rlambda` allocate into. So `letrena r` bound a region name and an arena at
once, and tied the arena's lifetime to the name's scope, as Tofte and
Talpin's static and dynamic regions are one (from memory). That stopped
being enough as soon as data had to outlive the region it was analysed in:
freezing.

## Places, a kind of their own (done 2026-09-27)

- A **place** is a name of kind `place`, with `place ≤ region`: every place
  is also a region, the region of the data allocated in it directly. A
  place may stand wherever a region may, but not the other way round.
- `letrena p` and `letreap p` bind a place: an arena, freed when the body
  ends, or a heap of its own that the collector also collects. `p` is also
  a value, of type `(place p)`.
- `letregion r` binds a region only: no memory, and no value. Its data is
  wherever it was allocated.
- A `poly` may bind `(p place)`; `(place x)` and a place binder take only
  a place, so `(place r)` of a `letregion`'s `r` is refused.
- Regions keep their meaning and syntax everywhere else: effects `(read
  r)`, `(write r)`, `(alloc r)`, `(await r)`, `(goto r)`, `(comefrom r)`,
  masking, `@` constants and `private-regions`.

The allocators are for now `(poly ((r place)) …)`, allocating at the
place's own region: `rcons`'s type is `(poly ((r place)) (poly ((t1 type)
(t2 type)) (subr (alloc r) ((place r) t1 t2) (pairof t1 t2 r))))`.

## Two relations on lifetimes, each one-directional

Write `a ≤ b` for "`a` won't outlive `b`": `a` may stop being usable
before `b` does, never after. Then there are two things one may need to
say about a value `X`:
- **An upper bound, "X won't outlive `p`"** (`X ≤ p`). X is usable no
  longer than `p` lives. Data allocated in `p` needs this: it must not be
  used after `p`'s memory is given back.
- **A lower bound, "X outlives `q`"** (`q ≤ X`). X stays usable at least
  until `q` ends, and perhaps longer, wherever its memory is. A result that
  leaves a scope needs this.

Rust's `&'a T` (a reference usable for at most `'a`) and `T: 'a` (a type
that outlives `'a`) are the same two directions; Cyclone's region
subtyping is one outlives order used both ways (both from memory).

## What relies on which (an audit of the code, 2026-09-27)

Everything so far rests on the **upper bound**, carried by *mention*: a
value whose type mentions a region cannot be used outside that region's
scope. The lower bound appears only implicitly, from lexical nesting and
the runtime's order of places.

| mechanism                                                           | relies on                                                                                                                                                               |
| ------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `close_region` (`check.rs`): the body's type may not mention `r`    | Upper bound: anything mentioning `r` (its data, a `(place r)`, a closure with `(alloc r)` or `(read r)` in its latent effect) won't outlive `r`'s scope.                |
| …and no `comefrom` left after masking                               | Upper bound, for continuations: one captured inside won't outlive the scope.                                                                                            |
| types made of types (a heap list of an arena's refs)                | Upper bound, carried structurally: the container mentions `r` too, so it won't outlive `r` either, wherever its own memory is. So storing across places needs no check. |
| masking                                                             | Neither: it is about who can observe, not how long.                                                                                                                     |
| `region_exit` (`regions.rs`) ends `h` and every newer place         | Outlives, as a total order: older places outlive newer ones, a stack, which lexical nesting guarantees. Green threads break it (the actors note's Q1).                  |
| "anything too big for a chunk … goes to the heap … Either is sound" | Lower bound: data in a place that lives longer than claimed is always safe.                                                                                             |
| quarantine of ended reaps                                           | Upper bound, made good at run time: a dead frame slot may still point into an ended reap, so its chunks are not reused until a collection finds nothing pointing there. |
| plain `cons` into the heap                                          | Lower bound, trivially: the heap outlives everything.                                                                                                                   |

**What `letfreeze` changes.** Every construct so far *keeps* a mention.
`letfreeze` is the first to *replace* one: its region `r` becomes `(const
p)`. Replacing a mention needs two lower bounds the checker has never
checked explicitly:
1. **The data's memory outlives the new bound**: `p ≤ place(data)`, the
   "too big goes to the heap" argument, now in the checker;
2. **The new bound outlives the scope**: `scope ≤ p`, or the result could
   not be used.

So mention stays the upper-bound mechanism, unchanged, and lower bounds are
checked exactly where a mention is dropped or replaced: `letfreeze` now;
later, messages copied between heaps, and anything stored in a place whose
lifetime does not follow from lexical nesting.

## The order, by nesting

Within one program the order is lexical. Each region or place variable is
bound somewhere, and `a ≤ b` holds when:
- `a` and `b` are the same;
- `b` is bound around `a`'s binder: an enclosing `letrena`, `letreap`,
  `letregion` or `letfreeze`, or a `poly`'s or `plambda`'s binder (a
  procedure's regions and places outlive anything its body binds);
- `b` is `heap`, or a region constant (`@l`), which never end.

Where nesting does not decide (two binders of one `poly`, a caller's
place and region), a bound is written on the binder, below.

## The allocators: a place and a region

An allocation puts data at region `r` into place `p`. It needs `r ≤ p`:
the data won't outlive `r` (by mention), and `r` won't outlive `p`, so the
data won't outlive its memory. A region bound inside `p`'s scope satisfies
it, and so does `p` itself.

So the allocators take both, with a **bounded binder**, `(r region p)`:
"a region `r` that won't outlive `p`":

```
rcons : (poly ((p place) (r region p))
          (poly ((t1 type) (t2 type))
            (subr (maxeff (alloc r) (alloc p)) ((place p) t1 t2) (pairof t1 t2 r))))
```

- Instantiation checks that the solved `r` won't outlive the solved `p`,
  by the order above.
- A bounded region binder that nothing solves defaults to its bound, so
  `(rcons p 1 nil)` with no type expected allocates at `p`'s own region,
  as it does today.
- `(alloc p)` keeps the place live: a closure that allocates into `p`
  mentions `p` in its latent effect, and so cannot leave `p`'s scope,
  whatever region its data is at. When `r` is `p`, the effect is `(alloc
  p)`, as today.
- A user's procedure may bind a bounded region too, which is how a library
  builds data at its caller's region in its caller's place.

## `heap`

`heap` is a place name always in scope, the top of the order: plain `cons`
is `rcons` into `heap`. Freezing into the heap is the common case.

## Freezing

`(letfreeze r p body …)` binds a region `r`, bounded by `p` (`r ≤ p`,
where `p` is a place in scope, `heap` when omitted:
`(letfreeze r body …)`). The body builds, and may mutate, data at `r`, and
its result, at a type mentioning `r`, leaves with `r` replaced by `(const
p)`.
- **The upper bound, by mention, as for any region:** nothing whose type
  mentions `r` escapes, except the result, retyped. So at the end the
  result is the only way into `r`'s data, and nothing that could write
  `r` survives.
- **Lower bound 1, memory:** each allocation at `r` goes into a place that
  outlives `p`: `p` itself, a place bound around `p`, or `heap`. Plain
  `cons` goes into the heap, so it always qualifies.
- **Lower bound 2, the scope:** `p` is bound around the `letfreeze`, so it
  outlives it.
- **`(const p)`** is a region, not a place (nothing can be allocated at
  it):
  - it admits no `write` and no `init`, so `set-car!` on a frozen list
    fails to check, needing `(write (const p))`;
  - reads of it are pure, as reads of a frozen bloblet's fields are;
  - it mentions `p`, so frozen data won't outlive `p`;
  - `const` alone means `(const heap)`.
- **Cost:** none at run time. Nothing is copied or marked; the old aliases
  are all gone by typing. This is the static counterpart of
  `bloblet-freeze`, which freezes one object and relies on the header's
  frozen bit to refuse the old aliases' writes; pairs have no header.

`(listof T (const p))` is then the immutable list, which `confirm` may
check a size of.

## What else the split touches

- **Green threads and actors.** Places end newest first, since a place's
  handle is a position in one stack. Interleaved threads would end each
  other's places, so each thread needs its own stack of places before any
  preemption (the actors note's Q1). A process's private heap is then a
  `letreap` with the process's extent.
- **Messages between heaps or nodes.** A type is transmissible when it
  mentions no place but `heap` and no region but `const` (and addresses).
  Freezing is how a program makes something it can send.
- **Dynamic checks.** Membership in an arena or reap is checkable at run
  time by address, now that values are addresses. Membership in a region
  is not: it exists only in the analysis.

## Steps

1. **Places as a kind** (done 2026-09-27): `place ≤ region`, `(place p)`,
   `letrena`/`letreap` binding places, `letregion` binding regions, in both
   checkers, the lowering, both compilers, register code from both, and
   the evaluator.
2. **The order by nesting**, in both checkers: each region and place
   variable knows the binder around it; `a ≤ b` by the rules above.
   *Done 2026-09-27.*
3. **Bounded region binders and the allocators with a place and a
   region**, with the default to the bound and `(alloc p)`. Test: a graph
   whose nodes and edges are two regions of one arena, and a region bound
   outside a place refused for it. *Done 2026-09-27*
   (`run/two-regions-one-place.fx`, `run/caller-place.fx`,
   `regions/region-outlives-place.fx`, `regions/caller-region-outside.fx`).
4. **`heap` as a place name.**
5. **`letfreeze` and `(const p)`**, into `heap` first, then into any place
   in scope. *Into the heap done 2026-09-27*, ahead of steps 2–4: the
   allocators could only allocate at a place's own region, so a
   `letfreeze`'s data could only be the heap's, and lower bound 1 held
   with nothing to check. `const` is `Region::Frozen` (`r-frozen`); what is
   done to it is never masked, so a write to it is refused wherever it
   happens. Tests: a list built with `set-cdr!` inside and frozen, then
   `set-car!` on it refused; an allocation into a place that does not
   outlive the bound refused.
6. **Later: written outlives constraints** between places, for places whose
   order nesting does not decide (threads, and places passed around).
