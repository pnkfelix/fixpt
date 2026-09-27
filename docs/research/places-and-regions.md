# Places and regions

Design note, 2026-09-27, from a discussion with the user. It splits what
FX-26 calls a region into two things:
- a **region** is for analysis: a name in types and effects, erased
  before anything runs;
- a **place** is for allocation: memory that data is put in, with a
  lifetime.

## Where FX-26 stands

Most regions are already analysis only:
- `@l`, `@t`, the region variables of `poly`, and `private-regions` name
  sets of locations for effects and aliasing. They are FX-87's regions:
  Lucassen's are names for sets of locations and manage no memory.
- Plain `cons` at type `(listof int @l)` allocates in the collected heap.
  It does so even inside a `letrena r` body at type `(listof int r)`. The
  checker's record of each allocation's region stopped being used to
  allocate when `rcons` came, and is gone (2026-09-27).

Only one thing is dynamic: the value of type `(region r)` that `letrena`
and `letreap` bind. `rcons`, `rnew`, `rmake-array`, `rmake-icell`,
`rmake-bloblet` and `rlambda` allocate into it.

So the conflation is narrow: `letrena r` binds a region name and an arena
at once, and ties the arena's lifetime to the name's scope. That is
Tofte and Talpin's design, where static and dynamic regions are one (from
memory). It stopped being enough as soon as data had to outlive the
region it was analysed in: freezing, below.

## The split

**Regions** keep their meaning and syntax: `@r` constants, `(r region)`
binders, `private-regions`, and effects `(read r)`, `(write r)`,
`(alloc r)`, `(await r)`, `(goto r)`, `(comefrom r)`. Masking works on
regions, as now.

**Places** are new names, of a new kind:
- `(p place)` in a `poly` binder;
- a type `(place p)`, of a place as a value;
- one place always exists: `heap`, the collected heap, which outlives
  everything (Rust's `'static`).

A place is bound by the forms that make memory:
- `(arena p body …)` binds `p`, an arena, freed when the body ends (today's
  `letrena`'s memory);
- `(reap p body …)` binds `p`, a heap of its own that the collector also
  collects (today's `letreap`'s memory).

The allocators take a place and allocate at a region:

| operation             | type                                                                                                                             |
| --------------------- | -------------------------------------------------------------------------------------------------------------------------------- |
| `(rcons p x y)`       | `(poly ((p place) (r region)) (poly ((t1 type) (t2 type)) (subr (alloc r) ((place p) t1 t2) (pairof t1 t2 r))))` with `r` in `p` |
| `(rnew p v)`          | the same shape, making `(ref t r)`                                                                                               |
| `(rmake-array p n v)` | making `(arrayof t r)`                                                                                                           |
| `(rmake-icell p)`     | making `(icell t r)`                                                                                                             |

Plain `cons`, `new`, `make-array` and `make-icell` allocate in `heap`.

## Bounding a region by a place

Data allocated in place `p` at region `r` must not be reachable after `p`
ends. Types mention regions, not places, so the checker needs to know
which places a region's data may live in: the constraint `r in p`, read
"region `r` is bounded by place `p`".

The user's question was whether the system should allow or force this
bound. The answer differs by place:
- **A place that ends (`arena`, `reap`): forced.** Soundness needs it. An
  allocation `(rcons p x y)` at region `r` requires `r in p`. Every value
  whose type mentions `r` is then treated as mentioning `p`, and so
  cannot leave `p`'s scope. That is today's rule for `letrena`, applied to
  the place rather than the name.
- **`heap`: never needed.** It never ends, so `r in heap` holds for every
  `r` and is not written.

Two more choices, both allowed:
- **Several regions in one place.** One arena can hold a graph's nodes at
  `n` and its edges at `e`. Reading nodes then does not conflict with
  writing edges: finer effects, one lifetime.
- **One region in several places.** `r in p1` and `r in p2` together bound
  `r` by both places, so `r` lives only as long as the shorter.

**How the bound is established, in stages.**
1. **By nesting.** A region bound inside a place's scope (by `letregion`,
   below, or by the sugar for today's forms) is in that place, and cannot
   outlive it, because its binder is inside. No constraint syntax is
   needed. This covers everything today's `letrena` and `letreap` do.
2. **By constraints in signatures.** A procedure that allocates into a
   place its caller gives needs `r in p` in its type, as `rcons`'s type
   has above. The syntax is a `where` clause on `poly`:
   `(poly ((p place) (r region)) (where (r in p)) T)`. Its caller must
   establish the constraint where it instantiates `p` and `r`.
3. **Outlives between places.** Rust's and Cyclone's lifetimes (from
   memory: Cyclone's region subtyping by outlives constraints, Grossman,
   Morrisett, Jim, Hicks, Wang and Cheney, PLDI 2002). `(p1 outlives p2)`
   lets data in `p1` be stored in `p2`'s data, and `r in p1` then implies
   `r in p2`. It is for later: nesting gives it wherever places are
   lexical.

## A region binder that makes no memory

`(letregion r body …)` binds a region only. What the body does to `r` is
masked, and the body's value may not mention `r`, as `letrena`'s may not
today. With no place of its own, its data lives in `heap`, or in a place
bound outside it.

Today's forms become sugar, keeping their meaning:
- `(letrena r body …)` = `(arena r (letregion r body …))`, a place and a
  region with one name, the region in the place;
- `(letreap r body …)` = the same with `reap`.

## Freezing

`(letfreeze r body …)` binds a region only, as `letregion` does, and
makes the body's value immutable as the region ends.
- **Why it is sound.** The checker already refuses to let anything whose
  type mentions `r` escape the body, except through the result. So at the
  end the result is the only way into `r`'s data, and nothing that could
  write `r` survives.
- **The frozen type.** The result's type has `r` replaced by a region
  `const`, on which there can be no `write` and no `init`. So
  `(set-car! xs 1)` at `(pairof int t const)` fails to check, since it
  needs `(write const)`. Reads of `const` are pure, as reads of a frozen
  bloblet's fields are. So `(listof T const)` is the immutable list, and a
  frozen bloblet is `(bloblet (frozen T …) const)`.
- **Places.** If the data was allocated in `heap`, the frozen value can go
  anywhere. If it was allocated in a place `p` bound outside (`r in p`),
  the frozen data still lives in `p`, so the result is `const` bounded by
  `p`: one `const` region per place, `(const p)`, where plain `const`
  means `(const heap)`. So freezing into an arena needs stage 2 above.
- **Cost:** none at run time. Nothing is copied or marked, and the old
  aliases are all gone by typing.

This is the static counterpart of `bloblet-freeze`, which freezes one
object and relies on the header's frozen bit to refuse the old aliases'
writes. Pairs have no header, so lists could not be frozen that way.

## What else the split touches

- **Green threads and actors.** Places end newest first today, since a
  region handle is a position in one stack (`regions.rs`,
  `region_exit`). Interleaved threads would end each other's places. So
  each thread needs its own stack of places before any preemption: the
  actors note's Q1 (`docs/research/actors-and-distribution.md`). A
  process's private heap is then a `reap` with the process's extent.
- **Messages between heaps or nodes.** A type is transmissible when it
  mentions no place but `heap` and no region but `const` (and addresses).
  Freezing is then how a program makes something it can send.
- **Dynamic checks.** Membership in an arena or reap is checkable at run
  time, by address against the place's chunks, now that values are
  addresses. Membership in a region is not: it exists only in the analysis
  (`docs/research/confirmation.md`).

## Tasks

1. **PR1 (M). The terminology refactoring, with no change of meaning.**
   *Begun 2026-09-27:* the type `(place r)` in place of `(region r)`, and
   `letregion`, in both checkers, the lowering, both compilers, register
   code from both, and the evaluator; `letrena` and `letreap` keep their
   meaning. Then, as the user chose, places are a kind of their own,
   `place`, with `place ≤ region` (a place is the region of the data
   allocated in it directly): `letrena` and `letreap` bind places,
   `letregion` a region, `(p place)` binds one in a `poly`, and
   `(place x)` and a place binder take only a place. The allocators are
   `(poly ((r place)) …)`, allocating at the place's own region; several
   regions in one place, with `r in p` and `(alloc p)` for the place's
   liveness, are PR2.
   - `place` kind, `(place p)` type, `arena` and `reap` forms, and
     `letregion`, in both checkers.
   - `letrena` and `letreap` as sugar.
   - The allocators take a `(place p)` and require `r in p`. At first,
     `r in p` holds only when `r` and `p` are one binder's two names
     (stage 1, by nesting).
   - The lowering, both compilers, the evaluator written in FX-26, and
     `docs/fx26.md`.
   - Test: every existing region test passes unchanged.
2. **PR2 (S). Several regions in one place, by nesting**: `letregion`
   inside `arena`, with `r in p` recorded for a region bound in a place's
   scope. Test: a graph whose nodes and edges are two regions of one
   arena.
3. **PR3 (M). `letfreeze` and `const`**, heap only at first. Test: a list
   built with `set-cdr!` inside, frozen, and then `set-car!` on it is
   refused.
4. **PR4 (M). `where` constraints**: `(r in p)` in `poly` types, checked at
   instantiation. Test: a library procedure that builds a list in its
   caller's arena.
5. **PR5 (M). `(const p)`**: freezing into a place.
6. **PR6 (L, later). Outlives between places.**
