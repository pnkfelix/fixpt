# Acyclic regions: frozen data as evidence of finiteness

2026-09-28. Written after the user asked whether `finite` was "a specific
region, rather than a class of size", whether the approach has precedent,
and whether kind data could be attached to regions so that finite data
can still be freed region by region. It records what the design is, the
rename made (`finite` the region became `acyclic`), and what it costs.

## The design

A cycle in data needs a write after the data is made: a `set-cdr!`, a
`set` of a reference, an array's or an I-cell's. Each such write has the
effect `(write r)` on the region `r` the data lives in. So data that
nothing ever wrote after making it has no cycle, and a walk over its
parts ends.

FX-26 turns that into regions:

- `(const p)`: data frozen into place `p`. Nothing may write it any more;
  it may have been written, and so may be cyclic, before it was frozen.
- `(acyclic p)`: the same, and never written at all, only built. No cycle
  runs through it.
- Plain `const` and `acyclic` are `(const heap)` and `(acyclic heap)`.

`(acyclic p)` is `const` data too, not the other way round: `(acyclic p)
≤ (const p)`. Both checkers represent the pair as one region carrying a
flag: `Region::Frozen(place, acyclic?)` in Rust and `(r-frozen p acyclic?)`
in `check.fx`. That flag is the kind data on the region the user asked
for. The place carries lifetime and memory management; the flag carries
what may be assumed about the data's shape.

Data gets there in two ways:

- **Frozen after building.** `(letfreeze (r p) body …)` gives the body a
  fresh writable region `r`, and freezes what it made into place `p` as
  the body ends. The data is `(acyclic p)` if the body never wrote `r`,
  and `(const p)` if it did. The writes are counted as masking sees them,
  before it could hide them (`regions/const-is-not-acyclic.fx`).
- **Built in order.** `cons` (or `rcons` into a place) may allocate
  straight into an acyclic region, since frozen data cannot be written,
  and a pair whose tail is a `(listof T (acyclic p))` is itself acyclic.
  The parser's trees and `table.fx`'s bucket spines are built this way.

Then termination: in the size-change check (`docs/fx26.md`), the `car` or
`cdr` of a pair at an acyclic region is a part of it, strictly smaller.
So a structural walk over acyclic data needs no `spin`. The checker's
existing rule, that no write may reach a frozen region, is the whole
proof of acyclicity. There is no separate cycle analysis, and no separate
immutability type constructor.

`(acyclic e (x body) else)` (`docs/research/confirmation.md`) covers the
remaining case: `const` data found at run time to have no cycle is given
to `body` at `acyclic`.

## Memory management: acyclic data in an arena

Frozen regions are a family indexed by place, not one global region. So
acyclic data can be managed by region like anything else. It is built in,
or frozen into, an arena, and given back when the arena ends:

```
(define len (poly ((p place)) (subr (read (acyclic p)) ((listof int (acyclic p)) int) int))
  (plambda ((p place))
    (letrec ((go (subr (read (acyclic p)) ((listof int (acyclic p)) int) int)
               (lambda (xs n) (if (null? xs) n (go (cdr xs) (+ n 1))))))
      go)))
(letrena a (len (letfreeze (r a) (the (listof int r) (rcons a 1 (rcons a 2 (rcons a 3 nil))))) 0))
```

(`tests/programs/run/acyclic-in-a-place.fx`.) Data frozen into `a` cannot
outlive `a` (`regions/frozen-outlives-place.fx`), and only the heap's
frozen data is left to the collector.

Until 2026-09-28 the place-polymorphic `len` above did not check. The
reason was not in the list types: neither checker's inference solved a
place binder that appeared inside a frozen region, `(acyclic p)` or
`(const p)`, from the actual argument's region. Both now take the
actual's place (the heap, when the actual is frozen into the heap). They
also count such a region as open while its place is unsolved.

## Sizes: the ladder

The user expected a ladder of sizes: 1, 2, 3, …, finite, unbounded. For
frozen lists it is there, with the region supplying the last two rungs:

| type                 | what it promises                   | rung      |
| -------------------- | ---------------------------------- | --------- |
| `(nlist T 3)`        | frozen and acyclic, exactly 3 long | 3         |
| `(nlist T finite)`   | frozen and acyclic, length unknown | finite    |
| `(listof T acyclic)` | the same as the row above          | finite    |
| `(listof T const)`   | frozen, may be cyclic              | unbounded |
| `(listof T @r)`      | writable: no promise               | (none)    |

`(nlist T finite)` and `(listof T acyclic)` are each other's subtypes
(`docs/research/sizes.md`). The ladder exists only for frozen data, and
must: a size, like acyclicity, is a fact that a write can destroy, so it
can only be a stable fact about data nothing can write. It attaches to
where the no-write guarantee lives, which is the region.

## The rename

The region was spelled `finite` until 2026-09-28, the same word as the
size. The user, who designed the language, had read it as a size, which
shows how well the overloading hid the design. `(listof T finite)` meant
"at the frozen region whose data is all acyclic", and the reader had to
know that.

Now:

- `acyclic` and `(acyclic p)` are the region: named for what it promises,
  as `const` is.
- `finite` is only a size: `(nlist T finite)`, `(nat finite)` (which is
  `nat`), and a size binder's argument.

A description `finite` is therefore the size wherever it is given. The
special case in `proj`, which read the region `finite` as the size when
the binder was a size binder, is gone from both checkers. `finite` where
a region is expected is an error that points to `acyclic`. Every `.fx`
source and test program was rewritten mechanically: a `finite` token was
kept only as the size argument of `nlist` and `nat`.

## Precedent

The pieces are well known. I know of no work that combines them this
way, and I have not searched for one; this may be a gap in my knowledge
rather than a new point.

- **Acyclicity from building without writing** is folklore. It is why
  data in strict ML and in Haskell is well-founded, and why proof
  assistants accept structural recursion over inductive types. ML gets it
  by making lists immutable and confining mutation to `ref`. FX-26 keeps
  Scheme's mutable pairs, so it recovers immutability afterwards, by
  region.
- **Freezing** has close relatives. Gordon, Parkinson, Parsons, Bromfield
  and Duffy, "Uniqueness and Reference Immutability for Safe
  Parallelism" (OOPSLA 2012), converts isolated mutable data to
  immutable. Pony's `recover`, `iso` and `val` do the same. Rust's move
  from `&mut` to shared `&` is a cousin. `letfreeze` is the idea at the
  granularity of a region.
- **Sized types** with a top element: Hughes, Pareto and Sabry, "Proving
  the Correctness of Reactive Systems Using Sized Types" (POPL 1996), and
  Abel's later work. Their sizes run up to ∞, and inductive data is finite
  by construction. `nlist` and `nat` are in that family.
- **Regions and effects**: FX-87 and FX-91 (Gifford, Lucassen, Jouvelot,
  Sheldon, O'Toole), and Tofte and Talpin's region inference.
- **The combination**: a frozen region's flag as the evidence of
  acyclicity, feeding a size-change termination check.

## Costs, and what could change

1. **Granularity.** Frozenness is per region, all or nothing. `table.fx`
   needed its buckets' spines acyclic but their entry pairs writable (a
   key set again changes its entry in place). It worked only because a
   list's elements may live in a region other than its spine's. Data
   that is partly written will keep needing such splits.
2. **Only frozen data.** Writable data promises nothing about its shape,
   even when a program happens never to make a cycle. Proving that would
   need to track which fields are written, not just which regions are.
   That is a type-system extension, left for discussion
   (`docs/research/type-and-effect-directions.md`).
3. **Cycles through procedures.** Landin's knot, a procedure kept in a
   region that it reads, loops with no cyclic data. It needs `spin`, and
   the checker requires it (`regions/knot-through-a-ref.fx`). Acyclic
   regions do not change that. A knot needs a write, so it cannot be tied
   through an acyclic region itself, only through a writable one that a
   procedure kept in acyclic data reads; there the existing rule applies.
