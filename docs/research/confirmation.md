# Confirming a type at run time

Design note, 2026-09-27, from a discussion with the user: subtype
ascription by dynamic confirmation. A value whose static type is weaker
than wanted (a list of unknown length) is checked at run time against a
stronger type (a list of three), and used at the stronger type if it
passes.

Citations are from memory unless they name a file; check them before
relying on them.

## Two steps, in order

1. **Mutable to immutable, statically.** A check says something only
   about data nobody can change afterwards: a list checked to have three
   cells could have a fourth added a moment later. So data is frozen first
   (`letfreeze`, in `docs/research/places-and-regions.md`), which is
   static and costs nothing at run time. There were two other ways:
   - *Copy*, always sound, at O(n). `datum-list` does this today, as
     `%fx26-list-copy`.
   - *Freeze in place, checked at run time*, as `bloblet-freeze` does
     with the header's frozen bit. Pairs have no header, so this cannot
     work for lists.
2. **Immutable to size-indexed, dynamically.** `(listof T const N)` is a
   list of exactly `N` elements. Only an immutable list may have a size
   index, since only its size cannot change.

## The form

Failure shows in the type, as FX does elsewhere, rather than as a hidden
trap. So `confirm` branches, the way `tagcase` does:

```
(confirm e T (x body) else)
```

If `e`'s value is a `T`, `body` runs with `x` bound to it at type `T`;
otherwise `else` runs. `T` must be a subtype of `e`'s static type with its
checkable parts strengthened. A `confirm` that aborts to a prompt on
failure is a library procedure over this form.

## What can be checked

- **Sizes.** Counting `N + 1` cells at most, O(N).
- **Tags of sums**, as `tagcase` already does.
- **Types of values in a `datum`**, for the parser's and the reader's
  data: `datum-int?` and the others, generalised to a type grammar.
- **Places**, by address: data in an arena or reap is in that place's
  chunks, which the runtime knows now that values are addresses.
- **Not regions.** They exist only in the analysis. A region in the
  confirmed type must be the static type's region, or `const`, which the
  static side established.
- **Not functions by walking them.** A closure can be confirmed only if it
  carries its type (`docs/research/type-and-effect-directions.md`, "Closures
  that carry their types"), or by wrapping it so that each call is checked,
  as Racket's contracts do.

## Cycles

A walk of a value against a recursive type must not diverge on cyclic
data. The standard technique: remember the (object, type) pairs already
visited. A value has finitely many objects, and a recursive type is a
regular tree with finitely many distinct subterms, so there are finitely
many pairs and the walk ends. What a revisit means depends on how the type
is read:
- **Inductively** (a finite list or tree, and anything with a size): a
  pair met again on the current path is a cycle, and a cycle is not a
  finite list, so it fails. Tortoise and hare is the constant-space case
  for a list; the runtime's proper-list test (`%fx26-list?`) uses it.
  With a size `N`, the walk is bounded by `N + 1` steps anyway.
- **Coinductively** (a stream, or a graph type): a revisit succeeds. This
  is the greatest fixpoint.

A list built by `cons` and frozen cannot be cyclic unless it was built
with `set-cdr!` inside the `letfreeze`, which is allowed. So the check
must handle cycles even on frozen data.

**Precedents:**
- **Recursive subtyping**: Amadio and Cardelli, "Subtyping Recursive
  Types", TOPLAS 1993; Brandt and Henglein, "Coinductive Axiomatization of
  Recursive Type Equality and Subtyping", 1998. The same assumption-set
  technique, for comparing two types.
- **`equal?` on cyclic data**, which R7RS requires to terminate: Adams and
  Dybvig, "Efficient Nondestructive Equality Checking for Trees and
  Graphs", ICFP 2008, with union-find over pairs. SRFI 38 and R7RS's datum
  labels do the same for printing.
- **Serialization with sharing**: Java serialization's handle table.
- **Regular tree types**: XDuce (Hosoya and Pierce) checks values against
  them with tree automata.
- **Checking at each access instead of all at once**: Racket's chaperones
  and impersonators (Strickland, Tobin-Hochstadt, Findler and Flatt,
  OOPSLA 2012), after Findler and Felleisen's higher-order contracts
  (ICFP 2002). This is the only way for functions and for data that
  stays mutable.
- **Static types with dynamic checks where static reasoning stops**:
  Flanagan's hybrid type checking (POPL 2006); Greenberg, Pierce and
  Weirich's manifest contracts (POPL 2010).

**Cost.** The visited set can be a hash set of (address, type state). Mark
bits, as the collector uses, would need a bit per type state rather than
one per object, so a hash set is simpler to start.

## Finite data (done 2026-09-27)

`finite`, `(finite p)`: what a `letfreeze` gives when its body never wrote
its region, only built it: frozen data no cycle runs through. So
finiteness is a property of the frozen region, and so of lists and trees
alike, and a size index (below) refines it. `(listof T finite)` is the
finite list of unknown size.

## Sizes

- **What a size can be:** a literal; then a variable bound by `poly`, in a
  kind `size`: `(poly ((n size)) (subr pure ((listof T const n)) (listof U
  const n)))` is `map`'s shape.
- **Arithmetic on sizes** (`append`'s `n + m`) is where this becomes an
  indexed type system, as in Xi and Pfenning's Dependent ML (PLDI 1998,
  POPL 1999), not full dependent types. `confirm` is the way back in
  wherever the static reasoning stops.
- **What sizes buy:**
  - bounds checks on `array-ref` that need no test;
  - costs that depend on sizes, as Reistad and Gifford's
    (`GiffordHistory/papers/lfp94.pdf`), for the time direction;
  - responsiveness: recursion over a size-indexed list whose size strictly
    decreases is bounded, and so need not be `spin`. That is how
    structural recursion stops being `spin` without full dependent types.

## Tasks

1. **CF1 (M). `confirm` with literal sizes** on `(listof T const N)`,
   in both checkers, the lowering, both compilers and the evaluator.
   Needs PR3 (`letfreeze` and `const`). Test: a frozen list of three
   confirmed at three and refused at two; a list made cyclic with
   `set-cdr!` inside the `letfreeze` refused at every size, without
   hanging.
2. **CF2 (M). The type walk**: `confirm` against any first-order type
   (sums, products, lists, bloblets, datums), with the visited set, and
   inductive and coinductive readings. Test: cyclic data of each shape,
   under the timeout wrapper.
3. **CF3 (M). Size variables**: the `size` kind, with equality only (no
   arithmetic), so that `map` and `reverse` keep their sizes.
4. **CF4 (L, later). Size arithmetic**, and array bounds by size.
5. **CF5 (L, later). Functions**, by carried types or by wrapping.
