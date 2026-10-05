# Shapes: a third axis beside regions and places

Design note, 2026-09-30, from a discussion with the user. It asks what a
region describes, and proposes that one thing FX-26 has been putting in
the region slot, the *shape* of data, is a different kind of thing
altogether. Nothing here is built; it is the framing for decisions to
come. F13's fix (`soundness-findings.md`) is built in the meantime in
terms this note maps onto.

## What a region was for

Lucassen's regions are alias classes: "a region constant corresponds to a
countably infinite set of locations" (Lucassen, *Types and Effects*, MIT
thesis, 1987, §3; copy in `GiffordHistory/papers/`). Effects name them so
that two computations can be shown not to interfere. They manage no
memory.

The same thesis puts a second thing in the slot (§7.4, "Immutable
Regions", p. 115): one designated region, IM, on which no WRITE is
allowed. Reading and allocating in it may then be PURE, one set of type
constructors serves mutable and immutable data, and immutable data can
still be initialized imperatively, under a masking construct. Lucassen
gives as a reason that a circular immutable structure can then be made.
FX-87's implementation spells IM `@=`: its recovered checker answers
`(new 3)` with `(ref int @=)`, and `library/takl.fx` uses `(listof int
@=)` (`GiffordHistory/HISTORY.md`, `mit-psrg-fx/fx87/`). IM is not an
alias class. It is a policy (no writes) written where an alias class
goes, justified because the policy is stated in effects.

FX-26 has since put two more things there:
- **places** (`places-and-regions.md`, 2026-09-27): where data is
  allocated and how long it lives. `place ≤ region`; `heap` is a place.
- **acyclicity** (`acyclic-regions.md`, 2026-09-28): `(acyclic p)`, frozen
  data never written after it was built, and so without cycles; `(acyclic
  p) ≤ (const p)`. That note calls the flag "the kind data on the region
  the user asked for".

So `Region` (`ast.rs`) now holds four different things:

| in the slot                           | what it says                                  |
| ------------------------------------- | --------------------------------------------- |
| `@r`, region variables, `(globals g)` | an alias class, for effects (Lucassen's)      |
| `heap`, and the `p` of `(const p)`    | a place: where the data is, how long it lives |
| `const`                               | no writes: Lucassen's IM, FX-87's `@=`        |
| the flag of `(acyclic p)`             | the data's shape                              |

`Region::Frozen(Option<DVar>, bool)` is a place and a shape in one
region. Two soundness holes came from the seam: F2 (a closure reading
place-frozen data forgot the place) and F13 (`acyclic?`, typed `pure` over
`data`, forgot it the same way).

## The shape lattice (the user's)

```
flat  ≤  acyclic  ≤  graph  ≤  generative
```

- **flat**: no references at all. Bits: `int` as a fixnum, `char`,
  `bool`, the fixed-width integers, `f32`, `f64`; a flat array's
  elements.
- **acyclic**: references, but no path returns to where it began; sharing
  is allowed. Frozen and never written.
- **graph**: any structure of references, cycles too, but no *generated
  names*: nothing whose meaning is that it is this one and no other.
  Frozen.
- **generative**: holds generated names: anything a program can tell apart
  from a copy of it.

A shape is *deep*: a value's shape is the greatest among everything it
reaches (a frozen list of refs is generative). A region or a place is
*shallow*: it says where one cell is, and a list's elements have their
own. That alone says shape is not a region: the two are properties of
different things.

Each level has its own natural operations, and each is where FX-26
already needs to know the level:

| shape      | equality               | copying                   | printing, sending    | a walk ends?      | what else applies    |
| ---------- | ---------------------- | ------------------------- | -------------------- | ----------------- | -------------------- |
| flat       | the bits               | copying the bits          | the bits             | nothing to walk   | nothing, not a place |
| acyclic    | structural recursion   | a tree copy               | an s-expression      | yes (size-change) | a place              |
| graph      | bisimulation           | a copy with a sharing map | datum labels (`#0=`) | only with marking | a place              |
| generative | identity (exact `eq?`) | none: only referenced     | not faithfully       | —                 | a place, and regions |

The last column is the point. A location is a generated name: `new` makes
one, as ν does in the π-calculus. So mutable data is generative by
nature, and Lucassen's regions, alias classes of locations, only mean
anything at the top level. Below it there are no locations that matter:
the slot does a place's work and no more. Seen this way IM, `@=` and
`const` are the boundary between generative and graph ("no names below
here"); `acyclic` is the next boundary down; flat arrays the one below
that.

The day's other decisions fall on the same lines:
- `eq?` (`docs/fx26.md`, "Identity") is exact on generative data, and
  "`#t` means equal" below it, where the compilers may share and copy.
- `uniqueof` (`TODO.md` §19) is a generated name around graph-shaped
  contents: exact identity, contents read purely. Interning needs just
  that.
- Q6's flat arrays are the flat level made concrete, and Q6 first
  proposed a `flat` kind.
- Q8's generic operations (`equal`, `hash`, `->datum`, copying) are one per
  level of this table.

## Shape as a kind

FX-26 already has one shape kind: `data`, a subkind of `type`
(`Kind::Data`; `check.rs`, `is_data`), which admits base types, `datum`,
products and sums, and frozen pairs and bloblets of data. That is "shape
≤ graph", less the flat/acyclic distinctions. So the lattice reads
naturally as the kinds of type binders, with subkinding along it:

```
(t flat)  ≤  (t acyclic)  ≤  (t data)  ≤  (t type)
```

(`data` would be the graph level; whether to rename it `graph` is a
choice below.) A binder's kind then says what a polymorphic procedure may
do with its values: walk them without `spin`, compare them structurally,
copy them, print them, or only hold and pass them.

A kind alone does not say where data lives. For everything above flat,
data has a place, and a procedure that reads it reads that place. F13 is
exactly a `data` binder whose values' place was nowhere in the type. So
a shape kind above flat takes a place: `(t data p)`, `(t acyclic p)`,
with the plain forms meaning `heap`. This is F13's fix, below.

## Where the current constructs go

| construct                        | region            | place  | shape                             |
| -------------------------------- | ----------------- | ------ | --------------------------------- |
| `(ref T @r)`, arrays, i-cells    | `@r`              | `heap` | generative                        |
| `(listof T @r)`, mutable         | `@r`              | `heap` | generative (writable)             |
| `rcons p …`, `letrena p`         | `p` (as a region) | `p`    | generative                        |
| `(const p)`, `letfreeze (r p)`   | none: no writes   | `p`    | graph                             |
| `(acyclic p)`, `certify-acyclic` | none              | `p`    | acyclic                           |
| `(flatarrayof T R)`              | `R`               | `heap` | generative array of flat elements |
| products, sums, `datum`          | none              | `heap` | graph, or acyclic when built so   |
| `(globals g)`, `@globals`        | an alias class    | —      | — (bindings, not data)            |
| procedures                       | —                 | `heap` | see below                         |
| `define-generative` types        | —                 | —      | see below                         |

`letfreeze` is where data crosses from generative to graph: while its
body runs the region is writable; as it ends the writes stop and the
region becomes a shape at a place. `certify-acyclic` crosses from graph to
acyclic, on evidence.

## Two senses of "generative"

The lattice's top covers two different generated names:
- **runtime names**: locations (`new`, `cons` at a writable region),
  gensyms, `uniqueof`. Evaluation makes them; two evaluations make two.
- **nominal types**: `define-generative`, which makes a type equal only to
  itself. Its values need not have any runtime name: `up-tree` is the
  identity at run time.

The `data` kind already excludes the second kind (a generative type is
not data, "reading one in would be `up`"). Both are ν-bound names, so a
single top is plausible, but they behave differently: a value of a
nominal type could be flat or acyclic underneath, and copying it is
harmless at run time. Whether nominal types belong in the lattice at all,
or are a separate axis (abstraction, not shape), is open.

## Procedures

A procedure is not data (the `data` kind refuses it). It may hold
generated names in its closure, and compilers rebuild procedures freely
(lambda lifting, specialization), which is why `eq?` of procedures is
unspecified. It fits "generative" for what it may hold, but it cannot be
compared, copied or printed at any level. It may be a level of its own
beside the lattice, or simply "generative, and opaque".

## Syntax, if this is adopted

Nothing is decided; these are the questions it raises:
1. **Types.** Keep the one slot in `(listof T R)`, read as either an alias
   class (mutable, generative) or a shape at a place (frozen), which is
   what `Region::Frozen` already does, now named for what it means; or
   give frozen data a slot of its own. The first changes least: `const`
   and `acyclic` become two points of the lattice written where a region
   goes, and `flat` joins them for flat arrays.
2. **Kinds.** `flat`, `acyclic`, `data` (or `graph`), `type` as binder
   kinds, with places on the middle two.
3. **Names.** `data` or `graph` for the third level; `generative` or
   `type` for the top.
4. **Sizes.** `(nlist T n)` is acyclic by construction; its size is a
   refinement of the acyclic level.

## What F13 built (2026-09-30)

`(t data p)`: a `data` binder with a place, written as a region binder's
bound is, `(r region p)` (first proposed as `(t (data p))`). `t` is data whose frozen
regions are all `(const heap)`/`(acyclic heap)` or frozen into `p`; plain
`(t data)` is `(t (data heap))`. `acyclic?` and `length-is?`, which walk
their argument, become `(poly ((p place) (t data p)) (subr (read (const
p)) …))`: at `heap` the read is of heap-frozen data and erased, so
nothing changes for heap data; at an arena's place it names the place,
and a closure that walks place data cannot leave the place.
`certify-acyclic` and `certify-length` take the same binder and stay
`pure`. The place is solved from `t` (the one place its frozen regions
name, or `heap`). In this note's terms, `(t data p)` is "graph shape at
place `p`", so it carries over whatever the syntax becomes.

## Two axes, not one: shape, and how a type is defined (the user's, 2026-10-05)

Not designed yet; a note of the user's thinking, to tease apart before
the syntax above is settled. There are two distinct properties a type can
have, and so probably two distinct kinds, to be named, indicated and
composed in type expressions explicitly.

**Axis 1: the shape of the run-time values.** A bound on what the values
themselves look like in memory. The lattice above, refined:

```
flat  ≤  tree  ≤  acyclic  ≤  graphic  ≤  (the top)
```

- **flat**: no references.
- **tree** (name to choose): references, but no sharing: every heap
  object has a unique parent. New: the lattice above has no level
  between flat and acyclic.
- **acyclic**: sharing, but no cycles.
- **graphic**: cycles too, but no functions and no generated names:
  today's `data` kind, perhaps renamed so in this framing (the "graph"
  level above).
- **the top**: anything, functions and generative types included: values
  tied to the local environment's transient characteristics, which cannot
  be serialized, sent over the wire and meaningfully rebuilt.

So the question this axis answers is what can be done with a value:
walked without `spin`, copied, compared structurally, printed, sent.

**Axis 2: how the type itself is defined** (to name: *metatype*, *meta*,
*source*, *reflect*). A property of the type's definition, not of its
values, and purely static. The example is polytypism as PolyP has it:
every type there is the fixed point of a single-parameter functor. Two
distinct definitions can describe the same final structure once the
intermediate functors' names are taken out of the picture, and any value
can then be cast between them with no run-time effect. So "polytypic
(PolyP's)", "regular", and `type` itself form a chain, or a lattice, of
how a type is defined, each admitting more definitions than the one
below.
- Function types may move a type along this axis, but how is not yet
  clear. (An observation to check, not the user's: a functor whose
  parameter appears only in covariant positions, such as the result of a
  function type, `r -> a` in `a`, is still a functor; one with it in a
  contravariant position, `a -> r`, is not; and PolyP's regular types are
  sums of products only.)
- Part of the notion is a clear separation between a type parameter and
  what it resolves to: polytypic operations apply to a functor applied to
  a function type, since that function is abstracted away as the
  parameter. What matters is the definition's structure, not the
  arguments it is applied to.

**Why they are separate.** One axis bounds values; the other classifies
definitions. A regular, polytypic type may be applied to functions (top
of axis 1); a flat type may be defined in any way at all. Today `data` is
the only kind on either axis, and it mixes them: it bounds shape
(`graphic`) and, by refusing functions and generative types, says
something about definitions too. Two senses of "generative", above, are
the same tension: a nominal type is about the definition, a location
about the value.

**To do.** Name both axes and their levels; say how each is written (a
binder's kind, a bound on it, or both, `(t graphic p)` beside something
like `(f regular)` on a functor of kind `(=> (type) type)`); say how they
compose, and where each is checked (axis 1 by construction and
certification, as `acyclic` is; axis 2 from the definition, as the
checkers' kinds already are). Related: `docs/research/polytypic.md`
(PolyP's `cata`, and why FX-26 fixed the functor before higher kinds),
Q8's generic operations, and the higher kinds now in both checkers.

## Sources

| source                                                                                                                | where                                                                                          | seen        |
| --------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------- | ----------- |
| Lucassen, *Types and Effects: Towards the Integration of Functional and Imperative Programming*, MIT PhD thesis, 1987 | `~/Dev/LangPlay/GiffordHistory/papers/lucassen-1987-types-and-effects-thesis.pdf`, §7.4 p. 115 | read (§7.4) |
| FX-87's recovered implementation, `@=`                                                                                | `GiffordHistory/HISTORY.md`; `mit-psrg-fx/fx87/library/takl.fx`                                | read        |
| Milner, Parrow, Walker, "A calculus of mobile processes" (ν as name generation)                                       | —                                                                                              | from memory |
| `docs/research/places-and-regions.md`, `acyclic-regions.md`, `generative-types.md`                                    | this repository                                                                                | read        |
