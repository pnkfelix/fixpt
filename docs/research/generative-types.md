# Generative types, on their own

Design note, 2026-09-27, from a discussion with the user: what it would
take to add generativity to FX-26 as a concept of its own, not coupled to
the rest of the type system; whether a kind should separate structural
data, which can be read, printed and sent, from the wider universe that
includes generative types; and how this relates to GADTs and non-regular
families. Exploration only: nothing here is built.

Citations are from memory unless they name a file; check them before
relying on them.

## 1. FX-91's precedent

From the report (`GiffordHistory/papers/fx91-report.pdf`, §§2.2.6, 2.2.9,
2.3.11, 2.4.11) and the implementation (`GiffordHistory/fx-lang/fx91/private/impl.rkt`).

- **Where abstraction lives: only in `module` expressions.**
  `(module (define-abstraction id k dx) … (define-description id dx) …
  (define id e) …)` is a first-class module value, of type `(moduleof (abs
  id k) … (desc id dx) … (val id tx) …)`. `define-abstraction` is legal
  nowhere else.
- **Conversions.** For each abstraction that is not an effect, the module
  body (and only the body) has `up-id : rep → id` and `down-id : id →
  rep`. At higher kinds they are polymorphic: `(poly ((a k) …) (-> pure
  ((rep a …)) (id a …)))`. At run time both are `(lambda (x) x)`: the
  dynamic semantics substitutes the identity for them. Abstraction costs
  nothing.
- **Any kind.** An abstraction may be a type, a type constructor
  (`(->> k …)`), a region-free effect, and so on. Representations of the
  abstractions in one module may be mutually recursive.
- **Identity.** Outside, an abstract type is `(select e id)`: the module
  expression `e`, which must be pure ("to prevent type abstraction
  violation"), and the name. Two are equal when the expressions are
  syntactically equal and the names match (`unify-select?` compares
  `select-module` with `expression=-1?`). This is a path-dependent,
  applicative style of generativity: the path decides.
- **`define-datatype`** rewrites to a `define-abstraction` whose
  representation is the sum of products; a transparent `id-rep`
  description; constructors that are `up` applied to a `sum`; and
  matchers `id′~` that `down`, `tagcase`, and call a success or a failure
  continuation. It introduces these "in the current module binding".
- **Recursion.** FX-91 has no `mu` and no `dletrec`: a recursive datatype
  is recursive *through its abstract name*. So its recursive types are
  iso-recursive, folded by `up` and unfolded by `down`.
- **Effects and regions.** The FX-91 kernel has no regions (FX/R, with
  regions, was separate), so it says nothing about abstraction and the
  store. Effects may be abstracted like anything else.

**Verdict: FX-91 coupled generativity to modules, and through
`define-datatype` to recursion.** Abstractions exist only in `module`
bodies, their identity is a module path, and a recursive datatype is
recursive only by being abstract. It did not couple them to regions,
because it had none.

## 2. Generativity on its own, in FX-26

### What "independent" means

Three things that FX-91 bundled can be pulled apart:

| concept           | what it gives                                           | FX-91's carrier           |
| ----------------- | ------------------------------------------------------- | ------------------------- |
| **generativity**  | a new type, equal only to itself, whatever its insides  | `define-abstraction`      |
| **iso-recursion** | recursion through a name, folded and unfolded on demand | the abstract name         |
| **hiding**        | only some code may convert in or out                    | the `module` body's scope |

"Independent" here means: a form that gives generativity (and with it
iso-recursion, which comes free), with hiding added later through a
mechanism FX-26 already has, and no module system.

### The minimal form

```
(define-generative (name (param kind) …) rep)
(define-generative name rep)
```

It defines:
- a type constructor `name`, new, equal only to itself: `(name d …)`
  equals `(name d′ …)` when the descriptions are related by `name`'s
  variance, and equals nothing else;
- `up-name : (poly ((param kind) …) (subr pure (rep) (name param …)))`;
- `down-name : (poly ((param kind) …) (subr pure ((name param …)) rep))`.

Both conversions are the identity at run time, as in FX-91.

**How it could be built with no change downstream.** Expand it as it is
read, as `define-datatype` is, into:
1. a checker-only form that registers the type (as `define-type` is
   checker-only today);
2. two ordinary definitions, `(define up-name <type> (lambda (x) x))` and
   the same for `down-name`.

The checker checks those two definitions with `name` transparent, which
is the "inside" of the abstraction, as FX-91's module body is. Everything
else sees `name` opaque. The lowering, the evaluator, the compilers and
the machines then see only identity lambdas, which they can inline.

**Scope: per definition, statically.** Each `define-generative` form, at
top level, makes one new name. Dynamic generativity, a new type per
evaluation as ML functors have (Dreyer, Crary and Harper, 2003, from
memory), needs first-class or applied modules, which FX-26 does not have.
It would also make type identity a run-time matter, which the two
checkers and heap images would have to agree on. Leave it out.

**Hiding, later: program-private conversions.** `(private-regions @s)`
already makes a region constant the program's own. The same could make
`up-name` and `down-name` the program's own. A program (the front end is
one) is then FX-26's module boundary, with no new module system.

### A principle for everything else

**Opaque to comparison, transparent to safety.** Equality and subtyping
treat `(name d …)` as a name applied to arguments and never unfold it.
Every analysis whose soundness depends on what a value *contains* looks
through the name, to the representation with the arguments substituted:
- `regions_in`, for masking and for what may not escape a `letregion`;
- `no_knot`, the store-knot rule;
- `writes_in`, what a `letfreeze`'s value may not do;
- `cyclic`, the self-application rule for `spin`.

Hiding the type's structure from programmers must not hide the store from
the checker. So **an abstract type does not hide region effects.** A
value of an abstract type reaching a region is still, for masking, a
value reaching that region. FX-91 had no regions, so it gives no
precedent here, but the rule follows from what masking needs.

### Interactions, one by one

| part of FX-26              | effect of generativity                                                                                                                                         |
| -------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| structural subtyping       | `(name d …) ≤ (name d′ …)` by `name`'s variance, found once from `rep`; a name is never related to a different name or to a structural type                    |
| equi-recursive types, `mu` | unchanged: a name is a leaf to them; structural recursion stays equi-recursive                                                                                 |
| type families and knots    | unchanged; a family body may mention generative names                                                                                                          |
| non-regular recursion      | allowed *inside* a generative `rep` (`(nest a)` mentioning `(nest (pairof a a r))`), since the name is never unfolded to compare: iso-recursion                |
| regions, places            | a region parameter is a parameter like any other; regions in `rep` count as the name's footprint (transparent to safety)                                       |
| effects                    | conversions are `pure`; abstract effects (FX-91 had them) left out                                                                                             |
| `finite`, `const`          | `(name t finite)` just works: finiteness is a region's property                                                                                                |
| `no_knot`                  | looks through the name, with a visited set, as it does through frozen pairs                                                                                    |
| size-change termination    | `down-name` and `up-name` are the identity for tracking, so a `tagcase` on `(down-name x)` gives parts of `x`                                                  |
| inference                  | unification of `(name a …)` with `(name b …)` unifies arguments; with anything else it fails                                                                   |
| printing                   | `name` or `(name d …)`, which reads back                                                                                                                       |
| both checkers              | a new type node (`Ty::Named` in Rust, `ty-named` in `check.fx`), plus a table from name to parameters, `rep` and variance; about 16 Rust and 20 FX match sites |

### Generative datatypes

`define-datatype` stays transparent, as it is now. A generative variant,
say `(define-datatype (name …) #:generative (tag type …) …)`, would
expand as FX-91's does: `define-generative` of the sum of products, and
constructors that `up` a `sum`. Matching is `tagcase` over
`(down-name x)`. Sugar that lets `tagcase` accept `x` directly can come
later, once hiding exists, since it must respect who may `down`.

## 3. Serializable data versus generative types: a kind split

The user's idea: a kind for structural, non-generative types, whose
values can be freely read, printed, confirmed and serialized, kept apart
from `type`, which also holds generative and abstract types.

### Why the split is principled

**Deserializing is `up`.** Making a value of a generative type from bytes
does what `up-name` does: it asserts that a representation meets the
type's invariants. If anyone can deserialize into `name`, then anyone can
`up`, and hiding is gone. So a generative type can be read from outside
only through its owner's validator: its own `confirm`, a checked `up`.
Structural types have no invariants beyond their structure, so for them
reading and confirming are the whole story.

### The kind

- **`data ≤ type`**, as `place ≤ region` today (`Kind::fits`).
- **`T` is `data`** when it is built from:
  - `int`, `bool`, `char`, `string`, `symbol`, `unit`, `datum`;
  - products and sums of `data`;
  - lists and pairs of `data`, at any region;
  - frozen bloblets of `data`.

  It holds no `subr`, `ref`, `icell`, `arrayof`, `prompt-tag`,
  `composable`, `mark-key`, `place`, and no generative name. A generative
  type may opt in only by giving its validator.
- This is nearly the **transmissible** predicate of
  `docs/research/actors-and-distribution.md` (H1): "region-free apart
  from addresses, no mutable or control types". The two should be one
  definition, with addresses as the one addition for messages.

### How the existing plans fit

| operation                          | with the split                                                                                                                                                                 |
| ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `read`                             | unchanged: it returns `datum`, or `(F const)` from outside (`confirmation.md`, CF0), both `data`                                                                               |
| `acyclic : (F const) → (F finite)` | `F : (region) data`: over `data` the walk by representation (CF0's option 1) is exact, since no abstraction hides a cycle it should not see, and nothing opaque is walked into |
| `confirm`                          | defined over `data`; a generative type supplies its own                                                                                                                        |
| printing, `sexp=?`-style equality  | over `data`, generically                                                                                                                                                       |
| messages between nodes (N1)        | a message type must be `data` plus addresses; a type fingerprint of a `data` type is structural, so two programs agree on it without sharing definitions                       |
| generative types in messages       | only by opting in, with a validator run on receipt: the receiver's `up`                                                                                                        |

### Precedents (from memory)

| system                     | the distinction                                                                            | lesson                                                                                                       |
| -------------------------- | ------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------ |
| SML equality types `''a`   | a kind-like class of types admitting `=`; abstract types excluded unless declared `eqtype` | closest in shape; its friction came from propagating eqtype-ness through functors, which FX-26 does not have |
| Haskell `Typeable`, `Data` | type classes, derived per type; abstract types can hand-write instances                    | opt-in per type works; generic traversal falls out of `Data`                                                 |
| OCaml `Marshal`            | untyped; happily unmarshals into an abstract type or a closure                             | what not to do: it forges `up`                                                                               |
| Rust `Serialize`           | a trait, derived, opt-in per nominal type                                                  | nominal types serialize only through code their author wrote                                                 |
| Java `Serializable`        | a marker interface; deserialization bypasses constructors                                  | the gadget-chain attacks are the cost of letting deserialization skip validation                             |
| Modula-3 pickles           | generic, by run-time type information, with type fingerprints across programs              | structural fingerprints for cross-program identity                                                           |

**Verdict:** the split is sound and cheap, and it matches work already
planned: H1's transmissible check, CF0's `acyclic`, `confirm`, and
messages. Introduce `data` when its first consumer (a polymorphic
`confirm`, `acyclic` or `send`) is built. Let the checker decide
`data`-ness of concrete types, so that only binders say `(t data)`.
That avoids most of SML's friction.

## 4. Cost and disruption

### Stages

| stage | size | what                                                                                                                                                                                                                                     |
| ----- | ---- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| G1    | M    | `define-generative` read-time expansion (`top.rs`, `parser.fx`); `Ty::Named`/`ty-named` and the generative table in both checkers; variance from `rep`; comparison, unification, printing; conversions checked with the name transparent |
| G2    | S    | safety analyses see through names: `regions_in`, `no_knot`, `writes_in`, `cyclic`, grounding; size-change tracks through `up`/`down`                                                                                                     |
| G3    | S    | generative `define-datatype`; tests with non-regular representations (`nest`, a GADT-shaped `exp` with no refinement yet)                                                                                                                |
| G4    | S    | hiding: conversions made program-private, reusing `private-regions`' mechanism                                                                                                                                                           |
| G5    | M    | the `data` kind, `(t data)` binders, the `data`-ness check shared with H1, used by the first consumer                                                                                                                                    |

Tests at each stage go in a new `tests/programs/generative/`, which both
checkers compare on.

### What could be disrupted, and how to avoid it

- **`read`, `datum`, the reader and parser**: untouched. `datum` stays
  structural and `data`; nothing generative enters them.
- **Lowering, evaluator, compilers, machines**: untouched, if the
  conversions are identity lambdas made by expansion. The only risk is a
  call's cost where a conversion is not inlined; measure before adding a
  dedicated node.
- **Masking and regions**: safe only if every safety analysis looks
  through names (G2). This is the one place a mistake would be unsound,
  so G2 needs its own tests: a region reached only through an abstract
  value must not be masked, and a knot through an abstract type in the
  store must be caught.
- **Existing structural types**: unaffected. A name is a new leaf, and no
  existing rule unfolds it.
- **Heap images**: types are erased, so nothing is stored. Only N1's type
  fingerprints must include a generative type's identity if one is ever
  sent; G5 keeps them out unless opted in.

## 5. Relation to non-regular families and GADTs

A parallel effort is prototyping structural, equi-recursive non-regular
families with a budget and lemmas, against nominal, iso-recursive
families. Generativity bears on that question in two separate ways.

- **Representing recursion: generativity helps, but is more than
  needed.** A generative name is never unfolded to compare, so a
  generative representation may be non-regular. That gives the
  iso-recursive route with no decision procedure at all. What the
  non-regular question needs is iso-recursion; generativity supplies it
  as a side effect.
- **Abstraction: orthogonal.** Hiding a representation is about who may
  convert, not about how recursion is represented. A structural,
  budgeted route to non-regular families would leave generativity just as
  useful for abstraction.
- **GADTs need more than either.** Index refinement in `tagcase` arms,
  existentials in variants, and the variance rules of Scherer and Rémy
  (`papers/scherer-remy-esop13-gadts-meet-subtyping.pdf`) are separate
  work. Generativity makes their home simple: a generative datatype whose
  constructors state their result indices, since a name is compared only
  by its arguments.

## Recommendation

1. **Add generativity as its own form** (G1, G2): `(define-generative
   (name (param kind) …) rep)`, with `up-name` and `down-name`, the
   identity at run time. It is static, per definition, top-level only,
   with no modules. It is easy to explain ("a new type, with two ways in
   and out"), and it touches only the checkers and the read-time
   expanders. The rule to hold to is **opaque to comparison, transparent
   to safety**: never hide a region or a knot behind a name.
2. **Then generative datatypes and hiding** (G3, G4), hiding through the
   `private-regions` mechanism rather than a module system.
3. **Adopt the `data` kind** (G5) when its first consumer is built, as one
   definition shared with H1's transmissible check. Generative types stay
   out of `data` unless they supply a validator, because deserializing is
   `up`.
4. **Keep `define-datatype` transparent by default**, so nothing already
   built changes, and let the non-regular-family prototype decide how
   much structural machinery GADTs need. Generative datatypes are the
   fallback that works in any case.
