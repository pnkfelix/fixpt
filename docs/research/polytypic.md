# Polytypic programming: one definition, driven by the data's type

Research note, 2026-09-29. Nothing here is built. The question: can one
definition whose computation follows the structure of a type (equality,
hashing, printing, `map`, `fold`, copying) replace the boilerplate the
benchmark ports and the front end write by hand, and how would it fit
FX-26's regions, effects, termination checking, two checkers and two
compilers?

Sources are listed at the end with URLs and versions. Every one marked
*read* was fetched or opened for this note (2026-09-29). Those marked
*abstract* were checked only for their bibliographic details and
abstract, and their content is given from memory. FX-26 facts are from
the repository at commit `eaab38f`. The toy examples of §2.5 were added
later the same day and checked at commit `e623b23`.

## 0. At a glance

- **Recommendation: deriving.** A top-level form, `derive`, makes the
  checker generate ordinary FX-26 definitions for a datatype (equality,
  `->datum`, then hash and compare), which are then checked like any
  other definitions. Compare OCaml's ppx, Rust's `derive` and FX-91's own
  `define-datatype`. The kernel, K26 and the compilers stay as they are.
  A bug in the deriver gives a type error or a wrong answer, never an
  unsound program.
- **The generated code is one local `letrec` group, with one member per
  type node.** Three hand-written samples of what the deriver would emit
  check today (§4). An equality over a rose tree at `acyclic` checks as
  `pure`. The same shape over `(listof term @heap)` is correctly made to
  say `spin`. A family derived at `(acyclic p)` for any place `p` checks
  with only `(read (acyclic p))` and the element function's effect.
- **Not recommended now: type representations as values** (a `Rep` GADT,
  or `typerep` passed at `proj`), **nor a polytypic definition form**
  checked once over all types. The first needs GADTs (N4), rows of labels
  and effects computed from types, and it passes at run time what the
  types already prove. The second needs a typing rule for type-case and
  an elaboration that both checkers and both compilers must repeat
  exactly. Both would also lose termination proofs that deriving gets for
  free.
- **Toy examples, side by side (§2.5).** Each idea gets a snippet in
  its source language and one in FX-26. Eight FX-26 programs, in
  `docs/research/examples/polytypic/`, check and run today. Most pass
  dictionaries: an argument per type parameter, type classes as
  products, and a representation that *is* a dictionary of generic
  operations (C). A `Rep` GADT and `(derived …)` at the use are shown
  as proposed syntax.
- **The user's preference for dictionaries or tags over per-type copies**
  (§5, last paragraph) keeps the recommendation, with one reading made
  explicit. `derive` copies per *declaration*, never per type argument: a
  family's derived function takes its parameters' operations as
  dictionaries. Where one function is wanted for many types, a library
  of representation dictionaries (§2.5 C) works today with no language
  change. It costs `spin`, `(read @globals)` and allocation.
- **Found on the way** (§7, Q10): `acyclic?` is typed `pure` over any
  `(t data)`, so a closure that calls it on data frozen into an arena
  escapes the arena. Both checkers accept this. A run-time generic over
  `data` would inherit the same gap.

## 1. The boilerplate

By name, the 87 port files (`scheme-bench/`, `mllang-bench/fx/`) have
48 top-level definitions of equality, `->datum`, hashing or copying.
Equality and `->datum` alone appear in 22 of those files. Examples: `term=?` (twice), `obj-equal?`,
`obj->datum`, `sx->datum`, `mat->datum`, `syms=?`, `tree-copy`,
`list-copy` and `bool=?` (twice). The front end has about fifteen more:
`k-eff=?`, `k-size=?`, `k-syms=?`, `c-int=?`, `syn->datum` and others.

Roughly half are the structural function a deriver would produce. The
rest mean something else: equality of sets, Larceny's budgeted
`equal-hash`, copying a graph with its sharing, `destruc`'s custom
printing. Those stay hand-written.

The structural ones share one shape: a `tagcase` per sum, a field at a
time, a loop per list. Each has a hand-worked effect (`(maxeff (read
@heap) spin)` in `kb.fx`) that follows from the data's regions. Some
entries are not polytypic at all: `list->array`, `array->list` and
`bool=?` are missing polymorphic library functions (§6.5, stage P0).

## 2. Survey

### 2.1 Three ways to index a function by a type

| approach                                          | where the type is inspected                            | cost at run time                                              | systems                                                                                                              |
| ------------------------------------------------- | ------------------------------------------------------ | ------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------- |
| type classes, generic defaults                    | instance resolution, at compile time                   | a dictionary per call, unless inlined and specialized         | GHC.Generics, DeriveAnyClass, DerivingVia; Clean `generic`; Scala 3 `derives` with `Mirror`                          |
| type representations as values                    | a `Rep t` value, at run time                           | the representation is interpreted, unless partially evaluated | Cheney–Hinze LIGD, Generics for the Masses, SYB (`Data`, `Typeable`), MLton's `Generic`, Harper–Morrisett `typerec`  |
| code generated from the declaration               | the declaration, at compile time                       | none beyond hand-written code                                 | PolyP and Generic Haskell (by specialization), Template Haskell, ppx_deriving, Jane Street ppx, Rust `derive`, serde |
| universe (codes as data, in a dependent language) | codes, by ordinary evaluation, with types checked once | as the representation approach, unless erased or normalized   | Altenkirch–McBride, levitation (Epigram), Agda and Idris libraries; Idris elaborator reflection for deriving         |

### 2.2 The systems, briefly

- **PolyP** (Jeuring and Jansson, AFP 1996; Jansson and Jeuring, POPL
  1997) handles regular datatypes of one parameter, seen as fixed points
  of functors. A polytypic function is defined by cases on the functor's
  structure. The compiler specializes it to each type used, so the output
  is ordinary Haskell (*read*: the PolyP page).
- **Generic Haskell and polykinded types** (Hinze, POPL 2000 and MPC 2000;
  Hinze and Jeuring 2003). A generic value's *type* is indexed by the
  kind of its argument. For equality, `Eq⟨*⟩ t = t → t → Bool` and
  `Eq⟨κ→ν⟩ t = ∀a. Eq⟨κ⟩ a → Eq⟨ν⟩ (t a)`, so at `List` equality takes
  the elements' equality (*abstract*; the formula from memory). It is
  implemented by specialization, like PolyP. Altenkirch and McBride note
  that "typechecking at this level is not yet realized" (p. 7): Generic
  Haskell checks the specialized output, not the generic definition.
- **Type representations as values.** Cheney and Hinze (Haskell 2002)
  define a `data Rep τ` of type codes with embedding–projection pairs
  (*read*, pp. 2–3). Hinze's "Generics for the masses" (ICFP 2004) uses a
  type class `Generic g` whose methods are the cases, making a
  representation a class-polymorphic value (*read*, p. 3). SYB (Lämmel and
  Peyton Jones, TLDI 2003) walks any `Data` value with `gmapT`, and uses
  `Typeable` casts to pick the cases a traversal changes (*read*: the MSR
  page).
- **GHC.Generics** (Magalhães, Dijkstra, Jeuring and Löh, Haskell 2010).
  The compiler derives `Rep a`, built from `V1`, `U1`, `K1`, `M1`, `:+:`
  and `:*:`, and `from`/`to`. Generic defaults are written once over
  those constructors, and `DeriveAnyClass` fills in instances (*read*:
  base-4.22.0.0 docs). `DerivingVia` (GHC 8.6.1 and later) reuses an
  instance through `coerce` (*read*: GHC 9.14.1 guide). That is FX-26's
  lemma idea, erased identity coercions, used to share code.
- **Template Haskell** (Sheard and Peyton Jones, 2002) generates
  declarations at compile time. Deriving libraries use it for instances
  GHC cannot derive (*abstract*).
- **OCaml ppx.** `ppx_deriving` provides `show`, `eq`, `ord`, `enum`,
  `iter`, `map`, `fold` and `make`. "If a type is parametric, the
  generated functions accept an argument for every type variable before
  all other arguments", and for an abstract type a plugin "expect[s] to
  find the functions it would derive itself" in its module (*read*).
  Jane Street's `ppx_compare` is "usually much faster" than polymorphic
  compare, with `[@compare.ignore]`. `ppx_sexp_conv` gives `<fun>` for
  functions and `[@sexp.opaque]` for what may not be looked into.
  `ppx_hash` derives `hash_fold_t : Hash.state -> t -> Hash.state`,
  "follow[ing] the structure of the type; allowing user overrides at every
  level", in contrast to `Hashtbl.hash` (*read*: the three READMEs).
- **SML** has only equality types (`''a`) built in. MLton's
  `TypeIndexedValues` page and Vesa Karvonen's `Generic` library in
  mltonlib build type representations from combinators (`*`, `+`, `Y`
  for recursion, `iso` for user types). With them come `Eq`, `Ord`,
  `Hash`, `Pretty`, `Pickle`, `Read`, `Reduce` and `Transform`, all
  passed at run time (*read*: the page and the library's README).
- **Clean** has `generic` declarations over `UNIT`, `PAIR`, `EITHER`,
  `OBJECT`, `CONS`, `FIELD` and `RECORD`, with `derive` (report 3.0,
  ch. 7). §7.6 is "Generic Functions and Uniqueness Typing", the nearest
  precedent to carrying FX-26's effects through a generic's type (*read*:
  section structure only; the contents of §7.6 not seen).
- **Rust `derive`** runs a macro on a struct or enum. The generated impl
  bounds each type parameter by the same trait (`impl<T: Clone> Clone
  for Foo<T>`), and monomorphization then specializes it (*read*: the
  Reference). **serde** splits the work in two. `Serialize` maps a type
  into a fixed 29-type data model, "by invoking exactly one of the
  Serializer methods"; a `Serializer` maps the model to a format
  (*read*). That model plays the role FX-26's `datum` plays.
- **Scala 3.** `derives` asks the compiler for a `Mirror`, which carries
  product and sum structure "using types rather than terms", so it "ha[s]
  no runtime footprint unless used". Instance authors are told to summon
  instances for the cases, not to call `derived` recursively (*read*).
- **Dependent types.** Altenkirch and McBride (WCGP 2002) build a
  universe: a type `U` of codes, a decoding `El : U → Type`, and generic
  functions by recursion on codes. They observe that "the more
  specialized the set of codes, the larger the library of useful generic
  operations" (p. 6), and that the approach "should not introduce any
  overhead at runtime" (p. 19) (*read*). Levitation (Chapman, Dagand,
  McBride and Morris, ICFP 2010) makes every datatype a description
  interpreted in a universe that describes itself (*abstract*). Idris's
  elaborator reflection (Christiansen and Brady, ICFP 2016) lets deriving
  be written in Idris itself (*abstract*).
- **F# type providers** generate types, not functions, at compile time
  from an external schema (*read*). They matter here only as another
  instance of code made by the compiler from a description.
- **Intensional type analysis.** Harper and Morrisett (POPL 1995) pass
  types at run time and dispatch on them with `typerec`. Crary, Weirich
  and Morrisett (ICFP 1998) keep that power under type erasure by passing
  term-level representations whose types are indexed by the types they
  stand for (*abstract*). This is the typed foundation of the
  representation approach.
- **Staging.** Yallop (ICFP 2017) stages SYB in MetaOCaml. Code is
  generated per type at the call site, "20-30× faster than the unstaged
  version", and it "equals or outperforms handwritten code" (*read*,
  pp. 29:3, 29:11). Deriving is the same move, with the type known at
  the declaration.

### 2.3 What the costs are, measured

Magalhães, Holdermans, Jeuring and Löh (PEPM 2010) benchmarked the
Haskell generic libraries. SYB ran "10–15 times worse than hand-written"
at `-O1`, and 7–12 times with aggressive inlining. EMGM (a
representation-as-class library) came to about 1× only when inlining was
forced. Their conclusion: generic code *can* reach hand-written speed,
through inlining and specialization (*read*, pp. 6, 10). Yallop's figures
are those above. Generic code is fast only where the compiler turns it
into what deriving writes directly.

### 2.4 Lessons for FX-26

1. Whatever the surface, the fast systems end in per-type code:
   specialization in PolyP and Generic Haskell, monomorphization in Rust,
   expansion in ppx, inlining in GHC, staging in MetaOCaml.
2. Nominal and abstract types get their instance from their author (ppx,
   Rust, Haskell). FX-26's generative types follow the same rule (§3.2).
3. Functions and mutable state need a policy: `<fun>`, `opaque`,
   `ignore`, or refusal.
4. Parameters become arguments, one per *type* parameter (ppx, Rust,
   Hinze's polykinded types). FX-26's other kinds need none (§3.3).
5. A smaller universe gives more useful generics (Altenkirch and McBride).
   FX-26 already has a smaller universe: the `data` kind.

### 2.5 The ideas in toy code

Each idea below comes as a paper-sized example: the source language's
snippet, then FX-26's. One running type serves them all, a binary tree
of ints:

```
data Tree = Leaf Int | Node Tree Tree             -- Haskell
(define-datatype tree (leaf int) (node tree tree))  ; FX-26
```

In FX-26, `tree` is `(sumof (leaf (productof (1 int))) (node (productof
(1 tree) (2 tree))))`: `define-datatype` numbers a variant's fields from 1
(`top.rs`, `expand_datatype`).

**Today or proposed.** Every FX-26 snippet not marked *proposed* is an
excerpt of a whole program under `docs/research/examples/polytypic/`. Each
program was checked with `fixpt check` (both checkers agreed on every one)
and run with `fixpt eval`, at commit `e623b23`. The results are given
beside the snippets. Snippets marked *proposed* are syntax that does not
exist.

| file                    | idea                                                          | checked, ran | effect of the generic operation                        |
| ----------------------- | ------------------------------------------------------------- | ------------ | ------------------------------------------------------ |
| `eq-dict.fx`            | an argument per type parameter (Generic Haskell, ppx)         | yes          | `e`, the element function's                            |
| `dict-of-derived.fx`    | type classes as explicit dictionaries                         | yes          | `e`, the dictionary's                                  |
| `rep-dict.fx`           | a representation that is a dictionary (GM, MLton `Generic`)   | yes          | `(maxeff spin (read @globals))`                        |
| `sop-view.fx`           | one sum-of-products value type (GHC.Generics' view, untyped)  | yes          | `pure`, plus reads of `gv`'s constructors              |
| `datum-model.fx`        | serde's split, with `datum` as the model                      | yes          | `pure`                                                 |
| `cata-algebra.fx`       | PolyP's `cata`, with the functor fixed                        | yes          | `e`, the algebra's                                     |
| `derived-copy.fx`       | what `derive` would write: a copy per datatype                | yes          | `pure` (a family: `e`)                                 |
| `derived-groups.fx`     | §4's local group: `acyclic` descends, `@heap` must say `spin` | yes          | `pure`; `(maxeff (read @heap) spin)`                   |
| a `Rep` GADT            | Cheney–Hinze's type representation, typed                     | proposed     | would be `spin` (polymorphic recursion)                |
| `(derived eqd T)`       | instance resolution at the use                                | proposed     | as the derived function's                              |

The user prefers, for FX-26 now, systems that pass dictionaries or tags
over ones that copy code per type. So the examples lead with those, and
deriving comes last, as the contrast.

#### A. An argument per type parameter (Generic Haskell, ppx_deriving)

Generic Haskell gives a generic function's case for a type constructor
the functions for its arguments. This is Hinze's classic style, from
memory:

```haskell
eq {| Int |}              = (==)
eq {| :*: |} eqA eqB (a1 :*: b1) (a2 :*: b2) = eqA a1 a2 && eqB b1 b2
eq {| :+: |} eqA eqB (Inl a1) (Inl a2)       = eqA a1 a2
eq {| :+: |} eqA eqB (Inr b1) (Inr b2)       = eqB b1 b2
eq {| :+: |} _   _   _        _              = False
```

ppx_deriving follows the same rule for a parametric type: "the generated
functions accept an argument for every type variable before all other
arguments". Its README shows `[@@deriving map]` on `'a btree` giving `val
map_btree : ('a -> 'b) -> 'a btree -> 'b btree`. By that rule, `eq`
gives `equal_btree : ('a -> 'a -> bool) -> 'a btree -> 'a btree -> bool`.

FX-26 today (`eq-dict.fx`). One `list=?` serves every element type. It
is effect-polymorphic, and it checks without `spin` because its loop is
a local group:

```
(define list=?
  (poly ((t type) (e effect))
    (subr e ((subr e (t t) bool) (listof t acyclic) (listof t acyclic)) bool))
  (lambda (eq xs ys)
    (letrec ((go (subr e ((listof t acyclic) (listof t acyclic)) bool)
               (lambda (xs ys)
                 (cond ((null? xs) (null? ys))
                       ((null? ys) #f)
                       (else (and (eq (car xs) (car ys)) (go (cdr xs) (cdr ys))))))))
      (go xs ys))))
(list=? (lambda (a b) (list=? int=? a b)) lists lists)     ; #t, at (listof (listof int))
```

This is §3.3's typing rule in miniature: a `type` parameter adds an
argument, and one `e` covers it.

#### B. Type classes as explicit dictionaries

In Haskell a constraint is a dictionary the compiler passes. An instance
for a type constructor is a function from dictionaries to a dictionary:

```haskell
class Eq a where (==) :: a -> a -> Bool
instance Eq a => Eq [a] where ...
member :: Eq a => a -> [a] -> Bool
member x = any (== x)
```

FX-26 today (`dict-of-derived.fx`). The dictionary is a product, and
`list-d` is the instance `Eq a => Eq [a]`:

```
(define-type (eqd (t type) (e effect))
  (productof (eq (subr e (t t) bool)) (show (subr e (t) datum))))
(define list-d
  (poly ((t type) (e effect)) (subr pure ((eqd t e)) (eqd (listof t acyclic) e)))
  …)                                         ; eq and show, each a local loop
(define member
  (poly ((t type) (e effect)) (subr e ((eqd t e) t (listof t acyclic)) bool))
  …)
(member (list-d int-d) (list 2 3) xss)                     ; #t
((extract (list-d (list-d int-d)) show) xss)               ; ((1) (2 3))
```

Everything here is `pure` at `int`, and polymorphic in `e`. A datatype's
instance would be its derived functions,
`(product (eq tree=?) (show tree->datum))`. That combines the two: code
per *declaration*, and dictionaries passed at every *use*. The
dictionary is the one value FX-91's modules made first-class (§6.6).

#### C. A representation that is a dictionary ("Generics for the masses", MLton)

Cheney and Hinze's representation is a type-indexed value, `Rep τ`, and
a generic function interprets it (HW02, p. 2):

```
RInt :: Rep Int
R+   :: ∀α . Rep α → (∀β . Rep β → Rep (α + β))
R×   :: ∀α . Rep α → (∀β . Rep β → Rep (α × β))
rEqual (R× rα rβ) t1 t2 = case (t1, t2) of
                            (a1 :×: b1, a2 :×: b2) → rEqual rα a1 a2 ∧ rEqual rβ b1 b2
```

"Generics for the masses" turns this around: a representation *is* the
generic functions, one class method per type case (ICFP04, p. 3):

```haskell
class Generic g where
  unit     :: g Unit
  plus     :: (Rep α, Rep β) ⇒ g (Plus α β)
  pair     :: (Rep α, Rep β) ⇒ g (Pair α β)
  datatype :: (Rep α) ⇒ Iso α β → g β
  int      :: g Int
```

MLton's `TypeIndexedValues` page builds the same thing from combinators:
`inj (fn NONE => INL () | SOME v => INR v) (data (C0"NONE" + C1"SOME" t))`.

FX-26 today (`rep-dict.fx`). A representation is a product of the
generic operations. `rep-pair` and `rep-sum` are written once, for every
product and every sum:

```
(define-type (rep (t type))
  (productof (eq (subr walk (t t) bool)) (show (subr walk (t) datum)) (size (subr walk (t) int))))
(define rep-sum
  (poly ((a type) (b type)) (subr pure ((rep a) (rep b)) (rep (sumof (inl a) (inr b)))))
  (lambda (ra rb)
    (product
     (eq (lambda (x y)
           (tagcase x
             (inl u (tagcase y (inl v ((extract ra eq) u v)) (inr v #f)))
             (inr u (tagcase y (inl v #f) (inr v ((extract rb eq) u v)))))))
     (show …) (size …))))
```

A user type enters through its `from` (Hinze's `Iso`, MLton's `inj`),
`rep-con` names a constructor (MLton's `C1`), and `rep-delay` ties the
recursion (MLton's `Y`):

```
(define tree-view
  (subr pure (tree) (sumof (inl int) (inr (productof (1 tree) (2 tree)))))
  (lambda (t) (tagcase t (leaf (n) (sum inl n))
                         (node (l r) (sum inr (product (1 l) (2 r)))))))
(define rep-tree (subr walk () (rep tree))
  (lambda ()
    (rep-iso tree-view
             (rep-sum (rep-con 'leaf rep-int)
                      (rep-con 'node (rep-pair (rep-delay rep-tree) (rep-delay rep-tree)))))))
((extract (rep-tree) show) t1)       ; (node ((leaf 1) (node ((leaf 2) (leaf 3)))))
((extract (rep-tree) size) t1)       ; 3
((extract (rep-pair rep-int (rep-sum rep-int rep-int)) show)
 (product (1 7) (2 (sum inr 8))))    ; (7 8): a type with no declaration at all
```

What it shows, and what it costs:

- **It needs no new feature.** The existentials of Cheney–Hinze's `R×`
  (the `∀α β` of its components) are not needed: each component's type
  is hidden inside the closures of the product, as it is in "Generics for
  the masses". Their Haskell 98 encoding (`R× (Rep α) (Rep β) (τ ↔ (α ×
  β))`) *would* need existentials, which FX-26 lacks (N4).
- **Its effect is `walk`, `(maxeff spin (read @globals))`.** The knot
  runs through a closure: `rep-delay` calls `rep-tree`, a global. So
  termination and purity are lost, as §5's row (b) says. The derived
  `tree=?` in G below is `pure`.
- **Every step allocates.** `tree-view` builds a sum and a product per
  node, as Hinze's `fromData` does, and each `rep-delay` call rebuilds
  `rep-tree`. An I-cell could build it once.
- **The set of generic functions is closed.** `rep` lists `eq`, `show`
  and `size`, so adding `hash` changes every combinator. Hinze's `class
  Generic g` abstracts over `g`, the generic function's type
  constructor. FX-26 has no kind `type → type` (`gadts.md`) to do that.

#### D. One value type for all: a sum-of-products view as data (GHC.Generics, SYB)

GHC.Generics gives each type a `Rep` built from `U1`, `K1`, `M1`, `:+:`
and `:*:`. A generic function is a class over those (base-4.22.0.0's own
example):

```haskell
data Tree a = Leaf a | Node (Tree a) (Tree a) deriving Generic
class Encode' f where encode' :: f p -> [Bool]
instance (Encode' f, Encode' g) => Encode' (f :+: g) where
  encode' (L1 x) = False : encode' x
  encode' (R1 x) = True  : encode' x
instance (Encode' f, Encode' g) => Encode' (f :*: g) where
  encode' (x :*: y) = encode' x ++ encode' y
```

In FX-26 the view cannot be a *type* computed from `tree`, since there
are no type-level functions. It can be one *value* type, `gv`, for every
type. That is untyped, as SYB's traversals effectively are
(`sop-view.fx`):

```
(define-datatype gv (g-unit) (g-int int) (g-con symbol gv) (g-inl gv) (g-inr gv) (g-pair gv gv))
(define gsize (subr pure (gv) int)            ; written once, for every type
  (letrec ((gsize (subr pure (gv) int)
             (lambda (x)
               (tagcase x
                 (g-unit () 0) (g-int (n) 1) (g-con (c u) (gsize u))
                 (g-inl (u) (gsize u)) (g-inr (u) (gsize u))
                 (g-pair (u v) (+ (gsize u) (gsize v)))))))
    gsize))
(define tree->gv (subr mk-gv (tree) gv)       ; per type: what `deriving Generic` writes
  (letrec ((from (subr mk-gv (tree) gv)
             (lambda (t)
               (tagcase t
                 (leaf (n) (g-inl (g-con 'leaf (g-int n))))
                 (node (l r) (g-inr (g-con 'node (g-pair (from l) (from r)))))))))
    from))
```

`gv` is immutable, so every walk of it descends, and `geq` and `gsize`
are `pure`, unlike C. The same file has SYB's `everywhere (mkT f)`,
`gmap-int`, which applies `f` at every int whatever the type:

```haskell
everywhere (mkT ((+1) :: Int -> Int)) tree          -- SYB, from memory
```

```
(geq (gmap-int (lambda (n) (* n 10)) (tree->gv t1))
     (tree->gv (node (leaf 10) (node (leaf 20) (leaf 30)))))     ; #t
```

What it costs: `from` allocates a copy of the value. `to`, `gv->tree`,
is partial, since a `gv` does not say which type it came from, so it
must invent an answer for a `gv` that is not a tree's view. GHC's `to`
is total because `Rep Tree` is a type.

#### E. serde's split, with `datum` as the data model

serde's `Serialize` maps each type into a fixed data model, and each
format consumes the model. In FX-26, `datum` is the model. Each type
writes only its `->datum`, and consumers are written once over `datum`.
The consumers here are a `datum=?`, missing today (P0), and a count of
ints (`datum-model.fx`):

```
(define datum=? (subr pure (datum datum) bool)
  (letrec ((eq (subr pure (datum datum) bool)
             (lambda (x y)
               (cond ((pair? x)
                      (and (pair? y)
                           (eq (car x) (car y))
                           (eq (cdr x) (cdr y))))
                     ((datum-int? x)
                      (and (datum-int? y) (= x y)))
                     …))))
    eq))
(datum=? (tree->datum t1) (tree->datum (node (leaf 1) (node (leaf 2) (leaf 4)))))   ; #f
```

This is D with `datum` for `gv`. It is `pure`, it needs no new type, and
it loses the same things: a copy per call, and no way back without a
check. It is also what option (d) of §5 would do with a primitive, but
written in FX-26 and reaching only data that has a `->datum`.

#### F. PolyP: a function over a functor, and why FX-26 fixes the functor

PolyP writes one `cata` for every regular datatype, by the datatype's
pattern functor (`FunctorOf d`). From memory, after Jansson and Jeuring:

```haskell
cata :: Regular d => (FunctorOf d a b -> b) -> d a -> b
cata h = h . fmap2 id (cata h) . out
```

FX-26 cannot abstract over the functor, since it has no kind `type →
type`. What it can do is one fold per type, taking the algebra as a
dictionary, a product with one function per constructor
(`cata-algebra.fx`):

```
(define-type (tree-alg (b type) (e effect))
  (productof (leaf (subr e (int) b)) (node (subr e (b b) b))))
(define tree-cata (poly ((b type) (e effect)) (subr e ((tree-alg b e) tree) b)) …)
(define depth-alg (tree-alg int pure)
  (product (leaf (lambda (n) 0)) (node (lambda (x y) (+ 1 (if (< x y) y x))))))
(tree-cata depth-alg t1)                                      ; 2
```

`tree-cata` is what a deriver would write per type (P5's `fold`). Each
algebra is then a generic-looking function with no recursion of its own.
Its effect is the algebra's `e`, and `pure` here.

#### G. The contrast: what `derive` would write, a copy per datatype

ppx and Rust expand `[@@deriving eq]` / `#[derive(PartialEq)]` into the
per-type function. The proposed `(derive tree equal ->datum)` would write
this (`derived-copy.fx`, by hand):

```
(define tree=? (subr pure (tree tree) bool)
  (letrec ((eq (subr pure (tree tree) bool)
             (lambda (x y)
               (tagcase x
                 (leaf (n) (tagcase y (leaf (m) (= n m)) (else _ #f)))
                 (node (l r) (tagcase y (node (l2 r2) (and (eq l l2) (eq r r2))) (else _ #f)))))))
    eq))
```

It needs no view, no conversion and no dictionary, and it is `pure`. The
copy is per *declaration*, not per use. A family, `(ptree t)`, gets one
`ptree=?` that takes the element's equality as an argument, as in A. So
deriving is not the specialization the user wants to avoid: nothing is
copied per type argument. `derived-groups.fx` is §4's rose tree. At
`acyclic` the two-member group is `pure`. At `@heap` it must say
`(maxeff (read @heap) spin)`. Without `spin` both checkers refuse it: "a
part of a list that may be written is no smaller: it may be cyclic".

#### H. Proposed: a `Rep` GADT, tags passed at run time

The typed version of C passes a *tag* and dispatches on it. In Haskell
(with GADTs) that is:

```haskell
data Rep t where
  RInt  :: Rep Int
  RPair :: Rep a -> Rep b -> Rep (a, b)
geq :: Rep t -> t -> t -> Bool
geq RInt         x       y       = x == y
geq (RPair ra rb) (a1, b1) (a2, b2) = geq ra a1 a2 && geq rb b1 b2
```

*Proposed* FX-26, after N4 (constructor result types, existentials and
refinement in `tagcase`). None of this syntax exists:

```
(define-datatype (rep (t type))                          ; proposed
  (r-int                       : (rep int))
  (r-pair (rep a) (rep b)      : (rep (productof (1 a) (2 b)))))   ; a, b existential
(define geq (poly ((t type)) (subr spin ((rep t) t t) bool))   ; proposed
  (lambda (r x y)
    (tagcase r
      (r-int () (= x y))                                 ; here t = int
      (r-pair (ra rb) (and (geq ra (extract x 1) (extract y 1))
                           (geq rb (extract x 2) (extract y 2)))))))
```

Next to C, this needs three things more: existentials, refinement, and
polymorphic recursion (`geq` at `a` and `b` inside `geq` at `t`). It
says `spin` for the same reason C does: a recursive type's `rep` is
cyclic. What it would gain over C is an open set of generic functions,
since the representation is data, not a fixed product of operations. So
C is what FX-26 can do now, and H is what N4 would add.

#### I. Proposed: the dictionary found by type, `(derived …)`

Haskell finds `member`'s dictionary from the type at the call. *Proposed*
(§3.3's last row, P6), in FX-26:

```haskell
member t ts                                  -- Eq Tree found by instance resolution
```

```
(member (product (eq tree=?) (show tree->datum)) t ts)    ; today: written out
(member (derived eqd tree) t ts)                          ; proposed: the checker builds it
```

Both checkers would have to elaborate `(derived …)` to the same text. It
is a convenience, and B already works without it.

## 3. Structure in FX-26

### 3.1 What each type former contributes

A derived function walks the type's graph after abbreviations are
unfolded; a `define-datatype` is such an abbreviation. In the table,
*reads* is the read effect the walk adds, and *descent* says whether
recursing through the former is a descent that size-change accepts
(§4).

| former                                                   | `equal`, `hash`, `compare`             | `->datum`                        | reads                                    | descent                                                    |
| -------------------------------------------------------- | -------------------------------------- | -------------------------------- | ---------------------------------------- | ---------------------------------------------------------- |
| `int`, `nat`, `char`, `bool`, `string`, `symbol`, `unit` | a base operation (§6.5 lists the gaps) | itself (a datum's member)        | none                                     | n/a                                                        |
| `datum`                                                  | `datum=?` (missing)                    | itself                           | none                                     | `car`/`cdr` are parts                                      |
| `(productof (l T) …)`                                    | field by field, in label order         | a list of `(l v)` (Q4)           | none (immutable)                         | yes: `extract`                                             |
| `(sumof (tag T) …)`                                      | tags first, then the value             | `(tag v …)`                      | none (immutable)                         | yes: `tagcase`                                             |
| `(listof T acyclic)`, `(nlist T s)`                      | element-wise                           | a list                           | none                                     | yes                                                        |
| `(listof T (acyclic p))`, `(const p)`                    | element-wise                           | a list                           | `(read (acyclic p))`, `(read (const p))` | acyclic yes, const no                                      |
| `(listof T r)`, `r` writable                             | element-wise                           | a list                           | `(read r)`                               | no: may be cyclic, `spin`                                  |
| `(arrayof T r)`                                          | length, then by index                  | a vector                         | `(read r)`                               | the index loop ends; recursion through an element does not |
| `(ref T r)`, mutable bloblet field                       | contents (Q2: FX-26 has no `eq?`)      | contents                         | `(read r)`                               | no                                                         |
| frozen bloblet                                           | field by field                         | a vector                         | as its region                            | as a frozen pair                                           |
| generative `(N d …)`                                     | the owner's function, by name (§3.2)   | the owner's                      | that function's latent effect            | as the owner's                                             |
| `subr`, `composable`                                     | refused                                | `#<procedure>` (as `obj->datum`) | none                                     | n/a                                                        |
| `icell`, `prompt-tag`, `mark-key`, `place`               | refused                                | refused                          |                                          |                                                            |
| a type parameter `t`                                     | the function passed for `t`            | the function passed              | its effect `e`                           | not recursed into                                          |

Two subtleties from subtyping:
- **Sums have width subtyping.** A function derived at a wide sum accepts
  a narrower one, since parameters are contravariant, so that part just
  works. But a tag's *index* differs between two sum types, while its
  *name* does not. Hash and compare should use the tag's name
  (`symbol-name-hash` of a literal, which folds to a constant), so that
  two derived functions agree on a value whichever sum type they were
  derived at, and so do two programs (Q3).
- **Products have no width subtyping** (`soundness.md` §2.3: "same labels
  in order"). So equality field by field cannot miss a hidden field. With
  width on products, a run-time structural equality would compare fields
  the static type hides.

### 3.2 Generative types: opaque, unless you are the owner

The rule of `generative-types.md` is "opaque to comparison, transparent
to safety". A derived structural function *is* a comparison, so:

- **Outside, a generative name is a leaf.** The deriver calls the
  owner's function (`name=?`, and so on), which must be defined earlier,
  since a definition sees only those before it. If it is missing, the
  error says which one to write or derive. A set kept as a list must not
  be compared as a list.
- **At the owner's site,** `derive` of the generative type itself walks
  `rep` through `down-name`, which size-change already treats as the
  identity. So the derived function descends. Once hiding (G4) exists,
  deriving is allowed only where `down-name` is visible.
- **Safety stays transparent.** The effect of a call of the owner's
  function is its declared latent effect, already checked, so no region
  is hidden.
- **`datum->T`, the inverse of `->datum`,** is deserialization, which is
  `up`. It is derivable only for `data` types, with a generative type
  accepted only through its owner's validator (`gadts.md` decision 6).

### 3.3 Effects and regions in the types: polykinded types, specialized

Hinze's types are indexed by kinds of the form `κ → ν`. FX-26 has no such
kinds (`gadts.md`: "no kinds like `type → type`"). A family is declared
with first-order parameters and is always used applied. So the
polykinded type reduces to one rule, per parameter kind:

- a `type` (or `data`) parameter `t` adds an argument, the operation at
  `t`: `(subr e (t t) bool)` for equality;
- a `region`, `place`, `effect` or `size` parameter adds only a binder.

One effect variable `e` covers every element function, since effects in
`subr` are covariant and a caller instantiates `e` to the largest. So for
a family `(F (t type) (r region))`, derived at `(F t r)`:

```
F=? : (poly ((t type) (r region) (e effect))
        (subr (maxeff e reads spin?) ((subr e (t t) bool) (F t r) (F t r)) bool))
```

Here `reads` and `spin?` are computed from the graph as in §3.1. The
same holds for `hash` (result `int`), `compare` (result `int`) and
`->datum` (result `datum`). Making a datum allocates at `acyclic`, which
is pure to make data at (`docs/fx26.md`, "Datums": `datum` is a union
since 2026-10-08, made with `cons`), so `->datum` allocates nothing a
type sees.

`map` and `copy` produce data, so they need a result region. Each gets
another binder, `(s region)` or `(p place)`, and the effect `(alloc s)`,
with `rcons` into a place. Frozen results come from the existing rules:
`cons` may allocate straight into `acyclic`. `map` gets the element
functions `(subr e (t) u)`.

How else the types could be stated, and why not now:

| option                                     | what FX-26 would need                                                                                                                                                  | verdict                           |
| ------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------- |
| types computed per derivation (above)      | nothing new: each derived definition has an ordinary signature, which the checker verifies                                                                             | now                               |
| a kind of type descriptions, `(desc k)`    | kind-indexed descriptions (`fx-idiomatic-opportunities.md` L6), itself waiting on N4                                                                                   | later, if user derivers come (P6) |
| a `Rep` GADT indexed by types              | N4 (refinement, existentials), a generic view of labelled rows of products and sums, and an effect *computed* from `t`, such as `(rep t e)` carrying the walk's effect | not before N4, and costly after   |
| elaboration at `proj`, `(derived equal T)` | the checker picks or composes derived functions by type, like instance resolution, and both checkers must elaborate alike                                              | a later convenience (P6)          |

## 4. Termination

Deriving emits **one local `letrec` group per derived definition, with a
member per type node** reachable from the type: `term`, then `(listof
term @heap)`, and so on. It exports the group's entry as the definition's
value, as `fib` does in `fx26.md`. Two properties follow:

- **No global knot.** A top-level procedure that reaches itself through a
  global must say `spin` (`fx26.md`, "Redefinition"). A local group does
  not.
- **No higher-order inner loop.** The size-change check does not see a
  part passed through another procedure's parameter
  (`tests/programs/terminate/rose-tree.fx` is rejected though it ends).
  A flat group recurses on parts directly: a `tagcase` field, an
  `extract`, and `car`/`cdr` at an acyclic region.

Checked with `target/release/fixpt check` (both checkers, which agreed on
every one), on hand-written code of the shape the deriver would emit. The
first two are reproduced, for a rose tree of ints, in
`docs/research/examples/polytypic/derived-groups.fx` (§2.5 G). There the
refusal without `spin` also names the cause: "a part of a list that may be
written is no smaller: it may be cyclic".

| program (in `/tmp`, not in the repo)                            | result                                                                                                                                                                                              |
| --------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `rose=?` over `(sumof (leaf int) (node (listof rose acyclic)))` | `(subr pure (rose rose) bool)`: the flat group ends where `rose-tree.fx`'s nested loop could not be shown to                                                                                        |
| `term=?` over `kb.fx`'s `term`, lists at `@heap`                | accepted as `(subr (maxeff (read @heap) spin) …)`, which is `kb.fx`'s hand-written effect; declared without `spin`, refused: "a part of a list that may be written is no smaller: it may be cyclic" |
| `prose=?` for `(prose t (acyclic p))`, over any place `p`       | `(poly ((t type) (p place) (e effect)) (subr (maxeff (read (acyclic p)) e) ((subr e (t t) bool) …) bool))`; runs, `#f` as expected                                                                  |

So the deriver can *predict* `spin` rather than hope: a walk needs `spin`
exactly when some cycle in the type's graph passes through a former whose
descent column in §3.1 says no. It then declares the effect, and the
checker confirms it. Three consequences:

- **Families over a region parameter** need two derivations. The general
  one says `spin` and `(read r)`. The one at `(acyclic p)` does not. The
  `derive` form therefore takes a type *instance*, not just a name (§6.2).
- **`const` data** is certified with `acyclic` or `confirm` first, and
  then walked by the `acyclic` derivation.
- **Non-regular families** (`nest`, through a generative name) need
  polymorphic recursion within the group. Refuse them at first: "write it
  by hand".

A use of `prose=?` needed `(proj prose=? int heap pure)`, because `(pleaf
1)` says nothing about `p`. Deriving at `(acyclic heap)`, plain
`acyclic`, as well gives the common case with nothing to write.

## 5. The implementation options, weighed

Against FX-26's constraints: two checkers must agree (Rust as the oracle,
`check.fx` rule for rule); two compilers (Rust and `compile.fx`) and the
native code use static types to drop checks (`performance.md`, "Typed
primitives": `field k` where the type says the bloblet has field k, no
tag test); and the principle is to optimize from what the types already
prove.

| option                                                                                                   | checkers                                                                                                                             | compilers, native                                                                                                                                                                                                                                                               | types first?                                                                                           | termination                                                                   | soundness                                          |
| -------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------ | ----------------------------------------------------------------------------- | -------------------------------------------------- |
| **(a) deriving**: the checker generates ordinary definitions                                             | a generator in each, from resolved types to syntax; agreement testable as equal *text*, then checked by the rules both already share | nothing new: the output is ordinary code, typed primitives apply; at a monomorphic instance, base operations are direct (`=` becomes `int-...` ops)                                                                                                                             | yes: the type is used once, at generation                                                              | size-change proves it where the data is acyclic (§4)                          | nothing to trust: output is checked                |
| **(b) representations as values**: `Rep`/`typerep`, passed or inferred at `proj`, specialized when known | N4 GADTs; label rows; effects indexed by types; new rules in both                                                                    | "specialize at a known lambda" (`regcode.rs` `r_specialized`, `regcode.fx` `r-specialized`) is one level, for a small lambda argument, and never while specializing; unrolling an interpreter over a recursive representation needs a partial evaluator with memoization, twice | no: it passes at run time what the checker proved, and removes it again only if the optimizer succeeds | recursion follows a representation that is cyclic for recursive types: `spin` | a typed `typecase`; representations must be honest |
| **(c) a polytypic form**, checked once over type structure and instantiated by the compilers             | a type-case typing rule (Harper–Morrisett `typerec`) with effects computed by type, in both; the largest checker change              | types must reach the compilers, which today get erased code and a few recorded facts (`extract` positions); instantiation must be repeated identically in both                                                                                                                  | yes, after instantiation                                                                               | a new argument per polytypic definition                                       | a new rule in K26, with a proof                    |
| **(d) run-time primitives over `data`** (`equal?`, `hash`), as `acyclic?` is                             | one typed constant each                                                                                                              | walks representations with tag tests: the checks the types made needless come back; cannot tell a product from a sum, so no labelled `->datum`                                                                                                                                  | no                                                                                                     | `spin`, or bisimulation on cycles                                             | trusted axioms; §7 Q10                             |

**(a) fits best.** It is the only option that adds nothing the two
checkers must agree on beyond generating the same text, which is easy to
test, and nothing the compilers must learn. It is also the only one where
the native code gets the typed primitives without new optimization work.
It is also how FX-91 did `define-datatype` (§6.6).

(c) would be more expressive, but it asks the most of every component
that must agree. (b) is what SML must do for lack of a compiler hook; FX-26
has the hook. (d) is cheap, and `acyclic?` shows it works. But over `data`
it cannot see mutable data at all (none of the ports' `@heap` lists), and
it discards what the types proved.

**With the preference for dictionaries and tags** (the user, after this
note was first written: "systems that pass dictionaries or tags rather than
duplicating all the code to be specialized over every type"), (a) still
fits best, read this way:

- `derive` writes one definition per *declaration*, as `define-datatype`
  writes one constructor per variant. It never writes one per type
  argument. A family's derived function takes each `type` parameter's
  operation as an argument (§3.3, §2.5 A and G). That is dictionary
  passing, and it keeps §4's termination proofs.
- Instances can be passed as dictionaries, `(product (eq tree=?) (show
  tree->datum))`, to consumers written once (§2.5 B). This needs nothing
  new, and it is `pure` where the operations are.
- (b) in its dictionary form needs no new feature (§2.5 C), unlike the
  `Rep` GADT of the table (§2.5 H). It can be a library beside `derive`,
  for code that wants one generic function over many types. Its costs are
  measurable: `spin` and `(read @globals)` through the recursion's knot,
  and a view allocated per node. Tags proper (H) wait for N4.

## 6. Recommendation

### 6.1 The first feature

Derived **`equal` and `->datum`** for datatypes, sums, products and
lists, then **`hash` and `compare`**. `map`, `fold` and `copy` follow,
since they need result regions. These cover most of the structural
helpers in §1: `term=?`, `mat->datum`, `obj->datum` (with a policy for
`oproc`), `syms=?`, `chars=?`, `int-array=?` and `record=?`.

### 6.2 Syntax (**proposed**, nothing decided)

```
(derive TYPE OP …)
OP ::= name | (name GLOBAL)
TYPE ::= a datatype or type name | (poly ((binder kind) …) type-instance)
```

```
(define-datatype term (t-var int) (t-term string (listof term @heap)))
(derive term equal ->datum hash)           ; term=?, term->datum, term-hash

(define-datatype (prose (t type) (r region)) (pleaf t) (pnode (listof (prose t r) r)))
(derive prose equal)                       ; prose=? at any r: (read r), spin
(derive (poly ((t type) (p place)) (prose t (acyclic p)))
        (equal prose=?/acyclic))           ; no spin
```

- Default names follow the ports' own style: `name=?`, `name->datum`,
  `name-hash`, `name-compare`, `name-map`. They exist only when `TYPE` is
  a name. An instance must be named.
- A separate form, not a clause of `define-datatype`, so that it also
  serves `define-type` abbreviations, generative types (at the owner's
  site) and instances, as GHC's standalone deriving does. A clause could
  come later as sugar.
- Overrides per type, like ppx's attributes: `(derive obj (->datum)
  (with ((subr …) proc->datum)))`. Proposed only if the ports ask for it.

### 6.3 Typing

`(derive T op …)` stands for one `define` per op, whose type is computed
as in §3.3:

- a binder per parameter of the instance;
- an argument per `type` parameter;
- one `e`;
- `reads` and `spin?` from the graph;
- `(read (globals …))` for the owner functions it calls, found as
  `define*` finds them.

Its body is the local group of §4. The checker then checks the `define`
with its ordinary rules, so the computed type is verified, not trusted. A
mistake in the computation is an error pointing at the `derive` form,
with the checker's own reason. Derived definitions are subject to
redefinition like any others: redefining `term` breaks `term=?`, and it
is derived again.

### 6.4 Soundness (`soundness.md`)

- **K26 is unchanged.** `derive`, like `define-datatype`, is elaborated
  away (a row for §1.2's table). T1–T3 need nothing new.
- **T5 (termination)** applies to derived code as to any code. It is
  conjectured, with F8 and F9 open, so "derived and `pure`" is as
  trustworthy as "hand-written and `pure`": no less, and no more.
- **Semantic obligations** are not typing ones. Hash must agree with
  equality, compare must be a total order, and `datum->T` must invert
  `->datum`. A harness can test these on samples, as `gadts.md` proposes
  for lemmas.
- **Lemmas and subtyping.** Coercions are the identity, so a function
  derived at `B` serves an `A ≤ B` unchanged.
- Options (b), (c) and (d) would each add trusted rules. (d) would
  inherit Q10.

### 6.5 What each part needs

| part                                                | work                                                                                                                                                                                                                           |
| --------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| standard environment (`standard.rs`, `standard.fx`) | P0, before any deriving: `bool=?`, `datum=?`, `string<?` or `string-compare`, `symbol<?`, a hash combiner, `list->array`, `array->list`; each an ordinary polymorphic constant or FX-26 library function                       |
| Rust checker (`top.rs`, `check.rs`)                 | the `derive` form at the top level, where every type is known (declare-ahead and the REPL's session alike); a generator from resolved types to `Syntax`, using `unparse.rs` for signatures; the forms then checked as ordinary |
| FX-26 checker (`check.fx`, `parser.fx`)             | the same generator over its arena types, emitting the same text                                                                                                                                                                |
| agreement test                                      | for every `derive` in `tests/programs/derive/`, the two generators' output equal as text, beside the existing type and effect agreement                                                                                        |
| lowering and both compilers                         | only this: a checked top may stand for several generated definitions (the path `checked-tops` / `top_defining` already carries what a form runs)                                                                               |
| native code                                         | nothing; derived code gets `field k`, untagged `int` operations and direct `tagcase` as hand-written code does                                                                                                                 |

Why in the checker and not at read time, where `define-datatype` is
expanded today (`top.rs` `expand_datatype`, `parser.fx`
`parse-datatype`)? A syntactic deriver would see `terms`, an
abbreviation, and could only call a `terms=?`. Those per-name functions
would call one another as globals, and a knot through globals says `spin`
(§4). The flat group needs the abbreviations unfolded, and in an
incremental REPL session only the checker has them.

### 6.6 FX-91's sugars and FX-87's

- **FX-91's sugars are a closed set, each defined by the report as a
  rewrite into the kernel** (FX-91 report §2.4, p. 24: "we give its
  syntax …, provide an informal description of its usage and its
  rewritten form in terms of kernel constructs"). Users cannot define
  new ones. `derive` would be one more sugar of the same kind, defined by
  the language.
- **`define-datatype` was FX-91's deriver** (§2.4.11, pp. 29–30). From a
  sum of products it generates, per datatype, a `define-abstraction`, an
  `id-rep` description, a constructor per variant (`up` of a `sum`), and
  a matcher `id′~` per variant, with success and failure continuations.
  So per-type definitions generated from the type's declaration are
  already in the lineage. FX-26 kept the constructors and dropped the
  matchers, in favour of `tagcase`.
- **`match` picked equality by type** (§2.4.5, p. 26): a literal pattern
  expands to `(if (= pat v) …)`, where "`=` is the equality predicate
  defined on the type of the literal". This is type-directed choice of an
  equality, for base types only.
- **`sexp`** (§3.17, p. 40) is FX-91's universal datatype, with a
  hand-written `sexp=? : (-> read ((s1 sexp) (s2 sexp)) bool)`, and quote
  "desugar[ed] … by induction" on the constant into `t->sexp`
  constructors. FX-26's `datum` is its heir, and `->datum` is the
  missing direction, from typed data to the universal type.
- **FX-91's modules** (`moduleof`, §2.2.6, p. 10; Sheldon and Gifford,
  LFP '90, p. 1: an abstract type "packaged together with" its operations)
  are explicit dictionaries. `table.fx`'s bloblet of hash and equality
  is that idea without modules, and derived functions plug into it
  directly.
- **FX-87 typed some sugars before rewriting them.** In
  `mit-psrg-fx/fx87/old-impl/sugar.lisp`, the sugar keywords are a fixed
  list (lines 9–15). `desc-of-sugar` (line 238) types `let` and `do` by
  their own rules. `change-let-to-lambda!` (line 306) then rewrites the
  `let` into an application whose lambda's `subr` type is filled in
  from the typing. That is checker-side elaboration informed by types,
  the pattern recommended here. A hook for Mark Sheldon's "operation
  sets" (`init.lisp` lines 110–111, 140; `standard.lisp` line 950) is
  off, and its meaning is not documented in the code.

### 6.7 Stages

| stage | size | what                                                                                                                                                                                                                        |
| ----- | ---- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| P0    | S    | standard gaps (§6.5): `bool=?`, `datum=?`, string and symbol order, hash combiner, `list->array`, `array->list`                                                                                                             |
| P1    | M    | `derive` of `equal` and `->datum` for non-parametric datatypes, sums, products and lists; both checkers; text agreement; compilers accept generated tops; `kb.fx`'s `term=?` and `matrix.fx`'s `->datum` rewritten as tests |
| P2    | S    | `hash` (by tag name) and `compare`                                                                                                                                                                                          |
| P3    | M    | families and instances: element functions, one `e`, `(poly …)` instances at `(acyclic p)`; generative types at the owner's site                                                                                             |
| P4    | M    | `datum->T` for `data` types, with `confirm` (`confirmation.md`); a generative type through its validator                                                                                                                    |
| P5    | L    | `map`, `fold`, `copy` with result regions and places                                                                                                                                                                        |
| P6    | ?    | if wanted: `(derived op T)` resolved at `proj`, and derivers written by users in FX-26 over the checker's types as data (after L1)                                                                                          |

Each stage adds tests in `tests/programs/derive/`, compared by both
checkers and run on both compilers. The suite budget of about two
minutes is spent only on small programs.

## 7. Open questions for the user

1. **Syntax.** A separate `(derive TYPE OP …)` form, or a clause on
   `define-datatype`? Are the names `term=?`, `term->datum` and
   `term-hash` right, or should they follow `up-name` and say
   `equal-term`?
2. **Mutable storage.** Does equality compare a `ref`'s or an array's
   *contents* (OCaml's `=`, Rust's `PartialEq`) or its identity (SML)?
   FX-26 has no `eq?`, which is also what blocks several ports.
3. **Tag order.** Hash and compare by tag *name* (stable under width
   subtyping and across programs) or by declaration order (what a reader
   of the datatype expects of `compare`)?
4. **`->datum`'s shape.** A variant as `(tag v …)`; a product as `((l v)
   …)` or `(product (l v) …)`, which reads back as an FX-26 expression; a
   list as a list. And should `unit` have a datum?
5. **Where the deriver lives.** The checker, with resolved types
   (recommended, §6.5), or the read-time expander, syntactically as ppx
   does, giving up termination through abbreviations?
6. **Writable data.** Derive at writable regions (with `spin`, as the
   ports need today), or only at `acyclic` and `const`, pushing ports
   toward frozen data?
7. **Non-regular and polymorphically recursive families.** Refuse, as
   proposed, until someone needs them?
8. **Run-time generics over `data`** (option d). Wanted at all, beside
   deriving, for the REPL's printing say, given "types first"?
9. **User-defined derivers** (P6), written in FX-26 over the checker's
   types: wanted eventually? It is staging, as in Yallop's work, and it
   pulls L1 (types as finite data) forward.
10. **`acyclic?` and places (found while writing this).** Its type is
    `(poly ((t data)) (subr pure (t) bool))`, so it hides a read of data
    frozen into a place. This checks in both checkers, `f : (subr pure ()
    bool)`:

    ```
    (define f (subr pure () bool)
      (letrena p
        (let ((x (letfreeze (r p) (the (listof int r) (rcons p 1 nil)))))
          (lambda () (acyclic? x)))))
    ```

    A variant returns such a closure out of `letrena` and calls it after
    another arena has been used. It checks, and on native code it
    returned `#t` without a visible fault, so no crash has been shown. But
    it is F2's pattern (a closure forgetting its place) through a
    `data`-kinded constant. `certify-acyclic`, and any run-time generic
    over `data`, would have the same problem. Should it be recorded in
    `soundness-findings.md` and fixed, for instance by giving `data`
    binders a region or place of their own? (Done, 2026-09-30: F13,
    `(t data p)`; see `soundness-findings.md`.)

## Sources

Fetched or opened 2026-09-29 unless marked. "Abstract" means only the
bibliographic record or abstract was seen; content from memory.

| source                                                                                                                               | where                                                                                                                                                   | seen                          |
| ------------------------------------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------- |
| Jeuring, Jansson, "Polytypic programming", AFP 1996, LNCS 1129; Jansson, Jeuring, "PolyP", POPL 1997, doi 10.1145/263699.263763      | https://www.cse.chalmers.se/~patrikj/poly/                                                                                                              | read (project page)           |
| Hinze, "A new approach to generic functional programming", POPL 2000, doi 10.1145/325694.325709                                      | https://www.cs.ox.ac.uk/ralf.hinze/publications/index.html                                                                                              | abstract                      |
| Hinze, "Polytypic values possess polykinded types", MPC 2000, doi 10.1007/10722010_2                                                 | same list; its PDF link served a 1 KB stub                                                                                                              | abstract; formula from memory |
| Hinze, Jeuring, "Generic Haskell: practice and theory", 2003, doi 10.1007/978-3-540-45191-4_1                                        | same list                                                                                                                                               | abstract                      |
| Cheney, Hinze, "A lightweight implementation of generics and dynamics", Haskell Workshop 2002, pp. 90–104, doi 10.1145/581690.581698 | https://www.cs.ox.ac.uk/ralf.hinze/publications/HW02.pdf, pp. 2–3; copy in `docs/research/papers/cheney-hinze-hw02.pdf`                                 | read                          |
| Hinze, "Generics for the masses", ICFP 2004, doi 10.1145/1016850.1016882                                                             | https://www.cs.ox.ac.uk/ralf.hinze/publications/ICFP04.pdf, pp. 2–3; copy in `docs/research/papers/hinze-icfp04-generics-for-the-masses.pdf`            | read                          |
| Lämmel, Peyton Jones, "Scrap your boilerplate", TLDI 2003                                                                            | https://www.microsoft.com/en-us/research/publication/scrap-your-boilerplate-a-practical-approach-to-generic-programming/                                | read (summary page)           |
| Magalhães, Dijkstra, Jeuring, Löh, "A generic deriving mechanism for Haskell", Haskell 2010, pp. 37–48, doi 10.1145/1863523.1863529  | https://dl.acm.org/doi/10.1145/1863523.1863529                                                                                                          | abstract                      |
| GHC.Generics, base-4.22.0.0                                                                                                          | https://hackage-content.haskell.org/package/base-4.22.0.0/docs/GHC-Generics.html                                                                        | read                          |
| GHC User's Guide 9.14.1, DerivingVia                                                                                                 | https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/deriving_via.html                                                                        | read                          |
| Sheard, Peyton Jones, "Template meta-programming for Haskell", Haskell Workshop 2002, doi 10.1145/581690.581691                      | https://dl.acm.org/doi/10.1145/581690.581691                                                                                                            | abstract                      |
| Magalhães, Holdermans, Jeuring, Löh, "Optimizing generics is easy!", PEPM 2010                                                       | https://dreixel.net/research/pdf/ogie.pdf, pp. 6, 10                                                                                                    | read                          |
| Yallop, "Staged generic programming", PACMPL 1 (ICFP), art. 29, 2017, doi 10.1145/3110273                                            | https://www.cl.cam.ac.uk/~jdy22/papers/staged-generic-programming.pdf, pp. 29:1, 29:3, 29:11                                                            | read                          |
| Altenkirch, McBride, "Generic programming within dependently typed programming", IFIP WCGP 2002, doi 10.1007/978-0-387-35672-3_1     | https://people.cs.nott.ac.uk/psztxa/publ/wcgp02.pdf, pp. 6–8, 19                                                                                        | read                          |
| Chapman, Dagand, McBride, Morris, "The gentle art of levitation", ICFP 2010, pp. 3–14, doi 10.1145/1863543.1863547                   | https://personal.cis.strath.ac.uk/conor.mcbride/levitation.pdf                                                                                          | abstract                      |
| Christiansen, Brady, "Elaborator reflection: extending Idris in Idris", ICFP 2016, pp. 284–297, doi 10.1145/2951913.2951932          | https://dl.acm.org/doi/10.1145/2951913.2951932                                                                                                          | abstract                      |
| Harper, Morrisett, "Compiling polymorphism using intensional type analysis", POPL 1995, pp. 130–141, doi 10.1145/199448.199475       | https://dl.acm.org/doi/10.1145/199448.199475                                                                                                            | abstract                      |
| Crary, Weirich, Morrisett, "Intensional polymorphism in type-erasure semantics", ICFP 1998, pp. 301–312, doi 10.1145/289423.289459   | https://www.seas.upenn.edu/~sweirich/papers/typepass/typepass.pdf                                                                                       | abstract                      |
| ppx_deriving README (master)                                                                                                         | https://github.com/ocaml-ppx/ppx_deriving                                                                                                               | read                          |
| ppx_compare, ppx_sexp_conv, ppx_hash READMEs (master)                                                                                | https://github.com/janestreet/ppx_compare, https://github.com/janestreet/ppx_sexp_conv, https://github.com/janestreet/ppx_hash                          | read                          |
| MLton, TypeIndexedValues (master); mltonlib Generic (master)                                                                         | https://github.com/MLton/mlton/blob/master/doc/guide/src/TypeIndexedValues.adoc, https://github.com/MLton/mltonlib/tree/master/com/ssh/generic/unstable | read                          |
| Clean 3.0 language report, ch. 7                                                                                                     | https://cloogle.org/doc/                                                                                                                                | read (section structure)      |
| The Rust Reference, `derive`                                                                                                         | https://doc.rust-lang.org/reference/attributes/derive.html                                                                                              | read                          |
| serde data model                                                                                                                     | https://serde.rs/data-model.html                                                                                                                        | read                          |
| Scala 3 reference, type class derivation                                                                                             | https://docs.scala-lang.org/scala3/reference/contextual/derivation.html                                                                                 | read                          |
| F# type providers (dotnet/docs commit 8a54c99a)                                                                                      | https://learn.microsoft.com/en-us/dotnet/fsharp/tutorials/type-providers/                                                                               | read                          |
| Gifford, Jouvelot, Sheldon, O'Toole, *Report on the FX-91 Programming Language* (1993)                                               | `~/Dev/LangPlay/GiffordHistory/papers/fx91-report.pdf`: §2.2.6 p. 10; §2.4 p. 24; §2.4.5 p. 26; §2.4.11 pp. 29–30; §3.17 p. 40                          | read                          |
| Sheldon, Gifford, "Static dependent types for first class modules", LFP '90                                                          | `~/Dev/LangPlay/GiffordHistory/papers/lfp90.pdf`, p. 1                                                                                                  | read                          |
| FX-87 interpreter, BETA-0                                                                                                            | `~/Dev/LangPlay/GiffordHistory/mit-psrg-fx/fx87/old-impl/`: `sugar.lisp` lines 9–15, 238, 261, 306; `init.lisp` 110–111, 140; `standard.lisp` 950       | read                          |
