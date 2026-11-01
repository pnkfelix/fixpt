# Sets and maps: in the language, or in a library?

Research note, 2026-11-01. Nothing here is built. The question (the
user's): should FX-26 have sets and maps as first-class abstractions in
the language, as SETL does, instead of library types that sometimes have
to be tied closely to low-level details? The example given: an
`eqtable` has to work with the moving collector. And should Clojure be
the model rather than SETL, given that Clojure is mostly functional,
while FX-26 wants both purity and imperative code?

FX-26 facts are from the repository at commit `71de5b8`. The toy
programs are in `docs/research/examples/sets/`. Each was checked with
`target/release/fixpt check` (both checkers agreed on every one) and run
with `fixpt eval`, at that commit. Sources are listed at the end. Every
one marked *read* was opened for this note. Those marked *record* were
checked only for their bibliographic details or abstract, and their
content is given from memory. Those marked *memory* were not reached at
all: `clojure.org` is outside this session's network.

## 0. At a glance

- **The coupling to the collector is not, by itself, a reason for
  language support.** `eqtable` is already a kernel type: generative
  type 4, made only from an `identity` dictionary that only the standard
  procedures make, and hashed by address with a collection stamp
  (`docs/fx26.md`, "Identity"). Making sets "first-class" would move that
  trusted code into the compiler, not remove it. Ephemerons (`TODO.md`
  §59) and Larceny's two tablets (`TODO.md` §19) stay runtime work that
  the collector must know about, either way.
- **What language support would buy** is three things a library cannot
  have today:
  1. operations whose type says `pure` on a set used as a *value*;
  2. a way, checked by the types, to build a set by mutation and then
     use it as a value;
  3. a compiler that knows what the operations mean, so it can fuse set
     formers and, later, choose data structures as SETL's optimizer did.
- **Point 2 is FX-26's own contribution, and most of it is already
  there.** `letregion` masks mutation, and `letfreeze` turns a region's
  data into `const` at no cost. Together they are Clojure's
  `transient` / `persistent!` (§2.2), with the misuse refused by the
  checker instead of caught at run time. They are also SETL's value
  semantics without SETL's copy-elimination problem (§2.1).
  `sorted-set.fx` builds a set through a `ref` it masks, and the
  builder's type is `(maxeff spin (read (globals adjoin)))`: no `read`,
  `write` or `alloc` of any region.
- **The hard question is how keys are compared, not syntax.** A set of
  `T` needs `T`'s equality and hash. FX-26 has identity (the `identity`
  dictionary, which deliberately refuses frozen data) and, proposed,
  derived equality and hash (`polytypic.md`'s `derive`; the editor's
  request, `TODO.md` §110). A built-in `setof` would have to choose
  between dictionaries passed explicitly and a kind of types with
  equality (SML's `''a`, which `docs/fx26.md` lists as "not done"). That
  choice comes first, and set formers last: they can be macros over a
  walk (`former.fx`).
- **Found on the way** (§3.2). Both checkers accept an `eqtable` frozen
  by `letfreeze`, at `const` (`frozen-eqtable.fx`). Its lookups still
  rehash it after a collection, so the runtime writes memory the types
  call frozen. This is not unsound today. Every lookup writes the keys'
  region `kr`, so `par` refuses two lookups as interfering
  (`frozen-eqtable-par.fx`), and keys at a writable region are not
  transmissible. But the safety follows from a rule made for another
  reason ("no table keyed by frozen data").
- **Recommendation (§5).** A kernel `setof` and `mapof` in two forms: a
  value at a frozen region, with `pure` operations, and a mutable form
  at a region `r`, frozen with the `letfreeze` that already exists.
  Keys compared by a dictionary, identity or derived. Formers and
  quantifiers last, as macros. Read Clojure for the data structures and
  transients, SETL for the notation and the optimizer, and Koka's
  Perceus and Swift's copy-on-write collections for "value semantics
  that updates in place". FX-26 can prove statically what those last
  two check with reference counts at run time.

## 1. What the library costs today

`scheme-bench/set.fx`, the port of Larceny's SRFI 113 benchmark, is 643
lines, most of them the layers under the benchmark. FX-26 has no sets,
comparators or equality-keyed hash tables, so the port writes all three.
Every comparator procedure has one effect, `cmps`:

```
(define-effect cmps
  (maxeff (read @heap) (write @heap) (alloc @heap) spin
          (read (globals symbol-hash syms-list? … table-find))))
```

So an operation that means a value (is `x` in `s`?, the union of `s` and
`t`) has a type saying it writes the heap and may not end. Some of this
is the port being faithful: Larceny's sets are mutable hash tables, and
`set-find` escapes with `call/cc`. The rest is structural. A set of sets
has to store its elements' procedures in data, so all of them share one
effect, the largest. And a table is an array of buckets at `@heap`,
written as it grows, so nothing about it is frozen. The editor has the same need, 54
tables keyed by strings and structure (`TODO.md` §110).

A library can do better when the representation can be frozen.
`sorted-set.fx` keeps a set of ints as a sorted `(listof int acyclic)`.
`member?`, `adjoin` and `union` are then `pure`: lists at `acyclic` are
frozen and finite, and size-change sees each walk end. That is SETL's
model in miniature. But a sorted list is O(n) per operation. The
structures that do better (hash array mapped tries, balanced trees) need
nodes that are built and then never written. FX-26 can express those: a
node is an array frozen by a `letfreeze` of its own (§3.3). But nothing
like that exists yet, and every program that wants a set writes one.

## 2. The three models

### 2.1 SETL: values, and an optimizer that pays for them

SETL (J. T. Schwartz, NYU, from about 1969) has atoms, finite sets,
tuples and maps, where a map is a set of pairs. `f(x)` is the single
image, and `f{x}` the set of images. All of them are values: assignment
behaves like a copy. Programs are written with set formers, `{e(x) : x
in s | p(x)}`, and quantifiers, `exists x in s | p(x)`, whose witness
stays bound after the test (*memory*).

The language was meant to be made fast by its compiler. Two lines of
work matter here:
- **Choosing data structures.** Schonberg, Schwartz and Sharir chose
  representations for sets and maps at compile time from how they are
  used (POPL 1979, TOPLAS 3(2) 1981, *record*). SETL also had an
  optional *representation sublanguage*: "basings" declared that several
  sets share a base set, so that membership could be a field or a bit
  (*memory*). By the authors' own account the technique is tied to
  SETL's semantics, not general (*record*, the TOPLAS summary).
- **Finite differencing.** Paige and Koenig keep a costly set expression
  such as `#{x in s | p(x)}` up to date as `s` changes, instead of
  recomputing it: a generalization of strength reduction (TOPLAS 4(3)
  1982, *record*). Paige's later program transformation systems
  (RAPTS, APTS) built on it (*memory*).

What SETL lacked was a way to *know* that a copy was not needed. Value
semantics with in-place update needs proof that no one else holds the
value. SETL's optimizer inferred that, and could fail to (*memory*;
Freudenberger, Schwartz and Sharir's "Experience with the SETL
optimizer", TOPLAS 1983, *record*, reports on it). FX-26's regions give
that proof by construction: data at a region that `letregion` masks is
held by no one outside the body.

### 2.2 Clojure: persistent structures, and transients

Clojure's collections are persistent: a hash array mapped trie for maps
and sets, a 32-way trie for vectors. "Update" makes a new version that
shares most of the old one's structure. Equality is by value, across
collection types, and hashes are cached (*memory*). Mutation for speed
comes through **transients**: `(transient v)` gives a mutable version of
`v` in O(1), and `persistent!` turns it back in O(1), after which the
transient may not be used. A transient must not escape the code that
built it, and Clojure checked this at run time. Up to Clojure 1.6 it
checked that only the owning thread touched it; from 1.7 the check was
relaxed to one thread at a time (*record*, via the search results listed
under Sources; `clojure.org` itself was not reachable).

That is FX-26's `letfreeze` with the check moved. In `(letfreeze r
body …)`, the body mutates data at `r`. The value leaves with `r`
replaced by `const`, and the checker refuses any way left to write `r`
(`docs/fx26.md`, "Freezing"). Clojure checks "this transient was not
used after `persistent!`" when the program runs. FX-26 proves it before
the program runs, and the proof costs nothing at run time.

So "Clojure is heavily functional" is less of an objection than it
looks. Its collections are the functional part, and transients are its
imperative escape hatch, which is the part closest to FX-26.

### 2.3 Value semantics that updates in place: Swift and Koka

Two more recent designs answer "both purity and imperative code"
directly:
- **Swift's collections** are values with copy-on-write. A mutation
  first checks that the buffer is uniquely referenced, and copies it if
  not (*memory*).
- **Koka's Perceus** (Reinking, Xie, de Moura and Leijen, PLDI 2021,
  *record*) uses precise reference counts with *reuse*. When a value's
  count is one, a functional update reuses its memory in place. That
  gives "functional but in-place" programming: code written as pure, run
  as mutation.

Both find uniqueness at run time, from reference counts. FX-26 has a
tracing collector and no counts, but it can often prove uniqueness
statically instead: data at a region masked by `letregion`, or frozen by
`letfreeze`, has no other holder. Where it cannot prove it, the program
says so in its types, with a writable region. Neither Swift nor Koka
can say that.

## 3. What FX-26 has

### 3.1 The pieces

| piece                        | what it gives a set or map                                                            | where                                  |
| ---------------------------- | ------------------------------------------------------------------------------------- | -------------------------------------- |
| `letregion`, `letrena`       | mutation that does not show in the type of the code that does it                     | `docs/fx26.md`, "Regions that end"     |
| `letfreeze`                  | mutable to value, at no cost, checked                                                  | `docs/fx26.md`, "Freezing"             |
| `acyclic`                    | frozen, finite data, whose walks end without `spin`                                    | `docs/fx26.md`, "Finite data"          |
| `eqtable`, `identity`        | identity-keyed maps, hashed by address, kept right across collections                  | `docs/fx26.md`, "Identity"             |
| `derive` (proposed)          | equality and hash for a datatype, which equality-keyed tables need                    | `docs/research/polytypic.md`           |
| ephemerons (planned)         | weak-keyed tables whose values may refer to their keys                                 | `TODO.md` §59                          |
| `par`'s interference check   | a set read in parallel only when no branch writes it                                   | `docs/fx26.md`, "`par`"                |

### 3.2 Found on the way: an `eqtable` at `const`

`frozen-eqtable.fx` builds a table in a `letfreeze` and returns it:

```
(define* frozen-table (subr (maxeff (alloc @k) (write @k)) (key key) (eqtable key int @k const))
  (lambda (a b)
    (letfreeze r
      (let ((t (the (eqtable key int @k r) (make-eqtable (pair-identity)))))
        (begin (eqtable-set! t a 1) (eqtable-set! t b 2) t)))))
```

Both checkers accept it, and the lookups give `3` with effect `(write
@k)`: reading `const` is pure, and each lookup writes the keys' region.
`eqtable-set!` on the frozen table is refused, as a write of `const`
should be. But `eqtable-ref` may rehash the table after a collection
(`fixpt_runtime::eqtable`), relinking its entries in place. That is a
write by the runtime to an object the types call frozen.

It is safe today, for a reason given elsewhere: every operation writes
the keys' region "so that no table is keyed by frozen data". Because of
that `(write @k)`:
- `par` refuses two lookups of one frozen table as interfering
  (`frozen-eqtable-par.fx`: "one has (write @k) and another (write
  @k)");
- the table's type mentions a writable region, so it is not
  transmissible to a process.

If that rule were ever relaxed, for instance so that a lookup in a
frozen table only reads, the rehash would become a race. A built-in map
type should make this explicit: either a table cannot be frozen (its
type takes no `const`), or a frozen table is rehashed by the collector
itself, which then owns the address-dependent state.

### 3.3 What FX-26 lacks

- **A persistent structure written in FX-26.** A HAMT updated in a
  loop makes a new path of nodes per update, each built and then never
  written. FX-26 can say this. `(the (arrayof int const) (make-array 3
  7))` checks as `pure`, and so does a `letfreeze` around a
  `make-array` and its `array-set!`s, leaving at `(arrayof int const)`
  (both checked for this note, not kept as examples). So each node
  copy is a small `letfreeze`. What does not exist is the library, and
  nothing tells a compiler that a set is a set (§4, option C).
- **Equality-keyed tables** (`TODO.md` §110), which need derived or
  given equality and hash.
- **An iteration protocol** that a set former could expand to and that
  fusion could see. `former.fx` writes `{x*x : x in s | odd(x)}` as a
  higher-order walk. Its effect is the element functions' effect plus
  reads of the globals it calls. That is the right type, and the
  boilerplate is what syntax would remove.
- **`exists` with a witness**, which comes back as a sum in `former.fx`,
  since FX-26 has no binding that outlives a test.

## 4. Library, kernel, or syntax: the options

| option                                                | what it is                                                                                         | for                                                                                         | against                                                                                                |
| ----------------------------------------------------- | -------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------ |
| A. a library in FX-26                                 | `setof` and `mapof` written in FX-26, over lists, arrays and `eqtable`                              | nothing new to trust; a bug in it is a wrong answer, never an unsound program               | no frozen arrays, so no fast persistent structures that are `pure`; effects as large as `cmps` (§1)    |
| B. kernel types, as `eqtable` is                     | generative types whose operations the runtime implements, with trusted types                        | `pure` operations on frozen sets; the runtime may use any representation; GC coupling is contained | more trusted code; two checkers, both compilers and the evaluator must agree on each type            |
| C. B, plus forms the compiler knows                   | set formers and quantifiers as forms, not macros; fusion; later, representation choice             | SETL's optimizations become possible                                                        | each form needs typing rules in both checkers and lowering in every compiler                          |
| D. B, plus syntax only                                | formers and quantifiers as macros over B's walk                                                     | the notation, at no cost to the kernel                                                      | the compiler sees only calls, so no fusion beyond inlining                                            |

## 5. Recommendation

B, then D, with C kept possible:

1. **Decide how keys are compared.** Explicit dictionaries, as
   `identity` is now and as `polytypic.md` recommends for `derive`, fit
   what exists. A kind of types with equality would be shorter to write,
   but it is a new kind for both checkers. Recommended: dictionaries,
   with `derive` making them.
2. **Kernel `setof` and `mapof`, as values.** At a frozen region, every
   query `pure` but for the dictionary's effect. Built from a mutable
   form at a region `r`, then frozen by `letfreeze`, and so checked
   where Clojure checks at run time. Their representation is the
   runtime's concern (a HAMT, a sorted array, a bit set for small ints).
   SETL's representation choice would then be a runtime or compiler
   decision, not the program's.
3. **Settle §3.2 in that design.** Identity-keyed maps either cannot be
   frozen, or are rehashed by the collector. Equality-keyed maps hash by
   content and do not have the problem.
4. **Formers and quantifiers as macros** over a walk the kernel types
   provide (D). Move to forms (C) only if fusion or finite differencing
   is wanted.

On "Clojure or SETL": both, for different things. Clojure for the data
structures and transients, the nearest existing design to `letfreeze`.
SETL for notation (formers, maps as relations, `f{x}`) and for the
compiler research. Koka and Swift for the closest match to "purity and
imperative code", which FX-26 can do better, because it proves
statically what they check at run time.

## 6. Open questions for the user

1. Dictionaries or a kind with equality, for keys (§5.1)?
2. Should a frozen identity table be refused, or rehashed by the
   collector (§3.2)? And should the present acceptance be recorded in
   `soundness-findings.md` as a latent hazard?
3. Should the first step be option A (§4), a persistent map written in
   FX-26 with a `letfreeze` per node (§3.3), as a trial of the types
   and a benchmark for a kernel version?
4. Should `exists` bind its witness, as SETL's does, or give a sum
   (`former.fx`)?

## The toy programs

| file                     | shows                                                                                          | checked, ran | result                                    |
| ------------------------ | ---------------------------------------------------------------------------------------------- | ------------ | ----------------------------------------- |
| `sorted-set.fx`          | sets as sorted `acyclic` lists, `pure`; a set built by a masked `ref`, transient-style          | yes          | `(0 1 2 3 4 5 7 9 16 25 36 49)`           |
| `former.fx`              | `{x*x : x in s | odd(x)}` and `exists` with a witness, written out                              | yes          | `((1 9 25 49) (4))`                       |
| `frozen-eqtable.fx`      | an `eqtable` frozen by `letfreeze`, then looked up (§3.2)                                       | yes          | `3`, effect `(write @k)`                  |
| `frozen-eqtable-par.fx`  | two `par` branches looking up that table                                                        | refused      | "`par`'s branches interfere"              |

Running them here needed a local change not in this note: the heap's
reservation of address space (`fixpt_memmgmt::Words::new`) was refused
on a Linux machine with `vm.overcommit_memory = 0` and 15 GB of memory,
until it was mapped with `MAP_NORESERVE`.

## Sources

Searched or opened 2026-11-01. "Record" means only the bibliographic
record or an abstract was seen, and content is given from memory.
"Memory" means nothing was reached.

| source                                                                                                                                         | where                                                                                                                                                                     | seen                         |
| ---------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------- |
| Schonberg, Schwartz, Sharir, "Automatic data structure selection in SETL", POPL 1979, pp. 197–210                                              | https://hopl.info/showlanguage.prx?exp=1268                                                                                                                                | record                       |
| Schonberg, Schwartz, Sharir, "An automatic technique for selection of data representations in SETL programs", TOPLAS 3(2), 1981, pp. 126–143   | https://vldb.org/dblp/db/journals/toplas/toplas3.html; reprint summary at https://www.oreilly.com/library/view/readings-in-artificial/9780934613125/xhtml/B9780934613125500239.xhtml | record                       |
| Freudenberger, Schwartz, Sharir, "Experience with the SETL optimizer", TOPLAS 1983                                                             | named in the search results for the above                                                                                                                                  | record                       |
| Paige, Koenig, "Finite differencing of computable expressions", TOPLAS 4(3), 1982, pp. 402–454                                                 | https://vldb.org/dblp/db/journals/toplas/toplas4.html; https://scholarsmine.mst.edu/math_stat_facwork/355                                                                 | record                       |
| Schwartz, Dewar, Dubinsky, Schonberg, *Programming with Sets: An Introduction to SETL*, Springer, 1986                                         | —                                                                                                                                                                          | memory                       |
| Clojure reference, "Transients"                                                                                                                | https://clojure.org/reference/transients (not reachable from this session)                                                                                                 | memory                       |
| Thread-ownership check relaxed in Clojure 1.7                                                                                                  | https://clojurians-log.clojureverse.org/clojure-dev/2019-08-01; https://ask.clojure.org/index.php/3298/partition-partition-transducers-should-visibility-changes            | record (search results)      |
| Reinking, Xie, de Moura, Leijen, "Perceus: garbage free reference counting with reuse", PLDI 2021; MSR-TR-2020-42                              | https://www.microsoft.com/en-us/research/publication/perceus-garbage-free-reference-counting-with-reuse/                                                                   | record                       |
| Swift collections' copy-on-write                                                                                                               | —                                                                                                                                                                          | memory                       |
| FX-26: `docs/fx26.md` ("Identity", "Regions that end", "Freezing", "What a process may hold", "`par`"); `TODO.md` §19, §59, §110; `scheme-bench/set.fx`; `docs/research/polytypic.md` | this repository at `71de5b8`                                                                                                                       | read                         |
