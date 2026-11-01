# Graphs: languages built around them, and what a fold over one is

Research note, 2026-11-01. Nothing here is built. The questions (the
user's): are there graph-oriented languages, as SETL is set-oriented? And
how is a "fold" (a catamorphism) defined over a graph? Graphs can be
defined inductively, as a set of nodes and a set of edges, but that is
usually not a useful basis for a graph algorithm.

A companion to `sets-and-maps.md`, whose dictionary design (§5.1 there)
this note extends. FX-26 facts are from the repository at commit
`71de5b8`. The toy programs are in `docs/research/examples/graphs/`. Each
was checked with `target/release/fixpt check` (both checkers agreed on
every one) and run with `fixpt eval`, at that commit, with the local
change of issue #4. Sources are listed at the end. *Record* means a
bibliographic record, abstract, library documentation or search results
were seen, and content is otherwise from memory. *Memory* means nothing
was reached. `web.engr.oregonstate.edu` and `www.cs.tufts.edu`, which
host Erwig's and Mokhov's papers, are outside this session's network.

## 0. At a glance

- **There are graph-oriented languages, in five families** (§1):
  - graph rewriting (GP 2, GrGen.NET, GROOVE, AGG, PROGRES);
  - traversal DSLs (Green-Marl, GraphIt, Ligra);
  - vertex-centric frameworks (Pregel, GraphLab);
  - graph algorithms as linear algebra (GraphBLAS);
  - queries and logic (Datalog, Cypher, GQL).

  The closest to SETL in spirit is Green-Marl: a small language whose
  control structures are traversals, compiled for parallel machines.
  There is also a direct line from SETL. Paige's finite differencing
  was applied to graph algorithms written as set fixpoints, and Liu and
  Stoller's derivation of efficient programs from Datalog rules
  (TOPLAS 2009) continues it.
- **There is no single fold over graphs.** There are five answers, and
  each chooses a different structure to recurse on (§2):
  1. *Decomposition* (Erwig): a graph is empty, or one node's context
     and the rest. Any node may be taken first, so a fold depends on the
     order unless its function does not.
  2. *A quotient algebra* (Mokhov): `empty`, `vertex`, `overlay`,
     `connect`, with laws. A fold is well defined for target algebras
     that keep the laws.
  3. *Fold the search's tree* (King and Launchbury): depth-first search
     makes a spanning forest, an ordinary finite tree, and most
     algorithms are folds over it.
  4. *Equations solved as a least fixpoint* (Kildall, Datalog, Pregel,
     circular attribute grammars). This is a true catamorphism on a
     DAG, with memoization, and a fixpoint on a cyclic graph.
  5. *Closure over a semiring* (Carré, Dolan, GraphBLAS): one algorithm,
     and the semiring chooses the problem.
- **In FX-26, the types show the move from cyclic to finite** (§3).
  - In `dfs-forest.fx` the graph is a frozen array of successor lists
    at `const`, which may hold cycles. The search must say `spin`. Its
    result, a forest at `acyclic`, has a `pure` fold.
  - `lattice-fixpoint.fx` is a least-fixpoint solver over a lattice
    dictionary. It must say `spin`, since nothing in a type proves the
    lattice's height finite.
  - `semiring-closure.fx` is one closure that computes reachability with
    booleans and shortest paths with min-plus. It closes a matrix in a
    region and freezes it, and its type is `spin` with no region
    effects.
- **Recommendation** (§4):
  - a traversal primitive whose result is an `acyclic` spanning forest,
    with the visited set masked;
  - a least-fixpoint operator over a third dictionary shape, a lattice
    (bottom, join, equality, and an optional height bound that would let
    it drop `spin`);
  - semiring closure as a library over a fourth dictionary shape.

  Decomposition folds (answer 1) only as `nondet`, as for hash-ordered
  walks in `sets-and-maps.md` §5.1.

## 1. Graph-oriented languages

| family                    | examples                                                                                                  | the primitive                                                                                          |
| ------------------------- | --------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------ |
| graph rewriting           | GP 2 (Plump, York), GrGen.NET, GROOVE, AGG, PROGRES                                                       | rules that match a subgraph and replace it, applied nondeterministically until none applies            |
| traversal DSLs            | Green-Marl (Hong, Chafi, Sedlar, Olukotun, ASPLOS 2012); GraphIt (Zhang et al., OOPSLA 2018); Ligra       | BFS and DFS, or a frontier of vertices, as constructs, compiled to parallel code                       |
| vertex-centric            | Pregel, GraphLab, GraphX                                                                                   | a step per vertex that sends messages to neighbours, repeated in supersteps until nothing changes      |
| linear algebra            | GraphBLAS                                                                                                 | sparse matrix–vector products over a semiring                                                         |
| queries and logic         | Datalog, Cypher, ISO GQL, SPARQL property paths                                                            | recursive rules, or regular expressions over paths, computed as least fixpoints                       |
| functional libraries      | Erwig's FGL, Mokhov's `algebraic-graphs`, King and Launchbury's DFS                                         | an inductive or algebraic view of a graph (§2)                                                         |

Some details, as far as they were checked:
- **GP 2** programs are built from conditional rule schemata, applied by
  double-pushout rewriting with relabelling. A call of a rule set
  applies one applicable rule, chosen nondeterministically, and the
  language has explicit nondeterministic choice between subprograms. Its
  design favours a simple semantics, for formal reasoning. There is a
  compiler to C and an interpreter that explores the nondeterminism
  (*record*).
- **Green-Marl** gives graph analysis constructs that expose data
  parallelism, and a compiler that uses their meaning to optimize. It
  compiles to C++ (*record*).
- **GraphIt** separates *what* is computed (an algorithm language) from
  *how* (a scheduling language). The trade-offs among locality,
  parallelism and work are treated as the central problem (*record*).
  This is the representation choice SETL hoped to make automatically
  (`sets-and-maps.md` §2.1), made explicit instead.
- **Liu and Stoller** turn Datalog rules into specialized programs with
  worst-case time and space guarantees. Each combination of facts that
  makes a rule's hypotheses true is handled once, in constant time
  (*record*). Their method descends from Paige's (*memory*).

Rewriting has the clearest semantics but is the furthest from what a
graph algorithm usually is. The traversal DSLs are closest to how such
algorithms are written. The algebraic and logical families give the
most reuse: one solver, many problems.

## 2. What a fold over a graph can be

The trouble with "a set of nodes and a set of edges" is that it has no
induction in the useful direction. The sets are inductive, but an
algorithm recurses along *edges*, and edges make cycles. Each answer
below picks another structure to recurse on.

### 2.1 Decompose one node at a time (Erwig)

Erwig's inductive graphs (JFP 11(5), 2001, *record*) view a graph as
either empty or `c & g`. The context `c` is a node, its label, and its
edges in from and out to `g`, the rest of the graph. The key operation
is `match v g`, which gives `v`'s context and the remaining graph.
`ufold` folds over contexts, and FGL's default definition takes them in
whatever order `matchAny` gives (*record*, the library's documentation).
Depth-first and breadth-first search become unfolds: match the next
node, then continue with its successors.

The decomposition is not unique, since any node may be matched first.
So `ufold f` is well defined only when `f`'s result does not depend on
the order: counting, collecting into a set, a commutative and
associative combination. Elsewhere it is a function of the
implementation. This is the same problem as walking a hash-ordered set
(`sets-and-maps.md` §5.1), and in FX-26 it would be `nondet` for the
same reason. Search is different: `match v` names the node, so a
traversal's order is fixed by the program.

### 2.2 A quotient algebra (Mokhov)

Mokhov's algebraic graphs (Haskell Symposium 2017, *record*) build every
graph from four constructors: `empty`, `vertex x`, `overlay g h` (the
union) and `connect g h` (the union, plus an edge from every vertex of
`g` to every vertex of `h`). Laws relate them. `overlay` is commutative
and associative, `connect` is associative and distributes over
`overlay`, and so on (*record*; the full axioms from memory). Different
choices of axioms give undirected, reflexive or transitive graphs.
There are no malformed graphs, with an edge to a vertex that does not
exist (*record*).

`foldg` is then the catamorphism of that algebra, and `buildg` its
inverse (*record*, the library's documentation). It is well defined for
any target that satisfies the laws: the same one-way contract as a hash
(`sets-and-maps.md` §5.1), and also unchecked. This is the cleanest real
catamorphism. It suits building and transforming graphs (mapping
vertices, taking induced subgraphs, transposing) better than search.

### 2.3 Fold the search's tree (King and Launchbury)

King and Launchbury (POPL 1995, *record*: cited by Erwig, and the basis
of the `DFS` module in Haskell's `alex`) separate depth-first search
into two parts. First the search produces a spanning forest, lazily.
Then each algorithm is an ordinary function of that forest, sometimes
together with the edges the forest does not contain:
- reverse postorder, which is a topological order of a DAG;
- strongly connected components, by two searches;
- reachability, articulation points, and others.

Erwig notes that the focus is "a generated data structure, the
depth-first spanning forest". Launchbury's later slides call the
forest "a static value to aid reasoning" (*record*). The graph is
cyclic, but what is recursed on is a tree. The only imperative part is
the visited set, which they keep in a mutable array behind a pure
interface.

This is the answer that fits FX-26 best (§3.1). It is a real
catamorphism, over a structure computed for that purpose.

### 2.4 Equations solved as a least fixpoint

On a cyclic graph, the honest form of "a fold" is a system of
equations, one per node:

    x_v = f(label_v, { x_u | u a successor of v })

solved as the least solution in a lattice. This is Kildall's dataflow
analysis (POPL 1973), Datalog's semantics, Pregel's supersteps, and
circular reference attributes in attribute grammars (JastAdd; Magnusson
and Hedin) (*memory*). It is well defined when `f` is monotone, and
reached by iteration from bottom when the lattice has no infinite
ascending chains.

On a DAG the same equations have one solution, computed bottom-up with
memoization: a catamorphism with sharing (Gibbons, "An initial-algebra
approach to directed acyclic graphs", MPC 1995, *memory*). On a tree
there is no sharing, and it is the plain fold. So answer 4 extends the
fold, rather than replacing it.

### 2.5 Closure over a semiring

The algebraic path problem (Carré, *Graphs and Networks*, 1979;
Backhouse and Carré, 1975; *memory*) treats a graph as a matrix over a
semiring and asks for its closure A* = 1 + A + A² + …. Choosing the
semiring chooses the problem:
- booleans give reachability;
- (min, +) gives shortest paths;
- (max, min) gives widest paths;
- regular expressions give the language of paths.

Dolan's pearl "Fun with semirings" (ICFP 2013) writes one closure in
Haskell for all of them. Shortest paths, the regular expression of a
finite automaton and dataflow analysis are all reductions to linear
algebra over a suitable semiring (*record*, as described by a later
paper). GraphBLAS is the engineering version: sparse matrices, a
semiring per operation (*memory*).

Here the "fold" is the closure, and generic code is written once over
the semiring dictionary.

### 2.6 Cyclic structures in typed functional languages

For completeness. These keep sharing and cycles inside a datatype, so
that a fold sees them, rather than computing a tree to fold:
- Fegaras and Sheard's catamorphisms over datatypes with embedded
  functions (POPL 1996);
- Ghani, Hamana, Uustalu and Vene's cyclic structures as nested
  datatypes (2006);
- Hamana's initial-algebra semantics for cyclic sharing structures
  (TLCA 2009);
- Oliveira and Cook's structured graphs, with binders for sharing and
  cycles in PHOAS style (ICFP 2012).

All four are *memory*. They need either higher-rank types or nested
datatypes, which FX-26 has only partly (`docs/fx26.md`, "Higher kinds";
non-regular generative types). They are not pursued here.

## 3. In FX-26

### 3.1 The search's tree: `dfs-forest.fx`

The graph is a frozen array of successor lists:

```
(define-type graph (arrayof (listof int acyclic) const))
(define-datatype rose (rnode int (listof rose acyclic)))
(define-type forest (listof rose acyclic))
```

It is built by writes inside a `letfreeze`, so it is at `const`, and a
`(write r)` could have made a cycle. The example graph has one, 0 → 1 →
2 → 0. The search marks nodes in an array at a region that `letregion`
masks:

```
(define dfs (subr (maxeff spin (read (globals rnode))) (graph (listof int acyclic)) forest)
  (lambda (g roots)
    (letregion r
      (let ((seen (the (arrayof bool r) (make-array (array-length g) #f))))
        …))))
```

Its type has no region effects, only `spin`, since it ends only because
each node is visited once, which size-change cannot see. Its result is
at `acyclic`: lists built in order, never written. So the fold over the
forest is `pure`, with no `spin`:

```
(define reverse-postorder (subr pure (forest (listof int acyclic)) (listof int acyclic)) …)
```

The answer is `(5 4 0 1 3 2)`. The types show King and Launchbury's
separation exactly. The search, from a cyclic `const` graph to an
`acyclic` forest, is where termination is not visible to the checker.
Everything after it is a structural fold that the checker sees end.

### 3.2 Equations: `lattice-fixpoint.fx`

The lattice is a dictionary, the third shape after `sets-and-maps.md`'s
`(eq, hash)` and `(eq, compare)`:

```
(define-type (lattice (t type))
  (productof (bottom t) (join (subr pure (t t) t)) (same (subr pure (t t) bool))))
(define solve
  (poly ((t type))
    (subr spin ((lattice t) graph (subr pure (int (listof t acyclic)) t)) (arrayof t const))) …)
```

`solve` sweeps every node, joining each value with its equation's right
side, until a sweep changes nothing. The values live in an array at a
region of a `letfreeze`, so the solution leaves at `const`. The instance
asks which nodes reach node 3, in the lattice of booleans under `or`.
The answer is `(#t #t #t #t #t #f)`: all but node 5.

`spin` is there because termination depends on two facts no type
states: the lattice has finite height, and the step is monotone. The
checker's diagnostic says what it could not see: "the call of `sweep` in
`sweep` (it counts up, but nothing fixed bounds the count above), the
call of `loop` in `loop`". A lattice dictionary with a height bound,
the number of strict increases a value can make, would bound `loop` by
nodes × height. That could let a solver drop `spin` if the bound were
something size-change could use. That is a question for the
termination checker (§5).

### 3.3 Semirings: `semiring-closure.fx`

```
(define-type (semiring (t type))
  (productof (zero t) (one t) (plus (subr pure (t t) t)) (times (subr pure (t t) t))))
(define closure
  (poly ((t type)) (subr spin ((semiring t) (built t)) (matrix t))) …)
```

The closure is Floyd–Warshall–Kleene's triple loop, correct for
semirings in which every element's star is the unit (booleans, and
min-plus over non-negative weights). It copies the matrix into a region,
closes it in place and freezes it. Its type has no region effect, and
`spin` only for loops bounded by `n`.

With `min-plus` on the weights 0 -2→ 1 -3→ 2 -1→ 0 and 0 -9→ 2, the
distances from 0 are `(0 2 5)` and from 2 `(1 3 0)`. With `bool-sr` on
the same edges, 2 reaches 1. One algorithm, two problems.

A detail on the way. A matrix built in order and never written is
`acyclic`; one closed by writes leaves its `letfreeze` at `const`. And
arrays are invariant in their element type, so a list of `(arrayof int
acyclic)` rows is refused where `(arrayof int const)` rows are
expected. The example takes `(built t)` = `(arrayof (arrayof t acyclic)
acyclic)` and gives `(matrix t)` = `(arrayof (arrayof t const) const)`.
Covariance of frozen arrays in their elements' frozen region, as Kayak's
covariance of frozen lists (`docs/fx26.md`, "Frozen data is covariant"),
would remove the second type.

### 3.4 What is not tried

- **Erwig's decomposition.** `match` returns the rest of the graph,
  which for a persistent graph needs a persistent map
  (`sets-and-maps.md` §3.3). The order dependence of `ufold` is
  discussed in §2.1, not shown.
- **Mokhov's algebra.** A generative type with four constructors would
  check, but its laws would be a promise. FX-26 could state them as
  `assert`ed specifications (`docs/fx26.md`, "Specifications") and test
  them with `fixpt test`, but not prove them.

## 4. Recommendation

1. **A traversal primitive, in a library first.** Depth-first and
   breadth-first search from roots, returning an `acyclic` spanning
   forest, with the visited set masked (`dfs-forest.fx`), plus the edge
   classification (tree, back, cross, forward) as data. Algorithms are
   then `pure` folds. `spin` stays only on the search, which a
   `confirm`-style proof (`docs/research/confirmation.md`) or a fuel
   argument might remove later.
2. **A least-fixpoint operator over a lattice dictionary**
   (`lattice-fixpoint.fx`). Bottom, join and equality, with an optional
   height bound for termination. This one operator covers dataflow,
   reachability and Datalog-style rules. It is also where Paige's and
   Liu–Stoller's work would apply: incremental maintenance of the
   solution as the graph changes.
3. **Semiring closure as a library** over a semiring dictionary
   (`semiring-closure.fx`), for path problems.
4. **Decomposition folds only as `nondet`**, or with a promise of order
   independence, as for hash-ordered walks (`sets-and-maps.md` §5.1).
5. **Nothing in the kernel yet.** All of this checks today as library
   code. The cases for kernel support are the ones the sets note gives:
   frozen persistent structures for the graphs themselves, and a
   compiler that knows what the operations mean.

The dictionaries now come in four shapes: `(eq, hash)`, `(eq, compare)`,
lattice and semiring. If they are to be derived or resolved implicitly,
that is one design for all of them, not four.

## 5. Open questions for the user

1. Should the termination checker learn to use a lattice height bound,
   or a count of nodes not yet visited, so that a search or a solver
   need not say `spin` (§3.2)? Or is `spin` on the solver acceptable,
   given that its result is still a value?
2. Should frozen arrays be covariant in their elements' frozen region
   (§3.3), as frozen lists already are?
3. Is a graph library (traversal, fixpoint, closure) wanted before
   kernel sets and maps (`sets-and-maps.md` §5), as a client that would
   show what the kernel types need?
4. Are Mokhov's laws worth stating as specifications, as a test case for
   `assert` on algebraic laws?

## The toy programs

| file                    | shows                                                                                         | checked, ran | result                                      |
| ----------------------- | --------------------------------------------------------------------------------------------- | ------------ | ------------------------------------------- |
| `dfs-forest.fx`         | a search from a cyclic `const` graph to an `acyclic` forest, then a `pure` fold over it        | yes          | `(5 4 0 1 3 2)`                             |
| `lattice-fixpoint.fx`   | a least-fixpoint solver over a lattice dictionary; which nodes reach 3                         | yes          | `(#t #t #t #t #t #f)`                       |
| `semiring-closure.fx`   | one closure, two semirings: shortest paths and reachability                                    | yes          | `((0 2 5) (1 3 0) (1))`                     |

## Sources

Searched 2026-11-01. "Record" means a bibliographic record, abstract,
library documentation or search results were seen, and content is
otherwise from memory. "Memory" means nothing was reached.

| source                                                                                                                         | where                                                                                                                                                                                    | seen                                   |
| ------------------------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------- |
| Erwig, "Inductive graphs and functional graph algorithms", JFP 11(5), 2001, pp. 467–492                                        | https://www.cambridge.org/core/services/aop-cambridge-core/content/view/2210F7C31A34EA4CF5008ED9E7B4EF62/S0956796801004075a.pdf; FGL docs, https://downloads.haskell.org/ghc/6.8.3/docs/html/libraries/fgl/Data-Graph-Inductive-Graph.html | record                                 |
| Mokhov, "Algebraic graphs with class (functional pearl)", Haskell Symposium 2017, pp. 2–13, doi 10.1145/3122955.3122956         | https://eprints.ncl.ac.uk/239461; `algebraic-graphs` 0.5, https://hackage-origin.haskell.org/package/algebraic-graphs-0.5/docs/src/Algebra.Graph.html                                     | record                                 |
| King, Launchbury, "Structuring depth-first search algorithms in Haskell", POPL 1995                                            | cited by Erwig (above); `alex`'s DFS module, https://hackage.haskell.org/package/alex-meta-0.3.0.13/docs/src/DFS.html; Launchbury's slides, https://www.cse.chalmers.se/edu/course.2016/DIT960/slides/graph-algorithms-with-a-functional-flavour.pdf | record (title and venue not confirmed) |
| Hong, Chafi, Sedlar, Olukotun, "Green-Marl: a DSL for easy and efficient graph analysis", ASPLOS 2012                          | https://www.cl.cam.ac.uk/~ey204/teaching/ACS/R244_2017_2018/papers/hong_asplos_2012.pdf                                                                                                  | record                                 |
| Zhang, Yang, Baghdadi, Kamil, Shun, Amarasinghe, "GraphIt: a high-performance graph DSL", OOPSLA 2018                          | https://arxiv.org/abs/1805.00923                                                                                                                                                         | record                                 |
| Plump, "The design of GP 2", WRS 2011; Campbell, Courtehoute, Plump, CALCO 2019                                                 | https://arxiv.org/pdf/1204.5541; https://eprints.whiterose.ac.uk/195068/; https://eprints.whiterose.ac.uk/195047/                                                                        | record                                 |
| Liu, Stoller, "From Datalog rules to efficient programs with time and space guarantees", TOPLAS 31(6), 2009; PPDP 2003          | https://www3.cs.stonybrook.edu/~stoller/rules-TOPLAS.html                                                                                                                                | record                                 |
| Dolan, "Fun with semirings: a functional pearl on the abuse of linear algebra", ICFP 2013                                       | described in https://arxiv.org/pdf/2202.07577                                                                                                                                            | record                                 |
| Carré, *Graphs and Networks*, 1979; Backhouse, Carré, "Regular algebra applied to path-finding problems", 1975                  | —                                                                                                                                                                                        | memory                                 |
| Kildall, "A unified approach to global program optimization", POPL 1973                                                         | —                                                                                                                                                                                        | memory                                 |
| Magnusson, Hedin, circular reference attributed grammars (JastAdd)                                                              | —                                                                                                                                                                                        | memory                                 |
| Malewicz et al., "Pregel", SIGMOD 2010; GraphBLAS; Ligra (Shun, Blelloch, PPoPP 2013)                                            | —                                                                                                                                                                                        | memory                                 |
| Gibbons, "An initial-algebra approach to directed acyclic graphs", MPC 1995                                                     | —                                                                                                                                                                                        | memory                                 |
| Fegaras, Sheard, POPL 1996; Ghani, Hamana, Uustalu, Vene, 2006; Hamana, TLCA 2009; Oliveira, Cook, ICFP 2012                     | —                                                                                                                                                                                        | memory                                 |
| FX-26: `docs/fx26.md` ("Freezing", "Finite data", "Frozen data is covariant", "Specifications"); `docs/research/sets-and-maps.md` | this repository at `71de5b8`                                                                                                                                                             | read                                   |
