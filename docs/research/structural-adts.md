# Structural datatypes and GADTs, without generativity all the way down

Research note, 2026-09-30. No code was changed. The user's question: how
deeply is FX-26's GADT design (`gadts.md`, N1–N6) tied to generative
types? Could distinct ADTs and GADTs come instead from μ types, unions
and intersections, and value constructors that each give a singleton
type, with generativity kept only where abstraction needs it? Where does
that break, and what would lemmas have to supply?

Sources are listed at the end with where each was read and how much of
it. A claim marked *(from memory)* was not checked against a source.
FX-26 facts cite files in this repository. Every FX-26 program quoted
as "today" is a file under `docs/research/examples/structural-adts/`,
checked with `target/release/fixpt check` (both checkers agree on each)
and run with `fixpt eval`; syntax marked `; PROPOSED` exists nowhere.

## 0. The answer, up front

- **Plain ADTs: yes, and FX-26 already has them.** Sums and products are
  structural, a one-tag sum is a constructor's singleton type (`(sum
  circle 3)` synthesizes `(sumof (circle int))`), a multi-tag sum is the
  union of its tags' singletons, and `define-type` ties the knot through
  μ. What makes two datatypes distinct is their tags, not a name.
  Freeman and Pfenning's datasort refinements need nothing new: `even`
  and `odd` lists, or expressions that compute an `int`, are sums that
  width subtyping and equi-recursion already relate
  (`even-odd.fx`, `eval-datasorts.fx`).
- **GADTs: yes, for a large fragment, by guarded variants.** Xi, Chen and
  Chen, who introduced the idea, *define* a guarded recursive datatype as
  `μt.λα. ∃ᾱ₁[τ₁ ≡ α].σ₁ + … + ∃ᾱₖ[τₖ ≡ α].σₖ` (POPL 2003, §2.2): a
  μ over a sum whose variants carry a type equation (a *guard*) and
  existentials. Nothing in that reading needs a name. Add to FX-26's
  sums a guard and existential binders per variant, and a GADT is a
  structural type: `(expr int)` unfolds to the variants whose guards hold
  for `int`, which is a plain regular sum, the datasort `int-exp`
  exactly. Matching a variant adds its guard to the arm's facts, which is
  GADT refinement; FX-26's facts machinery for sizes (N5, and the
  conjunctive facts of `or` and `and`) is where it goes.
- **Variance comes out right on its own.** A guard is an equation, so
  comparing `(bad A) ≤ (bad B)`, whose one variant is guarded by `a =
  S`, asks whether `A = S` implies `B = S`,
  which fails unless `A = B`. Scherer and Rémy's counterexample (`gadts.md`
  E8) is refused by comparison, with no declared variance and no
  upward-closure analysis. Indices that no guard mentions are as
  covariant as their uses.
- **Where it breaks:**
  1. *Expansive* families, whose recursion mentions the family at a
     growing argument (nested types; an existential whose index grows,
     like `fst : exp (a × b) → exp a`): subtyping between them is
     undecidable (`nonregular-subtyping-survey.md` §2). That need not
     mean refusing them. §3.5 takes the user's position: accept them as
     family-application nodes, compared by congruence at a variance the
     checker derives, then by lemmas, then by unfolding within a depth
     bound, with three answers: proved, refuted with a path, or unknown
     with the growing chain. Only "unknown" asks for a lemma, and it is
     never taken as "yes". Of the three expansive families worked there,
     one comparison needs a lemma the programmer writes.
  2. *Size arithmetic past linear*, or facts the checker's
     Fourier–Motzkin step does not find: lemmas, of a new kind (§3.4).
  3. *Correlations inside one tag* (Castagna's `WrongTree`: a red node
     whose left child is red and right black, or the reverse): unions of
     same-tag payloads, nondeterministic tree automata, EXPTIME-hard to
     compare. Keep
     FX-26's sums tag-deterministic and refuse these (§3.2).
  4. *Phantom indices and invariants*: structurally, an index no guard
     constrains means nothing (`gadts.md` E7), and no structural type can
     say "sorted" or "validated". These are abstraction, and stay
     generative.
- **What generativity still buys**: unforgeability and invariants
  (abstraction), phantom indices, non-regular recursion for free, O(size
  of arguments) comparison, and names in messages. It does not buy
  distinctness (tags do that), nor a different run-time representation
  (FX-26's `up-` and `down-` are the identity). So: **structural by
  default, including GADTs; `define-generative` as a wrapper where a type
  must mean more than its structure**, which is the split Unison and Roc
  have reached from the other side (§5), and the one Freeman and Pfenning
  already drew in 1991, with the default the other way (§1.2).
- **Lemmas must supply** (§3.4, §3.5): subtyping between expansive
  families where the checker's own generalization fails (the existing
  `proves` lemmas; their body rule carries over, and today's checker
  proves them for generative nested families, `seq-lemmas.fx` and
  `term-lemmas.fx`); index facts the
  decision procedure misses (new: equations over sizes, proved by a
  *terminating* function, since induction, unlike FX-26's coinductive
  subtyping lemmas, is unsound if the proof may loop); and cases the
  union and intersection rules miss (the existing mechanism, with
  `typecase` in lemma bodies). The existing mechanism suffices for the
  first and third; the second needs extending.

## 1. What FX-26 has today, and what it shows

### 1.1 Constructors, singletons, unions

| FX-26 today                                        | Structural reading                                            | Shown by                        |
| -------------------------------------------------- | ------------------------------------------------------------- | ------------------------------- |
| `(sum tag e) : (sumof (tag T))`                    | a constructor applied: its singleton-tag type                 | `constructor-widens-refused.fx` |
| `(sumof (t₁ T₁) … (tₙ Tₙ))`                        | the union of `n` singleton-tag types                          | `docs/fx26.md`, immutable data  |
| width subtyping on sums                            | inclusion of those unions                                     | `even-odd.fx`                   |
| `define-type` with a cycle; `(mu t T)`             | μ, equi-recursive, a cycle through a constructor              | `docs/fx26.md`, recursive types |
| `tagcase`'s `else` sees the tags not named         | difference, the only negation needed                          | `logical-types.md` §1           |
| a family mentioning itself at fixed descriptions   | finitely many instances: regular                              | `family-nonexpansive.fx`        |
| a family mentioning itself at growing descriptions | refused: "`grow` expands without end"                         | `family-expansive-refused.fx`   |
| `define-datatype` constructors                     | globals returning the *whole* datatype, not their singleton   | `constructor-widens-refused.fx` |
| `(nlist T n)`, facts from `null?`                  | a built-in guarded family: `nil` when `n = 0`, else `n = m+1` | `docs/research/sizes.md`        |
| `define-generative`                                | a name, opaque to comparison, transparent to safety           | `generative-types.md`           |

The one thing on this list that works against the structural reading is
the last-but-two: `(circle 3)` has type `shape`, so it cannot be used at
`(sumof (circle int))`, though the `sum` form it expands to can
(`constructor-widens-refused.fx`, refused: "a just-circle is expected
here, and this is a shape").

### 1.2 Datasort refinements are already here

Freeman and Pfenning's refinements are "recursively defined subtypes of
user-defined datatypes", declared as `rectype`s over a datatype's
constructors, "which one can think of as subsets" (PLDI 1991, §1). In
FX-26 the refinement and the datatype are the same kind of thing, a
sum, and the refinement relation is ordinary subtyping:

```
(define-type lst  (sumof (nil unit) (cons (productof (hd int) (tl lst)))))
(define-type even (sumof (nil unit) (cons (productof (hd int) (tl odd)))))
(define-type odd  (sumof (cons (productof (hd int) (tl even)))))
(define head-odd (subr pure (odd) int)
  (lambda (l) (tagcase l (cons (hd tl) hd))))      ; no nil arm: an odd has none
```

`(define as-list lst e2)` accepts an `even` as a `lst`; `(define bad even
o1)` is refused (`even-odd-refused.fx`). Freeman and Pfenning needed
intersection types for this, because their constructors are functions of
one ML type and so must carry every refinement at once: `cons : (α ∗ α
?nil → α singleton) ∧ (α ∗ α singleton → α list) ∧ …` (§1). In FX-26 the
constructor is the `sum` form, which synthesizes the exact singleton of
its payload, and subsumption does the rest. **Intersections are not
needed for constructors.** They are needed for *functions* over several
refinements, which is Q7's `overload` (`logical-types.md` §8.1).

They also drew the line the user is asking about, the other way round:
"should recursive types be generative (as the ML datatype construct), or
should they be nongenerative …? Our conclusion is that generative types
should be the principal notion, but that non-generative recursively
defined subtypes can make a type system significantly more powerful and
useful" (§1). FX-26's sums were structural from FX-91 on, so here the
structural notion is the principal one already.

### 1.3 A typed evaluator today, as datasorts

`eval-datasorts.fx` is the GHC user's guide's `Term a` evaluator with one
structural type per index value:

```
(define-type int-exp
  (sumof (int-e int)
         (add (productof (l int-exp) (r int-exp)))
         (if-e (productof (c bool-exp) (t int-exp) (f int-exp)))))
(define-type bool-exp
  (sumof (bool-e bool)
         (is-zero int-exp)
         (if-e (productof (c bool-exp) (t bool-exp) (f bool-exp)))))
(define-type any-exp …)            ; all of them, untyped: both are subtypes of it
(define eval-int (subr pure (int-exp) int)
  (letrec ((eval-int (subr pure (int-exp) int) (lambda (e) (tagcase e …)))
           (eval-bool (subr pure (bool-exp) bool) (lambda (e) (tagcase e …))))
    eval-int))
```

It checks as `pure` (size-change descends the `tagcase` parts), runs to
`42`, and `1 + #t` cannot be built at `int-exp`
(`eval-datasorts-refused.fx`: "a int-exp is expected here, and this is a
(sumof (bool-e bool))"). `typecheck.fx` goes from `any-exp` to `(sumof (i
int-exp) (b bool-exp) (wrong unit))`; no conversion is needed to go back,
since the typed types are subtypes of the untyped one. With nominal
GADTs, `Term Int` and an untyped AST are unrelated types.

What this cannot do: one `eval` for every index (two functions, or an
`overload`), and indices that are not a finite set (`pair` at any `b`
and `c`). `expr-refinement-refused.fx` is the attempt with a type
parameter: an arm learns nothing about `a` ("a a is expected here, and
this is a bool"). That is the step guards add.

### 1.4 The red-black example

Castagna's essay takes Okasaki's red-black trees and states three of the
four invariants as recursive set-theoretic types (`RBTree`, `BTree`,
`RTree`, §2), leaving out "that every path from the root to a leaf should
contain the same number of black nodes" (fn. 7). `red-black.fx` states
the same three in FX-26 today; `red-black-refused.fx` refuses a red node
with a red child. The fourth invariant is a size index (§2.6). And his
`balance` needs `WrongTree(α) = (Red, α, RTree(α), BTree(α)) | (Red, α,
BTree(α), RTree(α))`, two payloads under one tag, plus a negation type
`β \ Unbalanced(α)`: the part FX-26 should not take (§3.2).

## 2. How it would look in FX-26

Everything in this section is proposed.

### 2.1 The type forms

One addition to sum variants, and one to what a family may say:

```
(sumof (tag T) …)                                              ; today
(sumof (tag (when P …) T) …)                                   ; PROPOSED: a guarded variant
(sumof (tag (exists ((b kind) …) (when P …)) T) …)             ; PROPOSED: with existentials

P ::= (= T T)          a type equation
    | (= s s) | (<= s s)   a size fact, as N5's
```

- **A guard** holds or not for given descriptions. For ground ones it is
  decided at once, and a variant whose guard fails is simply absent: the
  sum has that tag or it does not. A sum left with no variants is empty;
  `(sumof)` is accepted today, and a `tagcase` on it needs no arms (a
  scratch probe).
- **Existentials** are binders like a `poly`'s (an `exists` with no
  `when` hides a type without constraining it), compared under a binder
  environment as `poly` bodies already are (`recursive-subtyping.md`,
  "Where this stands"). Kinds `type` and `size` first; `region` and
  `effect` existentials are left out (§4.1).
- **The family** is the existing `define-type` with parameters, which may
  mention itself at other descriptions only non-expansively: at
  descriptions built from the family's own parameters used whole, from
  the variant's existentials, and from closed types. `(expr bool)` and
  `(expr b)` inside `(expr a)` are fine; `(grow (productof (l a) (r a)))`
  inside `(grow a)` is not, as today. This is the "non-expansive"
  condition of Kennedy and Pierce *(from memory, via
  `nonregular-subtyping-survey.md` §2)*, and it is what keeps the
  instances of a family finitely many up to renaming of binders.

### 2.2 How a `define-datatype` would read

`gadts.md`'s N4 syntax is kept; only its meaning changes, from a nominal
family to sugar for guards:

```
(define-datatype (expr (a type))                                          ; PROPOSED
  (int-e   int                                         => (expr int))
  (bool-e  bool                                        => (expr bool))
  (add     (expr int) (expr int)                       => (expr int))
  (is-zero (expr int)                                  => (expr bool))
  (if-e    (expr bool) (expr a) (expr a))
  (pair    ((b type) (c type)) (expr b) (expr c)       => (expr (productof (l b) (r c)))))
```

reads as

```
(define-type (expr (a type))                                              ; PROPOSED
  (sumof (int-e   (when (= a int)) int)
         (bool-e  (when (= a bool)) bool)
         (add     (when (= a int)) (productof (l (expr int)) (r (expr int))))
         (is-zero (when (= a bool)) (expr int))
         (if-e    (productof (c (expr bool)) (t (expr a)) (f (expr a))))
         (pair    (exists ((b type) (c type)) (when (= a (productof (l b) (r c)))))
                  (productof (l (expr b)) (r (expr c))))))
```

A variant `(k fields … => (F D …))` becomes `(k (exists (its binders)
(when (= param D) …)) (productof fields …))`; a variant with no `=>` has
no guard. This is Xi, Chen and Chen's translation (§2.2), with FX-26's sums
for their `+`.

**Constructors become forms**, not globals: `(pair x y)` is `(sum pair
(product (l x) (r y)))`, and synthesizes its singleton, `(sumof (pair
(productof (l (expr B)) (r (expr C)))))`. The singleton says nothing
about `a`; checked against `(expr A)`, subsumption asks for `A =
(productof (l b) (r c))` for some `b`, `c`, found by unification (`b :=
B`, `c := C`). So `(int-e 1)` fits `(expr int)`, fails `(expr bool)`
(guard `bool = int` refuted), and fails `(expr a)` for a rigid `a` unless
the facts say `a = int`. Making constructors forms also removes today's
read of a global per constructor call (a scratch probe of `(define c1
(circle 3))` reports `c1 : shape ! (read (globals circle))`).

### 2.3 What `(expr int)` is

With `a := int`, the guards decide: `int-e`, `add` and `if-e` stay;
`bool-e` and `is-zero` go (`bool = int` is false); `pair` goes (`int =
(productof …)` has no solution). What is left is

```
(sumof (int-e int) (add (productof (l (expr int)) (r (expr int))))
       (if-e (productof (c (expr bool)) (t (expr int)) (f (expr int)))))
```

which is `int-exp` of `eval-datasorts.fx`, and `(expr bool)` is its
`bool-exp`. A family at ground descriptions is the datasort system of
§1.3, generated. The two would be each other's subtypes, and the
existing algorithm compares them.

### 2.4 Matching narrows

A `tagcase` on `e : (expr a)`, `a` rigid (a `poly` binder in a declared
signature), checks each arm with the variant's guard added to the facts
and its existentials bound fresh and rigid:

```
(define* ev (poly ((a type)) (subr spin ((expr a)) a))                    ; PROPOSED
  (lambda (e)
    (tagcase e
      (int-e n n)                                       ; a = int: n : int is an a
      (bool-e b b)                                      ; a = bool
      (add (x y) (+ (ev x) (ev y)))                     ; a = int; ev at int
      (is-zero x (= (ev x) 0))                          ; a = bool; ev at int
      (if-e (c t f) (if (ev c) (ev t) (ev f)))          ; no guard: ev at bool, at a
      (pair (x y) (product (l (ev x)) (r (ev y)))))))   ; b, c fresh; a = (productof (l b) (r c))
```

`ev` calls itself at `int`, `bool`, `a`, `b` and `c`: polymorphic
recursion, which a declared `poly` already allows (`gadts.md` E6).

**How the facts are used**, in both checkers:

- **Type equations are solved as substitutions.** `a = T`, `a` rigid:
  within the arm, `a` is `T` (the expected type `a` of the arm's body is
  `int`). `T₁ = T₂`, neither a variable: decompose, since FX-26's type
  formers are injective (a sum by its tags and their payloads, a product
  by its labels, a `subr` by its effect, parameters and result). A
  family application is *not* injective in general (a phantom parameter,
  or one reachable only through an empty type), so an equation between
  two applications is decomposed by unfolding them, never by equating
  their arguments (§3.5). A clash
  refutes the guard: the arm is unreachable, and not required. This is
  the "given" half of GHC's approach, and FX-26 has the signature in hand
  (`gadts.md`, "What N4 would have to teach the checker", point 2).
  Simonet and Pottier show that *inferring* such constraints is
  intractable (nonelementary, after Vorobyov; TOPLAS 2007, p. 37); checking
  against a declared signature needs only unification.
- **An equation whose solution is recursive** (`a = (productof (l a) (r
  int))`) is not a clash here, as it is in ML: under equi-recursion it
  has the solution `(mu x (productof (l x) (r int)))`, which the arm
  should take as `a`'s value. Equality over infinite trees is decidable
  (Maher 1988, cited by Simonet and Pottier, p. 37). *I have not worked
  through whether any real program needs this; refusing it (an occurs
  check) is the safe first step.*
- **Size facts** go where N5's already do. The recent conjunctive-facts
  work made each branch carry a list of facts (commit `bdda0ff`, in Rust
  `test_facts` and FX's `check-facts.fx`); a guard's facts join that
  list. Type equations are a second kind of entry in the same list, as
  `gadts.md` N4 planned ("N4 will put type equalities in the same
  context", `sizes.md`).
- **The scrutinee itself** is narrowed where it is a variable: in the
  `int-e` arm, `e : (sumof (int-e int))`. Today an arm binds only the
  payload, so `typecheck.fx` rebuilds each node; narrowing the variable
  is Q7's occurrence typing (`logical-types.md` §6.2), by binding, not by
  name.
- **Existentials may not escape** the arm, as a `letregion`'s region may
  not leave its body (`gadts.md` E4).
- **Exhaustiveness** is today's rule applied after pruning: the arms
  must cover the variants whose guards the facts do not refute. Exact
  exhaustiveness with GADTs is undecidable in general (Garrigue and Le
  Normand 2015, as cited by Dunfield and Krishnaswami 2019, §4); where
  the checker cannot refute a guard, the program writes the arm (an
  `(error …)`, which is `pure` and `void`) or a lemma (§3.4).

### 2.5 Worked examples

**Equality witness.** Dunfield and Krishnaswami encode `eq` and `refl`
as "the type 1 ∧ (s = t), which can be constructed as a unit value only
under the constraint that s equals t" (POPL 2019, fn. 2). Structurally:

```
(define-type (eq (a type) (b type)) (sumof (refl (when (= a b)) unit)))    ; PROPOSED
(define cast (poly ((a type) (b type)) (subr pure ((eq a b) a) b))
  (lambda (w x) (tagcase w (refl u x))))           ; in the arm, a = b
(define ok (eq int int) (sum refl #u))             ; the guard holds
(define no (eq int bool) (sum refl #u))            ; refused: int = bool is refuted
```

Anyone may write `(sum refl #u)`, but it fits `(eq A B)` only where the
checker can show `A = B`. So the witness is unforgeable in the way that
matters, with no generativity, which is what `gadts.md` E2 found missing
today ("anyone may build an `(eq int bool)` from two functions").

**Length-indexed vectors**, the user's own version of `nlist`:

```
(define-type (vec (t type) (n size))                                      ; PROPOSED
  (sumof (vnil  (when (= n 0)) unit)
         (vcons (exists ((m size)) (when (= n (+ m 1))))
                (productof (hd t) (tl (vec t m))))))
(define vhead (poly ((t type) (n size)) (subr pure ((vec t (+ n 1))) t))
  (lambda (v) (tagcase v (vcons (hd tl) hd))))     ; vnil's guard, n + 1 = 0, is refuted
```

This is Xi, Chen and Chen's own example, `λα.μt.λa:nat. ∃{0 = a}.1 +
∃{a′:nat, a′ + 1 = a}.α ∗ t(a′)` (§5), "a form of guarded datatype
constructor, where the guards are constraints on type index expressions
(rather than on types)". `nlist` stays as it is, a list of pairs the
checker knows; `vec` shows the same facts serving a user's sum. A native
`vhead` then needs no tag test at all: the checker knows the only tag.

**Typed format strings** (printf), a guard on a procedure type:

```
(define-type (fmt (a type))                                               ; PROPOSED
  (sumof (done  (when (= a string)) unit)
         (text  (productof (s string) (k (fmt a))))
         (int-f (exists ((r type)) (when (= a (subr pure (int) r)))) (fmt r))
         (str-f (exists ((r type)) (when (= a (subr pure (string) r)))) (fmt r))))
(define format (poly ((a type)) (subr pure ((fmt a)) a))
  (letrec ((go (poly ((a type)) (subr pure ((fmt a) string) a))
             (lambda (f acc)
               (tagcase f
                 (done u acc)                                          ; a = string
                 (text (s k) (go k (string-append acc s)))
                 (int-f k (lambda ((n int)) (go k (string-append acc (int->string n)))))
                 (str-f k (lambda ((s string)) (go k (string-append acc s))))))))
    (lambda (f) (go f ""))))
;; (format (sum int-f (sum text (product (s " apples") (k (sum done #u))))))
;;   : (subr pure (int) string)
```

Two things here I am not sure of. The guard equates `a` with a `subr`
type, effect included, so the closures must be `pure`; whether the
termination check accepts `go`'s calls from inside the closures it
returns (each on a part `k` of `f`) is untested. If not, `fmt` takes the
effect as a parameter, `(fmt (e effect) (a type))`. And a local `letrec`
binding a `poly` may need a form FX-26 does not have yet.

**Red-black trees with the fourth invariant**, black height as a size:

```
(define-type (black-rb (n size))                                          ; PROPOSED
  (sumof (leaf  (when (= n 0)) unit)
         (black (exists ((m size)) (when (= n (+ m 1))))
                (productof (v int) (l (rb m)) (r (rb m))))))
(define-type (rb (n size))
  (sumof (leaf  (when (= n 0)) unit)
         (black (exists ((m size)) (when (= n (+ m 1))))
                (productof (v int) (l (rb m)) (r (rb m))))
         (red   (productof (v int) (l (black-rb n)) (r (black-rb n))))))
```

All four invariants, structurally and non-expansively (`(rb m)` with `m`
an existential). Insertion returns a tree of height `n` or `n + 1`: a
result type `(exists ((m size)) …)` with a fact, which is N5c's planned
existential result (`sizes.md`), and the arithmetic stays linear.

### 2.6 Where intersections and unions come in

- **Unions** (Q7): `(union T …)` of disjoint shapes. Every sum has the
  same shape (a bloblet of kind 36), so a union of sums *is* a sum, and
  two sums with one tag must agree on its payload. The union of `(expr
  int)` and `(expr bool)` is not a union at all: `if-e` has different
  payloads in each. It is `(exists ((a type)) (expr a))`, or the
  untyped `any-exp`. In a structural GADT, "any index" is an
  existential, not a union.
- **Intersections of procedure types** (Q7's `overload`) are for
  functions with several refinements, where no single index says it:
  `append` of two `even`s is `even` and of two `odd`s is `even`, with
  Davies's value restriction and no distributivity. Parametric guards
  replace most of them (one `ev` in place of `eval-int ∧ eval-bool`).
- **Meets of data types**, for narrowing through nested patterns, can be
  computed rather than written: the meet of two sums is their common tags
  with the meets of their payloads, a product construction on the two
  graphs. It is an operation of the checker, not a new type former, and
  only for immutable data (the meet of two `ref` types is one of them or
  `void`, never a new cell type: Davies and Pfenning's unsoundness).

## 3. Decidability, algorithms, and lemmas

### 3.1 The fragments

| Fragment                                                   | Subtyping decidable?                | Cost, as I understand it                            | FX-26                                |
| ---------------------------------------------------------- | ----------------------------------- | --------------------------------------------------- | ------------------------------------ |
| regular sums and products, width, equi-recursion           | yes                                 | `O(#A·#B)` pairs on one trail                       | today (`recursive-subtyping.md`)     |
| plus unions merged by tag, meets computed                  | yes                                 | polynomial; a meet is product-sized                 | Q7 plans unions                      |
| plus the same tag with several payloads (nondeterministic) | yes                                 | EXPTIME-hard (Seidl, via Davies §1.6.8)             | refuse (§3.2)                        |
| plus arrows with ∨, ∧, ¬, semantic subtyping               | yes (Frisch, Castagna, Benzaken)    | exponential; algorithm and data structures involved | declined (`logical-types.md` §8.4)   |
| non-expansive families, ground descriptions                | yes                                 | finitely many instances: the regular case           | today, without guards                |
| plus guards with rigid variables: type equations           | yes, per question                   | unification per guard; binder environments on trail | proposed                             |
| plus linear size guards                                    | Presburger: yes                     | FX-26's Fourier–Motzkin is sound, incomplete on ℕ   | N5b, N5c                             |
| non-linear size guards                                     | no *(from memory: Hilbert's tenth)* | —                                                   | lemmas                               |
| expansive families (nested; growing existentials)          | equality yes, subtyping no          | equality: DPDA equivalence, impractical             | generative, or congruence and lemmas |
| inferring guards (no signatures)                           | decidable for equations             | nonelementary (Simonet and Pottier, p. 37)          | not done: signatures                 |
| exact exhaustiveness with GADTs                            | no (Garrigue and Le Normand)        | —                                                   | refute what the facts can; write arm |

Notes:

- **Why guarded, non-expansive families stay decidable** (my argument,
  not from a paper). A question `(F D) ≤ (G E)` unfolds to sums whose
  variants' guards mention `D` and `E`. For each left variant whose guard
  the facts do not refute, find the right variant of the same tag, and
  show that under the left guard the right one holds (unification, then
  solving for the right's existentials) and the payloads compare. The
  payloads mention `F` and `G` again only at the family's parameters,
  at existentials, or at closed types, so the pairs reaching the trail
  are finitely many up to renaming of binders, which is exactly the case
  the `poly` fix handles today. The trail's cycle check needs pairs
  compared up to that renaming, as for `poly`.
- **The complexity of the whole** is the existing algorithm's times the
  cost of unification per guard, as far as I can see. I have not
  measured anything: nothing is built.

### 3.2 Keep sums tag-deterministic

Davies's datasort bodies allow one constructor twice (`s = c S₁ ⊔ c
S₂`), and his inclusion algorithm then needs "the product of R₁ minus U₁
and R₂ minus U₂" (§5.5); he notes inclusion for such grammars is
EXPTIME-hard, "by an easy reduction from … inequivalence of finite tree
automata, … EXPTIME-complete by Seidl" (§1.6.8). Castagna's `WrongTree`
is this case. FX-26's sums allow each tag once, so the tag at a node
fixes the payload's type: a deterministic top-down automaton, which the
current trail compares in polynomial time. Unions of disjoint shapes
(Q7) keep that property; unions that put two payloads under one tag do
not. **Recommendation: refuse them.** Correlations between fields are
said by guards (a size shared by two children, as `rb`), by a finer tag
(`red-left`, `red-right`), or by an `overload` on the function that
needs them. The cost is Castagna's `balance` type, which also needs
negation.

### 3.3 What the checker does where it cannot decide

- **Expansive families** are refused today ("`grow` expands without
  end"), and where one is wanted it is `define-generative` (N1),
  compared by name and arguments. Proposed instead (§3.5): accept them,
  as the unmerged prototype (`nonregular-prototype.md`) did, as a family
  application node (`Ty::App`), with congruence first, lemmas next,
  unfolding on demand within a depth bound last, and three answers,
  proved, refuted with a path, or unknown with the growing chain; an
  unknown refuses the program and says which lemma would close it.
  Dunfield and Krishnaswami
  propose the same laziness for user type constructors: "treat
  user-defined type constructors like List as monotypes, expanding the
  definition only as needed: when checking an expression against a user
  type constructor, and for pattern matching" ("Discussion and related
  work", under "Extensions").
- **Size facts not found** leave a size `finite` or an arm required, as
  today (`sizes.md`: "Anything not shown is not assumed").
- **Union and intersection rules** are the syntactic ones of
  `logical-types.md` §6.1, sound and incomplete; the gaps (distributing
  a union through a product) are for lemmas.

### 3.4 What lemmas must supply

FX-26's lemmas today (`docs/fx26.md`, "Lemmas"): a definition of type
`(proves (poly (binders) (<= A B) hypotheses …))`, whose body is a
*guarded structural identity* (it takes apart what it was given and
rebuilds the same tags and labels, using itself only under a
constructor it rebuilt), with effect `spin`, never run, erased. Its
existence lets subtyping use `A ≤ B` where its rules fail.

| What is missing                              | What the lemma states               | Proof obligation                              | Existing mechanism?                                |
| -------------------------------------------- | ----------------------------------- | --------------------------------------------- | -------------------------------------------------- |
| subtyping the checker leaves unknown         | `(<= (F X) (G Y))` given hypotheses | guarded structural identity, may not end      | yes; needs family nodes to match against (§3.5)    |
| a guard or size fact the procedure misses    | `(= s s′)`, `(<= s s′)` over sizes  | a *terminating* proof by induction            | no: new propositions, and totality                 |
| an arm the checker cannot show unreachable   | that a guard is unsatisfiable       | as the row above, concluding a contradiction  | no; or write the arm with `error`                  |
| union and intersection rules' incompleteness | `(<= A B)` between two data types   | guarded identity, with `typecase` in the body | yes, once `typecase` exists (`logical-types` §6.3) |

- **Subtyping lemmas stay coinductive.** Subtyping is a greatest fixed
  point, so a proof that uses itself under a constructor it rebuilt is
  productive, and termination is not needed; that is why today's lemmas
  may say `spin`. §3.5 works this out for expansive families, where the
  proof calls itself at a growing argument: which parts of today's
  body rule carry over, which do not, and why coinduction stays sound.
- **Index lemmas must be inductive, and so must end.** `(= (+ n m) (+ m
  n))` proved by recursion on a natural is an induction; a "proof" that
  loops proves anything, and once erased nothing would catch it. Liquid
  Haskell: "using a recursive function to model a proof by induction is
  not sound if the recursive function is partial or non-terminating",
  and it "rejects any definition that it cannot prove to be total and
  terminating" (Vazou et al., Haskell 2018, §3). F*: a lemma "always
  returns the `():unit` value", and "the fact that it is total is
  extremely important—it ensures that the inductive argument is
  well-founded". Dafny's lemmas are ghost, and terminate by `decreases`.
  FX-26 has the pieces: `nat` and `(nat s)` values to recurse on, and
  size-change termination to show the recursion ends, with no `spin`.
  So an index lemma would be `(proves (poly ((n size) (m size)) (= (+ n
  m) (+ m n))))` whose body is a `pure` function (no `spin`, checked by
  size-change) over `(nat n)` witnesses, erased.
- **Index lemmas are applied, not searched for.** A subtyping lemma is
  found by the subtyping rule when its conclusion matches. An arithmetic
  fact has no such trigger, and searching all lemmas at every size
  question would be slow and surprising. Liquid Haskell passes a proof's
  postcondition in explicitly (its `?` combinator), and F* calls lemmas
  as unit-returning functions. Proposed: `(by (plus-comm n m) body)`,
  which adds the instantiated conclusion to `body`'s facts; erased.

**So: the existing mechanism suffices for subtyping** (rows one and
four), once expansive families exist as nodes a lemma can name (§3.5);
**index lemmas need an extension**: equations over sizes as
propositions, totality in place of guardedness, and an explicit form
to apply one. That extension waits on a program that needs arithmetic
beyond linear facts; none of the examples above does.

### 3.5 Expansive families, accepted: proved, refuted, unknown, and lemmas

Added 2026-09-30, at the user's request. §3.4 said subtyping lemmas
cover expansive families "unchanged in kind", while the checker refuses
such a family where it is defined (`family-expansive-refused.fx`:
"`grow` expands without end"), so a lemma about one never gets the
chance. The user's position: accept expansive families; the checker
answers proved, refuted or unknown, and only "unknown" demands a lemma.
This section takes that position seriously.

#### 3.5.1 The position, on its merits

It holds up, under six conditions, each argued below:

1. **Same family, never unknown.** `(F A) ≤ (F B)` is decided by
   congruence at a variance the checker derives when `F` is defined
   (§3.5.2), with no unfolding. Most questions a program asks are of
   this kind, and none of them needs a budget or a lemma.
2. **The checker generalizes before it asks.** When unfolding two
   different families grows a chain, the checker anti-unifies it into a
   candidate lemma and tries to prove that with its variables opaque, as
   the prototype did (`nonregular-prototype.md`, "Lemmas"). Only if that
   fails is the answer "unknown".
3. **Unknown refuses.** A budget that runs out is never "yes"; the
   program is refused with a message that names the lemma to write
   (§3.5.5). This is S3's rule for every depth bound (PLAN.md, "Next",
   S3: each "gives up by refusing or asking for `spin` or a proof, never
   by accepting").
4. **The budget is a property of paths, not of search order**, so that
   the two checkers answer alike (§3.5.6).
5. **Safety analyses read the definition, never the unfolding**
   (§3.5.2), since unfolding an expansive family does not end.
6. **A family application is not injective** in unification and guard
   equations (§2.4).

What it buys over "generative only": nested and indexed types that are
`data` (read, printed, confirmed, sent: §4.2), with no `up-`/`down-`,
related structurally to other types (a nested sequence to a list, a
typed term to an untyped one) by the checker or by one lemma. What it
costs: a budget in subtyping, where today there is none ("subtyping has
none (a coinductive trail)", S3), and so programs near the bound whose
fate depends on it; GHC warns of the same for its reduction depth
("any upper bound you could choose might fail unpredictably with minor
updates", quoted in `nonregular-subtyping-survey.md` §5). Condition 1
keeps that to questions between different families.

#### 3.5.2 What lifting the ban takes, in both checkers

The prototype (`nonregular-prototype.md`, branch
`worktree-agent-a2bb056cff956c295`, Rust only) built most of the
Rust half. What is needed, each in `check.rs`/`infer.rs` and in
`check.fx`'s files:

| Piece                  | What it does                                                                                    | Prototype had it?                   |
| ---------------------- | ----------------------------------------------------------------------------------------------- | ----------------------------------- |
| family node            | `Ty::App { family, args }`, interned; `ty-app` in `check.fx`'s arena; printed by name           | yes (Rust)                          |
| definition             | a mention at other descriptions becomes a node, where today it is refused                       | yes                                 |
| unfolding on demand    | `whnf` at `tagcase`, `extract`, checking against an expected type, unification                  | yes                                 |
| derived variance       | per parameter, a greatest fixed point, proved once per family (below)                           | no: arguments compared invariantly  |
| subtyping order        | congruence; then lemmas by family pair; then generalization; then unfolding within the bound    | congruence, unfolding, generalizing |
| three answers          | proved; refuted with a path; unknown with the chain and the lemma tried                         | yes                                 |
| the bound              | depth of family unfoldings along one path, the same number in both checkers                     | a count of 200 per question         |
| memo tables            | refutations kept (a failure is unconditional); "unknown" never kept as success                  | memoized unfolding                  |
| lemmas naming families | `lemma_may_apply` and `match_ty` match `Ty::App` by family, as they match `Ty::Named` today     | no: lemmas only found               |
| safety analyses        | regions, `no_knot`, `writes_in`, `cyclic`, `data`-ness from the definition, parameters symbolic | assumed no regions in bodies        |
| size-change            | a `tagcase` on a node unfolds one step; the fields are parts                                    | not needed there                    |
| unification            | two nodes of one family: unfold, do not equate arguments                                        | matched arguments first             |

Notes:

- **Derived variance.** For each parameter, start by assuming it
  covariant (and, separately, contravariant), and check the family's
  body against that assumption, with the family's own applications
  compared by the assumed variance: a coinductive proof of `∀a b. a ≤ b
  ⇒ (F a) ≤ (F b)`, arguments opaque. On failure, weaken to invariant
  and repeat until nothing changes. For `seq`, the body's `(seq (pair
  a))` needs `(pair a) ≤ (pair b)`, which follows from `a ≤ b`: `seq` is
  covariant, with no unfolding. This is GHC's role inference, "it
  starts with the role information of the built-in constants … and
  propagates roles until it finds a fixpoint" (Breitner, Eisenberg,
  Peyton Jones and Weirich, JFP 2016, §4.5), which handles nested types
  the same way: a parameter passed to the family's own application
  inherits that application's role. A parameter a guard mentions comes
  out invariant, as §0 said it should. It replaces the variance lemmas
  `seq-up` and `term-up` of §3.5.3.
- **Safety through a node.** Generative types already show the way:
  "the analyses of what a value holds look through the name …; for what
  the name was given, cautiously" (`docs/fx26.md`, generative types).
  A family node is the same: the regions, writable parts and knots of
  `(F D …)` are those of `F`'s body with the parameters standing for
  what `D …` hold, computed from the definition once. Walking the
  unfolding would not end.
- **What stays sound.** The only new way to say "yes" is congruence at
  a variance that was proved, or a lemma that was proved; unfolding
  says "yes" only when the trail closes, as today. A bound reached says
  "unknown", which refuses. A lemma is tried with the trail restored on
  failure, as the lemma rule already does (`recursive-subtyping.md`,
  "The hazard for the future").

#### 3.5.3 Three families, with their lemmas

Each is given as it checks today, generative, where it can be, and as
it would read structurally, marked `; PROPOSED`.

**(a) The nested sequence**, `(seq a) = nil | cons a (seq (pair a))`
(Bird and Meertens' `Nest`; `gadts.md` E6). Today, generative
(`seq-lemmas.fx`, both checkers agree): two lemmas, each calling itself
at the growing argument `(pair a)` with a coercion for pairs built from
the one it was given.

```
(define-type (pair (a type)) (productof (l a) (r a)))
(define-generative (seq (a type))
  (sumof (nil unit) (cons (productof (hd a) (tl (seq (pair a)))))))
(define* seq-up (proves (poly ((a type) (b type)) (<= (seq a) (seq b)) (<= a b)))
  (lambda (f s)
    (up-seq (tagcase (down-seq s)
              (nil u (sum nil u))
              (cons (hd tl)
                (sum cons (product (hd (f hd))
                                   (tl (seq-up (lambda ((p (pair a)))
                                                 (product (l (f (extract p l)))
                                                          (r (f (extract p r)))))
                                               tl)))))))))
;; seq-twin, the same body with up-seq2: (seq a) <= (seq2 b) given a <= b
(define small (seq (sumof (x int))) …)
(define wide (seq (sumof (x int) (y bool))) small)        ; by seq-up
(define other (seq2 (sumof (x int) (y bool))) small)      ; by seq-twin
```

Structurally, `seq-up` is not needed (derived variance) and `seq-twin`
is what the checker's generalization finds (the prototype found this
very lemma, "`∀x1. (nest (productof (l x1) (r x1))) ≤ (nest2 …)`", for
`nest-same.fx`). The one a programmer must write relates the sequence
to a type of another shape: a `(seq int)` is a list of perfect trees
of ints.

```
(define-type (seq (a type))                                               ; PROPOSED
  (sumof (nil unit) (cons (productof (hd a) (tl (seq (pair a)))))))       ; accepted
(define-type tree (mu t (union int (pair t))))                            ; Q7's unions
(define-type (lst (e type)) (sumof (nil unit) (cons (productof (hd e) (tl (lst e))))))
(define* seq-flat (proves (poly ((x type)) (<= (seq x) (lst tree)) (<= x tree)))
  (lambda (f s)
    (tagcase s
      (nil u (sum nil u))
      (cons (hd tl)
        (sum cons (product (hd (f hd))
                           (tl (seq-flat (lambda ((p (pair x)))
                                           (product (l (f (extract p l)))
                                                    (r (f (extract p r)))))
                                         tl))))))))
(define flat (lst tree) (the (seq int) …))    ; by seq-flat: int <= tree
```

The checker cannot find `seq-flat`: the chain `(seq int) ≤ (lst
tree)`, `(seq (pair int)) ≤ (lst tree)`, … generalizes to `∀x. (seq x)
≤ (lst tree)`, which is false without a hypothesis, and the prototype's
hypotheses come only "from pairing the two sides' new variables"
(`nonregular-subtyping-survey.md` §3); here the right side has none.
The hypothesis `x ≤ tree` is the programmer's idea. (Deciding a
non-regular type against a regular one is decidable in principle,
EXPTIME-complete by Kučera and Mayr, *from memory* via the survey §2;
a lemma is far simpler to check.)

**(b) De Bruijn terms**, `(term v)`, whose `lam` body has one more free
variable, `(term (maybe v))` (Bird and Paterson). Today, generative
(`term-lemmas.fx`): the variance lemma hands itself a coercion for
`maybe` that takes a sum apart and rebuilds it (inside a `the (maybe
b)`, since the arms alone synthesize two different one-tag sums). With it, a closed
term, a `(term void)`, is a term in any context, since `void ≤ int`;
without it, that is refused (`term-without-lemma-refused.fx`); and a
coercion that turns `some x` into `none` is refused as no identity
(`term-lemma-refused.fx`: "each arm rebuilds its own tag").

```
(define-type (maybe (v type)) (sumof (none unit) (some v)))
(define-generative (term (v type))
  (sumof (var v) (app (productof (f (term v)) (x (term v)))) (lam (term (maybe v)))))
(define* term-up (proves (poly ((a type) (b type)) (<= (term a) (term b)) (<= a b)))
  (lambda (f t)
    (up-term (tagcase (down-term t)
               (var x (sum var (f x)))
               (app (g x) (sum app (product (f (term-up f g)) (x (term-up f x)))))
               (lam body
                 (sum lam (term-up (lambda ((m (maybe a)))
                                     (the (maybe b)
                                       (tagcase m
                                         (none u (sum none u))
                                         (some x (sum some (f x))))))
                                   body)))))))
(define id-term (term void) (up-term (sum lam (up-term (sum var (sum none #u))))))
(define in-context (term int) id-term)                     ; by term-up
```

Structurally, `term`'s variance is derived (covariant: `(maybe a) ≤
(maybe b)` from `a ≤ b`), and `(define in-context (term int) id-term)`
needs no lemma at all.

**(c) A guarded family: well-typed terms in a typed context.** The
context `g` grows under `lam`, so `tm` is expansive; `idx`, a typed
de Bruijn index, is not (its recursion is at an existential).

```
(define-type (idx (g type) (t type))                                      ; PROPOSED
  (sumof (here  (exists ((g2 type)) (when (= g (productof (hd t) (tl g2))))) unit)
         (there (exists ((s type) (g2 type)) (when (= g (productof (hd s) (tl g2)))))
                (idx g2 t))))
(define-type (tm (g type) (t type))
  (sumof (var (idx g t))
         (app (exists ((s type))) (productof (f (tm g (subr pure (s) t))) (x (tm g s))))
         (lam (exists ((s type) (u type)) (when (= t (subr pure (s) u))))
              (tm (productof (hd s) (tl g)) u))))
(define-type nat-ix (sumof (here unit) (there nat-ix)))
(define-type uterm (sumof (var nat-ix) (app (productof (f uterm) (x uterm))) (lam uterm)))
(define* tm-erase (proves (poly ((g type) (t type)) (<= (tm g t) uterm)))
  (lambda (e)
    (tagcase e
      (var i (sum var i))                         ; (idx g t) <= nat-ix: by the rules
      (app (f x) (sum app (product (f (tm-erase f)) (x (tm-erase x)))))  ; s fresh
      (lam b (sum lam (tm-erase b))))))           ; s, u fresh; t = (subr pure (s) u)
```

A typed term is an untyped term, the same value: whatever prints,
compares or serializes `uterm`s takes `tm`s for nothing. `(idx g t) ≤
nat-ix` needs no lemma: the pair it reaches again, `(idx g2 t) ≤
nat-ix`, is the first up to renaming the existential. `(tm g t) ≤
uterm` does not close on the trail (the context grows), but the
checker's generalization finds `tm-erase` itself: the chain generalizes
to `∀x y. (tm x y) ≤ uterm`, and with `x`, `y` opaque each arm closes by
that very hypothesis, under the constructor it rebuilt. So `tm-erase`
is optional; written, it is documentation the checker verifies. (`app`'s
`exists` has no `when`: its argument's type is hidden, not constrained.)

**What carries over from today's body rule.** Today's rule
(`crates/fixpt-fx26/src/lemma.rs`, `rebuild` and `proof_coercion`):

| Part of the rule                                                               | (a) `seq`                          | (b) `term`                                   | (c) `tm`, guarded           |
| ------------------------------------------------------------------------------ | ---------------------------------- | -------------------------------------------- | --------------------------- |
| `up-`/`down-` stripped as conversions                                          | none to strip                      | none to strip                                | none to strip               |
| generative types unfolded (`unfold_all`)                                       | family nodes unfolded the same way | same                                         | same                        |
| each arm rebuilds its own tag, fields in order                                 | carries                            | carries                                      | carries                     |
| a hypothesis or proof applied only to what was given at that place             | carries                            | carries                                      | carries                     |
| itself used only under a constructor it rebuilt                                | carries, at `(pair x)`             | carries, at `(maybe a)`                      | carries, at a grown context |
| coercions: a hypothesis, a proof, itself, or a rebuilding lambda               | carries (`pair`)                   | carries (`maybe`, a `tagcase` in the lambda) | none needed                 |
| effect `spin`, never run, erased                                               | carries                            | carries                                      | carries                     |
| matched by head: `Ty::Named` of one name                                       | needs `Ty::App`                    | needs `Ty::App`                              | needs `Ty::App`             |
| arms bind existentials; the arm's guard is a fact while rebuilding             | —                                  | —                                            | new                         |
| the rebuilt variant's guard is shown at the target type                        | —                                  | —                                            | new, by ordinary typing     |
| used where the rules *fail*; for structural families, where they are *unknown* | changes                            | changes                                      | changes                     |

The body rule itself carries over unchanged; what changes is around it:
lemmas must be able to name a family node, arms of a guarded family
bind existentials and bring their guards as facts (which the typing of
the body already needs, §2.4), and the subtyping rule must consult a
lemma before unfolding, or when unfolding is unknown, rather than only
where the rules fail outright. Checking a lemma's body never needs the
lemma: the recursive call's result is an application of the target
family at the very arguments the rebuilt field expects, so the body
types by congruence.

#### 3.5.4 Is coinduction still sound at growing arguments?

My argument, to go to the soundness agent before anything is built.

- **The claim** a lemma makes is `∀x̄. H(x̄) ⇒ F[x̄] ≤ G[x̄]`, over types
  as trees, regular or not.
- **The relation.** Let `R` be `≤` together with every pair `(F[σ̄],
  G[σ̄])` whose instance `σ̄` satisfies the hypotheses `H`. Subtyping is
  the greatest relation closed under one step of the structural rules
  (a simulation), so it suffices that `R` is closed under that step.
- **The step.** Take a pair `(F[σ̄], G[σ̄])`. The body, checked with
  `x̄` rigid, takes `F[x̄]` apart one constructor and rebuilds each
  variant of `G[x̄]` with the same tag. Each field is either (i) related
  by the ordinary rules or a hypothesis, which holds of `σ̄` by `H`, or
  (ii) a recursive use at a new instance `τ̄` (`(pair x)`, `(maybe a)`,
  a grown context), whose hypotheses `H(τ̄)` the body had to supply as
  coercions built from the ones it was given. Since the body typed with
  `x̄` opaque, the same holds at `σ̄`: `H(τ̄[σ̄])` follows from
  `H(σ̄)`, so the field pair is in `R`. So `R` is closed, and `R ⊆ ≤`.
- **Growth does not matter.** `R` is defined by the quantified
  statement, not by a finite set of trees, so the instances `τ̄` may grow
  without bound. Regularity is what makes the *algorithmic* trail finite
  (Brandt and Henglein axiomatize regular recursive types, by their
  abstract); the proof principle, as Kozen and Silva state it, is for
  coterms in general, and its soundness needs only two things, which
  they name: "one can appeal to the coinductive hypothesis as
  long as there has been progress in observing the elements …
  (guardedness) and there is no further analysis of the tails
  (opacity)" (MSCS 2016, §3.1). Guardedness is "itself used only under a
  constructor it rebuilt"; opacity is "a proof applied only to what was
  given at that place", whose result is put into a field and never
  taken apart.
- **Quantified coinductive hypotheses have a precedent.** Cretin and
  Rémy's Fcc proves coercions by coinduction (rule PropFix: "if P is
  true assuming P in the unguarded coinduction environment, then P is
  true"), where a hypothesis may be used only once guarded by the
  η-expansion rules "that decompose computational types", and
  propositions may be quantified (PropForIntro), so a hypothesis can be
  used at another instance; they prove it sound by step-indexing (LICS
  2014, fig. 6 and its text). Their recursive types are μ-types, not
  nested families, so the growing case is my extrapolation.
- **GHC chose otherwise, for a reason FX-26 does not have.** Its
  `Coercible` solver "would refrain from building recursive evidence …
  for Coercible it would simply cause the program to loop when executed"
  (Breitner et al., §7.2); `coerce` runs its evidence. FX-26's lemmas are
  never run, and their existence is the proof, so recursive evidence is
  harmless: its effect is `spin` precisely because it is not called.
- **Where I am less sure.** (1) The guard in the prototype was "some
  pair of constructors above", not a check per use
  (`nonregular-prototype.md`, "Soundness caveats"); the lemma rule's
  per-use `guarded` flag is the one to keep. (2) Guarded families: the
  argument needs the arm's guard to hold of `σ̄` whenever the variant is
  inhabited, which is the semantic reading of a guard (§8, first
  bullet). (3) Fields of procedure type are rebuilt by a lambda
  (η-expansion), which is the identity up to typing, not up to `eq?`;
  harmless for an erased proof, but worth the agent's look. (4)
  Derived variance (§3.5.2) is the same argument with `H` = `a ≤ b`, so
  it stands or falls with this one.

#### 3.5.5 What an "unknown" says

The prototype's message (`nonregular-prototype.md`, "Unknown") showed
that naming the growth `X ↦ C[X]` is what makes an unknown readable.
For §3.5.3 (a) without `seq-flat`, proposed:

```
! flat.fx:9:17: `flat` is declared a (lst tree): is a (seq int) one?
  — undecided, not refuted: no path of 16 unfoldings closes.
  The comparisons on one path grew, each step X ↦ (pair X) on the left:
      (seq int) ≤ (lst tree)
      (seq (pair int)) ≤ (lst tree)
      (seq (pair (pair int))) ≤ (lst tree)
  Generalized: (seq x) ≤ (lst tree) for every x. That is not provable
  as it stands: at field `hd` it needs x ≤ tree, which nothing gives.
  A lemma that would close it, if you can prove it:
      (proves (poly ((x type)) (<= (seq x) (lst tree)) (<= x tree)))
  used here with x = int, where int ≤ tree holds.
```

What it must contain:
- the question, and that it is **undecided, not refuted**;
- the bound, as a number of unfoldings on one path;
- the chain, compressed to its first pairs and its growth;
- the generalized goal the checker tried, and the first subgoal that
  failed with the variables opaque: that subgoal is the missing
  hypothesis;
- the lemma to write, as a `proves` type the programmer can paste, and
  the instance at which it would be used, with its hypotheses checked.

The checker can suggest the hypothesis because proving the generalized
goal with opaque variables fails at a specific leaf, `x ≤ tree`; making
that leaf a hypothesis and proving the rest is what the programmer's
lemma then does. So the message's lemma type is found mechanically; its
body is the programmer's (and is itself mechanical, the family's
rebuild, which a later tool could write).

#### 3.5.6 Ergonomics and cost

Lemmas each example needs:

| Family        | Question                   | Generative, today | Structural, proposed        |
| ------------- | -------------------------- | ----------------- | --------------------------- |
| `seq`         | `(seq A) ≤ (seq B)`        | `seq-up`          | none: derived variance      |
| `seq`, `seq2` | `(seq A) ≤ (seq2 B)`       | `seq-twin`        | none: found by generalizing |
| `seq`, `lst`  | `(seq int) ≤ (lst tree)`   | not expressible   | `seq-flat`, written         |
| `term`        | `(term void) ≤ (term int)` | `term-up`         | none: derived variance      |
| `tm`, `uterm` | `(tm g t) ≤ uterm`         | not expressible   | none: found by generalizing |

One lemma in five questions, against three today with less said. The
common lemmas, variance and twins, are derived: variance by the fixed
point of §3.5.2, twins by anti-unification and an opaque proof. What is
left for the programmer is a relation to a type of another shape that
needs a side condition the checker cannot invent.

**Cost.** Only questions between two *different* families, or a family
and a structure, reach unfolding; same-family questions cost what
comparing their arguments costs. The prototype's worst example took
0.31 s for the whole run, lemma search included, and every other under
0.01 s, with a budget of 200 unfoldings (`nonregular-prototype.md`,
"The examples"); the front end has no expansive families, so it would
pay nothing. Derived variance costs one proof per family, at its
definition. Lemma candidates are indexed by their pair of families.
What the budget costs is predictability:

- **The two checkers must agree on "unknown".** A global count of
  unfoldings depends on the order of exploration, which two
  implementations will not share exactly. A bound on the depth of
  family unfoldings along each path does not: a question is unknown
  when some path reaches depth `k` without closing or failing, however
  it was reached. `k` is a constant of the language (16 in the sample),
  not a flag.
- **Refutations first.** A path that fails before the bound is a "no"
  with a witness, whatever other paths do; a breadth-first search finds
  the shortest (`nonregular-subtyping-survey.md` §5).
- **Stability.** A program that passes only because some path closed
  at depth 15 may stop passing when a type grows. The message's advice
  is then a lemma, which removes the dependence: with it the question is
  proved without unfolding.

## 4. Interactions with the rest of FX-26

### 4.1 Effects and regions

- Sums and products are immutable and in no region; making one is
  `pure`. Guards and existentials are erased, so constructors stay pure
  and matching reads nothing.
- A guard equating a type parameter with a type that mentions regions
  (`(= a (listof int r))`) brings those regions into the arm's
  substitution. Masking finds regions through the substituted type, as
  it does through any type (`regions_in`); since the guard's type is in
  the scrutinee's type already, no region appears that was not there.
- **Region and effect existentials are left out.** A variant hiding a
  region, `(exists ((r region)) (listof int r))`, would let a list at a
  region nothing names leave a `letregion`, which is what the escape
  rule forbids; an effect existential makes a procedure whose effect is
  a variable no licence accepts (`docs/fx26.md`, step 7). Both would
  need their own soundness argument.
- Guards over `subr` types equate effects too (§2.5, printf). Equality of
  effects is equality of atom sets, which both checkers have.
- Narrowing is by binding, and FX-26 variables never change, so a fact
  learned in an arm stays true (Typed Racket's hard case, a mutated
  variable, cannot arise: `logical-types.md` §5).

### 4.2 `acyclic`, shapes, the `data` kind, sizes

- Structural sums are built after their parts and never written, so they
  are acyclic; size-change descends `tagcase` parts (`eval-datasorts.fx`
  checks `pure`). Guards change nothing here.
- **A structural datatype is `data`** when its payloads are, and so can
  be read, printed, compared, confirmed and sent; a generative one is
  not, unless its owner supplies a validator ("deserializing is `up`",
  `generative-types.md` §3). This is a real gain for structural GADTs:
  confirming a datum as an `(expr int)` is a `confirm` walk over a regular
  type (`confirmation.md`, CF2), where a nominal `(expr int)` would need
  a hand-written checker like `typecheck.fx`. With guards over a rigid
  variable the walk needs the index, so `confirm` works at ground
  instances only.
- In `shapes.md`'s lattice, a structural datatype is graph or acyclic;
  a nominal one is at the top, generative, in the second of that note's
  two senses: "nominal types: `define-generative`, which makes a type
  equal only to itself. Its values need not have any runtime name". Moving
  GADTs to the structural side moves them down the lattice, where
  equality, copying and printing are generic (Q8).
- **Sizes**: `nlist` is the built-in guarded family, and N5's facts
  machinery is what guards need; N5c's existential results are §2.5's
  `(exists ((m size)) …)`.

### 4.3 `eq?`, representation, erasure

- `eq?` on immutable data means "equal" when `#t` and nothing when `#f`
  (`docs/fx26.md`, "Identity"), structural or not; generativity does not
  change that, since `up-` and `down-` are the identity.
- **No change of representation.** A guarded sum is a sum: a frozen
  bloblet with a tag symbol and a value (`docs/fx26.md`, immutable data).
  Guards and existentials are erased. `define-datatype` constructors
  become `sum`/`product` forms, which they already expand to.
- **What structural tags cost.** A tag is an interned symbol, and
  `tagcase` compiles to a chain of `eq` tests, one per arm
  (`crates/fixpt-fx26/src/cellular.rs`, "tagcase"); a constructor with
  fields is two objects (sum and product). ML's closed, generative
  datatypes exist partly so that tags can be small numbers per type, for
  compact representation and matching "with no backtracking" (MacQueen,
  Harper and Reppy on HOPE, HOPL 2020, §4.3.3), and Garrigue explains
  why structural tags cannot be numbered per program ("Separate
  compilation breaks it") and hashes them instead, at one extra word per
  constructed value (ML 1998, §4). FX-26 already pays this; structural
  GADTs add nothing to it. What they add is a saving: the checker knows
  which tags a pruned sum can have, so a compiler may drop tests, as
  `vhead` needs none.

### 4.4 Both checkers

Everything above is kernel work, written twice (`docs/fx26.md`, "Two
kinds of addition"):

- a guard and binders on a sum variant, in `Ty` (Rust) and in
  `check.fx`'s arena; printing and reading them back;
- guard evaluation at ground descriptions when a family is expanded
  (`Checker::knots` and its twin), and the non-expansive check, which
  replaces today's "same descriptions" rule;
- type equations as facts, beside the size facts, in the list the
  conjunctive-facts work introduced; substitution in checking mode;
- subtyping of guarded variants: implication of guards, then payloads,
  existentials under binder environments (the `poly` machinery);
- exhaustiveness after pruning; existential escape.

`check-synth.fx` is at the 1000-line limit (commit `bdda0ff`), so the
FX half goes in new files, as `check-facts.fx` did. I would guess it
the size of N4 as `gadts.md` sized it (L), and not more, since the
nominal family node N4 assumed is replaced by guards rather than added
to them.

### 4.5 Messages

Structural types print as structure. Today `(expr int)` prints as `(mu
%1 (sumof (lit int) (if-e (productof (c (mu %3 …)) …))))`
(`family-nonexpansive.fx`'s output), and a lemma's parametric `tree`
prints as `(mu %3 …)`; plain `define-type` names do survive (`a int-exp
is expected here`). Guarded families would make this worse unless a
family's instances keep their name for printing. That is a reason ML
gave for generativity (below), and the one cost here that is only
engineering: print `(expr int)` where the checker built it from `(expr
int)`.

## 5. Why ML chose generativity, and what the others do

MacQueen, Harper and Reppy give the rationales for SML's generative
datatypes (HOPL 2020, §4.3.3): consistency with LCF/ML's abstract types
and HOPE's datatypes; that "it made comparison of types in the type
checker simple, since datatype (and abstype) constructors behaved as
atomic, uninterpreted operators"; and that it "avoided a serious
technical problem that would have arisen if type equivalence treated
recursive types transparently", since Solomon had shown equivalence of
parameterized recursive types to be DPDA equivalence. And HOPE's closed
datatypes were for "optimized runtime representations of constructors
and optimized pattern matching". FX-26 answers each differently:
equi-recursion is already here and cheap for regular types; the DPDA
problem arises only for expansive families, which stay generative; and
representation is already uniform.

What generativity buys, against what FX-26 gets structurally:

| Concern                        | Structural, with guards                       | Generative                                        | So                            |
| ------------------------------ | --------------------------------------------- | ------------------------------------------------- | ----------------------------- |
| distinct datatypes             | by tags                                       | by name                                           | structural suffices           |
| unforgeable values, invariants | no: anyone may write `(sum circle 3)`         | yes, if `up-` is hidden (G4)                      | generative, where needed      |
| phantom indices                | meaningless (`gadts.md` E7)                   | meaningful, invariant                             | generative                    |
| GADT refinement                | guards                                        | N4 on a nominal family                            | either; structural is smaller |
| index variance                 | computed by comparison                        | declared, checked by Scherer and Rémy's criterion | structural is simpler         |
| non-regular recursion          | undecidable to compare; lemmas                | free (iso-recursive through the name)             | generative                    |
| cost of comparison             | graph pairs, times unification per guard      | arguments only                                    | both cheap for regular types  |
| messages                       | structure, unless names are kept for printing | names                                             | engineering (§4.5)            |
| `data`: read, print, send      | yes                                           | only with a validator                             | structural                    |
| separate compilation           | types agree without sharing a definition      | identity must be shared                           | structural                    |
| refinements (datasorts)        | subtyping of sums                             | a second layer (Freeman and Pfenning, Davies)     | structural                    |
| representation                 | tag symbols, chains of `eq`                   | the same in FX-26                                 | no difference                 |

Other languages have reached the same split:

- **Unison** has both: "Structural types are considered equivalent when
  their data constructors and parameters are structurally identical",
  but "A type is 'unique' by default", with the rule of thumb to ask
  "if the type you're defining has additional semantics or expected
  behavior beyond the information that's given in the type signature".
- **Roc**'s tag unions are structural, and `Color := [Red, Green,
  Blue]` makes "a _nominal_ type" over one (tutorial, "Nominal types").
- **MLstruct** decomposes a class type into a nominal tag intersected
  with a structural record, "fundamentally structural, while retaining
  the right amount of nominality"; nominality "is much demanded by users
  in practice" and "comes at no loss of generality, as type synonyms can
  be used if nominality is not wanted"; and "there is no primitive
  notion of nominal type constructor variance …: the covariance and
  contravariance of type parameters simply arise from the way class and
  alias types desugar" (OOPSLA 2022, §2.1.4, §2.2.6). That last is §0's
  point about variance.
- **Typed Racket** has "true union types" over structs that `define-struct`
  makes one by one: generative *constructors*, structural *sums* (POPL
  2008, §§2, 4.3). **TypeScript** narrows discriminated unions of object
  types by a literal-typed field, and gets nominality back with `unique
  symbol` brands ("no two `unique symbol` types are assignable or
  comparable to each other").
- **OCaml's polymorphic variants** are structural sums inferred by row
  unification; Castagna, Petrucciani and Nguyen argue that simulating
  unions by kinding "yields a type system whose behaviour is in some
  cases unintuitive and/or unduly restrictive", and propose semantic
  subtyping instead (ICFP 2016, abstract).
- **Scala 3's GADTs** show what goes wrong with open, covariant,
  *nominal* GADTs: `object Unsound extends Const[Any] with Expr[Int]`,
  a value of one class inheriting two instantiations (Parreaux,
  Boruch-Gruszecki and Giarrusso, Scala 2019, §3.2). A structural sum
  value has one tag and one payload, so no value can be in two
  instantiations that way; the guard decides membership.

## 6. The approaches against what FX-26 needs

"Needs" here: two checkers that agree; bidirectional checking with
signatures, not inference; effects and regions; decidable, cheap
subtyping for what the front end writes; good messages.

| Approach                                                           | ADTs are                      | GADT refinement                       | Subtyping                    | Cost                             | Fits FX-26?                                         |
| ------------------------------------------------------------------ | ----------------------------- | ------------------------------------- | ---------------------------- | -------------------------------- | --------------------------------------------------- |
| Generative ADTs (ML, GHC; FX-26 N1–N4)                             | nominal                       | equations on a named family           | congruence by variance       | cheap                            | yes; today's plan                                   |
| Polymorphic variants (OCaml)                                       | structural, rows              | none                                  | by row unification           | cheap; messages poor             | rows unneeded: FX-26 has width subtyping            |
| Datasort refinements (Freeman–Pfenning, Davies, Dunfield–Pfenning) | nominal, refined structurally | index refinements (Dunfield–Pfenning) | regular tree inclusion       | EXPTIME worst; fine in practice  | the refinement half is FX-26's sums already         |
| Semantic subtyping (CDuce)                                         | structural, ∨ ∧ ¬             | by intersections of arrows            | complete, decidable          | exponential; hard to write twice | too much for two checkers (`logical-types` §8.4)    |
| MLstruct (Boolean algebra)                                         | nominal tags ∧ records        | none                                  | Boolean algebra, NP-hard     | inference, no backtracking       | its variance-from-structure lesson, not its algebra |
| Occurrence typing (Typed Racket, TS)                               | unions of generative structs  | none                                  | syntactic, incomplete        | cheap                            | Q7's narrowing                                      |
| Guarded structural sums (this note)                                | structural, tags              | guards as facts                       | trail, guards by unification | cheap if non-expansive           | yes                                                 |

## 7. Open questions for you

1. **Should GADTs (N4) be structural by default?** Options: (a) N4 as
   `gadts.md` has it, on nominal families; (b) guards on structural
   sums, `define-datatype`'s `=>` as sugar for them, generative families
   only where written; (c) both, `#:generative` choosing. Recommendation:
   (b), with (c)'s keyword later, when hiding (G4) exists. It is smaller
   than (a) (no family node, no declared variance), keeps GADT values
   `data`, and costs nothing at run time.
2. **Constructors as forms returning their singleton?** Today `(circle
   3) : shape`. Options: keep; make them forms giving `(sumof (circle
   int))`; give the singleton only in checking mode. Recommendation:
   forms with the singleton. It is what refinements need (§1.1), and it
   drops a global read per construction. The cost: an unannotated
   `(define c1 (circle 3))` gets the one-tag type; a `the` restores the
   datatype.
3. **The guard language.** Options: type equations and linear size
   facts; add subtyping guards `(<= T a)` (Scherer and Rémy's "subtyping
   constraints", Scala's bounds) for covariant indices. Recommendation:
   equations and sizes only, until a program asks for a covariant index.
4. **Same-tag unions** (two payloads under one tag, CDuce's products).
   Recommendation: refuse, and keep sums tag-deterministic (§3.2).
5. **Expansive structural families** (§3.5). Options: (a) stay refused,
   generative only (today); (b) accept them as family nodes compared by
   congruence at a derived variance, with every other question between
   them refused; (c) as (b), plus the checker's own generalization,
   unfolding within a depth bound, and the programmer's lemmas where the
   answer is "unknown". Recommendation: (c), reached through (b). (b)
   alone already needs no lemma for `seq`'s or `term`'s variance, or for
   `tm`'s erasure (§3.5.3), and is decidable; (c) adds the budget, and
   with it the one kind of question two checkers must be made to
   answer alike (§3.5.6). The soundness argument (§3.5.4) goes to the
   soundness agent first.
6. **Index lemmas** (§3.4): propositions over sizes, proved by a
   terminating `pure` function, applied with `by`. Recommendation: design
   them with N5c, when inequalities first need a fact the procedure
   misses; not before.
7. **Names in printed types.** Recommendation: keep a family
   application's name for printing wherever the checker built the type
   from one, before guards land, since guards make structure longer.
8. **Tags: global or declared?** FX-26's tags are global symbols, as
   OCaml's and Roc's are; MLstruct and Typed Racket make each tag (or
   struct) generative. Recommendation: global, as now; a type that must
   not be forged is `define-generative`, not a private tag.
9. **Recursive solutions of guards** (`a = (productof (l a) (r int))`,
   §2.4): refuse with an occurs check at first, or take the μ?
   Recommendation: refuse, until an example needs it.

## 8. What I could not verify, or am unsure of

- That guarded, non-expansive families keep the trail finite (§3.1) is
  my argument, not a published theorem; Xi, Chen and Chen fold and unfold
  their datatypes iso-recursively (§2.2, `unfold((τ)T)`), and Dunfield
  and Krishnaswami leave recursive types and type constructors out of
  their formalism ("Extensions", in "Discussion and related work"). Nobody I read proves the equi-recursive,
  structural version sound; I believe the semantic reading (a guarded
  variant is empty when its guard fails) makes it straightforward, but it
  should go through the soundness agent before anything is built.
- Kennedy and Pierce's non-expansive condition, Friedman's inclusion
  result, Solomon's reduction (beyond MacQueen's summary), Aspinall's
  singleton types and Hilbert's tenth problem are from memory or from
  `nonregular-subtyping-survey.md`, which was itself from memory.
- The printf example's effects, and a `letrec` binding a `poly` (§2.5).
- The coinductive soundness of lemmas at growing arguments (§3.5.4) is
  my argument, resting on Kozen and Silva's account of guardedness and
  opacity and on Cretin and Rémy's quantified coinduction; neither
  treats non-regular families, and Brandt and Henglein's paper itself I
  know only through Kozen and Silva. The derived variance (§3.5.2), the
  checker's own generalization finding `tm-erase` (§3.5.3), and the
  depth bound's cost (§3.5.6) are argued, not run: no family nodes
  exist, and the prototype branch was not rebuilt for this note.
- I did not read Dunfield's thesis (CMU-CS-07-129), which unifies
  datasorts, indices, unions and intersections and is probably the
  closest precedent: no copy was found.
- I read no Scala 3, Ceylon or Roc compiler source; their behaviour here
  is from their documentation or papers as listed.

## Sources

Read 2026-09-30. Local copies are under `docs/research/papers/`
(uncommitted); text was extracted with `pdftotext`.

| Source                                                                                                                                                                                                                                                                                                                                       | Where                                                                                                                                | Seen                                                                                                      |
| -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------- |
| T. Freeman, F. Pfenning, "Refinement types for ML", PLDI 1991                                                                                                                                                                                                                                                                                | `papers/freeman-pfenning-pldi91-refinement-types-ml.pdf`, from https://www.cs.cmu.edu/~fp/papers/pldi91.pdf                          | read in part: §§1–2                                                                                       |
| R. Davies, *Practical Refinement-Type Checking*, PhD thesis, CMU-CS-05-110, 2005                                                                                                                                                                                                                                                             | `papers/davies-2005-thesis-practical-refinement-type-checking.pdf`, from https://www.cs.cmu.edu/~rwh/students/davies.pdf             | read in part: abstract, contents, §1.6.8, §4.5, §5.5 opening, §7.5                                        |
| J. Dunfield, F. Pfenning, "Tridirectional typechecking", POPL 2004                                                                                                                                                                                                                                                                           | `papers/dunfield-pfenning-popl04-tridirectional.pdf`, from https://www.cs.cmu.edu/~fp/papers/popl04.pdf                              | read in part: abstract, §1, §3.3                                                                          |
| J. Dunfield, N. Krishnaswami, "Bidirectional typing", ACM CSUR 2021 (arXiv 1908.05839)                                                                                                                                                                                                                                                       | `papers/dunfield-krishnaswami-2019-bidirectional-survey.pdf`, from https://arxiv.org/pdf/1908.05839                                  | read in part: intersection typing (§4.6ff.), GADTs paragraph                                              |
| J. Dunfield, N. Krishnaswami, "Sound and complete bidirectional typechecking … existentials and indexed types", POPL 2019                                                                                                                                                                                                                    | `papers/dunfield-krishnaswami-popl19-existentials-indexed-types.pdf`, from https://arxiv.org/pdf/1601.05106 (v4)                     | read in part: §1, §2, fig. 2, the coverage passage of §4, "Extensions"                                    |
| J. Dunfield, "Untangling typechecking of intersections and unions", 2010 (arXiv 1101.4428)                                                                                                                                                                                                                                                   | `papers/dunfield-2014-untangling-intersections-unions.pdf`, from https://arxiv.org/pdf/1101.4428                                     | downloaded, not read                                                                                      |
| J. Dunfield, *A Unified System of Type Refinements*, PhD thesis, CMU-CS-07-129, 2007                                                                                                                                                                                                                                                         | not found                                                                                                                            | title only (search result)                                                                                |
| H. Xi, C. Chen, G. Chen, "Guarded recursive datatype constructors", POPL 2003                                                                                                                                                                                                                                                                | `papers/xi-chen-chen-popl03-guarded-recursive-datatypes.pdf`, from https://www.cs.bu.edu/~hwxi/atslangweb/MYDATA/GRDT-popl03.pdf     | read in part: §1, §2.2–2.3, §5 (indexed lists)                                                            |
| V. Simonet, F. Pottier, "A constraint-based approach to guarded algebraic data types", TOPLAS 2007                                                                                                                                                                                                                                           | `papers/simonet-pottier-toplas07-guarded-adts.pdf`, from http://cambium.inria.fr/~fpottier/publis/simonet-pottier-hmg-toplas.pdf     | read in part: abstract, §1.4–1.5, the decidability remarks (p. 37)                                        |
| G. Scherer, D. Rémy, "GADTs meet subtyping", ESOP 2013, and INRIA RR-8114                                                                                                                                                                                                                                                                    | `papers/scherer-remy-2013-gadts-meet-subtyping-long.pdf` (already local)                                                             | read in part: the passages on private types and closure; the rest via `nonregular-subtyping-survey.md` §4 |
| G. Castagna, "Programming with union, intersection, and negation types", arXiv 2111.03354v4, 2024                                                                                                                                                                                                                                            | `papers/castagna-2024-union-intersection-negation.pdf`, from https://arxiv.org/pdf/2111.03354                                        | read in part: §2 (red-black trees), §3.1–3.2, §3.3, polymorphic variants comparison                       |
| A. Frisch, G. Castagna, V. Benzaken, "Semantic subtyping", JACM 55(4), 2008                                                                                                                                                                                                                                                                  | `papers/frisch-castagna-benzaken-jacm08-semantic-subtyping.pdf`, from https://www.irif.fr/~gc/papers/semantic_subtyping.pdf          | read in part: abstract, §1, the regular-terms definition                                                  |
| G. Castagna, T. Petrucciani, K. Nguyen, "Set-theoretic types for polymorphic variants", ICFP 2016                                                                                                                                                                                                                                            | `papers/castagna-petrucciani-nguyen-icfp16-polymorphic-variants.pdf`, from https://www.irif.fr/~gc/papers/icfp16.pdf                 | abstract and opening of §1                                                                                |
| J. Garrigue, "Programming with polymorphic variants", ML Workshop 1998                                                                                                                                                                                                                                                                       | `papers/garrigue-ml98-polymorphic-variants.pdf`, from https://caml.inria.fr/pub/papers/garrigue-polymorphic_variants-ml98.pdf        | read in part: §§1–2 opening, §4 (compilation)                                                             |
| L. Parreaux, C. Y. Chau, "MLstruct", OOPSLA 2022, extended version v8.0                                                                                                                                                                                                                                                                      | `papers/parreaux-chau-oopsla22-mlstruct-v8.pdf`, from https://lptk.github.io/files/[v8.0] mlstruct.pdf                               | read in part: §1, §2.1.4, §2.2 opening, §2.2.6                                                            |
| L. Parreaux, A. Boruch-Gruszecki, P. G. Giarrusso, "Towards improved GADT reasoning in Scala", Scala 2019                                                                                                                                                                                                                                    | `papers/parreaux-boruch-gruszecki-giarrusso-scala19-gadt-reasoning.pdf`, from http://lptk.github.io/files/[v.2.0.1] scala19_gadt.pdf | read in part: §1, §3.2–3.3                                                                                |
| S. Tobin-Hochstadt, M. Felleisen, "The design and implementation of Typed Scheme", POPL 2008                                                                                                                                                                                                                                                 | `papers/tobin-hochstadt-felleisen-popl08-typed-scheme.pdf` (already local)                                                           | read in part: §2, §4.3                                                                                    |
| D. MacQueen, R. Harper, J. Reppy, "The history of Standard ML", HOPL IV, 2020                                                                                                                                                                                                                                                                | `papers/macqueen-2020-history-of-standard-ml.pdf` (already local)                                                                    | read in part: §4.3.3 (datatypes)                                                                          |
| N. Vazou, J. Breitner, W. Kunkel, D. Van Horn, G. Hutton, "Theorem proving for all", Haskell 2018                                                                                                                                                                                                                                            | `papers/vazou-et-al-haskell18-theorem-proving-for-all.pdf`, from https://arxiv.org/pdf/1806.03541                                    | read in part: abstract, §3 (totality and termination)                                                     |
| F* book, "Lemmas and proofs by induction"                                                                                                                                                                                                                                                                                                    | https://fstar-lang.org/tutorial/book/part1/part1_lemmas.html                                                                         | read in part, through a fetch summary with quotes                                                         |
| Dafny reference manual, lemmas                                                                                                                                                                                                                                                                                                               | https://dafny.org/latest/DafnyRef/DafnyRef                                                                                           | fetch summary only; the lemma section was truncated                                                       |
| Liquid Haskell documentation, specifications                                                                                                                                                                                                                                                                                                 | https://ucsd-progsys.github.io/liquidhaskell/specifications/                                                                         | fetch summary only (the `?` combinator)                                                                   |
| Unison documentation, "Unique and structural types"                                                                                                                                                                                                                                                                                          | https://www.unison-lang.org/docs/fundamentals/data-types/unique-and-structural-types/                                                | read, through a fetch summary with quotes                                                                 |
| Roc mini-tutorial (new compiler)                                                                                                                                                                                                                                                                                                             | https://github.com/roc-lang/roc/blob/main/docs/mini-tutorial-new-compiler.md                                                         | read in part: "Tag union types", "Nominal types"; little detail                                           |
| TypeScript Handbook, "Narrowing" (discriminated unions, exhaustiveness)                                                                                                                                                                                                                                                                      | https://www.typescriptlang.org/docs/handbook/2/narrowing.html                                                                        | read in part, through a fetch summary with quotes                                                         |
| TypeScript Handbook, "Symbols" (`unique symbol`)                                                                                                                                                                                                                                                                                             | https://www.typescriptlang.org/docs/handbook/symbols.html                                                                            | read in part, through a fetch summary with quotes                                                         |
| D. Kozen, A. Silva, "Practical coinduction", MSCS 2016                                                                                                                                                                                                                                                                                       | `papers/kozen-silva-mscs16-practical-coinduction.pdf`, from https://www.cs.cornell.edu/~kozen/Papers/Structural.pdf                  | read in part: §3.1–3.2, §4.1 (guardedness and opacity)                                                    |
| J. Cretin, D. Rémy, "System F with coercion constraints", CSL-LICS 2014                                                                                                                                                                                                                                                                      | `papers/cretin-remy-lics14-coercion-constraints.pdf`, from http://gallium.inria.fr/~remy/coercions/Cretin-Remy!fcc@lics2014.pdf      | read in part: abstract, contributions, the propositions and coercions judgments (PropFix, guarding)       |
| J. Breitner, R. Eisenberg, S. Peyton Jones, S. Weirich, "Safe zero-cost coercions for Haskell", JFP 2016                                                                                                                                                                                                                                     | `papers/breitner-eisenberg-pj-weirich-jfp16-safe-coercions.pdf`, from https://www.seas.upenn.edu/~sweirich/papers/coercible-JFP.pdf  | read in part: §4.5 (role inference), §6.4, §7.2                                                           |
| M. Brandt, F. Henglein, "Coinductive axiomatization of recursive type equality and subtyping", TLCA 1997                                                                                                                                                                                                                                     | download refused (Springer returned HTML); search abstract                                                                           | abstract only, and as Kozen and Silva describe it                                                         |
| PLAN.md, "Next", S3; `crates/fixpt-fx26/src/lemma.rs`                                                                                                                                                                                                                                                                                        | this repository                                                                                                                      | read (S3's entry; `rebuild`, `proof_coercion`, `lemma_may_apply`, `unfold_all`)                           |
| J. Garrigue, J. Le Normand, GADT exhaustiveness undecidable, 2015                                                                                                                                                                                                                                                                            | cited by Dunfield and Krishnaswami 2019, §4                                                                                          | not read                                                                                                  |
| M. Maher, equality over infinite trees, 1988; S. Vorobyov, nonelementary bound, 1996                                                                                                                                                                                                                                                         | cited by Simonet and Pottier, p. 37                                                                                                  | not read                                                                                                  |
| H. Seidl, EXPTIME-completeness of tree-automata inequivalence, 1990                                                                                                                                                                                                                                                                          | cited by Davies, §1.6.8                                                                                                              | not read                                                                                                  |
| A. J. Kennedy, B. C. Pierce, "On decidability of nominal subtyping with variance", 2007                                                                                                                                                                                                                                                      | `docs/research/nonregular-subtyping-survey.md` §2                                                                                    | from memory (the survey's)                                                                                |
| D. Aspinall, "Subtyping with singleton types", CSL 1994                                                                                                                                                                                                                                                                                      | —                                                                                                                                    | from memory                                                                                               |
| This repository: `docs/fx26.md`, `docs/research/gadts.md`, `generative-types.md`, `logical-types.md`, `nonregular-subtyping-survey.md`, `nonregular-prototype.md`, `recursive-subtyping.md` (first part), `shapes.md`, `sizes.md`, `PLAN.md` (Q7), commit `bdda0ff`, `crates/fixpt-fx26/src/cellular.rs` (tagcase), `tests/programs/lemmas/` | this repository                                                                                                                      | read                                                                                                      |
