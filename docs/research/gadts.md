# GADTs, non-regular families and generative types: a plan

Design note, 2026-09-27, drawing together three pieces of work done for the
user's question "should we think about GADTs now, before building more on
plain datatypes?":

- `nonregular-subtyping-survey.md`: the literature (citations marked sure or
  from memory);
- `nonregular-prototype.md`: a Rust-only prototype of structural checking
  of non-regular families (branch `worktree-agent-a2bb056cff956c295`,
  commit `11bb8fa`, not merged);
- `generative-types.md`: generativity on its own, and a kind for
  serializable data.

Each idea has a toy example, Haskell or OCaml beside FX-26, in "Toy
examples" below (E1 to E8); those FX-26 can say today are checked files
under `docs/research/examples/gadts/`.

## What we learned

- **Regular families stay structural.** `(rose t r)` and the rest, tied as
  knots, with equi-recursive subtyping: decidable and cheap, and what
  `finite`, size-change descent and recursive subtyping already rely on.
- **Non-regular families (GADTs, nested datatypes) cannot be compared
  structurally in general.** Equality is decidable but impractical;
  subtyping is inclusion, which is undecidable, and its "yes" is not even
  semi-decidable. A structural checker for them must sometimes say
  "unknown".
- **In practice the structural check did well.** The prototype decided
  every example in under a second with a budget of 200 unfoldings;
  congruence settled most questions; nested datatypes closed with one lemma
  found by anti-unification. Its messages were good: a path for "no", the
  growth `X ↦ C[X]` and the lemma tried for "unknown".
- **But the deeper limit is meaning, not decidability.** Structurally, a
  phantom index means nothing: the prototype proved, correctly, that a list
  "starting at 0" is one "starting at 1". Indices mean something only if a
  family's variance is declared (invariant) or the family is nominal. And
  GADT refinement needs evidence FX-26 cannot state today: no existentials,
  no refinement in `tagcase` arms, no kinds like `type → type`.
- **Generativity is cheap to add on its own.** FX-91 tied it to modules;
  FX-26 need not. Its rule: opaque to comparison, transparent to safety
  (region analyses, `no_knot` and the `spin` rules look through a
  generative name).

## Decisions proposed

1. **Non-regular families are nominal.** A family application is a node,
   compared with itself by the family's variance and never unfolded in
   comparison; values enter and leave by constructors and matching. This
   is the survey's recommendation and the generative note's G1, one
   mechanism. (E6, E7.)
2. **Variance is declared or inferred, and checked once** against the
   body; indices are invariant by default. A GADT index may be covariant
   only under Scherer and Rémy's upward-closure condition (few FX-26 types
   qualify, given width sums and region and effect subsumption). (E7, E8.)
3. **Lemmas are erased identity coercions.** An ordinary `define` whose
   declared type is a proposition, `(proves (<= A B))` or with hypotheses
   `(proves (<= (nest a) (nest b)) given (<= a b))`. The checker verifies
   the body: its type, that each arm rebuilds the same tag from coerced
   fields (mutable fields passed through unchanged), and that recursion is
   guarded (productive, as `cofix` requires: termination is not needed).
   Its existence in scope is the proof; nothing calls it, and it is dead
   code unless run on purpose, for debugging, where it is an ordinary
   function (a `trace` effect, ignored by the purity condition, gives
   println). A harness can run each on samples and check the result
   `equal?` to the input: a free test of the checker. Lemmas relate
   *different* nominal families too (`nest` and `nest'`), so they are not
   tied to structural checking. Precedents: coercion semantics of
   subtyping (Mitchell; Breazu-Tannen, Coquand, Gunter and Scedrov), erasable
   coercions (Cretin and Rémy, LICS 2014), Haskell's `Coercible` (all from
   memory). (E2, E6, E8.)
4. **GADTs proper** add three things: constructors with their own result
   types, existentials in variants, and refinement: a `tagcase` arm checks
   with the equalities its constructor states. The bidirectional checker is
   the base for it. (E1 to E5; what the checker must learn is spelled out
   under "Toy examples".)
5. **Size indices are their own sort**, with a decision procedure of their
   own (Dependent ML; sized types), not types to unfold. `confirm`'s sizes
   (CF1, CF3) use it. (E5.)
6. **A kind `data ≤ type`** for structural, non-generative types: what
   `read` returns, what `acyclic` walks exactly, what `confirm` checks, and
   what an actor may send between machines (one definition with the actor
   notes' "transmissible"). Deserializing is `up`, so a generative type is
   `data` only if its owner supplies a validator. It arrives with its first
   consumer, and the checker works out `data`-ness of concrete types, so
   only binders say `(t data)`.
7. **Structural checking of non-regular families stays optional**, as the
   prototype has it, and never treats "unknown" as "yes". Its best use may
   be as a suggester: its growing chain gives the skeleton of the coercion
   (decision 3) a programmer would write.

## Toy examples

Small examples, of the size a paper would use, one per idea above. Each
gives the Haskell (GHC's GADT syntax) or OCaml it comes from, then FX-26:

- **today**: a file under `docs/research/examples/gadts/`, checked with
  `fixpt check` and run with `fixpt eval` (both checkers agree on each;
  results below, with the `target/release/fixpt` of 2026-09-29);
- **proposed**: syntax for N4 that does not exist yet, marked `; proposed`,
  kept close to `define-datatype`. Not checked; the spelling is open.

| File                            | Today's FX-26 says                            | Shows                                            |
| ------------------------------- | --------------------------------------------- | ------------------------------------------------ |
| `eval-dynamic.fx`               | checks; runs, `-97` (3, and a `wrong`)        | E1: evaluator with tags checked at run time      |
| `eval-phantom.fx`               | checks; runs, `3`                             | E1: phantom-typed constructors, untyped `eval`   |
| `eval-phantom-refused.fx`       | refused: `(exp bool)` where `(exp int)`       | E1: `1 + #f` cannot be built                     |
| `eval-closures.fx`              | checks; runs, `3`                             | E1: an expression is its meaning; no tags        |
| `eq-coercions.fx`               | checks; runs, `42`                            | E2: equality as two coercions, not a proof       |
| `rep-dictionary.fx`             | checks; runs, `"(1 . (#t . 2))"`              | E3: a `rep` as a dictionary                      |
| `exists-closures.fx`            | checks; runs, `44`                            | E4: existentials as closures                     |
| `vec-head.fx`                   | checks; runs, `3`                             | E5: safe `head` of a sized list                  |
| `vec-head-refused.fx`           | refused: `(nlist int 0)` where `1`            | E5: no head of the empty list                    |
| `vec-head-hole.fx`              | refused since the fix (F10)                   | E5: a hole in size inference, found here         |
| `nest-polyrec.fx`               | checks; runs, `3`                             | E6: nested type, polymorphic recursion           |
| `phantom-transparent.fx`        | checks; runs, `0`                             | E7: a phantom index means nothing, transparently |
| `phantom-generative-refused.fx` | refused: `(counted zero)` not `(counted one)` | E7: generative and invariant, it means something |

### What N4 would have to teach the checker

Every proposed example below leans on the same three additions (decision
4), so here they are once:

1. **A variant states its result type.** `(tag field … => (expr int))`; a
   leading list of binders, `((b type) …)`, gives the constructor its own
   type variables, and one not mentioned in the result is **existential**.
   A variant without `=>` means `(expr a)`, as `define-datatype` does today.
2. **Refinement in `tagcase` arms.** The scrutinee's type is `(expr a)`
   with `a` rigid (a `poly` binder, from a declared signature). An arm for
   `int-e` unifies `(expr int)` with `(expr a)` and checks its body under
   the local equation `a = int`: the expected type `a` of the body *is*
   `int` there. Equations, not inequalities, which is why indices are
   invariant (decision 2; E8). GHC asks the same, "type refinement is only
   carried out based on user-supplied type annotations", and FX-26's
   bidirectional checker already has the signature in hand.
3. **Impossible arms and escape.** An arm whose equation cannot hold
   (`vnil`'s `0 = n + 1`) is not needed for exhaustiveness. An
   existential's type may not leave its arm, as a `letregion`'s region may
   not leave its body.

### E1. The typed evaluator

The example every GADT paper starts from. GHC's user's guide:

```haskell
data Term a where
    Lit    :: Int -> Term Int
    IsZero :: Term Int -> Term Bool
    If     :: Term Bool -> Term a -> Term a -> Term a
    Pair   :: Term a -> Term b -> Term (a,b)

eval :: Term a -> a
eval (Lit i)      = i
eval (IsZero t)   = eval t == 0
eval (If b e1 e2) = if eval b then eval e1 else eval e2
eval (Pair e1 e2) = (eval e1, eval e2)
```

`eval` returns a plain `a`, with no tag to check: an ill-typed `Term` cannot
be built, and each equation knows what `a` is.

**Proposed** (N4):

```
(define-datatype (expr (a type))                                   ; proposed
  (int-e  int                                           => (expr int))
  (bool-e bool                                          => (expr bool))
  (add    (expr int) (expr int)                         => (expr int))
  (if-e   ((b type)) (expr bool) (expr b) (expr b)      => (expr b))
  (pair   ((b type) (c type)) (expr b) (expr c)         => (expr (productof (l b) (r c)))))

(define* eval (poly ((a type)) (subr spin ((expr a)) a))           ; proposed
  (lambda (e)
    (tagcase e
      (int-e (n) n)                                   ; a = int, so n : a
      (bool-e (b) b)                                  ; a = bool
      (add (x y) (+ (eval x) (eval y)))               ; a = int; eval at int
      (if-e (c t f) (if (eval c) (eval t) (eval f)))  ; a = b, b fresh
      (pair (x y) (product (l (eval x)) (r (eval y)))))))  ; a = (productof (l b) (r c))
```

`eval` calls itself at `int`, `bool` and `b`: polymorphic recursion, which a
declared `poly` already allows today (E6).

**Today**, three weaker versions, each checked:

- `eval-dynamic.fx`: untyped `expr`, and values tagged `vint`, `vbool` or
  `wrong`. `(add (int-e 1) (bool-e #f))` is accepted and evaluates to
  `wrong`. The core of it:

  ```
  (define-datatype val (vint int) (vbool bool) (wrong unit))
  (define* eval (subr spin (expr) val)
    (lambda (e)
      (tagcase e
        (int-e (n) (vint n))
        (add (x y) (tagcase (eval x)
                     (vint (m) (tagcase (eval y) (vint (n) (vint (+ m n))) (else v (wrong #u))))
                     (else v (wrong #u))))
        …)))
  ```

- `eval-phantom.fx`: phantom types (Leijen and Meijer). A generative
  `(exp a)` wraps the untyped `expr`, and smart constructors give it its
  index, so building `1 + #f` is refused (`eval-phantom-refused.fx`). But
  `eval` is still the one above, and an `(exp int)`'s result is still
  checked for `vint`, in an `else` that never runs. This is where the
  report's "phantom indices mean nothing structurally" bites: the index is
  sound only because `exp` is generative and invariant (E7).

  ```
  (define-generative (exp (a type)) expr)
  (define* add-x (subr pure ((exp int) (exp int)) (exp int))
    (lambda (x y) (up-exp (add (down-exp x) (down-exp y)))))
  (define* if-x (poly ((a type)) (subr pure ((exp bool) (exp a) (exp a)) (exp a)))
    (lambda (c t f) (up-exp (if-e (down-exp c) (down-exp t) (down-exp f)))))
  ```

- `eval-closures.fx`: an expression is its own meaning, a thunk (the
  tagless-final idea with a single interpreter). `eval` is a call and is
  fully typed, but an expression can no longer be inspected, printed or
  optimized; abstracting over the interpreter needs a kind `type → type`.

  ```
  (define-type (exp (a type)) (subr pure () a))
  (define add-x (subr pure ((exp int) (exp int)) (exp int))
    (lambda (x y) (lambda () (+ (x) (y)))))
  (define eval (poly ((a type)) (subr pure ((exp a)) a)) (lambda (e) (e)))
  ```

What N4 adds over these: one datatype that can be both inspected and
evaluated without a run-time check.

### E2. The type-equality witness

```haskell
data Equal a b where
  Refl :: Equal a a

cast :: Equal a b -> a -> b
cast Refl x = x
```

Matching `Refl` teaches the checker `a = b`; the witness is a proof, and
`cast` is the identity at run time.

**Proposed**:

```
(define-datatype (eq (a type) (b type))                   ; proposed
  (refl ((c type)) => (eq c c)))
(define cast (poly ((a type) (b type)) (subr pure ((eq a b) a) b))
  (lambda (w x) (tagcase w (refl () x))))                 ; in the arm, a = b
```

**Today** (`eq-coercions.fx`): a pair of functions, one each way. It works
as a cast, but proves nothing: anyone may build an `(eq int bool)` from two
functions of their own, and the checker learns nothing from holding one.
Leibniz equality (`forall f. f a -> f b`) would be a proof, but needs a
kind `type → type`.

```
(define-type (eq (a type) (b type)) (productof (to (subr pure (a) b)) (from (subr pure (b) a))))
(define refl (poly ((a type)) (eq a a))
  (plambda ((a type)) (product (to (lambda ((x a)) x)) (from (lambda ((x a)) x)))))
(define cast (poly ((a type) (b type)) (subr pure ((eq a b) a) b))
  (lambda (w x) ((extract w to) x)))
```

Decision 3's lemmas are the checker-side cousin: a `proves` definition is an
erased coercion whose existence convinces the checker, but it states `A ≤
B` of fixed families, where `eq` would carry an equation as a value.

### E3. Type representations

Cheney and Hinze's representation types, the basis of generic programming
with GADTs:

```haskell
data Rep a where
  RInt  :: Rep Int
  RBool :: Rep Bool
  RPair :: Rep b -> Rep c -> Rep (b, c)

show :: Rep a -> a -> String
show RInt        n      = Prelude.show n
show RBool       b      = if b then "#t" else "#f"
show (RPair b c) (x, y) = "(" ++ show b x ++ " . " ++ show c y ++ ")"
```

**Proposed**:

```
(define-datatype (rep (a type))                                        ; proposed
  (r-int                                => (rep int))
  (r-bool                               => (rep bool))
  (r-pair ((b type) (c type)) (rep b) (rep c) => (rep (productof (l b) (r c)))))

(define* show (poly ((a type)) (subr spin ((rep a) a) string))         ; proposed
  (lambda (r x)
    (tagcase r
      (r-int () (int->string x))                         ; a = int
      (r-bool () (if x "#t" "#f"))                       ; a = bool
      (r-pair (rb rc) (string-append (show rb (extract x l)) (show rc (extract x r)))))))
```

**Today** (`rep-dictionary.fx`, abridged below): the representation is the dictionary of
operations itself, built by one constructor per type former; this is the
project's dictionary passing. It is closed (only `show` is in it) and
cannot be compared: there is no `rep a → rep b → (maybe (eq a b))`, which
is what dynamic typing with GADTs rests on. `polytypic.md` weighs the two.

```
(define-type (rep (a type)) (productof (show (subr pure (a) string))))
(define r-int (rep int) (product (show (lambda ((n int)) (int->string n)))))
(define r-pair
  (poly ((a type) (b type)) (subr pure ((rep a) (rep b)) (rep (productof (l a) (r b)))))
  (lambda (ra rb) (product (show (lambda ((p (productof (l a) (r b)))) … ((extract ra show) (extract p l)) …)))))
```

### E4. Existential packing

```haskell
data Showable where
  MkShowable :: a -> (a -> String) -> Showable   -- the dictionary, explicitly

showIt :: Showable -> String
showIt (MkShowable x f) = f x
```

**Proposed**: a binder not in the result is existential; in the arm it is
a fresh type, and may not escape it.

```
(define-datatype showable                                        ; proposed
  (mk-showable ((a type)) a (subr pure (a) string) => showable))
(define show-it (subr pure (showable) string)
  (lambda (s) (tagcase s (mk-showable (x f) (f x)))))            ; x : a, a fresh
;; (tagcase s (mk-showable (x f) x)) is refused: a would leave its arm
```

**Today** (`exists-closures.fx`): the object encoding. The operations are
applied to the hidden state ahead of time, and closures keep the state. Two
counters, one over an `int`, one over a `string`, share a type:

```
(define-type counter (productof (next (subr spin () counter)) (get (subr pure () int))))
(define by-int (subr pure (int) counter)
  (letrec ((mk (subr pure (int) counter)
             (lambda (n) (product (next (lambda () (mk (+ n 1)))) (get (lambda () n))))))
    mk))
```

For a toy like this the closures lose nothing. The cost shows when an
operation returns the hidden type: each such result must be wrapped again
(as `next` does, by calling `mk`), and a closure is made per operation per
state, where an existential packs the state once with a shared dictionary.

### E5. Length-indexed vectors and a safe `head`

```haskell
data Nat = Z | S Nat
data Vec (n :: Nat) a where
  VNil  :: Vec Z a
  VCons :: a -> Vec n a -> Vec (S n) a

vhead :: Vec (S n) a -> a
vhead (VCons x _) = x          -- no VNil equation: it cannot match
```

**Today** (`vec-head.fx`): FX-26 already has this, not as a GADT but as a
sort of sizes (decision 5, N5): `(nlist t n)` is a list of `n` elements.

```
(define head (poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) t))
  (lambda (xs) (car xs)))
(define tail (poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) (nlist t n)))
  (lambda (xs) (cdr xs)))
(define three (nlist int 3) (cons 1 (cons 2 (cons 3 nil))))
(+ (head three) (head (tail three)))
```

`((proj head int 0) (the (nlist int 0) nil))` is refused
(`vec-head-refused.fx`). **But `(head (the (nlist int 0) nil))`, with the
size left to inference, is accepted by both checkers and fails at run time
with "expected a pair: ()"** (`vec-head-hole.fx`). Inference leaves `n`
unsolved from `n + 1 = 0`, so `finite`; `(+ finite 1)` is `finite`, which
`(nlist int 0)` fits. The F4 guard of `soundness-findings.md` refuses the
same thing when the argument is a `(nlist int finite)` ("`n` is the size of
… something inside one"), but not here. A soundness bug to fix, independent
of GADTs. *Fixed (2026-09-29, F10 of `soundness-findings.md`):* the
explanation above was near but not exact. Inference solved `n = -1` (the
size less the constant), and nothing asked that a solved size be a
natural. Now both checkers refuse `vec-head-hole.fx`: "the size `n` would
be -1, which is not known here to be no less than 0".

**Proposed**, for a user's own sized family (N4 with N5's sort):

```
(define-datatype (vec (t type) (n size))                    ; proposed
  (vnil                          => (vec t 0))
  (vcons ((m size)) t (vec t m)  => (vec t (+ m 1))))
(define vhead (poly ((t type) (n size)) (subr pure ((vec t (+ n 1))) t))
  (lambda (v) (tagcase v (vcons (x xs) x))))                ; no vnil arm: 0 ≠ n + 1
```

The `vcons` arm's equation `n + 1 = m + 1` is a size fact, decided by N5's
procedure, not by unfolding types; that is decision 5.

### E6. Nested types and polymorphic recursion

```haskell
data Nest a = None | More a (Nest (a, a))

count :: (a -> Int) -> Nest a -> Int
count _ None       = 0
count f (More x t) = f x + count (\(y, z) -> f y + f z) t
```

**Today** (`nest-polyrec.fx`): `nest` must be generative, since its
structure never closes into a cycle (N1); `count` calls itself at `(pair a)`,
that is `(productof (l a) (r a))`, which its declared `poly` allows.

```
(define-type (pair (a type)) (productof (l a) (r a)))
(define-generative (nest (a type))
  (sumof (none unit) (more (productof (hd a) (tl (nest (pair a)))))))
(define* count (poly ((a type)) (subr spin ((subr pure (a) int) (nest a)) int))
  (lambda (f n)
    (tagcase (down-nest n)
      (none u 0)
      (more (hd tl)
        (+ (f hd)
           (count (lambda ((p (pair a))) (+ (f (extract p l)) (f (extract p r))))
                  tl))))))
```

Decision 3's lemma for it, `nest-up`, is `tests/programs/lemmas/nest.fx`: the
same walk, as an erased proof that `(nest a) ≤ (nest b)` when `a ≤ b`.

### E7. What a phantom index means

The prototype's finding, in four lines. Under a transparent abbreviation
the index is thrown away (`phantom-transparent.fx`, accepted):

```
(define-type (counted (i type)) (listof int acyclic))
(define from-zero (counted zero) (list 0 1))
(define from-one (counted one) from-zero)          ; accepted: both are lists
```

Made generative (N1), invariant by default (N2), it is refused
(`phantom-generative-refused.fx`):

```
(define-generative (counted (i type)) (listof int acyclic))
(define from-zero (counted zero) (up-counted (list 0 1)))
(define from-one (counted one) from-zero)          ; refused: (counted zero)
```

GHC makes the same choice with roles: a GADT index, or a declared `type
role Counted nominal`, may not be `coerce`d across.

### E8. Why GADT indices stay invariant

Scherer and Rémy's counterexample, OCaml, where objects have width
subtyping (`< m : int >` ≤ `< >`):

```ocaml
type +'a bad = K : < m : int > -> < m : int > bad   (* the + must be refused *)
let get_eq : 'a bad -> ('a, < m : int >) eq = function K _ -> Refl
```

If `bad` were covariant, a `< m : int > bad` would be a `< > bad`, and
`get_eq` on it would give `(< >, < m : int >) eq`: any object cast to one
with an `m`. FX-26's sums have width subtyping too, so the same example
transfers exactly:

```
(define-datatype (bad (a type +))                          ; proposed, and refused
  (k (sumof (m int)) => (bad (sumof (m int)))))
;; (bad (sumof (m int))) ≤ (bad (sumof (m int) (n bool))) by the +, then
;; matching k teaches a = (sumof (m int)): an (n #t) passes as a sum with
;; only m, and a tagcase with only an m arm falls off the end.
```

So `(sumof …)` is not upward-closed, nor is any type with region or effect
subsumption in it; hence decision 2's "few FX-26 types qualify". Their
paper's justification of a sound `+` is itself a coercion written by case
analysis (`let coerce : α exp → α′ exp = function …`), which is decision
3's lemma in other clothes.

### Sources for the examples

- GHC User's Guide 9.14.1, "Generalised Algebraic Data Types (GADTs)",
  <https://downloads.haskell.org/ghc/latest/docs/users_guide/exts/gadt.html>
  (fetched 2026-09-29; `Term a` and the rigidity requirement quoted from it,
  cut to four constructors).
- Scherer and Rémy, "GADTs meet subtyping", ESOP 2013,
  <https://arxiv.org/abs/1301.2903> (v1; `docs/research/papers/`): the
  `bad` counterexample, the `coerce` sketch, upward closure (§1).
- Cheney and Hinze, "A lightweight implementation of generics and
  dynamics", Haskell Workshop 2002 (`docs/research/papers/cheney-hinze-hw02.pdf`):
  representation types (E3).
- From memory, not rechecked: Leijen and Meijer, "Domain specific embedded
  compilers", DSL 1999 (phantom types, E1); Carette, Kiselyov and Shan,
  "Finally tagless, partially evaluated", JFP 2009 (E1); Bird and Meertens,
  "Nested datatypes", MPC 1998 (E6); Mitchell and Plotkin, "Abstract types
  have existential type", TOPLAS 1988 (E4); Xi, Chen and Chen, "Guarded
  recursive datatype constructors", POPL 2003, and the `Vec` example's
  folklore form (E5).

## GADTs and latent propositions: one idea about two things

The user's question, 2026-10-08: is there a deeper connection between
unions with Typed Racket's latent propositions (`docs/fx26.md`, "What a
test proves is in its type") and GADTs, in the code and the static
reasoning each enables; and if so, should their syntax be linked?

**Both are hypothetical reasoning in a branch.** A test that comes out a
certain way at run time adds an assumption, and the branch is checked
under it: Γ, ψ ⊢ e. They differ in what ψ is about.

| Feature                    | Prop. about       | Example ψ          | Refines by                   | Dies when          |
| -------------------------- | ----------------- | ------------------ | ---------------------------- | ------------------ |
| union, latent propositions | a value, a path   | `(shape 0 int)`    | meet: `val ∧ int`            | a write it reads   |
| GADT `tagcase` arm         | a type variable   | `(= a int)`        | equation, `a` rigid          | never (types stay) |

The difference in the third column is the variance story of E8. A meet
on a value's own type is sound under subtyping, so narrowing needs no
invariance. An equation on an index is substituted everywhere the index
is used, both in and out, so the index must be invariant. The fourth
column is the path rule's mutation condition. A type variable has none.

**The link is a translation, not an analogy.** A GADT elaborates into a
union of guarded existentials. That is Xi, Chen and Chen's "guarded
recursive datatype constructors", and it is how GHC checks a match: each
arm is an implication constraint (OutsideIn(X), Vytiniotis, Peyton Jones,
Schrijvers and Sulzmann, JFP 2011; from memory). E1's `expr`, so read:

```
(expr a) ≅ (union (int-e int)                              given (= a int)
                  (bool-e bool)                            given (= a bool)
                  ∃b. (if-e (expr bool) (expr b) (expr b)) given (= a b)
                  …)
```

Read the other way, a latent-proposition type is a GADT of two
constructors with its evidence erased. `(bool (then P) (else Q))` is
`(union (#t given P) (#f given Q))`, which is Agda's `Dec P` or Haskell's
`data Dec p where Yes :: p => Dec p; No :: Not p => Dec p`. A shape
predicate is a function returning a `Dec` whose payload is one bit. Both
features let a run-time tag tell the checker something it could not know
statically. A union's tag says what a value is. A GADT's says what a
type is.

TypeScript's discriminated unions sit between the two (from memory): a
test of a tag field narrows the object's type, a path, but never a type
parameter. Refining the parameter is exactly what N4 adds. FX-26 already
has the half before it: after a `typecase` has excluded every other
shape, the evaluator's `val` narrows to its `other` datatype, which
`tagcase` then takes apart (`eval-values.fx`, 2026-10-08).

### What to link, and what not

1. **One language of propositions.** Latent propositions have atoms:
   `(shape i S)`, `(acyclic i)`, `(nat i)`, `(length i j)`, and the size
   comparisons `(< a b)`, `(<= a b)`, `(= a b)`. This note has `=> (expr
   int)` on variants (N4) and `(proves P given Q)` for lemmas (decision 3).
   These become one grammar. A type equation `(= a int)` is one more atom,
   `given` is the keyword for "holds under" everywhere, and a variant's
   `=> (expr int)` is sugar for `given (= a int)` on a variant of result
   `(expr a)`, which is also how the checker would elaborate it. A
   size-indexed variant's guard (E5, `vcons`: `(= n (+ m 1))`) is then
   literally a size fact, of the kind `<` and `null?` already prove.
2. **Parameters by name** (decided by the user, 2026-10-08). Latent
   propositions name arguments by position (`(shape 0 int)`), while
   guards name type variables. So a `subr` type may name its parameters,
   `(subr pure ((x val)) (bool (then (shape x int))))`, and propositions
   refer to them by name, as guards refer to binders. Numbered references
   stay for unnamed parameters. Naming is also what a dependent `subr`
   needs, so that a result's type can mention an argument (M5's functors
   already bind one). `TODO.md` §65.
3. **Two rules in the checkers, not one.** Meet-narrowing of values and
   equational refinement of rigid variables keep separate soundness
   conditions: mutation for the first, variance for the second. A shared
   syntax is cheap. A shared rule would force one feature into the
   other's constraints. They meet in one place: a guard that is a value
   fact (a size from a field, `(nat i)`) is checked by the size rules,
   which are the same whether a test or a constructor proved the fact.

Sources, from memory and not rechecked: Tobin-Hochstadt and Felleisen,
"Logical types for untyped languages", ICFP 2010 (latent propositions);
Xi, Chen and Chen, POPL 2003 (guarded types); Vytiniotis et al., JFP 2011
(implication constraints); Norell's Agda thesis, 2007, and the Agda
standard library (`Dec`).

## Stages

| Stage | Size | What                                                                                         |
| ----- | ---- | -------------------------------------------------------------------------------------------- |
| N1    | M    | nominal families: a type node, in both checkers; safety analyses look through (G1, G2), done |
| N2    | S    | variance declared, checked once; invariant by default, done                                  |
| N3    | M    | lemmas: `proves` types, checked as erased identity coercions, done                           |
| N4    | L    | GADTs: constructor result types, existentials, refinement in `tagcase`                       |
| N5    | L    | size indices as their own sort, for `confirm` (CF1, CF3)                                     |
| N6    | M    | the `data` kind, with `read` and `acyclic` (CF0), done (acyclic; read later)                 |

`define-datatype` stays transparent by default; a generative variant is
`generative-types.md`'s G3, and hiding (G4) comes when wanted.
