# PLDI '89 control effects: the cases, for review

Jouvelot & Gifford, *Reasoning about Continuations with Control Effects*,
PLDI '89. The file is `GiffordHistory/papers/pldi89-jouvelot.pdf`. Page
numbers here are **PDF pages**; proceedings page = PDF page + 217.

No implementation of control effects survives. The archived FX-87 has none.
So these cases are the specification FX-26's step 1 is built against. They
are written down, and reviewed, **before** any code exists, so that the code
is checked against the paper and not against my reading of the paper after
the fact.

## What each claim rests on

Every expected result is marked with one of three bases:

- **STATED**: the paper says it, at the cited place.
- **DERIVED**: it follows from the paper's rules. The rules used are cited
  and the steps given, so it can be checked.
- **TRANSCRIBED**: the paper writes the example in untyped Scheme. The typed
  FX-26 form is mine.

The TRANSCRIBED parts are where I am most likely to be wrong. Three problems
recur:

1. **Several examples return a continuation as the value of its own `cwcc`**,
   `(cwcc (lambda (x) x))` for instance. The result type is then the
   continuation's own type, `t = (subr (goto r) (t) void)`, which is recursive.
   KFX has no recursive types, so these need the kernel's `dletrec`.
2. **One example (C4) is not well typed as written.** It calls a continuation
   of one type with `0`. That is fine in Scheme; the typed transcription keeps
   only the part that types.
3. **The paper states masking conditions but not where masking is applied.**
   I read it as applying to the whole expression under test, which is how
   FX-87's checker reports a top-level form's effect. Expected results say
   "after masking" when they mean that.

Region constants such as `@k` stand in for the paper's "some region r". Free
variables an example needs are listed with the types I give them.

The initial environment used throughout: FX-87's standard environment
(`new`, `get`, `set`, `cons`, `car`, `cdr`, `set-car!`, `set-cdr!`, `+`, with
the region-polymorphic types in `crates/fixpt-fx87/src/standard.fx`), plus
`void` and:

```
cwcc : (poly ((r region)) (poly ((t type)) (poly ((e effect))
         (subr (maxeff (comefrom r) e)
               ((subr e ((subr (goto r) (t) void)) t))
               t))))
```

**STATED**, p. 4. The paper writes the binders one to a `poly`, `(poly (r
region) …)`. FX-87's surface wraps each binder list in parentheses, which is
the only change.

---

## C1 — `twice`: KFX without control (p. 3)

Checks that the kernel reproduces the paper's own example before any control
is involved.

Paper, verbatim:

```scheme
(plambda (t type)
  (plambda (e effect)
    (lambda (f (subr e (t) t))
      (lambda (x t)
        (f (f x))))))
```

Transcription (FX-87 surface; only the binder parentheses change):

```scheme
(plambda ((t type))
  (plambda ((e effect))
    (lambda ((f (subr e (t) t)))
      (lambda ((x t)) (f (f x))))))
```

Expected:

- type `(poly ((t type)) (poly ((e effect)) (subr pure ((subr e (t) t)) (subr e (t) t))))`.
  **STATED**, p. 3.
- effect `pure`. **DERIVED**: the `plambda` rule gives `pure` (p. 3).
- The inner lambda's latent effect is `(maxeff e (maxeff e pure …))`, which
  normalises to `e`. **DERIVED**: application rule, p. 3.

---

## C2 — `cwcc`'s type (p. 4)

Expected: `cwcc` is bound in the initial environment to exactly the type
above. **STATED**, p. 4.

---

## C3 — a well-behaved use: control effects masked (p. 5)

Paper, verbatim: `(+ (cwcc (lambda (f) (f 0))) 1)`, which "has both `(goto r)`
and `(comefrom r)` effects for some region r. However, it is easy to prove that
this expression is well-behaved … Its control effects can thus be masked"
(p. 5).

Transcription:

```scheme
(+ ((proj (proj (proj cwcc @k) int) (goto @k))
    (lambda ((f (subr (goto @k) (int) void))) (f 0)))
   1)
```

The projections are `r = @k`, `t = int`, and `e = (goto @k)`, the latent
effect of the argument, whose body `(f 0)` calls the continuation. `(f 0)` has
type `void`, and the argument must return `int`: this needs `void ≤ int`
(kernel note on `void`).

Expected:

- type `int`. **DERIVED**: the result type `t` of `cwcc`, projected to `int`.
- before masking, effect `(maxeff (comefrom @k) (goto @k))`. **STATED**
  ("both `(goto r)` and `(comefrom r)` effects", p. 5). The exact form is
  **DERIVED** by the application rule (p. 3): `cwcc`'s instance has latent
  effect `(maxeff (comefrom @k) (goto @k))`, and the `proj`s, the `lambda`, the
  literals and `+` are pure.
- after masking, effect `pure`. **STATED** ("its control effects can thus be
  masked", p. 5). Checked against the conditions (p. 6): the expression
  imports only `cwcc` and `+`, and neither type mentions `@k`, because `cwcc`
  binds its region. The result type `int` does not mention `@k`.

---

## C4 — the `goto` example: `(f g)` has a control effect (p. 4)

Paper, verbatim:

```scheme
(let ((x (cwcc (lambda (f)
                 (cwcc (lambda (g) (f g)))
                 (h)
                 f))))
  (horrible-effects)
  ...
  (x 0)
  ...)
```

"between the evaluations of `(f g)` and `(h)`, `(horrible-effects)` will be
executed; thus these expressions cannot be reordered" (p. 4).

Transcription: **only the argument to the outer `cwcc`**. The whole `let` does
not type. `x` is the continuation `f`, since the argument returns `f`, and
`(x 0)` passes it `0`, which is not a continuation. Let
`K = (dletrec ((k (subr (goto @k) (k) void))) k)`: the continuation, whose
argument type is its own type, since it is returned as its own result. Free
`h : (subr pure () unit)`.

```scheme
(lambda ((f K))
  ((proj (proj (proj cwcc @k) K) (goto @k))
   (lambda ((g K)) (f g)))
  (h)
  f)
```

The inner `cwcc` has to be projected on the same region `@k` with `t = K`,
because `(f g)` passes `g` where `f` takes a `K`.

Expected:

- the subexpression `(f g)` has effect `(goto @k)`. **DERIVED**: `f`'s latent
  effect is `(goto @k)`, and the application rule gives it to the call (p. 3,
  and "providing a continuation with a `(goto r)` latent effect", p. 4).
- the body's effect includes `(comefrom @k)` and `(goto @k)`. **DERIVED**,
  the same way. This is the property behind the paper's "cannot be
  reordered": `(f g)` has an effect, so moving `(h)` past it is not
  allowed.

---

## C5 — `cwcc` calls cannot be pure (p. 4)

Paper, verbatim:

```scheme
(let* ((f1 (cwcc (lambda (x) x)))
       (x (horrible-effects))
       (f2 (cwcc (lambda (x) x))))
  ...)
```

"a compiler cannot common subexpression eliminate calls to `cwcc` … Thus the
`cwcc` calls cannot be pure" (p. 4).

Transcription: one of the two identical calls. `K` as in C4.

```scheme
((proj (proj (proj cwcc @k) K) pure) (lambda ((x K)) x))
```

Expected:

- effect `(comefrom @k)`, not `pure`. **STATED** ("cannot be pure", p. 4). The
  exact form is **DERIVED** from `cwcc`'s latent effect with `e = pure`.
- still `(comefrom @k)` after masking. **DERIVED**: the result type `K`
  mentions `@k`, so the `comefrom` condition (p. 6) fails.

---

## C6 — storing a continuation: `comefrom` not maskable (p. 6)

Paper, verbatim:

```scheme
(begin (cwcc (lambda (f)
               (set x (lambda () f))))
       (h))
```

"isn't continuation discarding, since the well-behaved context
`(begin [] ((get x)))` returns a caught continuation" (p. 6).

Transcription. Let `C = (subr (goto @k) (unit) void)`. Free `x : (ref (subr
pure () C) @x)` and `h : (subr pure () unit)`. `set` returns `unit`, so `t =
unit`, and the argument's latent effect is `(write @x)`.

```scheme
(begin ((proj (proj (proj cwcc @k) unit) (write @x))
        (lambda ((f C))
          ((proj (proj set @x) (subr pure () C)) x (lambda () f))))
       (h))
```

Expected:

- before masking, effect `(maxeff (comefrom @k) (write @x))`. **DERIVED**
  (application rule, p. 3).
- after masking, still includes `(comefrom @k)`. **DERIVED** from the
  `comefrom` masking theorem (p. 6): the expression imports `x`, whose type
  mentions `@k`. This is the typed form of the paper's STATED point that the
  expression "isn't continuation discarding" (p. 6).
- `(write @x)` is not masked either: `x` is imported and its type mentions
  `@x` (FX-87's memory masking, p. 6).

---

## C7 — the contrived example: `goto` not maskable without free variables (p. 7)

Paper, verbatim:

```scheme
(let ((x (cwcc (lambda (f)
                 (let ((y (cons f f)))
                   (cwcc (lambda (g)
                           (set-cdr! y g)
                           (f y)))
                   ((car y) y))))))
  (cwcc (lambda (h)
          (set-car! x h)
          ((cdr x) x))))
```

"an expression with a goto effect that cannot be masked, even though this
expression has no free variables … thus requiring the supplementary check on
the regions appearing in return type" (p. 7). The expression meant is `x`'s
binding expression, the first `cwcc` form.

Transcription: the binding expression only. The types are mutually
recursive. `y` is a pair of continuations, and the continuations are passed
that pair:

```
P = (dletrec ((p (pairof k k @p)) (k (subr (goto @k) (p) void))) p)
K = (dletrec ((p (pairof k k @p)) (k (subr (goto @k) (p) void))) k)
```

```scheme
((proj (proj (proj cwcc @k) P)
       (maxeff (alloc @p) (comefrom @k) (write @p) (read @p) (goto @k)))
 (lambda ((f K))
   (let ((y ((proj (proj cons @p) K K) f f)))
     ((proj (proj (proj cwcc @k) P) (maxeff (write @p) (goto @k)))
      (lambda ((g K))
        ((proj (proj set-cdr! @p) K K) y g)
        (f y)))
     (((proj (proj car @p) K K) y) y))))
```

The outer argument's latent effect covers everything its body does:
- `cons` allocates in `@p`;
- the inner `cwcc` call has `(comefrom @k)`, and its argument writes `@p` and
  jumps to `@k`;
- `car` reads `@p`;
- `((car y) y)` calls a continuation.

`cons`, `car` and `set-cdr!` have both type variables in one `poly`, so both
are projected at once (`(proj E D1 D2)`, as FX-87 parses it). `cwcc` has one
binder per `poly`, so one `proj` each.

**This is the transcription I am least sure of.** The paper does not type
it, and the latent effects I projected for `e` are my own accounting. Two
things are meant to hold regardless: both `cwcc`s share `@k`, because
`set-cdr!` puts `g` where `f` was; and the continuation argument type is `P`.

Expected:

- after masking, the effect still includes `(goto @k)`. **STATED** (p. 7). It
  has no free variables. The condition that blocks masking is the one on the
  result type: `P` mentions `@k` (p. 6 theorem, and p. 7's "the supplementary
  check on the regions appearing in return type").
- The checker must **not** mask it just because there are no free variables.
  That rule would be the memory-effect rule; the paper's point is that it is
  unsound for `goto`.

---

## Questions for the reviewer

1. **Where is masking applied?** I assume at the whole expression under test
   (note 3 above). If you read the paper, or FX-87, as masking at every
   subexpression that meets the conditions, C4's "the body's effect includes
   `(comefrom @k)`" needs rechecking.
2. **`void` as a subtype of every type.** It is needed for C3 to type, and
   the paper does not state it.
3. **C7's projected latent effects.** Right, or too much?
