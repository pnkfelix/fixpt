# Sizes: lists that say how long they are

Design note, 2026-09-27 (`docs/research/gadts.md`, N5;
`docs/research/confirmation.md`, CF1, CF3, CF4). With the user: sizes
before GADTs, since they need the same machinery (facts learned in a
branch, existentials) in a small domain that stays decidable; and a top
size, `finite`, for a list known to end but not how soon.

## What a list type can know

From least to most:

| type                | what is known                                          |
| ------------------- | ------------------------------------------------------ |
| `(listof T r)`      | nothing: `r` may be written, so the list may be cyclic |
| `(listof T const)`  | it will not change; it may be cyclic                   |
| `(listof T finite)` | it will not change, and it ends                        |
| `(nlist T finite)`  | the same: it has some length, not known here           |
| `(nlist T n)`       | it has exactly `n` elements                            |

So `(nlist T finite)` and `(listof T finite)` are the same type, each a
subtype of the other; `(nlist T n) ≤ (nlist T finite)` forgets the length. A
list that may be cyclic has no length, and is no `nlist`: `acyclic` or
`confirm` is the way in.

## The forms

- **Types.** `(nlist T size)`, its pairs frozen in the heap; `(nlist T size p)`,
  frozen into place `p`, as `(finite p)` is.
- **Sizes.** A literal (`0`, `3`), a variable of kind `size`, `(+ s s)`,
  `(- s k)` with `k` a literal, and `finite`, the top: some size.
- **Binders.** `(poly ((n size)) …)`, so `map` is
  `(poly ((t type) (u type) (n size)) (subr e ((subr e (t) u) (nlist t n)) (nlist u n)))`.
  A size binder may be instantiated with `finite`, so `map` over a
  `(nlist t finite)` gives a `(nlist u finite)`.

## What the checker learns and uses

- **`cons`** onto a `(nlist T n)`, frozen, gives a `(nlist T (+ n 1))`; `nil`
  where a `nlist` is expected is a `(nlist T 0)`.
- **In a branch** of `(null? xs)` with `xs : (nlist T n)`: `n = 0` in the
  `then`, `n ≥ 1` in the `else`. These are facts, kept in a context as
  `acyclic?`'s certified variables are; N4 will put type equalities in the
  same context.
- **`cdr`** of a `(nlist T n)` is a `(nlist T (- n 1))` where the facts show
  `n ≥ 1`, and a `(nlist T finite)` where they do not: never an error, only
  less known. `car` is as for any list.
- **Comparing sizes**: `(nlist T s) ≤ (nlist U s′)` when `T ≤ U` and the facts
  show `s = s′`, or `s′` is `finite`.
- **Size-change**: a `nlist`'s `cdr` is a part, as a finite list's is.

## Deciding facts

Sizes are naturals, facts are linear: equalities and `≥`. N5a needs only
literals; N5b equalities between variables and literals plus `n ≥ 1`,
decided by normalizing each side to a sum of variables and a constant;
N5c arithmetic and inequalities in general, by Fourier–Motzkin
elimination over the few facts in scope (Dependent ML's approach, from
memory: Xi and Pfenning). Anything not shown is not assumed: the answer
is then `finite`, or an error saying which size could not be shown equal.

## `confirm` for sizes

`(confirm-length e n (x body) else)`: if `e`, a list that is data and
frozen, is acyclic and has `n` elements (`n` a size expression the
checker can compute from variables in scope, or a literal), `body` runs
with `x : (nlist T n)`; otherwise `else`. Sugar, as `acyclic` is, over a
test and a certifying conversion the checker accepts only in its branch.

## `nat`, and sizes as values (the user's, 2026-09-27)

- **`nat`**, a base type below `int`: never negative. Size-change then has
  a bound below for free on a `nat` that counts down; typing `(- n 1)` as a
  `nat` needs the fact `n ≥ 1`, which N5b's facts give.
- **`(nat s)`**, the singleton: exactly the size `s`, as Dependent ML's
  `int(n)` (from memory). What links values to sizes: `length : (nlist T n)
  → (nat n)`, `confirm-length` with a length computed at run time, and an
  array index `(nat i)` with the fact `i < n` (CF4).

## Stages

| stage | what                                                                                                                                      |
| ----- | ----------------------------------------------------------------------------------------------------------------------------------------- |
| N5a   | done: the `nlist` type with literal sizes and `finite`; `cons`, `nil`; `nlist finite` as `listof finite`; `confirm-length` with a literal |
| N5b   | done: kind `size`, variables in `poly`; facts from `null?`; `cdr`; equalities                                                             |
| N5c   | arithmetic and inequalities (Fourier–Motzkin); existentials for results such as `filter`'s; array bounds                                  |
| N5d   | `nat` and `(nat s)`; `length`; `confirm-length` with a run-time length                                                                    |
