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
| `(vec T finite)`    | the same: it has some length, not known here           |
| `(vec T n)`         | it has exactly `n` elements                            |

So `(vec T finite)` and `(listof T finite)` are the same type, each a
subtype of the other; `(vec T n) ≤ (vec T finite)` forgets the length. A
list that may be cyclic has no length, and is no `vec`: `acyclic` or
`confirm` is the way in.

## The forms

- **Types.** `(vec T size)`, its pairs frozen in the heap; `(vec T size p)`,
  frozen into place `p`, as `(finite p)` is.
- **Sizes.** A literal (`0`, `3`), a variable of kind `size`, `(+ s s)`,
  `(- s k)` with `k` a literal, and `finite`, the top: some size.
- **Binders.** `(poly ((n size)) …)`, so `map` is
  `(poly ((t type) (u type) (n size)) (subr e ((subr e (t) u) (vec t n)) (vec u n)))`.
  A size binder may be instantiated with `finite`, so `map` over a
  `(vec t finite)` gives a `(vec u finite)`.

## What the checker learns and uses

- **`cons`** onto a `(vec T n)`, frozen, gives a `(vec T (+ n 1))`; `nil`
  where a `vec` is expected is a `(vec T 0)`.
- **In a branch** of `(null? xs)` with `xs : (vec T n)`: `n = 0` in the
  `then`, `n ≥ 1` in the `else`. These are facts, kept in a context as
  `acyclic?`'s certified variables are; N4 will put type equalities in the
  same context.
- **`cdr`** of a `(vec T n)` is a `(vec T (- n 1))` where the facts show
  `n ≥ 1`, and a `(vec T finite)` where they do not: never an error, only
  less known. `car` is as for any list.
- **Comparing sizes**: `(vec T s) ≤ (vec U s′)` when `T ≤ U` and the facts
  show `s = s′`, or `s′` is `finite`.
- **Size-change**: a `vec`'s `cdr` is a part, as a finite list's is.

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
with `x : (vec T n)`; otherwise `else`. Sugar, as `acyclic` is, over a
test and a certifying conversion the checker accepts only in its branch.

## Stages

| stage | what                                                                                                                            |
| ----- | ------------------------------------------------------------------------------------------------------------------------------- |
| N5a   | the `vec` type with literal sizes and `finite`; `cons`, `nil`; `vec finite` as `listof finite`; `confirm-length` with a literal |
| N5b   | kind `size`, variables in `poly`; facts from `null?`; `cdr`; equalities                                                         |
| N5c   | arithmetic and inequalities (Fourier–Motzkin); existentials for results such as `filter`'s; array bounds                        |
