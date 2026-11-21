# A `moduleof` whose members' types name earlier members

Research note, 2026-11-20, for Heist's should-work note, entry 11
(`TODO.md` §304): module files that restate their parameter chains. It
proposes one extension, settles the questions it raises, and compares it
with the route that needs none. **Step 1 of §6 is built** (2026-11-20, both
checkers): `Ty::MemberSel` (`ty-member`), read in a written `moduleof`
(`select_members`, `k-select-members`), closed by a binding's paths
(`name_module`'s `path_opened`, `k-path-opened`) or by the left side's
members in a comparison and a reshape (`members_closed`,
`members_closed_as`); tests `modules/dependent-moduleof*.fx`. **Step 2 is
built** (2026-11-21): inclusion leaving out a member a kept one names gives
its types by their own names (`left_members_types`, `k-reshaped-type`), and
`restrict` keeps it as `%hidden:x` (`vals_kept`, `k-vals-kept`). **Step 3
is built** (2026-11-21): an item's type naming an earlier item's own types
names them as that member's (`items_as_members`, `k-items-as-members`).
Steps 4 and 5 are not.

## 1. The problem, in Heist's own files

`heist/editor/frame.fx` begins:

```scheme
(module-parameters ((m-base (load-moduleof "base.fx"))
                    (m-buffer (load-moduleof "buffer.fx" m-base))
                    (m-resolve (load-moduleof "resolve.fx" m-base m-buffer))
                    (m-syntax (load-moduleof "syntax.fx" m-base m-buffer m-resolve))
                    (m-sexp (load-moduleof "sexp.fx" m-base m-buffer m-resolve m-syntax))
                    (m-index (load-moduleof "index.fx" m-base m-buffer m-resolve m-syntax m-sexp))
                    (m-view (load-moduleof "view.fx" m-base m-buffer m-resolve m-syntax m-sexp m-index))))
```

Each module is an instance, a maker applied, so its abstract types are
named by the variable it is bound to (`fx26.md`, "Modules"). A file that
uses `view.fx`'s module must be told which `base`, `buffer`, … it was
made over, so it binds each and passes them: a telescope, restated in every
file, quadratic in the chain's length. The editor has 132 such entries in
12.8K characters, ratfink an 18-line chain in 8 files.

The obvious remedy, one module holding the others, fails: a bundle's type
cannot say that its `buffer` is over its own `base`.

```scheme
(moduleof (val base (load-moduleof "base.fx"))
          (val buffer (load-moduleof "buffer.fx" base)))   ; `base` is not bound here
```

## 2. What the sources and the checkers say today

- **FX-91 §2.2.6** (`papers/gifford-jouvelot-sheldon-otoole-1992-fx91-report.pdf`,
  p. 10): "A moduleof expression is a binding construct." Its rule checks
  each `desc` in `TK[∪ idᵃᵢ :: kᵢ]` and each `val`'s type as `[∪ dxₖ/idᵈₖ]
  txⱼ :: type` in the same context: the `abs` names in scope, the `desc`
  names substituted, the `val` names nowhere. So the proposal below departs
  from FX-91, deliberately. (Our FX-91 front end reads `val` types with the
  `val` names in scope, `fixpt-fx91/src/parse.rs`'s `new_alpha`: looser than
  the report, to be looked at on its own.)
- **Sheldon** (`papers/sheldon-1989-ms-thesis-…pdf`, §4.1.5, pp. 47-48):
  "The system presented in this thesis has no concise way to express
  sharing constraints … This is awkward and entails extra subroutine
  calls." The chains are that awkwardness. FX-91's transparent `desc` was
  the first answer; this would be the second.
- **The precedent** is Standard ML's signatures, where a later
  `structure User : USER where type t = Base.t` names an earlier
  structure spec of the same signature; and the theory behind it, Leroy's
  manifest types and Harper and Lillibridge's translucent sums.
- **FX-26's machinery** is most of the way there:
  - `Ty::Module { abs, descs, vals }` (`ast.rs`), its `abs` binders in
    scope in its descriptions and values' types, as FX-91's.
  - `Ty::ParamSel(k, t)`, `(select $k t)`: in a procedure's type, the
    type `t` of its `k`th parameter. "A call puts the argument's for it."
    A dependent subroutine, M5. The proposal is the same thing indexed by
    member, not parameter.
  - Paths and strengthening (`fx26.md`): `(select (with mid a) t)` is
    `mid.a..t`, "a module is a value made once and never changed, and so
    is each of its values, so a path names the same module wherever it is
    read in its base's scope". A `let` or `define` of a path keeps the
    path's types (ML's strengthening).
  - The rule to relax, said plainly there: "A module item's `define` of a
    path is opaque still, as an item's type may not name what its module
    made."
  - Inclusion, `Checker::module_sub` (`check.rs`): the same values, by
    name and in order, `reshape` making fewer or another order; abstract
    types paired as a `poly`'s binders are, or defined by the other side's
    transparent ones.

## 3. The proposal

**A `val` member's type may name an earlier `val` member of the same
`moduleof`**: `(select x t)`, a path `(with x y)` in it, or an argument of
a `load-moduleof`, `x` an earlier member. Nothing else changes: `abs` and
`desc` as FX-91 has them, and a `val`'s type still sees the `abs` names
and the `desc`s substituted.

```scheme
;; editor/env.fx: the chain, said once, by the file that makes it
(module-parameters ())
(define base ((load-module "base.fx")))
(define buffer ((load-module "buffer.fx") base))
(define resolve ((load-module "resolve.fx") base buffer))
…
(define view ((load-module "view.fx") base buffer resolve syntax sexp index))
```

Its module's type, which `(load-moduleof "env.fx")` gives, is then the
dependent one:

```scheme
(moduleof (val base (load-moduleof "base.fx"))
          (val buffer (load-moduleof "buffer.fx" base))
          (val resolve (load-moduleof "resolve.fx" base buffer))
          …)
```

and `frame.fx` takes one parameter:

```scheme
(module-parameters ((env (load-moduleof "env.fx"))))
(hide (include env::base) (include env::buffer) … (include env::view))
```

Its types are `env.base..t`, `env.view..u`, …: every file given the same
`env` agrees on them, by path. The driver applies `env.fx` once. A layer
past `view` is a module over `env` (`frame.fx` above); one that later
files take with it is the next bundle, `(val env (load-moduleof "env.fx"))
(val frame (load-moduleof "frame.fx" env))`, nested rather than merged.

## 4. The questions, and the answers proposed

1. **Scope: earlier members only.** A telescope, in written order, as a
   module's items see the items before them and a parameter list's types
   the parameters before them. No member names a later one or itself: the
   type is well founded, and what a module item's value may read is what
   its type may name.

2. **Soundness, Sheldon's Design Constraint 1** (thesis p. 21: "Value
   expressions occurring in descriptions must not have read effects").
   For a module `m` of such a type, a member's `(select x t)` means
   `(select (with m x) t)`: a selection through a path of a module's
   fields, which are immutable (a module is a `product`, not settable).
   It reads nothing, so two of them name one module and one type.
   Equality stays by path, as `select`'s already is.

3. **Binding (strengthening).** A variable `m` of a dependent type has
   each member's sibling selections put as `m`'s paths: `buffer`'s
   `(select base t)` becomes `m.base..t`. The representation is a member
   selection `Ty::MemberSel(k, path, t)` beside `ParamSel`, resolved where
   the type is bound, as `ParamSel` is where a procedure is called.

4. **Inclusion.** `a ≤ b` when each of `b`'s members is one of `a`'s, of
   a type `a`'s is included in once `b`'s sibling selections are read as
   `a`'s members' (a dependent product's depth subtyping: earlier
   components the same module, later ones' types compared in their light).
   FX-91 lets members be permuted; a dependent `b` may be in any order
   that keeps each member after those it names, and `reshape` makes the
   product in `b`'s order from values that exist already.

5. **Dropping a member that a later one names** (width; `restrict`). A
   `b` without `base` cannot write `(select base t)`, so its `buffer`'s
   type says `t` otherwise: abstract, `(moduleof (abs t type) …)`, which
   `a`'s fits by M4 once its selection is read as `a`'s path. `restrict`,
   dropping a member a kept one names, keeps it unnamed, as it keeps an
   abstract type unnamed today (`(abs %hidden:t type)`): `(val
   %hidden:base …)`, present, never named by a client, so that what was
   kept still means what it meant.

6. **`with`, `include`, `select`.** `(with m buffer)` has `buffer`'s type
   with its selections read as `m`'s paths; `(include env::buffer)` of a
   path aliases its types by that path, `env.buffer..t`, as `(include m)`
   of a name aliases `m..t` (`fx26.md`, "include"); an `include` of a
   path must so be allowed where today it takes a module's name.

7. **Reps and `.fasl`s.** One node more beside `param-sel`
   (`reps.rs`, `check-reps.fx`): `(member-sel k path t)`. A module type
   in a `.fasl` keeps it as written; nothing else changes there.

8. **The expander's shapes** carry names alone, and a member's names do
   not depend on which `base` it is over, so `Shape` is unchanged; a
   `load-moduleof` with members as arguments is read for its names as one
   with parameters is.

9. **Both checkers**, as every feature: `Ty::MemberSel` and FX-26's
   counterpart (`check-types-arena.fx`'s variants, `k-type-shape`,
   `check-reps.fx`), the item rule relaxed in both module checkers, and
   `restrict`, `module_sub`'s and `k-module-sub`'s inclusion alike.

## 5. Against the route that needs no extension

The chain can be shortened today by **flattening and accumulating**
(checked on a two-stage example, 2026-11-20): each stage takes the
previous one `qualified` and `include`s it openly, so the shared types
become the stage's own type members; the next stage takes one parameter
whose type, `(moduleof (abs t type) (val …) …)`, names no argument and no
sibling, which FX-91 allows; application reconnects `t` to the original's.
Its costs: the accumulated type written by hand (or a `load-moduleof`
with its parameters' types made the result's own `abs`, an existential
seal); a convention every file must follow; one namespace per stage, so a
diamond, two stages that both re-export `base`, clashes at the join.

| | dependent `moduleof` | flatten and accumulate |
| --- | --- | --- |
| change to the type language | one (§4) | none (or an existential `load-moduleof`) |
| departs from FX-91 §2.2.6 | yes | no |
| namespaces | one per member, nested | merged per stage |
| diamonds | fine | clash at the join |
| what Heist writes | the chain once, in `env.fx` | a convention in every file |
| where the work is | inclusion, `restrict`, both checkers | little |

## 6. If it is built, the order

1. `Ty::MemberSel`, its reps, printing, both checkers, `moduleof` read
   with earlier members in scope: a written type alone, tests of a
   module given at one, its `with` and `select`.
2. Inclusion with dependencies, and `restrict`'s hidden member.
3. A module's item typed by its earlier items' paths, so a file's
   module (`env.fx`) has the dependent type.
4. `include` of a path, aliasing by it.
5. Heist's `frame.fx` chain as a test, and the editor's files as a
   measure: entries and characters before and after.
