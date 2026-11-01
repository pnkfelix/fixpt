# `acyclic`: shallow or deep?

Report, 2026-11-01. Nothing here is built. It comes from a question in
the discussion behind `sets-and-maps.md` and `graphs.md` (PR #3): can a
value at `acyclic` ever become part of a cycle? It can, and the user is
concerned that the meaning of `acyclic` is "too subtle at best and
unsound at worst". This report says what `acyclic` promises as built,
audits everything that relies on it, and sets out the options, including
the user's suggestion of splitting it into a shallow region and a deep
one.

FX-26 facts are from the repository at commit `d17e05c`. The programs
are in `docs/research/examples/acyclic/`. Each was checked with
`target/release/fixpt check` (both checkers agreed on every one) and run
with `fixpt eval`, at that commit. Running `fixpt` in the cloud session
needed the local change described in issue #4.

## 0. At a glance

- **As built, `acyclic` is shallow.** A value at `acyclic` was built and
  never written, so *its own pairs* form no cycle, and a walk over their
  `car`s and `cdr`s ends. What those pairs hold need not be frozen. A
  frozen list may hold a `ref`, and a cycle can run through the list and
  the `ref` (§1).
- **The documents read as deep.** `docs/fx26.md` calls it "frozen data no
  cycle runs through, all of it", and `acyclic-regions.md` says "No cycle
  runs through it." Read literally, both are false of
  `cycle-through-ref.fx` and `cycle-through-closure.fx`. The same misreading
  got into PR #3's first draft of `graphs.md` §2.7.
- **No unsoundness was found** (§2). Every use of `acyclic` in the checkers,
  the compilers, the runtime and the verifier needs only the shallow
  promise, or checks the deep one for itself through the `data` kind.
  In particular:
  - the termination checker counts only the `car` and `cdr` of a pair at
    `acyclic` as smaller, so a walk around the cycle needs `spin`
    (`walk-needs-spin.fx`, refused without it);
  - `letfreeze` counts `init` as a write, so an I-cell knot leaves at
    `const`, not `acyclic` (`icell-knot.fx`);
  - `acyclic?`, `certify-acyclic` and the SMT sorts take only data.
- **The risk is the next consumer.** Anything new that walks "acyclic
  data" deeply, on the strength of the documents, would be unsound: a
  printer's fast path, a serializer, a derived equality typed `pure`
  without `spin`, or reference counting with no cycle collector.
- **Found on the way** (§3): printing any cycle that runs through a `ref`
  overflows `fixpt eval`'s stack, with or without `acyclic`
  (`print-ref-cycle.fx`). The printer's cycle search looks only through
  pairs and vectors, but its printing walk also enters boxes and records.
- **Making `acyclic` deep would break variadic procedures** (§4.2). A
  `vsubr`'s rest list is `(listof t acyclic)` for any `t`, procedures and
  refs included (`%vlambda`'s type in `standard.rs`).
- **Recommendation** (§5):
  - keep `acyclic` shallow, and reword the three places that describe it;
  - name the deep property as a property of types, not as a region,
    since the `data` kind already decides it;
  - add tests that pin the shallow behaviour down;
  - fix the printer.

  If a deep region is wanted after all, §4.3 has names.

## 1. Two cycles through frozen data

The shallow reading promises only that a frozen value's own pairs form
no cycle. Two programs show what is still possible.

**Through data, a cycle needs a recursive type through writable
storage** (the user's observation). In `cycle-through-ref.fx`:

```
(define-type cell (ref (listof cell acyclic) @r))
(define c cell (new (the (listof cell acyclic) (list))))
(define l (listof cell acyclic) (list c))
(set c l)
(eq? c (car (get (car (get c)))))      ; #t
```

The list `l` is frozen and was never written. Writing it into `c` closes
the cycle `c → l → c`. Without a recursive type through the `ref`, the
write is refused: a `(ref (listof int acyclic) @r)` cannot hold a list
of such refs.

**Through a procedure, no recursive type is needed.** In
`cycle-through-closure.fx`, no type is recursive. There is a list of
thunks at `acyclic` and a `ref` holding such a list:

```
(define-type thunk (subr (maxeff (read @r) spin) () int))
(define-type thunks (listof thunk acyclic))
… (let ((c (the (ref thunks @r) (new (the thunks (list))))))
    (let ((f (the thunk (lambda () (length (get c))))))
      (let ((l (the thunks (list f))))
        (begin (set c l) ((car (get c)))))))      ; 1
```

The thunk captures `c`, so `c → l → f → c` runs through `f`'s
environment, which a procedure's type does not show. The only trace is
Landin's-knot rule (`regions/knot-through-a-ref.fx`): a procedure kept
in a region it reads must say `spin`. Without `spin` in `thunk`, the
program is refused ("a procedure kept in `@r` reads `@r`, so it could
reach itself"). That rule needs the procedure to *read* the region. A
procedure that captures a `ref` without using it leaves no trace in the
types. Whether its closure then still holds the `ref` is up to closure
conversion, and was not tested.

So a cycle through frozen data always passes through storage that is
not frozen, or through a procedure's environment.

## 2. Audit: what relies on `acyclic`

Every use found by searching the Rust sources for `acyclic`, and
`standard.rs` for types that mention it, was read. Each is classed by
what it needs. "Shallow" means it needs only "these pairs form no cycle
among themselves". "Deep" means it needs "nothing reachable is on a
cycle".

| use                                                                                       | where                                                     | needs                                     | holds? |
| ----------------------------------------------------------------------------------------- | --------------------------------------------------------- | ----------------------------------------- | ------ |
| size-change "parts": a pair's `car` and `cdr` at `acyclic` are smaller                    | `terminate.rs`, module comment                            | shallow                                   | yes (§2.1) |
| `letfreeze` gives `acyclic` only if the body wrote nothing at its region                  | `check.rs`, `mask`: `Write` and `Init` both count          | shallow                                   | yes (§2.2) |
| `cons` may allocate straight into `acyclic` when the tail is a list there                 | `docs/fx26.md`, "Finite data"                             | shallow                                   | yes, by construction |
| inference defaults an unsolved region to `acyclic` where a `poly` only builds pairs there | `infer.rs`, `default_regions` (`TODO.md` §174)           | shallow                                   | yes |
| `apply` shares a list at `acyclic`, not copying it (F11)                                  | `cellular.rs`, `apply_shares`; `infer.rs`                 | shallow: nothing can write the list       | yes |
| a `vsubr`'s rest list is `(listof t acyclic)`, any `t`                                    | `standard.rs`, `%vlambda`                                 | shallow                                   | yes |
| `acyclic?` and `certify-acyclic`, the run-time check behind `(acyclic e …)`               | `standard.rs`; `prim.rs`, `%fx26-acyclic?`               | deep, and checked: `(t data p)` only       | yes |
| the verifier's sorts: lists at `acyclic` of ints, bools, or such lists                    | `smt_theory.rs`, `sort_of`                                | deep, and checked: elements must be sorts | yes |
| the `data` kind: frozen pairs and bloblets "of data"                                      | `docs/fx26.md`, "The `data` kind"                         | deep, by its own definition               | yes |
| frozen data is covariant in the order of lifetimes                                        | `docs/fx26.md`, "Frozen data is covariant"               | neither (about places)                    | unaffected |

Not audited: the typed-cell verifier's use of `writes_in`
(`typed_cells.rs`), the certificates `cellular.rs` emits for `apply`,
`dynamic`, and whether an effect variable could carry a write to a
freezing region past `mask`. The checker written in FX-26 (`check.fx`)
was not read separately. It agreed with the Rust checker on every
program here.

### 2.1 Termination

`walk-needs-spin.fx` walks the cycle of §1: from a cell, through its
list, and back through `get`. Declared without `spin`, both checkers
refuse it: "nothing smaller, or related, is passed by the call of
`cells` in `cell`". The `car` of `l` is `c`, a part and so smaller. But
`(get c)` is not a part of `c`, so the cycle has a step with no
decrease. This holds in general: a cycle through frozen data passes
through writable storage or a procedure (§1), and neither reading a
`ref`, an array or an I-cell, nor calling a procedure, is a "part" step.
`terminate.rs`'s comment, "each was made before what holds it, and none
can be changed, so no cycle runs through them", is right about the parts
it lists. It is not a claim about what they hold.

### 2.2 `letfreeze` and I-cells

An I-cell is filled by `init`, not by `write`. `icell-knot.fx` ties a
knot at a `letfreeze`'s own region: a pair whose `car` is an I-cell,
filled with the pair. `mask` notes `Atom::Init` as well as
`Atom::Write`, so the value leaves at `const`. `(eq? x (icell-get (car
x)))` is `#t`, and declaring `x` at `acyclic` instead is refused.

## 3. Found on the way: printing a cycle through a `ref`

`print-ref-cycle.fx` makes a cycle through a `ref` and a writable list,
with no acyclic data at all, and evaluates `c`. `fixpt eval` aborts:
"thread 'fixpt' has overflowed its stack". A cycle through pairs alone
prints with datum labels, `#0=(1 2 . #0#)`.

The cause is in `crates/fixpt-runtime/src/print.rs`. `find_shared`
looks for nodes on a cycle only through pairs and vectors (`interesting
= v.is_pair() || … ObjType::Vector`). But `put`, the printing walk, also
enters boxes (`ObjType::Box`, which is how a `ref` is represented) and
records (`obj_ref`). So a cycle through either gets no label, and `put`
recurses until the stack ends. `find_shared`'s work budget does not
help, since the recursion is in `put`.

The fix is to make `find_shared` visit what `put` visits (issue #6).
This is independent of `acyclic`. The printer has no fast path that trusts
`acyclic`, and it should not get one unless `acyclic` becomes deep.

## 4. The options

### 4.1 Keep `acyclic` shallow, and say so

Change nothing in the type system. Reword the three descriptions:
- `docs/fx26.md`, "Finite data", now "frozen data no cycle runs
  through, all of it". Proposed: "frozen data whose own pairs form no
  cycle: a walk over its `car`s and `cdr`s ends. What it holds need not
  be frozen: a cycle may still pass through a `ref`, array or I-cell it
  holds, or through a procedure's environment, but never through its
  pairs alone. Data that is deep as well, nothing writable and no
  procedure anywhere in it, is `data` at `acyclic`."
- `docs/research/acyclic-regions.md`, "The design", now "No cycle runs
  through it." Proposed: "No cycle runs through its own pairs."
- `terminate.rs`'s comment, which is already accurate, could add "what
  they hold may be on a cycle, through storage that is not frozen".

Add tests that pin the behaviour down, so that a change to the measure
or to `letfreeze` is caught: `walk-needs-spin.fx` (refused) and
`icell-knot.fx` (refused at `acyclic`), as
`crates/fixpt-fx26/tests/programs/terminate/` and `regions/` programs.

Cost: none in the language. Risk: the shallow meaning stays subtle, and
a future consumer must check `data` for itself.

### 4.2 Make `acyclic` deep

Require that everything reachable from data at `acyclic` be frozen and
procedure-free. In effect, a pair may be made at `acyclic` only if its
`car`'s type is `data` (or a type parameter bounded by `data`).

This breaks at least the variadic procedures. `%vlambda` has type
`(poly ((e effect) (t type) (r type)) (subr pure ((subr e ((listof t
acyclic)) r)) (vsubr e t r)))`. So a variadic procedure of procedures,
or of refs, takes its rest list at `acyclic`, and `apply` shares such a
list without copying it on the strength of that region (F11). Under a
deep `acyclic`, `vsubr` would need a second, shallow region for its rest
list. That is option 4.3 with extra steps.

How much other code it breaks was not measured. A crude search finds
606 lines mentioning `acyclic` in the FX-26 sources and ports, and 116
of them also mention `subr`, `ref`, `arrayof`, `icell` or a writable
`@` region. But most of those are procedure types *taking* acyclic
lists, not lists *of* procedures, and element types are usually behind
aliases. A real count needs the checker instrumented: report each pair
type made at `acyclic` whose element type is not `data`, then run the
test suite.

### 4.3 Split: a shallow region and a deep one (the user's suggestion)

Keep `acyclic` as it is, and add a second frozen region for the deep
property. The checker would admit a pair at the deep region only when
its contents' types are `data` at a frozen region, so the deep region
repeats the check the `data` kind already makes. Two things argue
against making it a region:
- **Deepness depends on the type, not the region.** `(listof int
  acyclic)` is already deep. `(listof cell acyclic)` is not, and the
  difference is `int` against `cell`, which the checker decides as "is
  this `data`?". A deep region would need the same check at every
  allocation, and a type parameter in a deep list would need a `data`
  bound anyway.
- **`const` has the same split.** A shallow `const` spine may hold refs.
  A deep `const` is transitively immutable, as D's `immutable` and
  Pony's `val` are. So deep against shallow is a second axis, across
  `const` and `acyclic`. As regions that makes four, where one property
  of types would do.

If it is a region all the same, names for the deep one:

| name                         | connotation                                                                                                   | for                                                  | against                                         |
| ---------------------------- | ------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------- | ----------------------------------------------- |
| `founded` (or `wellfounded`) | set theory's axiom of foundation: membership has no infinite descent, as in the hereditarily finite sets SETL is built on | says exactly "no infinite descent through anything it holds" | a technical word                                |
| `ground`                     | logic programming: a term with nothing left to bind                                                          | short; "fully settled"                               | says nothing of cycles; clashes with "ground type" |
| `inert`                      | nothing in it can change or act                                                                              | covers both no writable storage and no procedures    | says nothing of cycles                          |
| `acyclic*`                   | the starred, transitive variant                                                                              | obvious pairing                                      | a modifier spelled as a name                    |

For the second-axis reading, the established word in the immutability
literature is *transitive*: `(transitive acyclic)` and `(transitive
const)`, or `(deep acyclic)` and `(deep const)`.

### 4.4 Name the deep property as a property of types

Give the `data` test a name usable without a binder. For example `(deep
T)`, a type that checks that `T` is `data` and then stands for `T`. Or
a bound on definitions, as `(t data p)` is on binders. Each future
consumer that needs depth then says so in its type, and the checker
refuses it at a non-deep type. This is the targeted defence against the
risk in §0.

## 5. Recommendation

4.1 and 4.4 together:
1. Reword the three descriptions (§4.1), so that no one else reads
   `acyclic` as deep.
2. Add `walk-needs-spin.fx` and `icell-knot.fx` as tests.
3. Fix the printer (§3, issue #6).
4. When the first consumer that needs depth arrives, add `(deep T)`, or
   use `data` directly, rather than a second region.

This keeps every current use sound, as audited. It costs nothing now,
and it moves the subtlety from a sentence that could be misread to a
type that will be checked. A deep *region* (4.3) is worth it only if
programs need to annotate deepness where a type cannot carry it. No such
case came up. If one does, `founded` is the name I would choose.

## 6. Open questions for the user

1. Was `acyclic` meant to be deep (the documents' wording), or is the
   shallow meaning the intended one? The audit suggests that every
   current use needs only the shallow one, and `vsubr` depends on it.
2. Is deep against shallow better as a second axis on frozen regions
   (`const` and `acyclic` both), as a property of types (`(deep T)`, or
   `data`), or as a third region?
3. Should the checker be instrumented (§4.2) to measure what a deep
   `acyclic` would break, before deciding?
4. Should the unaudited paths of §2 (`dynamic`, effect variables
   through `mask`, the typed-cell verifier) be audited next, as part of
   `soundness.md`'s work?

## The programs

| file                       | shows                                                                                         | checked, ran       | result                                                      |
| -------------------------- | --------------------------------------------------------------------------------------------- | ------------------ | ----------------------------------------------------------- |
| `cycle-through-ref.fx`     | a cycle through frozen data, via a recursive type through a `ref`                            | yes                | `#t`                                                        |
| `cycle-through-closure.fx` | a cycle through a closure's environment, with no recursive type; the knot rule asks for `spin` | yes                | `1`, effect includes `spin`                                 |
| `walk-needs-spin.fx`       | a walk around that cycle, declared without `spin`                                             | refused            | "nothing smaller, or related, is passed by the call of `cells` in `cell`" |
| `icell-knot.fx`            | an I-cell knot at a `letfreeze`'s region leaves at `const`                                     | yes                | `#t`; refused if declared at `acyclic`                      |
| `print-ref-cycle.fx`       | printing a cycle through a `ref`, with no acyclic data                                         | checks; eval crashes | "fatal runtime error: stack overflow"                     |
