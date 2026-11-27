# Constructors with a home: tagged generative types

Research note, 2026-11-26, from the user's question. Status: **proposed,
not built**; the choices made so far are the user's (§6). No code was
changed.

## 1. The question

Hitting M-. on a constructor in an editor should go to where its data is
defined. With keyword constructors (`(#:ok v)`, `datatype-macro.md`,
"Keyword constructors: decided") it cannot: a label belongs to no
definition. It is a structural tag that any number of sums may use, and
the sums are divorced from their constructors. The user's idea: move
entirely to the keyword form, then *reintroduce* constructors that are
not keywords, each defined somewhere, which sum types can name: a
`(define-constructor …)`. Is that new, or is it what unions already give?

## 2. What FX-26 has now

| | Constructs by | A definition to go to? | Told apart at run time by |
|---|---|---|---|
| `sumof`'s labels, `#:ok` or `ok` | `(#:ok v)`, `(sum ok v)`: any sum with the label | No: a label is no definition's | the label's symbol |
| `define-datatype`, `define-data` | the procedure `circle` | The procedure's, yes. But its type is a transparent `sumof`, so `(#:circle 2)` makes one too, and a `tagcase` arm names the label, not `circle` | the label's symbol |
| `oneof` | nothing: its members are types | — | the value's shape |
| `define-generative` | its seal, `up-t` | Yes | nothing: it has no shape of its own |

Structural labels having no home is by design (`structural-adts.md`, §0:
"what makes two datatypes distinct is their tags, not a name"). Each
nominal form that does have a home cannot be one of several members of a
union: `oneof` says of a generative or abstract type that it "has no
known shape and is no member (yet)" (`docs/fx26.md`, "Unions of
shapes"). The proposal fills that "(yet)". It is not a restatement of
unions.

## 3. The primitive

`define-constructor` combines three things:

1. **A fresh type identity, bound to a name where it is defined.**
   `define-generative` does this already.
2. **That identity visible at run time.** This is new. A generative type
   over `int` is the `int` itself at run time (both conversions are the
   identity, `generative-types.md`, §1), which is why it has no shape.
3. **Making and taking apart its values.** Its seal makes one; its unseal
   takes one apart. New: a `typecase` arm that tests for the type.

Only the second is missing, so the primitive is an option on the form
that exists, not a new form:

```scheme
(define-generative name string #:tagged #:seal make-name #:unseal name-text)
(define-generative (wowie (t type)) t #:tagged #:seal make-wowie #:unseal wowie-of)
(define-type answer (oneof (wowie int) name nil))
```

A **tagged** generative type's values carry its identity: a header word,
or a box around what is otherwise unboxed. So its shape is known, and it
is distinct from every other shape and every other tagged type's. It may
then be a `oneof` member, told apart by its tag.

- **It is a choice, not the default.** Tagging costs a word, or an
  allocation, per value. An untagged generative type costs nothing at run
  time, as now.
- **Its name is the binding's**, for printing and errors. No symbol is
  passed in: the identity comes from the definition, not from a name (the
  user's, 2026-11-26).
- **A family's seal is already polymorphic**, `(poly ((t type)) (subr
  pure (t) (wowie t)))`, so a parametric constructor needs no `plambda`
  written by the user.
- **Testing is public; taking apart is not.** Wherever the type is in
  scope, a `typecase` arm (or a `oneof`'s dispatch) may test for it,
  since that is what membership needs. Only code that has the unseal gets
  the payload. Elsewhere an arm binds the value at type `name`, sealed.
  So a module that hides its unseal keeps its representation hidden even
  from code that tells its values apart.

## 4. The sugar

`define-constructor` is a macro over it, the seal named as the
constructor:

```scheme
(define-constructor make-name string)           ; tagged generative `make-name`, payload string
(define-constructor (make-wowie (t type)) t)    ; a family: (make-wowie int), (make-wowie string), …
```

with the family head every such form reads (`define-generative`,
`define-data`). `define-datatype` becomes a macro too: its constructors
each a tagged generative type, the datatype the `oneof` of them, named by
`define-type`. M-. on a constructor, or on an arm that names one, goes
to that constructor's definition by ordinary scope, which also gives a
module's constructors qualified names (`m::make-name`) and lets a module
hide one.

The labels stay structural. Two libraries' `#:ok`s remain one label, as
the design intends; two libraries' `make-ok`s are two constructors.

## 5. Order: keyword-only labels first

Today `(sumof (ok T))` and `(sumof (#:ok T))` are one label, and so are
`(sum ok v)` and `(sum #:ok v)`. Before a bare name in a variant, or at a
list's head, can mean "this constructor", the bare spelling of a label
must be retired: labels written only as keywords everywhere (sums,
products, `extract`, `tagcase` arms), then the bare spelling refused,
then given to constructors. So the user's order is the necessary one.

## 6. Identity: one tag per definition (the user's, 2026-11-26)

A tagged type inside a module's maker is a distinct static type in each
instance, `b1..box` and `b2..box`. Their run-time tags could be:

- **one per definition**, every instance sharing it; or
- **one per instance**, made when the module is made.

**Chosen: one per definition**, keyed by where it is defined (the file,
or the form, and the name), and kept in a `.fasl` as a link, as a
keyword is (`fasl::Link::Keyword`). One per instance would make building
a module allocate, against the rule that loading a file is pure
(`parse_load`: "a loaded file is one value for all its loads, made once,
so making it must be pure").

### Where it could go wrong

A module over a parameter, applied twice:

```scheme
;; b.fx, a module over m
(define-generative box (select m t) #:tagged #:seal make-box #:unseal unbox)

(define b1 ((load-module "b.fx") a-int))      ; b1..box holds an int
(define b2 ((load-module "b.fx") a-string))   ; b2..box holds a string
```

`b1..box` and `b2..box` are different types, whose values carry the same
tag. A test that chose between them by tag could take a `b1` box for a
`b2` one, and give back its `int` as a `string`.

### Why it does not, under two rules

The invariant: **no run-time test ever chooses between two types that
may share a tag.** A tag is tested only to choose among the members of
one type the checker made, so two rules keep it:

- **R1. A `oneof` refuses two members that may share a tag.** `(oneof
  b1..box b2..box)` is refused: the checker sees one definition behind
  both. This is the rule `oneof` already has for two sums with a tag in
  common, and it covers a family's instances too: `(oneof (wowie int)
  (wowie string))` is refused. Under abstraction, if a module type may
  say "an abstract type, tagged", two such types the checker cannot show
  come from two definitions are refused together: `(oneof (select p box)
  (select q box))` with `p` and `q` parameters. That is sound, and
  restrictive: to put two instances in one union, wrap each in a
  constructor of its own.
- **R2. Nothing casts from a dynamic or top type down to a tagged type.**
  An `any` whose `typecase` could recover any type would accept a `b1`
  box as a `b2..box`. That is the one way per-definition tags go wrong,
  and only per-instance tags would survive it. FX-26 has no such `any`
  (`eval.md`, "why `any` is not needed"), and `datum`'s `typecase`
  covers datum shapes only, which a tagged type is not.

**R2 is a constraint on the language from here on.** If a dynamic `any`
with downcasts is ever wanted, this choice is to be revisited, for
per-instance tags or for refusing a downcast to a tagged type made in a
module's maker.

### Staging and reloading

A staged fresh load of a file (`eval.md`, "Decided (the user's,
2026-11-26)") has new static types but the program's instance's tags,
keyed by the same definition. R1 keeps that sound: a `oneof` of the
program's `box` and the staged one is refused, and values cross between
them only where a type lets them. So does a file edited and reloaded with
its payload's type changed, under the same tag.

## 7. Interactions

- **`generative-types.md`, §2, "Generative datatypes"** proposed
  `(define-datatype … #:generative …)`: one generative name over a sum
  whose tags stay structural. That hides a whole datatype behind one
  name. This note makes each constructor nominal. The two compose: a
  tagged generative type's payload may be such a sum.
- **The `data` kind** (`generative-types.md`, §3): a tagged generative
  type is not `data` unless it gives a validator, as any generative
  type. Reading one from outside is its seal.
- **Printing**: a tagged value can print its constructor's name,
  `#<make-name "x">`. Its payload is printed only where the unseal is in
  scope.
- **Equality**: same tag, then equal payloads. Comparing two values of
  types that may share a tag is refused by the same R1 reasoning.
- **Without any of this, M-. on a label** can still be helped: the
  checker knows the sum each `(#:ok x)` was checked against, so an
  editor's query (`query.rs`) could go to the `define-type` naming it,
  where one does. Cheap, and useful now. Where nothing named the type,
  there is still no home.

## 8. Steps

1. **Measure the migration.** Count the programs, tests and front-end
   files that write labels bare (sums, products, `extract`, `tagcase`
   arms, `define-datatype` variants).
2. **Keyword-only labels.** Rewrite them, warn on the bare spelling, then
   refuse it.
3. **`#:tagged` on `define-generative`.** The heap's header or box, the
   shape in both checkers, `oneof` membership with R1, `typecase`'s arm,
   every machine (cellular, register, native, the lowering's, the
   evaluator's), the `.fasl` link.
4. **`define-constructor`**, a macro; then `define-datatype` over it.
5. **M-.**: constructors resolve by scope; labels by the expected type
   (§7), as a query.

## 9. Open questions

1. **Spelling**: `#:tagged` on `define-generative`, or a form of its own
   with `define-constructor` as its only spelling.
2. **The arm**: in `typecase` (dispatch by type, where a `oneof`'s
   members are told apart now), or in `tagcase` with a constructor where a
   label is. `typecase` is the natural fit if a datatype is a `oneof`.
3. **Abstract tagged types**: whether a module type says "tagged" (a
   kind, `tagged ≤ type`?), and how much R1 then refuses in practice.
4. **The definition's key**: the file and the name, or the form's place,
   for a definition inside a `lambda` (a maker's module) or a staged
   module.
5. **Representation**: a header word on an existing object, or a box
   (two words and an allocation for an `int` payload), and whether the
   compilers can unbox one whose tag is known.
