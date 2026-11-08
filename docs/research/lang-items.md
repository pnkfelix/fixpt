# Lang items: the standard library's special names, tagged

Research note, 2026-11-08, written up from a discussion with the user while
designing binders of descriptions (`typed-macros.md`, item 8): whether a
template's free description names are read at the top level whole-type or
name by name. Status: **proposed, not built**. The design was
agreed in outline. The open questions in §9 are still to be settled before
anything is built.

## 1. The problem

A type is read in two kinds of position, and the two do not agree on what a
name is.

- **Head position**, `(listof T)`: the head is looked up in the description
  scope first (`parse_type_list`), but only a binding that is a function (a
  family, a generative type with parameters, a variable of an arrow kind)
  is used. A binding of any other kind is passed over, and the head is then
  the built-in form of that name, from a fixed list (`TYPE_FORMS`,
  `parse.rs:66`).
- **Bare position**, a lone symbol: it is looked up in the description
  scope. Only when nothing binds it does it fall back to the built-in
  constructors (`CONSTRUCTORS`, `kinds.rs:38`, which give `listof` its kind
  `(=> (type region) type)`) or to the standard base types (`Checker::base`,
  which a program may redefine, `DONE.md` §88).

So whether a name is the built-in form depends on the *kind* of what binds
it, and the same name can mean two things in one type. Both checkers agree
on each of these, so the problem is in the language rule, not in a mismatch
between the checkers:

```scheme
;; A binder of kind `type`: the head is the built-in list, the argument the binder.
(poly ((listof type)) (subr pure ((listof listof)) int))   ; checks
;; A family: it takes the head over.
(define-type (listof (a type)) a)
(define x (listof int) 5)                                  ; checks; x is an int
;; A base type is an ordinary name:
(define-type bool int)                                     ; checks; bool is now int
```

(An earlier draft of this note said a type form's head is never looked up;
it is, by kind, as above.)

For hygiene this means that a template's names, heads included, can be
captured where the macro is used: a `(listof …)` a template writes is the
use's own family if one named `listof` is in scope there. Whatever rule
binders of descriptions picks must read each of them where the macro was
defined, and today which of them is a binding depends on the kind of what
binds it, a rule drawn by a hard-coded list rather than by the language.

The list also mixes three different things:
- binding forms and forms with their own grammar (`poly`, `subr`, `moduleof`);
- primitives whose meaning only the compiler can give (`pairof`, `ref`);
- at least one plain abbreviation, `listof`, which the parser builds out of
  pairs (`parse.rs:942`):

```rust
// FX-87's `listof`: a pair whose tail is the list itself, or the empty list
let slot = self.arena.ty(Ty::Link(None));
let pair = self.arena.ty(Ty::Pair(t, slot, r, true));
```

There is no list case in `Ty`. `(listof T R)` is, in the language's own
terms, `(mu l (oneof nil (pairof T l R)))`, which `union_of` already
normalizes to the pair that may be `nil`.

## 2. The idea

Following Rust's lang items (`#[lang = "…"]`), separate two things that are
fused today:

- **what a name means**: an ordinary binding in the standard library, which
  is scoped, shadowable, renamed by hygiene and reached through `#%fx`;
- **what the compiler knows about it**: a *tag* carried on that binding,
  which the checkers, the compilers and the runtime agree on.

The compiler finds a special thing by its tag, never by the name it is
spelled with. A program that shadows `listof` then simply has its own
`listof`, as it may have its own `=`. The standard one stays reachable as
`(with #%fx listof)`, and the checker still knows it is the list, because
the tag went with it.

## 3. The prerequisite: `#%fx` as a module with source

There is no standard library written in FX-26 for tags to sit on.
- The standard bindings are a table in Rust (the lowering's table of
  standard names).
- `crates/fixpt-fx26/src/standard.fx` is generated from that table
  (`standard_fx26_module`), and `standard-primitive` maps each name to a
  runtime primitive by its string.
- `docs/fx26.md` says it outright: "there is no prelude every program sees".

So the first stage is a real `#%fx` module, with source, that both front
ends load before every program. That needs decisions of its own:
- **Loading cost.** Every run would read and check the module. It should be
  cached as the front end's native code is (`fixpt prewarm`), keyed by the
  module's text.
- **Order.** The module's own types use the items it declares. Declared
  items (§5) need no definitions, so they can come first, and the defined
  items follow in source order.
- **`(with #%fx n)`** keeps its meaning (`docs/fx26.md`, "`#%fx`, the
  standard bindings"). It becomes a component selection from a real module.
- **The generated `standard.fx`** and the lowering's table become views of
  the module and its tags, rather than its source.
- **Variadic standard procedures** (`list`, `append`, `string-append`)
  run as primitives that take their arguments as they are. A definition
  would make a list of them. These stay declared items (§5), not
  definitions.

## 4. The tag

```scheme
(define-type #:lang list (listof (t type) (r region))
  (mu l (oneof nil (pairof t l r))))
(declare-type #:lang pair pairof (=> (type type region) type))
(declare #:lang cons cons
  (poly ((r region) (a type) (b type)) (subr (alloc r) (a b) (pairof a b r))))
```

The spelling is a placeholder. What matters:

- **The tag is not an identifier in any scope.** It is a keyword-like name
  at a meta level. Shadowing, renaming, `select`, `with` and re-export all
  act on the binding's name, and the tag goes with the binding.
- **Only `#%fx` may declare tags.** A program that writes `#:lang` is
  refused, at least until there is a reason to allow it.
- **Each tag is declared exactly once**, and every tag the compiler requires
  must be declared. Both are checked when `#%fx` is loaded.
- **The declaration is checked against what the compiler expects.** Each
  tag has an expected kind (for a type) or type (for a value) in the tag
  table (§6). A tagged definition whose kind or type differs is refused.
  The library cannot misstate an item, so trust sits in one table rather
  than in each use. (Rust's compiler does the same for a lang item with the
  wrong number of generic parameters.)

## 5. Two kinds of item

As in Rust, where some lang items are defined in `core` and others are
intrinsics:

- **Defined items**: the library gives the meaning as an ordinary
  definition. The compiler relies on the tag only for identity: to print,
  to know a list's tail is a list for the termination check, to fill a
  default. `listof` is one.
- **Declared items**: the library names the item and states its kind or
  type, and the compiler supplies the meaning. `pairof`, `ref` and the base
  types are declared types. `cons`, `car`, `cdr`, `set-car!`, `set-cdr!`,
  `nil` and the rest of the primitives are declared values. The runtime
  primitive each runs as (today `standard-primitive`'s strings) is keyed by
  its tag.

## 6. The tag table

One table of tags, read by both checkers, both compilers and the runtime:
data in the style of `macros-kernel.fx`, held equal to the Rust side by a
test, as `reserved-words` is to `KEYWORDS`. Each entry gives:
- the tag;
- defined or declared;
- for a type, its kind, with any default parameter (§9, question 1);
- for a value, its type, and the runtime primitive it runs as, if any.

## 7. Today's built-ins, sorted

Read from the parser's arms (`parse_type_list`, `parse.rs`) on 2026-11-08.
In the discussion I guessed that `nlist`, `nat`, `restrict` and `oneof`
might be sugar like `listof`. None of them is: `nlist` and `nat` have
`Ty` cases of their own, `oneof` normalizes, and `restrict` takes component
names.

| stays syntax | why |
| --- | --- |
| `poly`, `mu`, `dletrec`, `proves` | bind names |
| `moduleof`, `restrict`, `select` | take component names, which are not descriptions |
| `subr`, `->`, `->*` | an effect, parameters and a specification in a grammar of their own |
| `productof`, `sumof`, `tupleof`, `bloblet` | labels or field lists, of any length |
| `oneof`/`union`, `anyof`, `allof` | any number of members, normalized |
| `(bool …)` | a procedure's refined result, not a type |

| becomes a declared type | kind |
| --- | --- |
| `pairof` | `(=> (type type region) type)` |
| `ref`, `icell`, `mark-key` | `(=> (type region) type)` |
| `arrayof` | `(=> (type region) type)`, but see §9, question 1 |
| `narrayof` | `(=> (type size region) type)` |
| `nlist` | `(=> (type size) type)`, with an optional place |
| `nat` | `(=> (size) type)`, and bare `nat` is `(nat finite)` |
| `place` | `(=> (region) type)` |
| `prompt-tag` | `(=> (type type effect region) type)` |
| `composable`, `oneshot` | `(=> (type type effect region) type)` |
| the base types (`int`, `bool`, `char`, `string`, …), `nil`, `false`, `void` | `type` |

| becomes a defined type | definition |
| --- | --- |
| `listof` | `(mu l (oneof nil (pairof t l r)))`, region `acyclic` by default |

Effects (`read`, `write`, `alloc`, …) and region words (`acyclic`, `@heap`)
are left out of this note. They are the same question one level over and
should follow whatever is decided here.

## 8. What it does for hygiene

Binders of descriptions (stage 1) can go ahead treating the forms in
`TYPE_FORMS` as syntax. As each one becomes a lang item, it leaves the list
and becomes an ordinary name in `#%fx`, which hygiene already handles: a
template's free name is read where the macro was defined. No extra work is
needed per item.

It also changes the reserved-words fix (binders of descriptions' first
step: `letregion`, `letfreeze` and others missing from `KEYWORDS`): the type
constructors' names should **not** be reserved against
description binders, as was suggested before this note. They are on their
way to being ordinary names, and reserving them would be work to undo.

## 9. Open questions

1. **Parameters a fixed kind cannot say.**
   - `(listof T)` defaults its region to `acyclic` (`TODO.md` §198);
   - `nlist`'s place is optional;
   - `arrayof` with a size in the region's place is a flat array;
   - `nat` is both a type and a function.

   Either type families get default parameters, or each of these splits
   into two names. Default parameters are the more general answer, and the
   one a user's own families would want too.
2. **Printing.** A type built from a lang item can print by the binding's
   name as it is in scope where the message is about (more honest when the
   program shadows it), or by the tag's canonical name (more stable). Today
   the printer recognizes the list's shape.
3. **The checker's knowledge of a defined item.** For `listof` the tag is
   identity only, but the termination check's "a list's tail is smaller"
   follows from the definition anyway. If every defined item's special
   treatment can be derived from its definition, defined items need no tag
   at all, and only declared items do. Worth checking item by item.
4. **Effects and regions.** Whether `read`, `alloc`, `acyclic` and the rest
   go the same way (§7).
5. **Loading `#%fx` in the bootstrap.** The FX-26 front end checks itself.
   Its own sources would then depend on `#%fx`, which must be loadable
   before the front end that loads it exists.

## 10. Staging

1. `#%fx` as a module with source, loaded and cached by both front ends,
   with the standard values as declared items (§3).
2. The tag mechanism and table, with one item: `listof`, the clearest
   defined case. Its head leaves `TYPE_FORMS`.
3. The declared types, one at a time, each leaving `TYPE_FORMS` and
   `CONSTRUCTORS`.
4. Effects and regions, if §9 question 4 says so.

Each stage lands in both front ends, as every mode does.
