# Signatures from files: `load-moduleof` and narrowing

Heist's request (2026-10-27, against `8793b0cb`): a design exploration
of two type-level forms for linking multi-file programs, and six module
problems found along the way. Nothing here is built yet.

## The request, briefly

Heist's editor is 15 files and about 7000 lines, with about 40 mutable
globals and tables of commands that files fill as they load. They want
`(load-module "editor.fx")` to load all of it. Every load must be pure to
make, so each stateful file became a `load-input` `lambda` that makes the
file before it and `include`s it: a chain. They would prefer the
conductor's shape (`conductor.fx`): each file a function of the modules it
uses, each parameter typed by a `moduleof`. They don't use it because every
signature is written out by hand. Fixpt's own front end pays the same:
about 20 `*-types.fx` files with signatures like `check-types-sig`
(`check-types-types.fx:287`), kept in sync by hand.

The proposal:

- `(load-moduleof "core.fx" ed world)`: the type of the module the file
  gives, applied to those arguments, making nothing.
- `(moduleof-only T name …)`: `T` with only those names. It drops names,
  not types: a kept value whose type mentions a dropped abstract type
  keeps it, unnamed.

## Summary

- **`load-moduleof` is sound, and fits Fixpt's existing design.** A file's
  interface is already its type (M7, `first-class-modules.md`); this only
  lets a program name that type. With the arguments limited to regions,
  effects, types and *paths* (variables bound to modules), applying a file
  at the type level is exactly M5's call rule. Recommended, first.
- **The result is a signature, not a link to an instance.** An abstract
  component of the result is a binder, as in any `moduleof`. Two
  `load-moduleof`s of one file are the same module type, and which `t`
  you have comes from the module you select through. That avoids
  OCaml's strengthening question (Q2) and the applicative-functor
  question (Q1).
- **Narrowing is sound as proposed, and is the same work as lifting
  `hide`'s restriction.** A dropped abstract type becomes an unnamed binder
  of the narrowed type. That is what `hide` would need to show a hidden
  abstract type, which it refuses today (`modules/hide-escape.fx`).
  Every narrowed type can be printed: an unnamed binder goes first with a
  hidden name, and dropped descriptions are written out where used.
- **A deeper cause, worth a decision:** a pure file's `define-generative`
  types can't be shared between two files that load it, even though every
  load is one value (§68). Sheldon's rule restricted to loads would fix
  that (Q2, last part).
- **Bugs A, B, D and F reproduce; C is intended; E is real.** A, B and D
  are checker bugs I'd fix. E is docs plus `fixpt run`. F is a design
  decision.

## Q1. Files with parameters

A `module-parameters` file's type is `(poly ((ed region) (world effect))
(subr pure () (moduleof …)))`. A `load-input` file that takes modules has
type `(subr pure ((core : SIG)) (moduleof … (select $1 actor) …))`, a
dependent subroutine (M5). Applying either at the type level is a walk
down the type, taking arguments as it goes:

- a `poly` binder takes a region, effect or type, substituted as `proj`
  does;
- a `subr` of no parameters takes nothing;
- a `subr` whose parameters are modules takes one path each, substituted
  for `$1`, `$2`, … as M5's call does;
- the walk ends at a `moduleof`, which is the result.

**Sound.** Substituting a path for a dependent parameter is what M5 does
at every call, and M5 already requires the argument to be a path. A
`load-moduleof` claims only "a module made this way has this type", never
"these two have the same types". So it doesn't need applicative functors
(Leroy 1995, OCaml's `F(X).t`), which would be *unsound* here. Heist's
makers allocate, so two applications of `buffer.fx` to one `core` may give
two different abstract types. Dreyer, Crary and Harper (2003), and later
F-ing modules (Rossberg, Russo and Dreyer), make a functor applicative
only when its body is pure. FX-26's effects say which files are pure, so
an applicative reading could come later for pure makers [inf].

**How far the first version should go:**

- The arguments: regions, effects, types, and variables bound to modules.
  Not general expressions: `(load-moduleof "buffer.fx" ((make-core)))` is
  refused, as M5 refuses it at a call. Bind it with `let` first.
- Inside a file, the arguments are names the file binds. So `buffer.fx`
  is itself a `plambda` over `ed` and `world`, around a `lambda` over
  `core`:

  ```scheme
  ;; buffer.fx, a load-input file
  (plambda ((ed region) (world effect))
    (lambda ((core (load-moduleof "core.fx" ed world)))
      (module …)))
  ;; a client of buffer that also has core:
  (lambda ((core (load-moduleof "core.fx" ed world))
           (buffer (load-moduleof "buffer.fx" ed world core)))
    …)
  ```

- A client that has `buffer` but not `core` can't write `buffer`'s type:
  the type mentions `core`. That is the right answer, not a gap. Either it
  takes `core` too, or it takes `buffer` narrowed to names whose types
  don't mention `core`'s abstract types, or the narrowing leaves them
  unnamed (Q-narrowing below). Most of `core`'s types are transparent
  (`actor`, `msg`, `reply` are `define-type`s over `ed` and `world`), so
  in practice little would be lost.

**What is hard:**

- **Both checkers, agreeing.** The type form has to be read by Rust's
  checker and by `check-read*.fx`, and both front ends have to load the
  file named. The front end written in FX-26 reads no files: Rust supplies
  each loaded text (`supply_loaded_in`), found by where its load starts.
  The cheapest way is to make the parsers treat `load-moduleof` as a load
  of the same key as `load-module`/`load-input` (Q4). Then supplying the
  text, the cycle check and the hidden global need nothing new.
- **Arguments that reshape.** M4 makes a module given at a type with fewer
  components into one of that type. Whether a path argument of a
  dependent call is reshaped, or must match, needs checking before the
  first version promises narrowed parameters.

## Q2. Abstract type identity

Two `load-moduleof`s of one file give one module type, whose abstract
components are binders. Identity is never in a signature; it is in the
path selected through. OCaml's trouble was different: `module type of M`
gives `M`'s signature *without* the equations `t = M.t` (unstrengthened),
and people wanted them; the idiom to keep them is `module type of struct
include M end`. Fixpt has nothing to keep, because two bindings of a file
don't share abstract types today anyway. So: unstrengthened, and
deliberately so.

### Why neither "fresh" nor "shared" (the user's question, 2026-10-27)

The user asked what a signature's abstract types should mean. If each
`load-moduleof` made them fresh constants, no module could ever fit the
signature. If all `load-moduleof`s of a file shared them, values could
move between two instances of a maker. Both are wrong. The third reading
is the one FX-26 already has: an abstract type in a `moduleof` is bound
by whatever has that type. A parameter typed by a signature stands for
the argument's own `t`, put in again at each call. Checked on `00c190c5`,
with `make` a `lambda` giving a module with a `define-generative t int`:

```scheme
(define-type sig (moduleof (abs t type) (val zero t) (val value (subr pure (t) int))))
(define c1 (make))
(define c2 (make))
(define twice (subr pure ((c : sig) (select c t)) int) …)
(twice c1 (with c1 zero))   ; accepted: (select c t) is c1..t
(twice c2 (with c2 zero))   ; accepted: c2..t
(twice c1 (with c2 zero))   ; refused, both checkers:
                            ; "argument 2 is a c2..t, where a c1..t is expected"
```

`load-moduleof` only supplies `sig`. This is how F-ing modules (Rossberg,
Russo and Dreyer) reads a signature: its abstract types are existentially
bound, and each match finds their witnesses in the module given,
separately for each match.

**The user's alternative: one unification variable per `load-moduleof`**,
given a type when the signature is first linked to a real module. Its
nearest relatives are Backpack (Kilpatrick, Dreyer, Peyton Jones and
Marlow, 2014), whose holes have identity variables that linking settles
by unification, and MixML (Rossberg and Dreyer), whose linking joins an
imported abstract type to an export [from memory, not re-read]. In
FX-26:

- **A variable set once is a sharing constraint.** One `load-moduleof`
  named by a `define-type` and used for two parameters would force both
  to be the same instance. Binders keep them independent. When one module
  is passed to both, `(select core actor)` is one type on both sides, so
  linkage gives the sharing.
- **It clashes with a file checked once.** Every load of a file is one
  value, checked once for all its clients. A variable in it would be set
  by the first client to link, and a second client passing another
  instance would be refused, as with ML's weak type variables. A variable
  copied for each application is a binder again.
- **Its errors are far from their cause.** At the REPL, or across files,
  the form that sets the variable can be far from the one that disagrees.

Backpack needs unification because its holes are filled at package level,
by linking, with no function applied. FX-26 has dependent subroutines
over modules (M5), so application settles them, and binders are enough.
Holes would be worth it for files that don't take their dependencies as
parameters, as Heist's chain didn't. That is a larger design, deferred
until `load-moduleof` exists and parameters still prove too costly.

### The real limitation

The real limitation is elsewhere, and older than this proposal. Here
`x.fx` is a pure file with a `define-generative t`:

```scheme
;; y2.fx, a load-input file: a function made over x.fx's module
(let* ((x (load-module "x.fx")))
  (lambda () (module (define twice (subr pure ((select x t)) int) …))))
```

Both checkers refuse it: `` `x..t` is a module's abstract type, not known
outside the scope where the module is named ``. The same `x..t` can't
leave the file even though every load of `x.fx` is the one value
`%shared:x.fx`. (Datatypes are transparent, a `sumof`, so the front end's
`*-types.fx` share theirs; only `define-generative` types stay apart.
Heist has 8.) So `y.fx` can't offer an operation on `x.fx`'s type to a
client who loaded `x.fx` too.

Sheldon's rule settles this: `(input "f")` is a pure expression, and two
`select`s of textually equal pure expressions are one type (LFP90 §2.1.3;
`sheldon-combining-modules.md` §2). Restricted to loads, it is sound in
Fixpt in a way it wasn't for Sheldon. Since §68, a key is one value, made
once, so "the same text" is "the same value" by construction, as long as
a file is never loaded again under its key once changed.

The proposal: a variable bound to a load, directly, is an alias for the
path `%shared:K`, and its abstract types are `%shared:K..t`. That reverses
part of the user's decision of 2026-10-08 ("two bindings of one file keep
theirs apart"), so it is the user's call. It would also let the
`*-types.fx` files hold `define-generative` types, and let a pure file's
abstract types appear in other files' interfaces. It would not change
makers: each application of a `lambda` still makes new types, and should.

## Q3. Effects from hidden globals

A file's procedures that call into a file it loads read that file's
hidden global, `(read (globals %shared:core.fx))`. In a signature:

- **Keep them** (recommended for the first version). They are true. A
  module given at a type fits if its effects are within the type's, so a
  signature that names the reads of the real file accepts the real file.
  Its cost is noise.
- **Don't generalize them** into an effect variable: a `poly` the file
  didn't have would claim more than was checked, and every client would
  have to instantiate it.
- **Strip them only everywhere at once.** If a `%shared:` global is never
  redefined, reading it is unobservable, and the checker could drop those
  reads from every effect, not only from signatures. I haven't verified
  that nothing (a `,load` at the REPL of a file that changed, say)
  redefines one. If nothing does, that is a small, separate change that
  removes the noise in every type Heist prints. `separate-compilation.md`
  §2.3 option (b), `(globals-of U)`, is the larger version, for when units
  are compiled apart.

## Q4. Cost

A `load-moduleof` needs the file checked, and what it loads. If the
parsers treat it as a load of the file's key, it is the same work as a
`load-module`. The first load of a key defines `%shared:K`, checked once
however many forms name it (`loads-and-places.md`). So a file named by
`load-moduleof` in ten clients and made once by the conductor is checked
once.

What it costs at run time: if the first version simply hoists
`%shared:K` as a load does, the file's value is made even when only its
type is named. That is pure by §68 (for a `load-input` file, a closure),
so it can't be observed. A later version can record "checked, type known,
not made" for the key, and hoist only on a real load.

## Narrowing: `moduleof-only`

The proposal's semantics are right, and only the type-level form is
needed:

- A dropped value: gone. Width subtyping (M4) already accepts the full
  module.
- A dropped transparent type: a kept type that used it is written out in
  full. Nothing is lost but the name.
- A dropped abstract type that a kept value mentions: an *unnamed*
  abstract component, a binder the client can't write. The client can
  receive and pass such values, but not name or inspect them. This is
  existential packing, and it is sound.
- Turning a kept `desc` into an `abs` is ascription, which M4 allows
  already ("abstract types where it has transparent ones"). A
  `(sealing name …)` clause in the form would save writing the
  `moduleof`.

**Printing:** an unnamed binder can always go first in the `moduleof`,
with a hidden name (`%hidden:t`, the mark `hide` already uses). So every
narrowed type prints; it just isn't all writable by hand, which is the
point.

**It is `hide`'s missing half.** `hide` is "the ascription done for you",
and it refuses a hidden abstract type in a type the module shows
(`modules/hide-escape.fx`). Narrowing needs the same unnamed binder that
lifting that refusal needs, so they should be built together.

**What narrowing costs a client:** the classic sharing problem (Sheldon's
thesis §4.1.5, "awkward"). A client given `buffer` narrowed so that
`core`'s `actor` is unnamed, and given `core` too, can't pass one's
actors to the other: nothing says the unnamed type is `(select core
actor)`. Narrow only what a client doesn't need to relate.

## Q5. What Sheldon, LFP90 and FX-91 say

- **For:** in both Sheldon's system and FX-91, a file's interface is the
  type of its module, checked, not written (Sheldon's `input`; FX-91's
  `load`, whose `.fxt` cache holds just the type and effect,
  `separate-compilation.md` §2.2). Neither gives a way to *name* that type
  in a program, so a parameter's type had to be written out by hand there
  too. `load-moduleof` is the missing name, not a new idea.
- **For:** LFP90's dependent subroutines are what makes the type-level
  application sound: the result type is written in terms of the
  parameter, and a call substitutes it.
- **For Q2's alternative:** Sheldon's `select` on any pure expression, by
  textual identity, with `input` pure.
- **Caution:** Sheldon's thesis calls sharing between modules "awkward"
  without a way to say two types are equal (§4.1.5). Narrowing makes more
  types unnamed, so more sharing has to go through parameters.
- **Not found:** none of the three has a narrowing form; FX-91's `extend`
  goes the other way.

## What I would do

1. **`load-moduleof`, as above**: arguments regions, effects, types and
   paths; parsed as a load of the key; the type found by walking the
   file's type. Test it on Fixpt first: replace `check-types-sig` and a few
   other hand-written signatures with `load-moduleof`s of the files they
   describe, and check that both checkers agree and the front end is
   unchanged. Then Heist's `core.fx` and `buffer.fx`.
2. **Narrowing and `hide`'s unnamed types together**, after (1).
3. **Ask the user** whether a load's abstract types should be the key's
   (Q2). It is independent of (1) and (2), and the smaller change.
4. Separately, decide whether reads of `%shared:` globals are effects at
   all (Q3).

A lower-tech alternative: a `fixpt signature FILE ARG…` that prints the
`moduleof` for a `*-types.fx` file, plus a check that the written one
still matches. It costs nothing in the checkers, but it is out of the
language, and the copies still have to be kept.

## The problems Heist found

Each one reproduced on `00c190c5` (the repros are below each).

**A. `include` loses type functions. Bug, both checkers.** It needs no
files:

```scheme
(define before (module (define-type (box (s type)) (productof (state (ref s @ed)) (name string)))))
(define m (module (include before) (define-type thing (productof (n int)))
  (define take (subr pure ((box thing)) string) (lambda (b) (extract b name)))))
;; a (productof (n int)) has no `name`
```

`(import before (type box))` works. So the names an `include` gives to
types don't carry a description function's parameters, and `(box thing)`
is read as `thing`.

**B. The made-before check ignores `with`'s scope. Bug, both checkers, in
any module.**

```scheme
(define outer (module (define f (lambda () (let ((m (module (define f (subr pure () int) (lambda () 5))))) (with m (f)))))))
;; `f` uses `f`, before it is made
```

The `f` inside `(with m (f))` is `m`'s. The scan for what an item names
treats it as the outer item. Accepted at the top level only because
globals have no made-before check.

**C. `->*` items can't be called while a module is made. Intended**
(`docs/fx26.md`, the `->*` row: "A module value naming one is refused"):
a `->*`'s effect is found after the module's values are made, and
something made has to know the effect first. It could be lifted by
finding the effects of a module's `->*` lambdas before checking the items
that are values. They are already found callees first, in groups. Not a
priority unless Heist hits it often.

**D. `include` of a call in a `module-parameters` file. Bug: the checkers
disagree.**

```scheme
;; a.fx
(module-parameters ((ed region)))
(define-type cell (ref int ed))
(define mk (subr (alloc ed) () cell) (lambda () (new 0)))
;; b.fx
(module-parameters ((ed region)))
(include ((proj (load-module "a.fx") ed)))
(define z (subr (alloc ed) () cell) (lambda () (mk)))
;; (define m ((proj (load-module "b.fx") @heap)))
;; FX-26: `cell` is not a type        Rust: accepts
```

The same `include` in a `module` expression, or in a `load-input` file's
`lambda`, agrees. So the cause is likely the FX-26 front end's handling
of a file of parameters, where an included call's type names aren't
collected [inf; not traced yet].

**E. Relative paths. Real, docs and behaviour.** A load in a loaded file
is from that file's directory. A load in a program run by `fixpt run` is
from the current directory, and by `fixpt eval` from the program's.
`docs/fx26.md` (the M7 paragraph) and `docs/fx26-grammar.md` (the
`load-module` entry) say "from the program's directory (the current one at
the REPL)", which is wrong for `fixpt run`, and say nothing of loads
inside loaded files. I'd make `fixpt run` resolve from each file's
directory, as `eval` does, and fix both docs.

**F. No top-level `include`. A decision for the user.** The 2026-10-01
design kept modules out of the REPL's globals (`with` only; "a REPL
import would make module components globals"). `import` at the top level
(2026-10-15) has already relaxed that by name. A top-level `include`
would be `import` of every name `m` gives. It would have to know `m`'s
type when the form is read, which the top level can (an earlier global's
type is known) but a module can't (`import` is expanded before anything
is known of `m`, so it needs the names). Feasible; whether it is wanted
is the user's call.
