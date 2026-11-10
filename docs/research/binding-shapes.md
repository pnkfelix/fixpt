# Binding shapes: a module's names known before its types

Status: a design for the user to review (2026-11-10). Nothing here is
built. It grew out of Heist's request that module files use macros
(`heist/docs/requests/fixpt-macros-from-heist.md`, item 1) and the
conversation that followed, in which the user asked whether the set of
*bindings* could be known at expansion time, with only the *types*
waiting for the checker.

## The problem, and where it comes from

The expander must know what every name in a macro's expansion refers to.
At the top level it knows: a template's free name becomes `(with
#%toplevel name)`, and a macro imported from a file has its names
qualified by the file's hidden global, `(with %shared:key name)`. A
module file's own macros were refused for exactly this reason. A use of
the macro may sit inside a local binding of the same name, `(lambda
(helper) (m 1))` where the template calls the file's `helper`, and FX-26
has no reference to a module's own item that a local cannot capture.

Ordinary hygiene handles this by renaming: the expander sees the local
binder `helper`, sees that a reference the macro introduced would be
captured by it, and renames the binder. That needs the expander to see
every binder around a use. Herman's design assumes it can
(`typed-macros.md`, "Where it runs: parsing knows what is bound": "every
binder it meets is either a kernel form's … or a macro use's"). In FX-26
two forms break that assumption:
- `(with m body …)` binds whatever names `m`'s module type has;
- `(include m)`, in a module or at the top level, binds every name `m`
  gives.

Both bind by a type, and a type exists only after checking, which comes
after expansion. Every other binder is visible in the syntax: `lambda`,
`let`, `letrec`, `tagcase`'s arms, a module's `define`s, `import` (which
lists its names).

That one gap has already cost FX-26 several workarounds, each built as
its own mechanism:
- **`with`'s type names fall back.** Inside `(with m …)`, a type name `t`
  is read as `(select m t)` *falling back* to what `t` means outside,
  settled once `m`'s type is known (`Arena::with_fallback`,
  `modules.rs`), because the parser cannot tell whether `m` gives `t`.
- **`import` marks types and effects** as such, `(import m x (type t)
  (effect e))`, because it is expanded before anything is known of `m`.
- **Top-level `include` is resolved by the driver.** Its names are known
  only from `m`'s type, so the program runner hands each front end the
  `import` it amounts to once the form is checked; a type defined before
  it cannot name what it gives.
- **`with` brings no macros**, so macros need a special form of their
  own, `import-with-syntax`, which takes only a top-level name bound
  literally to `(load-module "path")` of a file without parameters.
- **A file cannot use its own macros**, the restriction Heist hit.

## The idea

Separate a module's *binding shape* from its *type*. A **shape** is what
the expander needs and nothing more: the names a module gives, each with
its namespace (value, type, effect, macro), and, for a name that is
itself a module, that module's shape. A shape has no types in it. Values'
types, regions, effects and abstract types' meanings all stay with the
checker, after expansion, as today.

Shapes are read from the syntax, before expansion of what uses them.
Where a shape cannot be read from the syntax, the program writes one, in
the form of a `moduleof`, and is refused if it does not. The checker,
once it has the type, confirms that the type gives exactly the names the
shape promised. So the expander works from a promise that is checked,
and a module whose names disagree with its shape is refused, never
miscompiled.

With every module's shape known at expansion:
- **Every binder is visible to the expander.** `(with m body …)` binds the
  names of `m`'s shape, and `(include m)` the same; both are as visible
  as `lambda`'s parameters. Hygiene can then be the standard kind, and
  nothing needs the qualifiers' special cases to avoid capture.
- **A shape can contain macros.** A module's `define-syntax` is part of
  its shape, so `with` and `include` can bring a module's macros, and
  `import-with-syntax` becomes an ordinary `include`.

## The precedents

**Bawden, "First-class Macros Have Types" (POPL 2000).** This is the
closest. Bawden makes macros first-class by giving them *types*, and a
macro's type is the description of the environment frame its expansions
refer to. A `template` expression describes a frame: its names, the
macros among them with their expanders, and the types of its values
(`(make-promise (value <plain>))`). `instantiate` makes a frame of that
shape at run time. A macro value at run time is just that frame, and a
use of it is expanded statically from its type, its free names compiled
as fixed slots of the frame. His module system (§5.2) is built from
exactly this: an interface is a template, a module is an instance, and
`open` makes aliases for the names the interface exports
(`define-alias`, from Waddell and Dybvig).

Two of his observations decide this design:
- **Expansion depends on types, so the types it depends on must be known
  without inference.** §8: "type-inference depends on knowing data flow,
  and data flow depends on having parsed the program, and first-class
  macros make parsing depend on types, closing the loop." His answer is
  that every type a macro use depends on is declared. Here the loop is
  the same, with `with` in place of a first-class macro, and the answer
  is the same in kind: what expansion depends on, the shape, is read
  from the syntax or declared, and the rest of the type is inferred
  afterwards as now.
- **A macro's type is generative.** "New base types are generated by
  macro definitions appearing in template expressions", equal only to
  themselves. Two modules may give a macro under one name, and a use is
  expanded by the one the shape says, so the shape must say *which*
  macro, not only that there is one. FX-26's abstract types already work
  this way (`define-generative`, `m..t`).

Where FX-26 differs from Bawden: his macro types are a full type system
for macro values (procedures taking and returning frames, declared on
every `lambda`); FX-26 needs only the shapes, and only of modules,
because a module is its one kind of first-class environment.

**Herman, "A Theory of Typed Hygienic Macros" (2010).** A macro's
*binding signature* says, before its use is expanded, which of its
operands are binders and what is in their scope. That is what lets
Herman's expander know every binder. Shapes are the same thing for
modules: a module's binding structure, known before its types. With
both, FX-26's expander knows every binder: kernel forms by their own
binding structure, macro uses by their signatures, and `with` and
`include` by shapes.

**Racket's units** (Flatt and Felleisen, "Units: Cool Modules for HOT
Languages", PLDI 1998; Owens and Flatt, "From Structures and Functors to
Modules and Units", ICFP 2006). A unit is a first-class value, but
invoking one binds exactly the names its *signature* lists. Signatures
are written in the syntax, so expansion knows them, and they may contain
macros. That is the same split: the binding structure is static even
though the module value is first-class. (Cited from memory; the papers
are not in `~/Dev/LangPlay/papers/`.)

**Waddell and Dybvig, "Extending the Scope of Syntactic Abstraction"
(POPL 1999).** A module system whose exports, macros included, are known
to the expander, with `import` making aliases. Its modules are
second-class; FX-26's files are close to that case already.

## A module expression's shape

Each form that makes a module, and where its shape comes from:

| module expression | its shape |
| --- | --- |
| `(module item …)` | its items' names, read in order: `define`, `define*`, `define-rec`, `define-type`, `define-effect`, `define-generative` (the type, and its `up-t`/`down-t` inside only), `define-datatype` (type and constructors), `define-syntax`, `import` (its names), `include` (the included module's shape), without what `hide` hides; a use of a macro that makes definitions adds what its expansion defines, since items are expanded in order |
| `(load-module "path")` | the file's items, read the same way; a file with `module-parameters` gives a `plambda` or `lambda` whose result has that shape |
| `(load-input "path")` | the shape of the file's one expression |
| `(extend e0 e1)` | `e0`'s names, then `e1`'s, `e1`'s winning |
| `(the T e)`, a module given where `T` is wanted | `T`'s names |
| `(restrict T name …)` | the names listed |
| a variable | its binding's shape: a `define` or `let` of a module expression has that expression's; a parameter, or a `define` with a type, has the shape of its declared `moduleof` |
| `(with m x)`, a module `x` that `m` gives | `x`'s shape inside `m`'s |
| a call of a functor, `(f a)` | the shape of `f`'s result: its declared `subr` type's `moduleof`, or the shape of its body where `f` is a `lambda` bound to a variable directly |
| `(proj e d …)`, `((proj (load-module "f") @r))` | the shape of `e`'s body, which a `plambda` does not change |
| `(load-moduleof "f" …)`, as a type | the file's shape |
| `if`, `tagcase`, `let` with a module result | the shape of the expected `moduleof` if one is written; otherwise its arms' shapes must be the same, or it is refused with a request to write one |

A `moduleof`'s shape is its members' names: `val`, `abs` and `desc` for
values, types and effects, and a new member kind for macros (below).

What has no shape: a module made by `stage`, by a call whose type is not
written, or by any expression the table does not cover. `with` or
`include` of it is refused: "the names `m` gives are not known here:
give it a type, `(the (moduleof …) e)`". This is the price, and it is
Bawden's: where expansion depends on something, that something is
declared.

## The checker's check

Once a module expression is typed, its type's names must be exactly its
shape's names, in the same namespaces; a module's nested modules
likewise. A mismatch is refused where the expression is, naming the
names that differ. That check is what makes a shape a promise rather
than a guess, so the expander's decisions are sound by construction: the
expander never resolves a name to a binding the checked program does not
have.

In the common cases the check cannot fail, because the shape and the
type are read from the same syntax (a `module`'s items, a declared
`moduleof`). It does work in the cases that join shapes: `extend`, `if`,
a functor's body.

## Expansion with shapes

**`with` and `include` become visible binders.** `(with m body …)` binds,
in `body`, each name of `m`'s shape. The expander treats it as it treats
a `let` of those names. Where a reference a macro introduced would be
captured by one of them, the expander renames, as for any binder. A name
`m` gives cannot be renamed, since it is `m`'s, so instead the expander
rewrites that `with` into explicit bindings, `(let ((x%5 (with m x)) …)
body)` and `(select m t)` for types, under fresh names that it can
rename. `(with m x)` with a single variable as its body binds nothing
visible and stays the primitive selection.

**Hygiene becomes ordinary renaming.** Template binders are made fresh,
as now. A use's binder that would capture a reference the template
introduced is renamed, the transparent convention Herman's design
already names. `#%fx`, the standard environment, remains how a template
names a standard binding wherever it is used. `#%toplevel` and
`%shared:key` stay for what they are today, the top level and the one
value every load of a file is, but they are no longer the only defences
against capture.

**A file's own macros.** With every binder known, a file's macro used
later in the same file needs nothing special: its template's free names
resolve to the file's items by scope, and a local binder that would
capture one is renamed. This is Heist's item (a).

**`with` and `include` bring macros.** A module's shape includes its
`define-syntax`es. `(include m)` brings `m`'s macros with its other
names, so `import-with-syntax` becomes `include`, and works in a module
file as anywhere: Heist's items (b) and (c), the latter because a file
with `module-parameters` has a shape like any other.

## Macros in shapes

A macro's member in a shape names *which* macro it is, as Bawden's
generative macro types do. A first stage that keeps expansion static:
- **A macro member is identified by where it is defined**: the module
  expression whose item it is, which for a file is the file (as
  `%shared:key` already identifies a file's values). Two modules give the
  same macro exactly when they are, or come from, the same definition.
- **A module of a macro member is used by name.** The expander must know
  which definition a use of `(with m (twice x))` expands by, so `m` must
  be a path whose shape is known to come from one definition: a variable
  bound to a `module` or `load-module`, a `select` from one, a parameter
  whose declared type says which (below). An `if` choosing between two
  modules that give different macros has no shape with that macro in it.
- **A template's free names refer into the module.** A use of `m`'s
  macro expands its free names to `(with m name)`, `m` being the path the
  use reached the macro by, renamed if the use's own binders would
  capture it. That is Bawden's compiled access to a slot of the frame.
  A template may name only what the module's type shows, as
  `import-with-syntax` requires today, because a module's run-time
  product holds only its shown values. A later stage could keep hidden
  values as hidden slots.
- **A functor's parameter** may take a module with a macro only if its
  declared type names the macro's definition. A first stage can refuse
  this, or allow only `(load-moduleof "f" …)` types, where the file names
  the definition. Bawden's `(type-of template delay)` is the general form.

Earlier, the user and Claude leaned against macros in the types of
first-class modules (`typed-macros.md`, "Leaning: narrower macros by
`let-syntax`, not in module types", 2026-11-08): a use would depend on
which module value reached it, and that needed signatures computed from
code. Shapes are exactly those signatures, made cheap by keeping them
separate from types and static by construction. The leaning is worth
revisiting in their light, but the first stage above stays narrow: macro
members only where a definition is named, which covers files and literal
modules, Heist's cases.

## What it retires

- `with`'s fallback types: a `with` body's type name is `m`'s exactly
  when `m`'s shape has it, known at parse time.
- `import`'s `(type …)` and `(effect …)` marks: the shape says which
  namespace each name is in. The marks could stay accepted, for clarity.
- The driver's resolution of top-level `include`: the shape gives its
  names where the form is, and a type defined before it can name them.
- `import-with-syntax` as a form of its own, with its conditions.
- The restriction on a file's own macros.

## What it costs

- **A shape pass** in each front end's expander, Rust and FX-26, done as
  items are expanded in order. Most of it is reading names from items,
  which the expanders already do for `hide`, `import` and module item
  ordering.
- **The checkers' check** of each module expression's type against its
  shape, in both checkers.
- **Renaming hygiene** for use binders in the expanders, with `with`
  rewritten where it would capture. The template side exists.
- **A refusal programs may meet**: `with` or `include` of a module of no
  known shape. Every Heist file is a `load-module`, a parameter with a
  `load-moduleof` type, or a literal module, all of which have shapes.
- **Error messages** must show names as written, not as renamed.

## Stages

1. Shapes for module values: the shape pass, `with`'s type names decided
   by shape (retiring the fallback), and the checker's check. No macros
   yet. The suite must agree with today's behaviour, except for refusals
   of `with` of a module of no shape.
2. Renaming hygiene in both expanders, with `with` and `include` as
   visible binders. A file's own macros allowed: Heist's (a).
3. Macros in shapes: `include` and `with` bringing them, in module files
   too; `import-with-syntax` re-expressed as `include`. Heist's (b) and
   (c).
4. Later: top-level `include` without the driver; macro members of
   functor parameters; hidden values in a module's run-time product.

## Answered (the user, 2026-11-10)

1. **Refusing `with` of a module of no known shape: yes.** Where the
   shape cannot be read, the program writes one.
2. **Macros in module shapes: not yet.** The 2026-11-08 leaning stands
   for now, perhaps revisited later. So "Macros in shapes" above is
   deferred, and stage 3 changes accordingly (below).
3. **`import-with-syntax` stays.** Without macros in shapes, `include`
   brings only values, types and effects, so it is not
   `import-with-syntax`, which is still the one form that brings a file's
   macros: it needs a fixed definition for them, which a file gives and
   an arbitrary module value does not. With every binder visible
   (stage 2), it is allowed in a module file, its macros scoped to that
   file (Heist's (b)), and of a file with module parameters, `lib` being
   the instance the importer names, `((proj (load-module "f") @r))`, a
   template's free names expanding to `(with lib name)`, renamed where a
   binder around a use would capture `lib` (Heist's (c)).
4. **A shape written as `(modnames member …)`** (the user's; first
   `mod`, the name still open): a form of its
   own, not a `moduleof`, the types left out. Its members: a bare symbol
   `x` or `(val x)` a value, `(abs t)` an abstract type, `(desc u)` a
   transparent one, `(eff e)` an effect, `(modnames m member …)` a module
   of that shape, the same form named, so it reads alike at every level.
   It may be written only where a value supplies the types: `(define m
   (modnames x y (abs t)) (stage …))`, the checker taking them from the value's
   type, the names exactly as written. Where nothing supplies them, a
   functor's parameter, say, a `moduleof` with its types is needed, and
   `modnames` is refused there, saying so. A `moduleof` serves as a shape
   wherever one is wanted, its types ignored by the expander.
   **Leaving names out seals** (the user's question, 2026-11-10): `(modnames
   x (abs t))` given a module that also has `y` is that module made into one
   of `x` and `t` alone, as `(the (moduleof …) m)` and `restrict` make one
   (a module fits a type of fewer values, M4). So `m`'s type has exactly
   the shape's names, which is what keeps the expander's view of what
   `(with m …)` binds and the checker's the same by construction. Naming
   something the module does not give is refused, as `restrict` refuses
   it. The cost is sealing's: where names are dropped, a new product at
   run time; where none are, nothing.

So the stages become:
1. Shapes for module values, `with`'s type names by shape, the checker's
   check, and `(modnames …)`.
2. Renaming hygiene, `with` and `include` as visible binders; a file's
   own macros (Heist's (a)).
3. `import-with-syntax` in module files and of files with parameters
   (Heist's (b), (c)).
4. Later: top-level `include` without the driver; macros in shapes, if
   the leaning is revisited.

## Naming a shape: `define-syntax` (the user's, 2026-11-10)

A typed shape is named already: `(define-type counter-sig (moduleof …))`,
which the expander reads from its syntax, defined before it is used (types
are declared ahead; a shape is not, so a name must be defined before a
use reads it). So are `load-moduleof` and `restrict`.

An untyped shape is named by `define-syntax`, not by a form of its own
(the user's question; a `define-modnames` was the first thought):
`(define-syntax counter-shape (modnames x y (abs t)))`. `define-syntax`
binds a name in the expander's environment to something that exists when
the program is expanded, and a shape is that: the expander uses it, the
checker only confirms it, no value has it at run time. Its second part
already says what is bound, `(syntax-rules …)` or a procedural
transformer, so `(modnames …)` is one more kind; a use checks the kind (a
shape's name where a macro is used, or a macro's where a shape is wanted,
refused). Racket's `define-syntax` binds compile-time values of any kind
in the same way, and its unit signatures are such bindings. And
`import-with-syntax` already brings a file's `define-syntax` names, so a
shape a library defines reaches the files that import it.

Not circular: a name is defined before its uses, so what it stands for is
known before any shape that depends on it is read; a cycle would need a
name reached through the shape it gives, which `with`, bringing no
macros, rules out.

A `define-syntax-type` is not needed for this. Named macro signatures, the
`syntax-contract`s (`typed-macros.md`), would be bound the same way,
`(define-syntax let1-contract (syntax-contract …))`, so `define-syntax`
names every expansion-time thing, unless the kinds turn out to need
different scoping.

Open (the user's alternative, 2026-11-10): `(define-syntax-shape name
member …)`, the kind in the head. Claude's lean: `define-syntax` with
`(modnames …)`, one defining form for every expansion-time thing, the kind
one word later, and `modnames` needed inline anyway, so the named form
reuses its member grammar. Easy to reverse.

## Step 1, built (2026-11-10): every form's binding structure, held to the checkers'

Every form the checkers parse now has its binding structure written in
Herman's notation, beside the kernel's, in `macros-kernel.fx`'s
`scope-forms`: `vlambda`, `typecase`, a program's `tagcase` (arms taking a
product apart, `(tag (x …) body)`), `case`, the `confirm-`s and `acyclic`,
the process forms (`spawn`'s mailbox and place, `par`, `pselect`'s arms),
`stage` and `session-check`, the bloblet forms, `module` (its items each in
scope in all of them), `with` and `extend`, and the definitions a module
holds (`define-generative`, `define-datatype`, `import`, `include`, `hide`,
`define-syscall`, `define-convention`). Two additions to the notation:
`item`, a module's item (a definition, a string, or an expression run as
the module is made), and `(shape A)`, what the module at address `A` gives,
which `with`, `extend` and `include` bind. Only the expander written in
Rust reads `scope-forms`, for now; the FX-26 one reads the kernel's alone,
so a template still uses the kernel's forms only.

**A program's walk** (`Mode::Program` in `macros.rs`): a program's form,
after expansion, aligned as a template with no pattern variables, so that
each binder and each reference is found with the environment it is in.
Where the checkers let a program do what a template may not, it does: a
reserved word bound or referred to (Heist binds `else`; a module gives
`spawn`), a field labelled by position, `else` as the form's word where a
clause may be either. A `(shape A)` level is not known yet: a name looked
for past one is left alone.

**Held to the checkers** (`tests/scopes.rs`): every test program the
checker accepts, 631 of them, its local value binders renamed as the walk
finds their scopes (`Checker::alpha_renamed`), checks to the same types
(9563 binders renamed), and every module file whose load checks is walked
(19). A name the walk cannot place is not renamed: one inside a
quasiquoted vector (no address reaches it), and the arguments of a
`load-moduleof`, which may be descriptions or module values, which only
what binds them tells apart (step 3 decides them by shape). Run by hand on
Heist's code and the front end's own `.fx` sources, every file walks.

**No stack for a list's length.** Aligning (`fill`), walking (`walk`) and
evaluating what a list's parts bind (`rib`, `eval`) loop down a list's
rest, and `fits` looks no deeper than a `union`'s members can differ
(`FITS_DEPTH`), as §229 did for quotes: the front end's own
`native-direct-arm64-layout.fx` has a `case` of 550 clauses.
