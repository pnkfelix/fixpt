# Binding shapes: a module's names known before its types

Status: a design for the user to review (2026-11-10); step 1 and part of
step 2 built (the sections at the end). It grew out of Heist's request
that module files use macros
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

So the stages become, numbered as the steps below are (step 1, every
form's binding structure walked, the groundwork built first):
2. Shapes for module values, `with`'s type names by shape, the checker's
   check, and `(modnames …)`.
3. Renaming hygiene, `with` and `include` as visible binders; a file's
   own macros (Heist's (a)).
4. `import-with-syntax` in module files and of files with parameters
   (Heist's (b), (c)).
5. Later: top-level `include` without the driver; macros in shapes, if
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

## Step 2 (2026-11-10): shapes read, written into forms, and held to types (Rust)

The expander written in Rust now reads every module's shape and writes it
into each form that opens one, and the Rust checker holds it to the type.
The FX-26 front end has none of this yet: it is the next part of step 2,
with `with`'s type names read by shape (retiring the fallback) and
`(modnames …)`.

**Written into the form.** After expansion, and before a top-level form
or a module file's forms are parsed, the program's walk (step 1's) finds
the shape of the module each `with`, `extend`, `include` and
`import-with-syntax` opens, and writes it in after the module:
`(with m #:shape ((x y) (t)) body …)`, values then descriptions; or
`#:shape #f` where it is not known (`macros/shapes.rs`). A shape written by
hand is thrown away and read again: only the walk writes one.

**Where a shape comes from**, as the table above has it: a binder's
from where its value comes, by its place in the form that binds it (a
`define`'s expression or written type, a `let`'s or `let*`'s expression, a
typed parameter's type, a `module-parameters` type, a `define-type`'s
description); a `module`'s, its items' exports, without what a `hide`
holds or what a hidden `include` gives (as the checkers' `hiding` leaves
out every name so marked, though the module define it too); a file's,
read from its text before the program that loads it is expanded, a
function's of its module if it takes module parameters; a `the`'s,
`moduleof`'s, `load-moduleof`'s, `restrict`'s and `(select m t)`'s from the
types (a type that is a module's has a shape of its own); a function's
result's from its body or its declared type. A file's module parameters
bind its names, each module not `qualified` included (`Ring::Shape`), as
the checkers make the file.

**Held to the type.** The checker reads the shape off the form
(`Parser::written_shape`) and, where the module's type is known, refuses
a type whose names, by namespace, are not exactly the shape's
(`Checker::shape_held`): `` `m` gives other names than were read from the
program before it was checked: its type has no `y` ``. A shape is so a
promise the checker keeps, never a guess the expander makes alone; no
program of the suite is refused by it.

**Fast enough to run on every form.** Reading a program's binding
structure was a test's alone in step 1, and quadratic in a list's length:
a list's rest was copied at each of its parts, by `split` and by `fits`,
and the walk's environment copied at each part (a module's items each a
level). Now a rest is taken apart, not copied, `fits` looks at a rest in
place (`fits_rest`), an environment is shared segments (`Env`), and
aligning is a loop over a stack of parts to fill (`Aligner::run`), so
that deep nesting takes no stack: the 100-deep nesting `tests/stack.rs`
holds the checker to fits the walk too. A file is walked once, its shapes
kept for when it is read to be checked. Checking the front end's own
sources cold, in a debug build, takes 57 s where it took 53 s.

**A module of no known shape is refused** (the user's answer 1), where the
checker finds its type a module's: `` the names `m` gives are not known
before it is checked: give it a type where it is bound ``. A name whose
definition the walk did not read, a top-level one checked already (read
from a fasl, a file's hidden global `%shared:…`, a staged step's
`stage-module`), has the shape its checked type says: the checker answers
the walk (`shaped`'s `Global`). Besides the forms above, a shape is read
from an `import`'s names (the module's member), a lambda's parameter of no
type of its own (the parameter of the procedure type the lambda is
declared at, through `allof` and `poly`), a description function applied
(its body), and a type defined ahead of a value it names (read again where
it is used). An `include`'s module is not in the scope of what any
`include` gives, as the checkers make the modules included first.

Counted 2026-11-10, with the checker's answers: the front end's own
sources, every with and include of a known shape (1238 unknown at first,
from an `include`'s module read in the scope of the others'); the test
programs, unknown only in the 7 written to be refused, each refused as it
expects; Heist's 7 subsystems, none unknown, all checked.

**What is written is what was relied on** (the user's, 2026-11-10). A
module's shape is the walk's, in memory: an environment of environments,
each value's own shape where it is a module's, each type's where it is a
module type's, a function's its parameters' and result's, so that a shape
in any positive place reaches a binder (a callback's parameter takes the
shape of what the procedure it is given to gives it). What the form that
opens a module carries is less: the names references in its scope asked
of it, and the answers, `#:shape ((x (not y)) (t))`, `x` and `t` given,
`y` not (the reference was taken to mean an outer `y`). The checker holds
the module's type to those answers alone: a name nothing asked, it may
give or not (subsumption). A member that is a module is opened by a form
of its own, which carries its own answers, so the record never nests.
Writing whole shapes, nested, came to 12.5 million names in the front
end's sources (a module of a types file gives some 50 to 350 names, each
form opening it wrote them all, and their members' over again); the
answers are a few names each.

**Its cost.** Checking the front end's own sources cold, debug build, with
frame pointers: 60.7 s with shapes, 56.1 s without (two runs each,
alternated), from 83.4 s before the answers alone were written, lookups
were by segments of an environment in hash tables, a program's nodes kept
their syntax three lists deep, a form's operands were moved and not
copied, and a file read for its shape was not read again to be parsed.

**Only what it gives is written; the absences are the checkers'** (the
user's, 2026-11-10). The record a form carries is the names asked of the
module that it gives, `#:relied ((x) (t))`: what a reference was taken to
find outside the module is not written, the checkers find it themselves,
each name the scope names that the module's type gives held to the list.
A value: of those the body names, the checker's `used`, as it reads the
`with` (an inner `with`'s values bound by its record, until it is checked:
`free_into`). A type, effect or function of descriptions: as the parser
reads it, each `with` with a record it is read past noting it, its type
held not to give it. Written so, the absences came to 111,301 names of the
119,094 written in the front end's sources (an `include` in a module of
items naming a hundred standard names noted each); now a median of 3 a form.

**`include` and `with` shadow by one rule**, innermost first, type names
as values: a module's own definitions, then what its `include`s give,
then what is outside it, the standard names too (a `with`'s, the same).
The parser read a type name in a module with `include`s from the
`include`s last, after what is outside, and a standard type (`int`)
before any `with`'s; values were read innermost first already, through
`(with %include …)`. No program of the suite, nor Heist's, reads a type
otherwise than before; Heist includes its own `keyword?`, `parse-number`
and `make-session`, values over standard ones, as it did. The walk takes a
part's own binders before the modules it opens, as the checkers do.

Checking the front end's sources cold: 60.7 s with shapes, 55.6 s without.

## Step 2 in FX-26 (2026-11-10): the same records, read and held alike

The expander and the checker written in FX-26 now do what the Rust ones
do, held to them form by form: `tests/scopes.rs`'s
`the_two_expanders_write_the_same_records` compares each test program's
top-level forms as each expander writes them (110 programs with a record,
all the same), and the checkers agree on every test program, the three new
ones of modules of no known shape (`modules/*-shape-unknown.fx`) among
them.

**The walk and the shapes** (`macros-walk.fx`, `macros-shaper.fx`,
`macros-shapes.fx`): the walk of step 1, then the shapes of expressions,
types and modules as `Shaper` finds them, and the records written into
each top-level form before the parser reads it, and into each file loaded,
each file shaped first by where its load is (the files the driver read,
`parser-loads.fx`). The top level's shapes are kept by the reading state
each form leaves, as the expander keeps its macros; a file's are found
again in each parse, at its places. The walk was cubic in FX-26 at first:
each part's syntax was written for a message it rarely said, and a node's
path grew by appending. Now a message is written when it is said, and a
program walk's paths are kept innermost step first (a template's as
before): a 520-binding `let*` walked in 3.5 s, from 502 s; the front end
compiling itself, within noise of no shapes.

**The checker** reads a type, effect or function of descriptions in a
`with` body by its record (a `with`'s mark carries its frame,
`k-withs-reading`), a module's `include`s' records together outside its
own types, and holds each `with`, each module included and each
`extend`'s first to its record where it is checked, with the Rust
checker's messages (`k-shape-held`).

**What no form the expander reads defines** has the shape its type says,
as the checker has it (the user's choice of the FX-26 checker over the
driver): before a parse that the checker goes on from, the expander is
told the shapes of the globals the forms name (`check-global-shapes!`,
`k-global-shapes`): a definition read from a `.fasl`, a session's or a
stage's module (`%stage-type`, a step's named types). A parse that begins
the standard environment's again is told none, whatever the checker held.

**The fallback for a name defined nowhere is retired**, in both front
ends: a name read in a `with` body that the record does not give is read
outside it, and one defined nowhere is said plainly, `` `nope` is not a
type `` (`with-type-missing.fx`, `with-effect-missing.fx`,
`with-applied-missing.fx`). A `with` with no record, as `(select m T)`
reads `T`, still falls back through `(select m n)`.

## `(modnames …)` (2026-11-10): shapes written, and sealing

Named by `define-syntax` (the user's choice over a `define-syntax-shape`),
written as a `define`'s or a `the`'s type, in both front ends alike
(`docs/fx26.md` has the language). The expander writes a shape's name out
where it is used and makes `(define x (modnames …) e)` a `(define x (the
(modnames …) e))` before the walk (`Macros::sealed_written`,
`macros-shapes.fx`'s `sealed-written`), so that the parsers, the checkers
and a driver that hands the checker written in FX-26 expanded forms see
the `modnames` alone; the walk reads a binder's shape from it. The
checkers give `the`'s type a slot, linked where the value is checked to
its type sealed to the names (`Checker::the_sealed`, `k-the-sealed`), and
hold the value to it as `the` holds a value to a `moduleof`: the same
subsumption, the same run-time reshape where names are dropped (the
user's, 2026-11-10: `modnames` restricts the names as `moduleof` does).
`(abs t)` must name a type the module has abstract and `(desc u)` one it
has transparent (the user's): `modnames` drops names, it makes no type
abstract. A module inside, `(modnames m …)`, is not sealed to fewer names
yet, as a `moduleof` is not: no reshape reaches inside a value, so both
would need one that makes a new product of the module inside.

Step 2 is done. Next, step 3: renaming hygiene, `with` and `include` as
visible binders, a file's own macros (Heist's (a)).

## Step 3, proposed (2026-11-10): one mechanism for hygiene, renaming

**The rule** is ordinary hygiene: a template's free name refers to the
binding visible where its macro is defined, whatever binds the name where
the macro is used; a template's own binders bind only the template's
references. What changes is how both front ends make it so: one
mechanism for every macro, `syntax-rules` and procedural alike, at the
top level, imported, and in a file (the user's, 2026-11-10: one mechanism
is easier to understand, and is what `expand-once` and `local-expand`
would build on). Qualifiers (`(with #%toplevel x)`, `(with %shared:key
x)`) stay as syntax a program may write, no longer what expansion writes.

**Marks.** Expansion writes each name a template introduces as an alias of
its use, `%~N:x`, `N` the use's expansion number, as procedural macros'
names are written now: a free name's meaning is `x` as bound in the
macro's definition environment (the top level, a file's items, the
standard environment); a template's binder is the use's own, fresh. An
alias says where a name came from and nothing else, so partly expanded
syntax keeps it (an `expand-once` gives back syntax with its marks).

**Resolution, after expansion.** When a top-level form, or a module
file's items, are fully expanded, a pass over the program's walk (step 1)
resolves every alias, and no alias reaches the checkers:
- A template's binder and its references: a fresh name, as now.
- A free alias `%~N:x`: what `x` is in `N`'s definition environment is
  its intended binding. A top-level macro's is the top level's, written so,
  `(with #%toplevel x)` or `#%toplevel:x`, which nothing captures (stage 1,
  built: the messages a reference to a name the top level lacks gives stay
  as they are). A file's own macro's is its file's item, which no
  qualifier names: the alias becomes `x`, and what would capture it is
  dealt with as below.
- Captured by a use's binder that can be renamed (a `lambda`'s or `let`'s
  parameter, a `tagcase` arm's): that binder, and every reference the walk
  found bound to it, renamed fresh; then the alias becomes `x`.
- Captured by a name a module gives, a `with`'s or `include`'s: the
  `with`'s body given `x` from outside under a fresh name, `(let ((x%k
  x)) (with m body))` with the alias made `x%k`, for a value. Nothing of
  `m` is renamed: its names are its interface. A type, effect or
  function of descriptions the same way, by `let-desc` (below): `(let-desc
  ((t%k t)) (with m body))`.
- Captured by an item of an inner module that defines `x` itself: the
  same, the outer `x` named fresh before the module; the module's own
  `x` keeps its name, which is its interface.
So no capture is refused: each is resolved by naming the outer binding
afresh where the capture is, never by renaming what a module gives.

**A file's own macros** (Heist's (a)) then need nothing of their own: a
file's `define-syntax` items are macros of the file, defined before the
items that use them, their definition environment the file's items (any
of them, hidden ones too) and the standard environment.

**Messages** show names as written: an alias and a fresh name are shown as
their base, as procedural aliases are now (`TODO.md` §228), and the
checkers' special cases for unbound aliases retire with the qualifiers.

**Held alike.** The walk, the renaming and the records are held between
the front ends as in steps 1 and 2 (`tests/scopes.rs`), on the test
programs and on new ones for each kind of capture, and every expansion of
the suite checks and runs as before: the change is of mechanism, not of
meaning.

**Local binding forms** (the user's, 2026-11-10): each namespace has one,
so that every capture is resolved where it is, and a program can bind as
locally as a macro does.
- `(let-desc ((name description) …) body …)`: descriptions bound in
  `body`, as `define-type`, `define-effect` and a description function's
  `define-type` bind them at the top level or in a module. Each clause's
  kind is read from its description (the user's, 2026-11-10): an effect
  form, a `dlambda`, or else a type; a bare name, of what it names.
  Recursive descriptions stay `dletrec`'s.
- `(let-syntax ((name transformer) …) body …)` (R7RS's, with FX-26's
  signatures): macros bound in `body` alone, the narrower route the
  2026-11-08 leaning named (`typed-macros.md`).

**Order of work.** (1) The resolution pass, in both front ends, for
procedural aliases (the checkers' special cases retired). (2) `syntax-rules`
templates writing aliases, not qualifiers, top level and imported. (3) A
module file's own macros. (4) `let-desc`. (5) Captures by `with`,
`include` and inner modules resolved by naming the outer binding afresh
(`let`, `let-desc`). (6) `let-syntax`.

**Stage 2, built (2026-11-10).** A `syntax-rules` template's free names
are written as aliases, `%~N:x`, as a procedural macro's are, at the top
level and in an imported file's macro alike (`Action::Alias`,
`act-alias`). Each expansion records its macro's definition environment
(the environment the macro is defined in, which its template's free names
refer into), by its number (`hygiene::DefEnv`, `Withs::def_envs`;
`macros.fx`'s `def-envs`): the top
level, or a file, its hidden global `%shared:key` and the values its
module shows; a template's check is expansion 0. The resolution writes a
free alias as the qualifier its definition environment says, so
expansions read as they did:
a top-level macro's `(with #%toplevel x)`, or `#%toplevel:x` where the walk
says the name is qualified (a description's, a specification's), or `x`
where written as is (a `globals` list); a file's macro's `(with %shared:key
x)` for a value its module shows, else `(with #%fx x)`. What the template
check refuses is refused as before, at the check. Left for later: a
file's macro's descriptions are still read through its module whole
(`Action::ModuleType`, `(select %shared:key τ)`), not by aliases, as
naming them one by one would need a type's qualifier for each name.

The FX-26 expander's two chains of files (the one the expander's forms
load, and `macros-shapes.fx`'s through `macros-shaper.fx`) are separate
instances, with separate state, so the table of definition environments
is handed to the resolution by `parser-top.fx` (`def-envs-given`), and its
type is structural (`def-env`), the same in each instance.

**Stage 3, built (2026-11-10).** A module file uses its own macros
(Heist's (a)): its `define-syntax`es, hidden or not, are defined in order
in a scope of the file's own (no macro of the program's: a file sees the
standard environment alone), and each item after one is expanded by them
before the file's shape is found (`Checker::file_own_expanded`;
`parser-top.fx`'s `loaded-own-expanded!`, run on the files the driver
read, before they are shaped). Their definition environment is the
file's items (`DefEnv::Within`, kind 2): a free alias becomes the plain
name, and a binder at the use that the plain name would reach, other
than the item's own definitions, is renamed `%x~N` with each reference to
it (counted apart from a template's fresh names, `%x:N`, in both front
ends alike). A `with` or `include` around the use, whose names may
include it, is refused for now (stage 5), and so is a typed hole in a
macro a file uses itself, whose contract a qualifier reads. A macro used
before its file defines it is refused. Found on the way: a procedural
macro of an imported file read what it renames as the importer's top
level (`(inc 5)` 500, not 6); a procedural macro now keeps its definition
environment as a `syntax-rules` one does. Open: a file's macro that makes
definitions defines its template's own names, `%raw:N`, as items of the
file's module, so they are in its type, unnameable.

**A property to prove, one day** (the user's, 2026-11-10): full expansion
is the same as repeated `expand-once` steps. What keeps it within reach:
- Resolution reads the fully expanded term and its marks alone, never how
  it was reached: aliases resolved once, after expansion, as now. An
  `expand-once` gives back syntax with its marks, unresolved.
- Marks are stable across steps: an expansion's aliases the same whether
  its use is expanded inside a larger expansion or alone. Expansions are
  numbered in the order they happen today, which a proof would have to
  number by something intrinsic (the use's place) or quotient by (marks
  equal up to renumbering). A gap noted, not yet closed.
