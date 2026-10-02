# First-class modules for FX-26: a design

Design note, 2026-10-01, from a discussion with the user. Nothing is
built yet. The user's decisions so far:
- Modules are a feature of their own, *beside* globals and the REPL, which
  stay as they are, rules and all. The front end is not ported to them
  now.
- Follow Sheldon's way: modules are values, typed by module types, with
  type identity through `select` on pure expressions (LFP90; thesis;
  `docs/research/modules.md` §2).
- A module's private definitions are never redefined. If FX-26 ever wants
  a redefinable binding inside one, it is a form of its own
  (`define-global`, say), designed then.

Why now: the front end already wants parameters over regions and effects.
Its compiler's data is all in `@k` (356 uses, 10 files) and its checker's
in `@t` (301 uses, 13 files); 33 effect aliases are built from them. Those
are a module's region and effect components, fixed for the whole program
today.

## What to adopt: FX-91, not the 1990 paper alone

Sheldon's LFP90 system is fully opaque and has no way for two modules to
agree on a type ("awkward", thesis §4.1.5). FX-91 is its superset with
transparent descriptions, and is what this repository's FX-91 front end
already implements and passes its conformance corpus with
(`crates/fixpt-fx91`, `tests/conformance/fx91/cases/tests.fx`):

```scheme
(module (define-abstraction t type bool)     ; abstract: t, up-t, down-t
        (define-description d bool)          ; transparent
        (define x (up-t #t)))
(moduleof (abs t type) (desc d bool) (val x t))
(with m body)        ; m's values (and descriptions) in scope in body
(select m t)         ; a description from m; also written m..t
m.x                  ; a value from m: (with m x)
```

`abs` takes any kind: `(abs e effect)`, `(abs r region)` are as legal as
`(abs t type)` (FX-91 report §2.2.6). So FX-91 already answers whether
modules can carry the region and effect parameters the front end wants:
yes, as abstract components.

## The design, in FX-26's terms

### Values and types

```scheme
(module
  (define-generative t (listof int @heap))   ; abstract component, up-t/down-t inside
  (define-type pair-of-t (pairof t t @heap))  ; transparent component
  (define-effect touches (read @heap))        ; transparent effect
  (define x t (up-t (list 1 2)))             ; value components
  (define-rec (f (subr …) …) …))
```

has type

```scheme
(moduleof (abs t type)
          (desc pair-of-t (pairof t t @heap))
          (desc touches effect (read @heap))
          (val x t)
          (val f (subr …)))
```

- **Abstract components** come from `define-generative`, FX-26's existing
  `define-abstraction`: inside the module, `t` with `up-t`/`down-t`;
  outside, only `(select m t)`, equal to nothing but itself. Abstract
  regions and effects, `(abs r region)` and `(abs e effect)`, come from a
  module's own `letrena`-style places and from effect parameters
  (below).
- **Transparent components** are `define-type` and `define-effect` inside
  the module: outside, `(select m pair-of-t)` *is* its definition, with
  `t` read as `(select m t)`. This is FX-91's `desc`, and the sharing
  story Sheldon's own system lacked.
- **Value components** are `define`, `define*` and `define-rec` inside the
  module, each seeing those before it, as at top level. They are never
  redefined: a module's definitions are fixed once it is made.

### Selection and opening

- `(with m body)` makes `m`'s value components the names in scope in
  `body`. Its types are written `(select m t)` there as anywhere: FX-91's
  `with` opens descriptions too, but then a body cannot be parsed until
  `m`'s type is known (FX-91 keeps such bodies unparsed until then); M1
  opens values only, so every body is parsed before it is checked.
- `(select m t)` in a type, an effect or a region. `m` must be a *path*:
  a variable bound to a module, or `(select p n)` for a module component
  `n` of path `p`. Two selects are equal iff their paths are the same
  binding and the same names (Sheldon's textual identity, with bindings
  in place of text, so shadowing cannot confuse it).
- Dot shorthand, as FX-91: `m.x`, `m..t`. Not in the first stage.

Sheldon allows any expression whose effect has no reads in a select, and
compares them as text. Paths alone are the first stage; general pure
expressions, `((f 2) .. t)`, wait for a need.

### Dependent subroutines: functors

A parameter's type may mention an earlier parameter, and the result may
mention any parameter:

```scheme
(define make-set
  (subr pure ((elt (moduleof (abs t type) (val < (subr pure (t t) bool)))))
        (moduleof (abs s type)
                  (val empty s)
                  (val add (subr pure ((select elt t) s) s))))
  (lambda (elt) (module …)))
```

The parameter list's form decides: a bare type is as today; `(name type)`
names the parameter for later types. A call substitutes the argument for
the name where the argument is a path; where it is not, a type that
mentions the parameter is an error, unless the call is bound by `let`
first (Sheldon's `let` rule: a `let`-bound module is opaque, its selects
not interchangeable with its defining expression's). This is LFP90 §2.2's
dependent subroutine, "of which ML functors are a restricted form".

### Effects, regions, and the front end's case

A module parameterized over a region is a dependent subroutine over a
module with an `(abs r region)` component, or more directly, a module
value made inside `(plambda ((k region)) (module …))`:

```scheme
(define compiler-over
  (plambda ((k region))
    (module
      (define-effect emits (maxeff (read @k) (write @k) (alloc @k)))
      (define r-declined (ref bool @k) (new #f))
      …)))
```

Each instantiation's components are at its own region. That is the
front end's `@k`, made a parameter, with `emits` a transparent effect
component of the instance.

### Globals and the REPL

- A module may be a global's value: `(define m (module …))`. Then
  `(select m t)` names the global, and the rules for globals hold: a
  redefinition of `m` re-checks what uses it, as for any global, and
  `(select m t)` of the new `m` is a new type, so uses that relied on the
  old one break, as a redefined generative type's do today.
- Inside a module there are no globals of its own: its definitions are
  components. A module's procedures that read the module's own components
  read them as fixed values, adding no `(read (globals …))`.
- The REPL can make, bind and open modules like any value.

### Run time

A module is a product of its value components, in order: a frozen
bloblet. `with` and `m.x` are `extract`s. Abstract, transparent, region
and effect components are erased. `up-t`/`down-t` are identities, as
`define-generative`'s are. So the compilers and the native code see only
products and `let`s, if the checker gives them those.

## Stages

| stage | what                                                                                                      | where                                       |
| ----- | --------------------------------------------------------------------------------------------------------- | ------------------------------------------- |
| M1    | `module`, `moduleof`, `with`, `select` on variables; abstract, transparent and value components; types    | Rust checker, lowering; REPL                |
| M2    | the same in the FX-26 checker and parser, the checkers agreeing                                           | `check-*.fx`, `parser.fx`                   |
| M3    | both compilers and native code: modules as products, `with` as `extract`s                                 | `cellular.rs`, `compile*.fx`, register code |
| M4    | subtyping of module types: width, and a transparent component where an abstract one is expected           | both checkers                               |
| M5    | dependent subroutines (named parameters), application by path, `let` opacity                              | both checkers                               |
| M6    | dot shorthand; paths through module components                                                            | reader, both checkers                       |
| M7    | a file is a module: `(load-module "file")`, checked as a `module` that sees only the standard environment | both checkers, REPL                         |
| later | abstract regions and effects; `plambda` over regions making modules                                       | both checkers                               |

M1 alone is usable at the REPL (lowered). Each later stage keeps both
checkers in agreement before the next begins, as the rest of FX-26 does.
Subtyping comes before functors (the user's, 2026-10-01): a module given
where a module type with fewer components is wanted needs it already, with
no dependent types at all, and FX-91's own tests are mostly of that shape.
Abstract regions and effects are not needed for a first deliverable:
without them a module's types name the regions it was made at, as any
value's do; they come when the front end's `@k` and `@t`, or another
client, needs them.

## A file is a module (M7), and separate compilation

Separate compilation is not part of M1–M7 (the user's, 2026-10-01). It
needs what `separate-compilation.md` lays out (facts keyed by file and
offset, content stamps, a carrier for compiled words with import tables,
cutoff by interface), a project of its own with no client yet. The two
meet in one place, which M7 builds and Q9 later caches:
- `(load-module "file")` reads the file, checks it as one `(module …)`,
  and gives its value, as FX-91's `(load "file")` does
  (`tests/conformance/fx91/cases/tests.fx`: `(let ((m (load "tests.fx")))
  (with m x))`), and Sheldon's `(input "file")`.
- **Its interface is its type.** The `moduleof` printed is the interface
  file: no format of its own, so long as `moduleof` can say everything a
  file exports.
- **A module file sees only the standard environment**, not the REPL's
  globals, as Sheldon's files saw only a fixed library: so a file means
  the same in every session, and can be compiled once and loaded anywhere.
  A module made at the REPL closes over what it likes, as any value does.
- Its compiled form, later: the code that builds the module's product, its
  type, and a stamp; loaded without checking again when the stamp says the
  file and what it was checked against are unchanged.

## Open questions

1. **The name.** `module`/`moduleof`, as FX-91, Sheldon and ML (and 1ML)
   say for exactly this: a first-class value carrying abstract types. The
   alternatives considered: *environment* (Scheme's first-class
   environments are reflective lookup tables, mutable in MIT Scheme, the
   opposite of a sealed abstraction); *vocabulary* (Forth's and Factor's
   word for a namespace, which hides names but carries no types and is
   not a value). Recommendation: `module`, keeping *unit* for the static,
   file-level layer `separate-compilation.md` proposes, should it come.
2. **Subtyping of module types.** FX-91 lets a module be used where a
   type with fewer components, or a component abstract where it is known,
   is expected. Decided: M4, before functors; exact match before it.
3. **Opening by `with` only, or also an `open`-like import of a module
   into the REPL's globals?** Recommendation: `with` only; a REPL import
   would make module components globals, which the sealing decision
   rules out.
