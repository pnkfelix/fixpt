# Typed hygienic macros

Design note, 2026-10-30, the user's request: adapt David Herman's typed
hygienic macros to FX-26 as a minimal prototype that uses FX-26's type
system as far as it will go, and say early what the type system itself
would need. Nothing here is built.

## Where FX-26 stands

- **No macros.** `docs/fx26.md` has left open since step 1 whether FX-26
  needs them ("Syntax. FX had no macros.").
- **Form names are reserved** ("Names", in the kernel's section):
  "Scheme would let a binding shadow a form; FX-26 parses before it knows
  what is bound." Both parsers dispatch on a form's head by name
  (`parse.rs`, `parser-exps.fx`), with no environment.
- **The derived forms are written twice**, once in each parser: `cond`,
  `case`, `and`, `or`, `let*`, `confirm-length` and `define-datatype`
  (`parse.rs`'s `parse_cond`, `parse_case` and the rest, and their twins
  in `parser-exps.fx`, `parse-cond`, `parse-case`). Each must agree with its twin, and each new one costs
  two implementations and a new rule for both to agree on.
- **`(with #%fx name)`** is the standard binding of `name`, whatever
  shadows it (`docs/fx26.md`, "`#%fx`"). The derived forms use it to call
  what they need. It is the one unshadowable reference FX-26 has.
- **Hole mode** (`Checker::describe_hole`, the Rust checker alone): a form
  checked with a hole in it, read as a reserved name, for the REPL. It is
  the nearest thing FX-26 has to checking a template.
- **The Scheme side** has a full macro system (`docs/macros.md`):
  `syntax-rules`, explicit and implicit renaming, syntax parameters. None
  of it is typed, and TODO.md (the REPL's speculation) stops at procedural
  macros "which run arbitrary Scheme".

## Sources

- **David Herman, *A Theory of Typed Hygienic Macros*, PhD dissertation,
  Northeastern, 2010**; and Herman and Wand, *A Theory of Hygienic Macros*,
  ESOP 2008, its first form. The basis of this note.
- **Alan Bawden, *First-class Macros Have Types*, POPL 2000.** A macro's
  type names its expander, and its value is the environment the expansion
  refers to: macros as members of modules (later, below).
- Culpepper and Felleisen, *Taming macros* (GPCE 2004), shape types:
  Herman's starting point, the shape alone. Ganz, Sabry and Taha, MacroML
  (ICFP 2001): typed macros as staging, arguments opaque. Rust's
  `macro_rules!` fragment specifiers (`$e:expr`, `$i:ident`): Culpepper's
  shapes, roughly, without binding structure, in daily use.

## Herman's system, as far as it matters here

The problem: hygiene is meant to preserve α-equivalence, but in Scheme
what binds what is known only after expansion, so α-equivalence of a
program with macros is defined by the expansion it is meant to constrain.
Herman breaks the circle by making a macro's binding structure part of its
interface, a type, checked against its definition and at each use.

**Types** (dissertation, Figure 3.1):

```
τ ::= expr | σ → expr                          form types
σ ::= τ | bvar | data | () | (σ . σ) | σ↓β | σ↑β | μA.σ | A | ∪{σᵢ}
β ::= ρ | γ        γ ::= ε | ρ :: γ | ℓ@γ        ρ ::= {ℓ : δ}
δ ::= NONE | VAR | RIB | ENV
```

- `expr`: any expression, **opaque**: the macro may place it, not inspect
  it, take it apart or rearrange it.
- `bvar`: a binding occurrence. `data`: a literal, for `quote`.
- `σ↓β` (import): a node in the scope of the bindings `β`. `σ↑β`
  (export): a node that offers bindings `β` to whatever imports it.
  Imports are inherited attributes and exports synthesized ones, an
  attribute grammar made modular (§2.4).
- Bindings come in four sizes: none, a variable, a rib (bound at one
  level), a ribcage (ribs in order, innermost first). `ℓ` is a tree address
  (`A`, `D`: car, cdr, read right to left as `cadr` is), relative to the
  innermost `μ`, `∪` or macro type around it.
- `μ` and `∪` give grammars; recursive types must be contractive, and a
  union's members must not overlap in shape.
- Subtyping is coinductive over the recursive types (Gapeyev, Levin and
  Pierce), imports normalized by pushing them inward.

**Examples** (dissertation, chapter 7):

```
formals    = μA.∪{()↑{}, (bvar . A)↑{A : VAR, D : RIB}}
lambda    : (formals expr↓{A : RIB} :: ε) → expr
let*-cl    = μA.∪{()↑ε, ((bvar expr) . A↓{AA : VAR} :: ε)↑ D@{AA : VAR} :: ε}
let*      : (let*-cl expr↓ A@ε) → expr
let       : ∪{named-let, std-let} → expr          (dispatch by shape)
```

**What it proves:** parsing before expansion, directed by the types;
α-equivalence of programs with macros, independent of expansion;
expansion type-sound and confluent; hence hygiene: α-equivalent programs
expand to α-equivalent programs.

**Two rules a programmer meets:**
- *Scope*: a template may place a body only where its signature's binders
  are bound. `(bad a e) ⇒ e`, declared `(bvar expr↓{A : VAR})`, is
  refused.
- *The shadow restriction* (the aliasing problem): `(K a b) ⇒ (lambda (a)
  (lambda (b) a))` changes its binding structure at `(K x x)`; a binder
  pattern variable may be referred to only where no other pattern binder
  could shadow it. `K` is refused; `K′`, through a temporary, is not.

**What it leaves open** (§7.3, §8.2): syntactic literals (`else`, `=>`);
definitions (only `expr` is a form type; `defn` is future work); macros
that define macros; ellipsis patterns and `syntax-parse`; procedural
macros ("would likely require integrating the type system with a
conventional type language, probably using constructs from typed
multi-stage programming"); a typed base language in which well-typed
input expands to well-typed output; polymorphic macro types; and linear
types, "since duplicating arguments is the source of many bugs such as
the duplication of run-time effects".

## The adaptation

### A kind of its own, `syntax`

Herman's syntax types become descriptions of a new kind, `syntax`, beside
`type`, `region`, `place`, `effect`, `size` and the rest (`ast::Kind`).
Not `shape`: FX-26 already says *shape* for what a union's members are
told apart by at run time (`Checker::shape`), and for
`docs/research/shapes.md`.

What FX-26 has that this reuses:
- **Recursive descriptions** (`dletrec`, `Ty::Link`), contractiveness
  (an abbreviation that is only a name is refused already), and the
  coinductive subtyping of `docs/research/recursive-subtyping.md`, with
  `ty_digest`'s minimal graphs to compare and key them.
- **Unions of disjoint members**: FX-26's `union` requires members of
  disjoint run-time shapes; Herman's requires members of disjoint
  syntactic shapes. The same discipline, over another universe.
- **Named, parameterized descriptions** (`define-type`, description
  functions of arrow kind, `docs/research/higher-kinds.md`): a syntax
  type like `formals` or `(clauses-of σ)` is an abbreviation of kind
  `syntax`, or a function to one.

### Labels, not tree addresses

Herman addresses binders by tree address because a canonical form needs
no α-equivalence on types. FX-26's products are canonical the same way,
with labels: a field's label is part of the type and never renamed. So a
signature names its parts, and scopes refer to the names. A sketch, to be
settled by the prototype:

```scheme
;; (for (x l) body): x bound in body alone.
(define-syntax for
  (syntax ((x bvar) (l expr)) (body (expr (in x))))
  ((for (x l) body) (for-each (lambda (x) body) l)))

;; A rib: the formals' binders, at one level.
(define-syntax-type formals
  (alt ()
       ((x bvar) . (xs formals)))
  (exports (rib x xs)))

;; let*'s clauses: each clause's expression in the scope of those before;
;; the whole exports a ribcage, innermost last.
(define-syntax-type let*-clauses
  (alt ()
       (((x bvar) (e expr)) . (cs (let*-clauses (in x)))))
  (exports (cage x cs)))
```

In a pattern, `(name σ)` gives a part's name and syntax type; `(in a …)`
is Herman's import of the bindings `a …` offer, outermost first;
`(exports …)` is an export, `rib` one level, `cage` levels in order. A
signature's names are the macro's pattern variables, so one form says
both the grammar and the binding structure, and a single-clause macro
needs no separate type. More than one clause is a union, its members
disjoint (`let` and named `let`).

### Where it runs: parsing knows what is bound

Herman's front end parses a use of a macro by the macro's type, before
expanding it (§7.1.1). For FX-26 that means:
- **The parser gets an environment.** Today it dispatches by name; it
  would also know which names are macros, and which local binders shadow
  them. It can, because every binder it meets is either a kernel form's
  (whose binding structure it knows) or a macro use's (whose signature
  says). Kernel form names stay reserved; a macro's name may be shadowed.
- **A use is parsed by its signature**: its binders found, and what is in
  their scope. The REPL can then resolve names, show scopes and say what
  goes next inside a use without running anything: what the speculation
  of TODO.md needs.
- **Expansion is transcription** of the matched clause's template, up to
  α-equivalence: the template's binders made fresh (Herman's hygienic
  convention); where a use's own binder would capture a free reference of
  the template, the use's binder renamed instead (the transparent
  convention), which α-equivalence allows. Fresh names are of the hidden
  `%` kind, so nothing a program writes can reach them.
- **Then the expansion is parsed and checked** as code is now.

**The prototype in the Rust front end alone.** `check_only` gives the
checker written in FX-26 a definition as *text*. So the prototype expands
in `parse.rs`, prints the expansion, and both checkers check what was
printed, agreeing as they do today; nothing of the FX-26 parser changes. The
port to FX-26 (the expander in the front end written in FX-26, read by
both) comes once the design has settled.

### Using FX-26's types and effects

This is where FX-26 can go past Herman's untyped base language.

1. **Duplicated arguments, by effect** (Herman's linearity remark, with
   FX-26's effects in place of linear types). Each `expr` pattern
   variable's uses in the template are counted. One used twice must be
   declared `pure`, `(expr pure)`, or the definition is refused: "`e` is
   expanded twice, and may do something each time". One used never
   discards its argument: a warning, unless it is `pure`. The effect is
   checked at each use against the argument's own effect, after the use
   is checked.
2. **Form types indexed by type and effect**: `(expr T E)`, an expression
   of type at most `T` and effect at most `E`; `(expr)` any. With them the
   template can be checked **once, at its definition**, each pattern
   variable a hole of its declared type and effect (hole mode's
   machinery), its binders variables of their declared types; a use then
   checks only its arguments against the signature. That is the "typed
   base language in which well-typed input expands to well-typed output"
   Herman leaves open, and the end of type errors reported inside an
   expansion. `T` and `E` may be the macro's own `poly` binders:
   `(for (x bvar t) (l (expr (listof t r) e1)) (body (expr unit e2 (in x))))`.
3. **Binders of every sort**: `bvar` binds a value variable; FX-26 binds
   type variables (`poly`), regions, places, effects, sizes and
   conventions too, each in its own namespace. A binder's syntax type says
   its sort, `(bvar type)`, `(bvar region)`, and so does a scope.
4. **Procedural macros, later, by opacity.** A transformer written in
   FX-26 may inspect only the structure and the `data` of its input, never
   an `expr`, and may place `expr`s and binders only through templates
   checked against its signature, on every path. Choosing among templates
   is then typed code like any other; its effect must allow it to run while
   the program is checked (pure, or allocating in its own place, and only
   stateless module files). Whether hygiene survives that is the open
   question to work through, not a claim.
5. **Macros in module types** (Bawden), later: a module type's member
   whose type is a macro's, generative, its expander in the type and its
   free references selects from the module value. Abstract (the signature
   alone: uses checked, not expanded) where a maker's parameter has it;
   manifest (the expander too) where the maker is given a module.

## What FX-26's type system would need, early

The user asked to know these before rather than after. In the order they
would be met:

| # | What | Why | When |
| --- | --- | --- | --- |
| 1 | A kind `syntax`, its descriptions (`bvar`, `data`, `()`, pairs, `expr`, `alt`, recursion) and their subtyping | Herman's syntax types | prototype |
| 2 | Binding signatures: imports `(in …)` and exports `(exports …)`, ribs and ribcages | what is new in Herman, and new to FX-26: nothing it has is an attribute | prototype |
| 3 | A parser with an environment of macros, and of the binders that shadow them | parsing by signature; macro names that may be shadowed | prototype |
| 4 | **Places unique to an expansion.** The checker written in FX-26 keeps its facts by place (`docs/fx26.md` on `with`: "one `with`'s fact read as another's"); a template, or an argument used twice, gives two expressions one place. A `Span` with an expansion's mark, and a source map from the printed expansion back to the source for errors | correctness of the checkers' facts; errors where the programmer wrote | prototype |
| 5 | An unshadowable reference to a binding where a macro is defined, as `#%fx` is to the standard ones; what a later redefinition of it means (`docs/fx26.md`, "Redefinition") | free references of templates to the program's own globals | prototype, if templates name globals; else soon after |
| 6 | The macro environment in the checker's marks and rollback (`try_top`, `rollback`) | the REPL tries forms and leaves nothing behind | prototype |
| 7 | Form types indexed by type and effect, `(expr T E)`, and templates checked with typed holes | well-typed in, well-typed out; duplication by effect | second step |
| 8 | Binders of each sort, and scopes in each namespace | macros that bind type variables, regions, places | second step |
| 9 | A form type for definitions, `defn`, exporting to the top level or a module | `define-command`; most macros a program wants | third step |
| 10 | Macro types as module members, generative, in `.fasl`s and `ty_digest` | Bawden's macros in modules | later |
| 11 | Transformers written in FX-26: opaque input, typed templates, the effect rule for running at check time | procedural macros | later |

Item 4 matters most: it is not about macros' types at all, but every
macro breaks it.

## The prototype

**Scope.** `define-syntax` at the top level, `syntax-rules`-style clauses
(no ellipsis yet: recursion through syntax types, as Herman's chapter 7
writes `let*` and `cond`), expression macros only, `bvar` binders of value
variables, `expr` arguments untyped, the duplication rule by declared
`pure`. In the Rust front end; the checker written in FX-26 checks the
printed expansion.

**Cases** (`crates/fixpt-fx26/tests/macros.rs`, programs beside it):
- `for`, `swap!` (Herman's hygiene example: the template's `tmp` against
  a user's `tmp`), `my-or` (its temporary against the user's), a template
  naming `#%fx` bindings;
- `let*` and named `let` written as macros, compared with the built-in
  ones' results;
- refused at definition: `bad` (a body outside its binder's scope), `K`
  (the shadow restriction), a duplicated argument not declared `pure`;
- refused at use: an argument not of its syntax type (a binder where an
  expression is wanted), with the error at the use;
- the REPL: a use's binders and scopes known before it expands, and a
  tried `define-syntax` leaving nothing behind.

**Then**: errors in expansions mapped back (item 4's source map); typed
form types and templates checked once (items 7 and 8); `defn` (item 9),
with `define-command` as its test; the derived forms of both parsers
rewritten as macros, once, which is the first payoff in this codebase
itself.

## Questions for the user

- The concrete syntax of signatures: labels as sketched, or Herman's
  addresses, or patterns and types apart as Herman writes them?
- Item 5: what a template's reference to a global means after the global
  is redefined: the global as it was where the macro was defined, or as it
  is where the macro is used (FX-26's redefinition re-runs definitions)?
- Ellipsis (`...`) in the prototype, or recursion through syntax types
  first, as Herman does?
