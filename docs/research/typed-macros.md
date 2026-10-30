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

### Syntax types are FX-26 types (no kind of their own)

A first draft of this note gave Herman's syntax types a kind of their own,
`syntax`. The user asked why (2026-10-30), and it does not need one. A
kind says where a description may stand; what Herman's grammar describes,
less its imports and exports, is the data a macro is given, and FX-26
types data already:

| Herman | FX-26 |
| --- | --- |
| `()`, `(σ . σ)` | `nil`, `(pairof σ σ acyclic)`: a use's syntax is immutable and finite |
| `μA.σ` | a recursive type (`dletrec`; a `define-type` naming itself) |
| `∪{σᵢ}` | `(union σ …)` |
| `data` | `datum`, what `quote` builds |
| `bvar` | an identifier in a binding position: a generative type of its own, not `symbol`, so that a binder is not a quoted symbol |
| `expr` | an expression, opaque: a generative type that programs are given no operation on, neither to look inside nor to make one but by a template |
| (none) | `label`: an identifier in the source, the keyword it names once parsed (below, "Keywords") |

So a syntax type is a type, of kind `data`, of the syntax objects a
macro's use is parsed into, and what FX-26 has for types is had for
these: recursion and its coinductive subtyping
(`docs/research/recursive-subtyping.md`), contractiveness (an abbreviation
that is only a name is refused already), `define-type` abbreviations,
`poly` and description functions (`(clauses-of σ)`, a macro polymorphic in
a syntax type, which Herman leaves to future work), and `ty_digest` to
compare and key them. Not `shape` for any of it: FX-26 says *shape* for
what a union's members are told apart by at run time
(`Checker::shape`), and for `docs/research/shapes.md`.

**Two disjointness rules, not one.** FX-26's `union` wants members of
disjoint run-time shapes; of the parsed syntax objects that holds by
construction, `expr` and `bvar` being generative. But a use is parsed
*before* its parts are known: in the source an `expr` may be a symbol or
a list, so `(union (pairof expr nil acyclic) (pairof bvar … ))` overlaps
there though its parsed objects do not. The macro checker keeps Herman's
own rule besides (dissertation §5.2.3, "Shapes", Figure 5.9): a syntax
type's source shape, with `expr` overlapping everything, and a union's
members of disjoint source shapes.

### Binding signatures: annotations the value checker erases

What Herman adds, and nothing in FX-26 has, is binding structure: which
binders scope over which parts. It becomes three annotations on these
types, read by the macro checker and erased by everything else (to the
checker of values, `(in σ x …)` is `σ`):
- `(named x σ)`: the part's name, `x`, by which scopes refer to it.
  Herman addresses parts by tree address so that types need no
  α-equivalence; a name in a type is never renamed either, as a product's
  label is not.
- `(in σ x …)`: `σ` in the scope of the bindings that the parts named
  `x …` offer, outermost first (Herman's import `σ↓β`).
- `(exports σ (rib x …))`, `(exports σ (cage x …))`: what `σ` offers to
  whatever brings it into scope: one level, or levels in order (Herman's
  export `σ↑β`, a rib or a ribcage).

The macro checker compares types with their annotations, so two syntax
types alike but for their binding structure are different signatures;
the value checker, having erased them, sees one type. The annotations
cross unions and recursion as Herman's do, pushed inward to the members
(his import normalization, §3.6.2); where they meet FX-26's own
normalization of unions is for the prototype to settle.

A sketch; the surface syntax is for the prototype to settle:

```scheme
;; formals: a rib of binders.
(define-type formals
  (union nil
         (exports (pairof (named x bvar) (named xs formals) acyclic) (rib x xs))))

;; let*'s clauses: each clause's expression in the scope of those before;
;; the whole a ribcage, innermost last.
(define-type let*-clauses
  (union nil
         (exports (pairof (pairof (named x bvar) (pairof (named e expr) nil acyclic) acyclic)
                          (named cs (in let*-clauses x))
                          acyclic)
                  (cage x cs))))
```

and, for a single-clause macro, a pattern annotated in place, which says
the same as the type it elaborates to:

```scheme
;; (for (x l) body): x bound in body alone.
(define-syntax for
  (syntax ((x bvar) (l expr)) (body (in expr x)))
  ((for (x l) body) (for-each (lambda (x) body) l)))
```

The pattern's names are the macro's pattern variables, so one form says
the grammar, the binding structure and what the template may refer to.
More than one clause is a union (`let` and named `let`).

### Keywords: names that are not variables

**Why** (the user, 2026-10-30): reading code that uses sums heavily, it
took too long to see that the occurrences of `sorted` were not a variable
but a variant's name. In FX-26 a tag is a bare symbol, `(sum sorted v)`,
`(extract q reply)`, `(sumof (sorted T) …)`, a `tagcase` arm, written
exactly as a variable reference is, and only its position says it is not
one. So are `tagcase`'s `else`, `module`'s `extend`, the `:` of a
parameter `(x : T)`, and this note's own `in`, `exports`, `rib` and
`cage`. The parser copes because it never asks what a name is bound to,
which is also why form names are reserved.

**Keywords**, `#:sorted` (Racket's spelling, the user's choice): a reader
token and a `datum` atom of their own type, `keyword`, interned, and
self-quoting as a number is. Never bound, never looked up, never renamed
by hygiene, never captured or shadowed. Then:
- **Tags and labels are keywords**: `(sum #:sorted v)`, `(extract q
  #:reply)`, `(product (#:n n) (#:reply c))`, `(sumof (#:sorted T) …)`,
  `tagcase` arms by keyword. Whether a flat form, `(product #:n n
  #:reply c)`, comes with them is a separate decision.
- **Herman's open problem of syntactic literals** (`else`, `=>`;
  dissertation §7.3.1) goes away rather than being solved: a literal in a
  pattern is a keyword, `#:else`, which nothing can bind, so it has no
  binding structure to get wrong.
- **In templates**, a tag is just placed: no binding analysis, no
  renaming.
- **`symbol->keyword` and `keyword->symbol`**: ordinary data operations,
  `(subr pure (symbol) keyword)` and back, as Clojure has (`(keyword
  'foo)`, `(symbol :foo)`); Racket, as far as I recall, goes through
  strings. They do not make tags dynamic: `extract`, `sum` and `tagcase`
  need their tag where they are checked, since the type `(sumof (#:ok T)
  …)` is about that tag, and a keyword computed at run time is a
  `keyword`, not `#:ok`. Only a singleton keyword type, `(keyword ok)`,
  as `false` and `(nat 3)` are singletons, would make a tag a value a
  procedure could be given: a later, larger step (row polymorphism's
  territory), which keywords leave open.

**A syntax type `label`.** Sugar that writes a field as a bare name, as
OCaml's `r.foo`, SML's `#foo r`, Racket's `point-x` and Clojure's
`(:foo m)` do, is a macro whose argument is a `label`: an identifier in
the source, which parsing makes the keyword, and which the template only
places:

```scheme
(define-syntax ext
  (syntax ((v expr) (f label)))
  ((ext v f) (extract v f)))        ; (ext q reply) is (extract q #:reply)
```

The signature says `f` is neither a binder nor a reference, so hygiene
has nothing to do, the REPL does not resolve `reply`, and "no field
`reply`" is said at the use. The rule "a bare name here is not a
variable" is then declared in a macro's type, not implicit in a parser's
dispatch. But the core forms keep their keywords, and such sugar stays a
library's: a bare-name sugar for every common form would hide the tags
again, which is what keywords are for.

**The transition.** Every product, sum and `tagcase` in this repository,
in Kayak, in Heist and in the user's editor writes its tags bare. Both
spellings are accepted for a while, a lint offering the rewrite; a sum's
tag at run time a keyword, so that a printed sum shows what the source
wrote (today it is a symbol). Keywords come before the macro prototype's
literals need them, and are worth having without macros at all.

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
2. **Expressions indexed by type and effect**: `(expr T E)`, an
   expression of type at most `T` and effect at most `E`; `expr` any.
   Since `expr` is a generative type, this is a generative applied to
   descriptions, as `Ty::Named` already is, covariant in both. With them the
   template can be checked **once, at its definition**, each pattern
   variable a hole of its declared type and effect (hole mode's
   machinery), its binders variables of their declared types; a use then
   checks only its arguments against the signature. That is the "typed
   base language in which well-typed input expands to well-typed output"
   Herman leaves open, and the end of type errors reported inside an
   expansion. `T` and `E` may be the macro's own `poly` binders:
   `(for ((x (bvar t)) (l (expr (listof t r) e1))) (body (in (expr unit e2) x)))`,
   where `(bvar t)` is a binder whose variable has type `t`.
3. **Binders of every sort**: `bvar` binds a value variable; FX-26 binds
   type variables (`poly`), regions, places, effects, sizes and
   conventions too, each in its own namespace. A generative type for each
   sort (`tvar`, `rvar`, `pvar`, `evar`, `svar`, names to settle), and a
   scope brings each binder into its own namespace.
4. **Procedural macros, later, by opacity.** Since syntax types are
   types, a transformer is an FX-26 procedure from its argument's syntax
   type to `expr`, checked by the checker as any procedure is. It may take
   apart pairs, lists and `datum`s of its input, never an `expr` (no
   operation on one is given); and it makes an `expr` only by a template,
   checked against its signature with the template's binders and scopes,
   on every path. Its effect must allow it to run while the program is
   checked (pure, or allocating in its own place, and only stateless module
   files). Whether hygiene survives that is the open question to work
   through, not a claim.
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
| K | Keywords, `#:tag`: a reader token, a `datum` atom of type `keyword`, interned and self-quoting; tags, labels and syntactic literals written with them; `symbol->keyword`, `keyword->symbol`; bare-symbol tags accepted through a transition | names that are not variables, seen as such; Herman's literals; tags in templates | before the prototype's literals; worth it alone |
| 1 | Syntax objects as data: generative types `expr` (opaque) and `bvar`; a syntax type is a `data` type over them, with `nil`, pairs, unions and recursion as FX-26 has them. Besides, Herman's check of a union's members for disjoint *source* shapes (`expr` overlapping everything) | Herman's syntax types, with no kind of their own | prototype |
| 2 | Binding signatures as annotations the value checker erases: `(named x σ)`, `(in σ x …)`, `(exports σ (rib …))` and `(cage …)`; compared with them by the macro checker, pushed through unions and recursion | what is new in Herman, and new to FX-26: nothing it has is an attribute | prototype |
| 3 | A parser with an environment of macros, and of the binders that shadow them | parsing by signature; macro names that may be shadowed | prototype |
| 4 | **Places unique to an expansion.** The checker written in FX-26 keeps its facts by place (`docs/fx26.md` on `with`: "one `with`'s fact read as another's"); a template, or an argument used twice, gives two expressions one place. A `Span` with an expansion's mark, and a source map from the printed expansion back to the source for errors | correctness of the checkers' facts; errors where the programmer wrote | prototype |
| 5 | An unshadowable reference to a binding where a macro is defined, as `#%fx` is to the standard ones; what a later redefinition of it means (`docs/fx26.md`, "Redefinition") | free references of templates to the program's own globals | prototype, if templates name globals; else soon after |
| 6 | The macro environment in the checker's marks and rollback (`try_top`, `rollback`) | the REPL tries forms and leaves nothing behind | prototype |
| 7 | `expr` applied to a type and an effect, `(expr T E)`, `(bvar T)`, and templates checked with typed holes | well-typed in, well-typed out; duplication by effect | second step |
| 8 | A binder type for each sort, and scopes in each namespace | macros that bind type variables, regions, places | second step |
| 9 | A form type for definitions, `defn`, exporting to the top level or a module | `define-command`; most macros a program wants | third step |
| 10 | Macro types as module members, generative, in `.fasl`s and `ty_digest` | Bawden's macros in modules | later |
| 11 | Transformers written in FX-26, ordinary procedures over syntax types: `expr` made only by templates, the effect rule for running at check time | procedural macros | later |

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

- The concrete syntax of signatures: names in the types as sketched, or
  Herman's addresses, or patterns and types apart as Herman writes them?
- Item 5: what a template's reference to a global means after the global
  is redefined: the global as it was where the macro was defined, or as it
  is where the macro is used (FX-26's redefinition re-runs definitions)?
- Ellipsis (`...`) in the prototype, or recursion through syntax types
  first, as Herman does?
- Keywords (decided: `#:tag`): a sum's tag at run time a keyword, as
  proposed, or still a symbol with keywords only in the source? And flat
  products, `(product #:n n #:reply c)`, or keep the pairs?
