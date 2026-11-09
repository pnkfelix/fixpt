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
- **Alan Bawden and Jonathan Rees, *Syntactic Closures*, LFP 1988**; Chris
  Hanson, *A Syntactic Closures Macro Facility*, Lisp Pointers IV-4, 1991
  (aliases, `identifier=?`); William Clinger and Jonathan Rees, *Macros
  That Work*, POPL 1991; William Clinger, *Hygienic Macros Through
  Explicit Renaming*, Lisp Pointers IV-4, 1991. The meaning of an
  expansion, and the procedural macros to come ("Syntactic closures: what
  an expansion means", below).
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

**A hypothetical extension: a keyword as a sum's constructor** (the
user's, 2026-10-30; decided to build, 2026-11-08, as the route the
`define-datatype` spike takes: `datatype-macro.md`, §5 (B)). `(#:tag e …)` in operator position
constructs a sum, as Haskell's capitalized constructors are told from
variables by how they are written; a `tagcase` arm then looks like the
construction it takes apart, `(tagcase r (#:sorted (xs) …) …)`. Keyword
*arguments*, which the user does not want now, would be in argument
positions, `(f #:x 1)`, so this would not stand in their way.
- **Today `define-datatype` makes tags variables**: each tag gets a
  constructor, a global procedure named by it (`expand_datatype`,
  `top.rs`), so `(sorted x y)` calls a procedure `sorted`. Keyword
  constructors would make those procedures unneeded.
- **What the arguments become, by arity**: none, `unit` (`(#:eof)`);
  one, the value itself, as `(sum #:ok v)` carries it and the standard
  sums do (`(sumof (done unit) (failed io-error))`); two or more, a
  product labelled from 1, as a datatype's variant is. Datatypes would
  then carry a one-member variant's member itself, not a product of one
  field (a bloblet less a value; `tagcase`'s `(tag (x) body)` binding the
  whole payload); code that `extract`s field `1` of one would change.
- **`#:eof` is a keyword, `(#:eof)` a sum.** A bare keyword where a sum
  is expected is a type error, which can say "did you mean `(#:eof)`?",
  rather than the expected type making a sum of it.
- **It wants flat products**: in `(product (#:n n) (#:reply c))` each
  field reads as a sum's construction, the reading by position again; so
  `(product #:n n #:reply c)`, and the types flat to match.
- **Typing as `sum`'s**: `(#:tag e)` is checked as `(sum #:tag e)` is, a
  sum of one tag that fits any wider sum with it. A core form, told by
  how it is written; `sum` stays the explicit form, and what macros
  expand to.
- **The snag** (the user's): with keywords first-class values,
  `(let ((k #:variant)) (k fooie))` is not `(#:variant fooie)`. It is a
  type error, not another answer (`k` is a `keyword`, which is not
  applied), and its message can name the right form; it is where every
  special form is, though `if` is never a value.
- **Decided (the user, 2026-11-08): no constructors as values.** The
  snag stays a type error: a keyword constructs only at a list's head,
  and a procedure that constructs is written as one, `(lambda (x) (#:ok
  x))`; the singleton types below are not to be built
  (`datatype-macro.md`, "Keyword constructors: decided").
- **A further step that removes the snag** (not taken): singleton keyword types. The
  literal `#:variant` of type `(keyword variant)`, below `keyword`, as
  `false` is below `bool` and `(nat 3)` below `nat`; a keyword of a
  singleton type applied constructs the sum, checked as the form is. Then
  `k` above keeps the singleton type and the two spellings agree, and
  constructors are first-class, `(map #:ok xs)`, which is what dropping
  the datatypes' constructor procedures costs. A keyword of plain type
  `keyword` (from `symbol->keyword`) is still not applied: its tag is not
  known. A compatible extension: what the first step accepts, the second
  means the same by, and it only accepts more. To settle then: that a
  `let` with no expected type keeps a literal's singleton type rather
  than widening it, as FX-26 decides `#f`'s by what is expected.

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
| 9 | A form type for definitions, `defn`, exporting to the top level or a module | `define-command`; most macros a program wants | third step; built at the top level, 2026-11-07 |
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
- a truthy `and` (`TODO.md` §197, the user's, 2026-11-05: by macro, not
  built in): `(and e1 e2 …)` giving `#f` or the last operand's value,
  `(let ((t e1)) (if (false? t) #f (and e2 …)))`, so that `(and (to-enf
  op) (to-enf arg) …)` chains `(oneof false enf)` results. Its test must
  be `#f` itself, not `bool?`, or a `#t` would count as failure; whether
  the checker narrows on `(eq? t #f)` or `(not t)`, so that `t` is the
  rest of its type after it, is to find out first. Hygiene: `t` against a
  user's `t` in `e2`;
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

## The prototype, as built (2026-11-06)

`crates/fixpt-fx26/src/macros.rs`, in the front end written in Rust:
`Checker::expand_forms` defines each `define-syntax` as it is read and
expands every use in the forms after it, before either checker sees them;
both check what it expands to, printed, as they agree on any form. Tests:
`tests/macros.rs`, the programs in `tests/programs/macros`.

**Signatures, in Herman's notation** (the user's answer): a signature is
the syntax type of a use's operands, all but the macro's name:

```text
σ ::= expr | bvar | id | data | type | label | ()
    | (σ . σ) | (σ …)                    a pair; a list, of pairs
    | (import σ β) | (export σ β)        σ↓β and σ↑β
    | (mu v σ) | v | (union σ …)
    | (literal name)                     a name written as it is (`else`)
    | (many σ)                           placed any number of times
β ::= (rho (ℓ δ) …)                      a rib, {ℓ : δ, …}
    | (cage ρ-or-(at ℓ) …)               a ribcage, innermost first; ℓ@γ
δ ::= none | var | rib | env
```

An address is a word of `A` and `D`, read right to left as `cadr` is, from
the innermost `mu`, `union` member or signature around it. `id` (a
variable referred to: a cell `swap!` takes), `type` (a description) and
`label` (a tag or a field's name) are FX-26's. Each signature in the tests
has a comment saying it in the names of "Binding signatures" above, the
readable form to move to:

```scheme
(define-syntax let1
  ;; As named: ((x bvar) (e expr)) (body (in expr x))
  ((bvar expr) (import expr (rho (AA var))))
  (syntax-rules ()
    ((_ (x e) body) (let ((x e)) body))))
```

(Written with `syntax-rules` since 2026-11-08: "Inferred signatures",
below.)

**Checked where defined**, Herman's rules:
- the signature: `mu` contractive; a `union`'s members told apart by
  their shapes in the source (`expr` anything but a form's name);
- each clause's pattern aligned with the signature: each pattern
  variable's syntax type, and the environment the signature declares
  around it (its imports evaluated over the pattern);
- the template, aligned with the signatures of the kernel's forms
  (`KERNEL` in `macros.rs`, written in the same notation: `lambda`,
  `let`, `let*` as Herman's let*-cl, `letrec`, `if`, `begin`, `and`,
  `or`, `quote`, `the`, `sum`, `extract`, `product`, `tagcase`, `cond`,
  applications) and of the macros, the macro itself among them. A kernel
  form not there is refused in a template;
- each pattern variable placed where the form takes its syntax type
  (subtyping, coinductive, binding structure alike), and in the scope of
  the bindings its signature declares, no more and no fewer, the
  template's own binders aside (`bad`, and its converse);
- a pattern binder referred to only where no other pattern binder may
  shadow it (the shadow restriction, `K`);
- a pattern variable with an expression in it placed at most once, affine,
  unless its part of the signature is `(many σ)` (2026-11-06, the user's
  choice of a substructural rule with an explicit opt-out over a lint);
  placed in a part another macro's signature says `many`, it counts as
  placed more than once, so a chain of macros that multiplies an argument
  says so in every signature on the way (`many-chain.fx`,
  `many-chain-refused.fx`). A copy is an expression of its own, its own
  facts (`many-copies.fx`): identity is by position, not place
  (`loads-and-places.md`, "Decided: identity by position");
- a template's tag or label a keyword (the user's answer).

**Expanded where used**: the use parsed by the signature (a binder where
one goes, a macro's name never bound), the first clause whose pattern
matches transcribed. The template's binders, and its references to them,
made fresh (`%tmp:3`); its other names the standard bindings, `(with #%fx
name)`, which nothing shadows; the kernel's form names as they are, as
no program binds one. So the use's names never capture the template's,
nor the template's the use's: `swap!` against a use's own `tmp`, `my-or`
against a use's `t`. A use of a macro inside an expansion is expanded in
turn.

**Done since:**
- A template naming the program's own globals (item 5), 2026-11-07: every
  name free in a template expands to `(with #%toplevel name)`, the top
  level's as it is where the macro is used, standard names too (the
  user's choice: `+` in a template is the top level's `+`, as a top-level
  procedure's is); `(with #%fx name)` written in a template means the
  standard one whatever the top level does. Each type a template writes
  expands to `(select #%toplevel T)`. Both front ends; `docs/fx26.md`,
  "`#%toplevel`".

**Not yet:**
- A macro's name may not be bound or defined at all, as a form's may not
  (Herman lets a local binder shadow a macro); a use binding one is
  refused, and a definition of one, however made (an `import`'s, a
  top-level `include`'s), and a macro of a global's name.
- A `with` binds what its module gives, which the expander cannot see:
  a macro used in its body, by a name the program wrote, of which the
  module gives a value is refused when the `with` is checked
  (`` `clamp` is a macro here, and `m` gives a value of that name ``),
  rather than the program seeming to call the value (the user's,
  2026-11-07). A template's use of a macro is the macro, by hygiene, and
  not refused. The way out, when one is wanted: `rename` and `prefix`
  for `import-with-syntax` (not built). Rust expander and checker only,
  as are macros: the FX-26 front end sees expansions.
- Errors inside an expansion are said where the template wrote the part,
  then at each use that made it, innermost first (2026-11-06,
  `loads-and-places.md`, "Done: identity by position"); the printed
  expansion's source map, for the checker written in FX-26's places,
  waits for the expander to be that front end's.
- The REPL: a macro defined in what is typed is defined for that alone
  (`Checker::macros_kept`); a use's binders and scopes are not yet shown
  before it expands.
- The front end written in FX-26 expands its own since 2026-11-07
  (`macros.fx`, `macros-align.fx`, `macros-types.fx`; the kernel's
  signatures and the keywords one file both read, `macros-kernel.fx`):
  `define-syntax` checked and defined, uses expanded, free names through
  `#%toplevel`, in `parse-tops`, each form before anything else sees it.
  The macros a form is read with are what the session's state it is read
  in says (a table from each state to the macros after it), the
  `define-syntax`es in the readings that make the state. Both expanders
  agree on every program in `tests/programs/macros` and those of
  `import-with-syntax` (`tests/macros_both.rs`, ported the same day: the
  file's forms the driver read, its load definitions in the state too, the
  standard names the driver gives, `standard-names!`), refusals too: a
  definition of a macro's name and a macro of a global's, in the parser
  (`guard-defs`, `global-macro`), as forms the checker refuses where
  the Rust one refuses them; a `with`'s body's macro by a name its module
  gives, in the checker (`k-with-used-at`), told what the expander found
  of the last parse (`check-macro-uses!`). An error in an expansion is
  said where the template wrote it, then at each use that made it, as the
  Rust front end says it (the user's design, 2026-11-07): each part a
  template makes is at a key of its own, a place past every text's, so
  that two expansions' copies of one part are apart; a table beside the
  trees says, by key, where the template wrote the part and which
  expansion made it (`source-of`), and the driver says an error at a key
  there and at each use (`syn.rs`'s `fx26_span`). Places stay places:
  nothing is packed into them.
- Ellipsis (the user's answer: later, as sugar for recursion), `defn`,
  binders of descriptions, procedural macros (items 7 to 11).

## FX-26's own extensions as binding information (2026-11-06)

The user asked (2026-11-06) whether FX-26's extensions to its type system
lend themselves to encoding binding structure, and what in the language
needs a macro system's extra care. Nothing here is decided.

### Effects as scopes, regions as binders

The strongest fit. Taha and Nielsen's environment classifiers (POPL 2003),
and Kiselyov, Kameyama and Sudo's refined ones (APLAS 2016) above all,
type generated code by the set of binders it may refer to, a classifier
per binder: a region discipline. In FX-26's terms:
- A template's `(lambda (x) body)` is a `letregion`: it brings a scope
  variable `ρx` in for `body`. A reference to `x` is an effect on `ρx`.
  Leaving the lambda masks `ρx`, as a closed region's effects are masked.
- Item 7's `(expr T E)` gains a third index, a set of scopes, `(expr T E
  S)`; Herman's `(in expr x)` is `S` and `ρx`.
- **Hygiene as a type.** An `expr` argument comes with the use's scope, a
  variable `s` the macro is polymorphic in, as it may be in an effect. The
  template may place it under its own binders, and cannot name them.
- **Escape is a check FX-26 has.** A use's expression that would refer to
  a template's binder is refused as a value that mentions a closed region
  is, or as `m..t` leaving `m`'s scope.
- **Subeffecting is weakening.** Code good in fewer scopes is good in more.

What effects do not give: Herman's *exports*, what a part offers its
siblings (`let*`'s clauses, a definition to its module). Effects flow up,
saying what is used, not what is offered. Modules give those (below).

### `anyof`, `oneof` and `allof`

- Herman's union, its members of disjoint *source* shapes, is a `oneof`
  read on source shapes, not an `anyof`.
- A macro of several clauses (`let` and named `let`) is better an `allof`
  of a signature per clause than Herman's `∪{…} → expr`: with typed
  results (item 7) each clause may give a type of its own, as `swap`'s
  members do.
- At a use, the syntax is concrete: expansion always knows which member
  applies, and nothing is split as rule 5 splits a call. The logical types
  earn their keep where a template is checked once, at its definition,
  against every clause.

### First-class modules as environments

| Herman | FX-26 |
| --- | --- |
| a rib, bindings at one level | a module type, `(moduleof (val x t) …)` |
| an import, `σ` in the scope of `x` | `(with m σ)`, which opens values, types and effects, innermost first, falling back outward |
| a ribcage, ribs in order | nested `with`s, or `extend` (`(with e0 e1)`) |
| a rib's binders distinct | `include`'s `` `x` is defined twice in this module `` |
| a definition offered outward (`defn`, item 9) | a macro that makes a module fragment its module `include`s |

Bawden's first-class macros are the same reading from the other side: a
macro's value is the environment its expansion refers to, a module (item
10). Clojure gets part of this: syntax-quote qualifies a template's free
symbols by namespace (`` `let `` is `clojure.core/let`), so a use cannot
capture a free reference; binders it leaves to the programmer (`x#`, a
gensym), which is why its macros are not hygienic. FX-26's qualification
is `(with #%fx name)`; item 5 is the same, of the module where the macro
is defined.

### Propositions, for procedural macros

What a test proves (`(bool (then P) (else Q))`) narrows run-time values;
for pattern macros, choosing a clause does that already. In a procedural
transformer (item 11), a shape test of a syntax object narrows it by
occurrence typing, its binding annotations with it: past the test, the car
is a binder whose scope is the cdr. And a test that two binders are one
(Racket's `bound-identifier=?`) proves in its `else` that they differ,
which is what Herman's shadow restriction is about: `K`, `(lambda (a)
(lambda (b) a))`, could be accepted on the branch where `a` and `b` are
known apart. Beyond Herman, and for item 11, not the prototype.

### What needs extra care

**Two namespaces, opened together.**
- A binder says its sort: a value, or a description of a kind (a type, an
  effect, a region, a size); item 8.
- Macros take descriptions too: a syntax type for a description, `(desc
  K)`, parsed as the description half of `parse.rs` parses one.
- **`with`.** What it opens depends on the module's *type*: each name is
  read as `(select m n)` falling back to what it is outside, settled where
  checked. Hygiene cannot wait for that. In a template's `(with user-m (f
  x))`, `user-m` must not capture the template's `f`: what an open binds
  is decided by the scopes of the module's expression as the use wrote
  it, as Racket binds a `require`'s imports by the context of what it
  names, never a name the template brought in.

**Taking values and types out of modules.**
- **A temporary seals.** `(let ((m counter)) …)` makes `m..t`, not
  `counter..t`. The duplication rule (above, "Using FX-26's types and
  effects", 1) asks a template to bind an argument used twice to a
  temporary; of a module, that gives it abstract types of its own, which
  the use's `counter..t` outside does not match. So a syntax type `path`:
  of no effect, compared by binding, so usable twice without a temporary,
  and what `select` takes.
- A template's fresh module binder is printed in types, `%g12..t`: errors
  need item 4's source map to say what the use wrote.

**Labels and keywords.**
- A label is never bound, so hygiene has nothing to do with it, but `n`
  and `#:n` are one label and bare ones are still read. A template writing
  `(product (x 1))` and binding an `x` of its own would have the label
  renamed by a renamer that does not know label positions. In templates,
  a label is a keyword or a `label` pattern variable; bare labels stay in
  ordinary code through the transition.
- **`define-datatype`.** A variant's name is a label, never renamed, and a
  global constructor, a binder, renamed fresh: a macro that makes a
  datatype gets a tag `circle` and a constructor `%g7`. Racket's
  `format-id` problem, worse with derived names (`make-point`). Keyword
  constructors (`(#:circle x)`, above) remove the binder half.
- Labels a procedural macro computes (`symbol->keyword`) are `keyword`s,
  their tags unknown: they need the singleton `(keyword n)`.
- A `tagcase` arm has a label beside binders, the payload's or since §191
  a positional list's; the macro checker knows its structure as it knows
  `lambda`'s.

**Regions in templates.** A template's `(letregion r …)` around a use's
expression must keep the expression from naming the fresh `r`: scopes as
regions give that, with an `expr` argument's effect polymorphic over
regions.

**Where to build.** Effects as scopes and modules as ribs: between them,
both of Herman's directions, imports and exports, on what FX-26 checks
already. **Decided (the user, 2026-11-06): not first.** The prototype
starts as close to Herman's foundations as it can: his binding
signatures (imports, exports, ribs and ribcages), his shadow restriction,
parsing directed by a macro's type. Scopes as regions, and modules as
ribs, are for after it, measured against it.

## Decided: macros come with a file, `import-with-syntax` (2026-11-07)

The user's design, the reasons in the conversation that led to it:

- **`with` imports no macros.** A module value's names are its type's,
  known only once it is checked; a macro must be known before anything
  is checked. So what brings macros is second-class, and names a file,
  the static thing FX-26 has: as Sheldon's system intends, macros are not
  values.
- **`(import-with-syntax lib)`**, a top-level form, `lib` a top-level name
  whose definition is literally `(load-module "path")` of a file without
  module parameters (the expander sees that in the syntax; anything else
  is refused). It brings all the file's names into the top level from
  where it is: its values, types and effects, as top-level `(include lib)`
  does, and its macros. `only` and `except` later (built 2026-11-07:
  `(import-with-syntax lib (only name …))`, macros and the rest alike).
- **Privacy by `hide`**: in the file, `(hide (define-syntax …))` keeps a
  macro to the file, as `hide` keeps a definition out of the module's type.
- **Hygiene across files**: an imported macro's template means what it
  meant in its file. A free name in it expands to `(with %shared:key
  name)`, the file's own (every load of a file is the one hidden global,
  `%shared:key`, which nothing shadows), a type to `(select %shared:key
  T)`; a use of another of the file's macros, hidden or not, is that
  macro. So an exported macro may name only what the file's module shows,
  refused where the file defines it otherwise.
- **When**: the macros come in where the form is, tied to the file `lib`
  named there; a later redefinition of `lib` changes none of them.
- **Not this**: a local binding shadowing a macro's name (Herman's), whose
  interaction with `with` is open (a `with` may bind a value of a macro's
  name, which the expander cannot see); designed after.
- **Built** (2026-11-07), in the Rust expander (`Checker::import_file_macros`,
  `Macros::define_file`), which both front ends' checkers then see the
  expansion of; what follows from "a template means what it meant where it
  was defined":
  - a file sees the standard environment alone, so a file's macro's free
    standard name is `(with #%fx name)`, not the importer's top level; a
    name neither the file's module shows nor standard is refused where the
    file defines the macro;
  - a type a file's macro writes is read through the file's module, `(select
    %shared:key T)`, `T` a whole type read as a `with` of the module reads
    types over the standard environment's alone (both checkers);
  - a file's macros are defined among themselves by their names there, and
    each has a name the importer has it by, `%syntax:key:name`, which no
    program writes: so one of them using another, hidden or not, reaches
    it;
  - a use of a file's macro in the file itself is refused, for now: no
    reference to a module's own items is one a local binding cannot shadow;
  - the names a file's `include`s give are known only once it is checked,
    so a file's macro cannot name them, not yet; a file of module
    parameters cannot be imported from, not yet;
  - a file's macro may not take the name of a macro defined already.
  Tests: `crates/fixpt-cli/tests/import_with_syntax.rs`, on four machines.

## Typed holes (2026-11-07, built)

The user's design, the step after the port (item 7 of the table above).

- **Written** with keywords, each part optional (the user's choice):
  `(expr #:type T #:effect E)`, `(bvar #:type T)`, in a signature that may
  be `(poly ((t type) (e effect)) σ)`. A part left out is a binder of the
  macro's, named for its hole (`%type-of-e`), so that a template that
  only moves an expression about needs nothing written, and one that
  depends on its type says which hole wants it. Plain `expr` and `bvar`
  are untyped, as before. (`(expr T E)` was refused: a list of three
  syntax types already means three operands.)
- **A template checked once, where it is defined** (the user: "a great way
  to go"): for each clause whose parts are typed, a hidden definition,
  `%template:name:k`, which neither front end shows, of the template as a
  procedure over its holes, each a parameter `(subr E (U …) T)` called
  where the template places it, given the template's binders in its scope.
  Made by transcribing the template as a use is, its holes' calls in place
  of a use's expressions (`template_checks`, `macros-templates.fx`); both
  checkers check it as any definition, and a redefinition of a global it
  uses has it checked again, as any definition that uses one.
- **Each use's expression held to its hole's type**, `(the (select
  #%toplevel T) e)` (none where `T` names the macro's own binders).
- **A hole of no effect, `pure`, may be placed any number of times**; one
  whose effect is not, only once, unless its signature says `(many …)`.
- **Refused, not skipped**: a macro some of whose `expr` parts are typed
  and some not; a typed macro's part that is not an `expr` or a `bvar`; a
  typed hole in an untyped binder's scope, or in a ribcage's or a part's
  exported rib's.
- **Expansions are still checked**, as a safety net.
- **Two tiers** (decided, the user, 2026-11-07): an untyped macro promises
  nothing, and each use's expansion is checked; a typed macro promises
  that a use whose expressions fit its holes expands to well-typed code,
  its template check a type system for macros, its refusals of some safe
  macros the price, made fewer by what signatures can say. Its expansions
  are still checked, a safety net that tests the promise (a disagreement
  is a bug in it), until it is trusted; then they need not be, and macros
  in module types (item 10), known by their signatures alone, can be.
- **What goes in a hole follows what its place requires** (the user's
  reading of the first such refusal, a hole where `letrec` wants a
  lambda): a syntax type, `lambda`, a narrower `expr` (a `lambda` or
  `rlambda`, in `plambda`s and `the`s, as `Checker::is_lambda` takes
  one), which the kernel's `letrec` bindings now say; a typed hole there
  is `(lambda #:type (subr E (A …) R))`, its stand-in in the check a
  lambda calling its procedure, of no effect, so its type is written out.
  An untyped `expr` part there is still placed (it promises nothing); a
  typed `expr` one is refused, and so is a use's expression that is not a
  lambda, where it is written, before it is expanded.
- **Found next, and right**: a typed template whose recursive binding is
  declared `pure`, with a hole in its scope, is refused (`it may not
  end`): a lambda a use gives may call it. Said honestly, `spin`, it is
  checked once and runs.
- Tests: `tests/programs/macros/typed-*.fx`, both front ends
  (`tests/macros_both.rs`).

## Macros that make definitions (2026-11-07, built)

Item 9, the user's order after typed holes; the design agreed before it
was built (the user: hygiene "largely consistent with my mental model …
circa R5RS").

- **Written** `(define-syntax name (-> σ defn) clause …)`; `(-> σ expr)`
  and a plain `σ` make an expression, as before.
- **A template is definitions**: the kernel's `definition`s,
  `macros-kernel.fx`, each exporting what it defines, with its scopes as
  the checkers have them: `(define x e)`, `e` not in `x`'s scope; `(define
  x T e)` and `(define* x T lambda)`, the initializer in it (a lambda may
  call itself; a reference from another initializer is the checker's to
  refuse); a `define-rec` group, each lambda in the whole group's; a
  `begin` of definitions, Herman's `let*` clauses, each in the scope of
  those before it, a ribcage. The address `()`, Herman's `ε`, names the
  part an annotation is on (`define-rec`'s group, its own import). A use of
  another such macro is a definition too, which exports what its
  signature says, `(-> (export σ β) defn)`, and nothing else ("Decided:
  signatures depend on their operands by address alone").
- **Hygiene, Herman's exports**: a name a use gives, a `bvar` part, is
  defined under that name, the program's; one the template writes is made
  fresh, as its other binders are, so nothing outside can name it, and
  each use has its own (`%count:1`, `%count:2`). A reference the template
  makes to a use's name is held to the shadow restriction, so a second
  definition's expression in the scope of the first's name says so in its
  signature: `(bvar expr bvar (import expr (rho (A var))))`.
- **Where**: at the top level alone (`Macros::expand_top`, `expand-top`):
  a use is the definitions it makes, in order, a `begin` of them spliced,
  each a form of its own at the use's place, as a top-level `include`'s
  forms are. Anywhere else, in a program or a template, refused: `` `m`
  makes definitions, which are made at the top level ``; so is a kernel
  definition in an expression's place.
- **The first tier only**: typed parts in such a macro are refused, "not
  yet", never ignored; each use's definitions are checked where they are.
- **Not yet**: definitions of types and effects (a template's type binder
  would be made fresh, and the types naming it are opaque to the
  expander: binders of types, item 8); `defn` as a part a use gives;
  names a template makes from a use's (`make-point` of `point`); uses in
  a module's items.
- **Found on the way**: a template's `(->* (T …) R)`, a definition's type
  and no type, was read through `(select #%toplevel …)` whole, which hid
  it; each of its types is read so now (`selected`), `letrec`'s too.
- Tests: `tests/programs/macros/defn-*.fx`, both front ends; a file's,
  `fixpt-cli/tests/programs/import-with-syntax/main-defn.fx`; the REPL,
  `fixpt-cli/tests/repl_macros.rs`.

## Decided: signatures depend on their operands by address alone (2026-11-07)

The user's question: does this become a dependent type system of its own?
In shape, yes: `(export (bvar expr) (rho (A var)))` speaks of parts of
the term it classifies, a union member chosen by a use is a case split,
and a typed hole whose type is another operand's description, `((type #:as
t) (expr #:type t))`, is a Π over syntax. Decided (the user, 2026-11-07),
to keep it small: **a signature refers to its own operands only by
address, and only as binders or as descriptions substituted whole; it
computes nothing.** Checking stays walking trees, comparing ribs as sets,
and the checkers' own comparison of types. What needs more, names
computed from a use's (`make-point` of `point`), exports that depend on
anything but the syntax's shape, descriptions computed from operands,
gets a design of its own rather than growing in.

A macro sees what a nested use defines only as that macro's signature
declares (`(-> (export σ β) defn)`), checked where it is defined, never
by its expansion (the user, 2026-11-07, "It matches my intent"); a
reference the declarations do not bind is refused, not read at the top
level. Built the same day, both front ends: the export is held to what the
template defines of what its uses give (its own binders, made fresh, are
none of it), `` this template defines `a`, and its signature says its uses
define `a`, `b` ``; a name bound in a nested use that does not export it,
referred to, is refused, `(with #%toplevel x)` the way to the top
level's (`defn-export*.fx`).

## Decided: a template's free description names, one qualified name each (2026-11-08)

Binders of descriptions (item 8) makes a template's types transparent, so
a free name inside one can no longer be read at the top level by wrapping
the whole type, `(select #%toplevel T)`, as today's expansions do: the
type may also hold a use's description and the template's own binders.
Three ways were weighed with the user: per-name `(select #%toplevel n)`,
whole-type `select` for the parts that are closed and per name inside the
rest, and a *qualified name*, one name that is already the top level's
(first called a "marked identifier", renamed since: see below). Decided
(the user, 2026-11-08, "the toplevel is such a special case as it is"):
**the qualified name**. Each free description name a template
writes becomes one symbol that both checkers read in the top level's
description scope, whatever binds the name where the use is, in any
description position: a type, an effect, a description function's head, a
`proj`'s argument.

Found on the way (both checkers agree on each): a type form's name in
head position, `(listof T)`, is looked up, but only a function binding it
(a family, an arrow-kinded variable) takes it over; a binding of another
kind is passed over for the built-in form, so `(listof listof)` under a
binder of kind `type` named `listof` is the built-in list of the binder.
So a template's heads can be captured too, and are qualified like any free
name: `(#%toplevel:listof int)`, where the top level binds no function
`listof`, is the type form. The names are not to be reserved against
description binders: they are to become ordinary bindings of a standard
library, each tagged for what the compiler knows of it (`lang-items.md`,
the user's, 2026-11-08).

Built 2026-11-08, both checkers and both readers: `#%toplevel:name`, which
a program may write too, the top level's `name` as a value (`(with
#%toplevel name)`) and in every description position (`docs/fx26.md`,
"`#%toplevel`, the top level's bindings"; `modules/toplevel-qualified-*.fx`).
The expander emits it since binders of descriptions' first stage (below).

**Renaming, not marks** (the user's question, 2026-11-08: do these differ
from alpha-renaming in any fundamental way?). They do not: the expander
rewrites symbols, two ways. A template's binder is renamed fresh, at the
binder and each reference (`%a:5`), alpha-renaming; a template's free name
is *qualified*, `#%toplevel:x`, a name resolved in one fixed environment,
nearer a syntactic closure over the top level than a mark. (Not renamed:
what the top level's `x` is is not fixed where the macro is defined, the
top level being redefinable, item 5.) KFFD's marks, and Flatt's sets of
scopes, record which expansion step brought an identifier in, so that what
binds it can be found later, where binding forms are themselves macros and
the structure is known only by expanding; Herman's binding signatures say
the structure before expansion, and with it hygiene is expansion that keeps
alpha-equivalence (Herman and Wand), which renaming at once gives. What
marks give that this does not, and where it would matter here:
- marks that cancel when applied twice tell what a transformer brought in
  from what the use gave, knowing no structure: the signature tells that;
- a mark is undone for `quote` and `syntax->datum`: no data position is
  renamed, the signature saying which are data;
- `free-identifier=?` against `bound-identifier=?`, for literals such as
  `else`: such words are reserved keywords here, never bound;
- **procedural macros** (item 11): a transformer compares identifiers,
  makes them in another's context (`datum->syntax`, `make-point` of
  `point`), and decides binding structure as it runs. A renamed symbol has
  lost the context such code asks about; there marks or scopes earn their
  keep, as they would for any deliberate break of hygiene, the names
  computed from operands that "Decided: signatures depend on their operands
  by address alone" keeps out.
`let-syntax` does not need them: with the program's binders renamed apart,
a template's free name is resolved where the macro is defined, to the
renamed binder in scope there, which no binder where it is used can be. The
top level, redefinable, is the one environment not resolved so early, which
is why its names are qualified rather than renamed.

## Binders of descriptions, the first stage (2026-11-08, built)

Item 8, its first stage, in both front ends (`docs/fx26.md`, "A
template's descriptions"). A template's description is aligned name by
name (`Aligner::desc`, `macros-align.fx`'s `desc`), not as one opaque
type: no grammar of descriptions in the kernel's signatures, but one
walk that knows the forms that bind (`poly`, `dlambda`, `mu`, `dletrec`),
the positions of labels and of values (`(globals g …)`, `(select m n)`'s
module), and the words of descriptions (the kernel's `description-heads`
and `description-words`, held to the checkers' `TYPE_FORMS` and
`EFFECT_HEADS` by a test); every other name is a reference in the
description namespace. What a description's binder binds is a rib of
what was found (`Bind::Direct`, `bind-direct`), so Herman's machinery,
imports, exports, the shadow restriction and the declared scopes, checks
descriptions as it does expressions: a namespace on each binder, rib
atom and reference (`Ns`), `dvar` and `(ℓ dvar)` for a description's
binder a use gives, the shadow restriction per namespace (a value's
binder never shadows a description's). A type with `poly`s at its top
exports their binders, which `define`, `define*` and `define-rec` put in
scope in what each defines (`Checker::bind_signature`'s).

Found and settled on the way: a type form's name at a list's head was
looked up first, a function binding it taking it over, so a template's
`(listof …)` could be captured; both checkers now read those heads, and
the effect forms', by name alone. That keeps template heads plain, and
only names qualified; when the standard library's names become its own
bindings (`lang-items.md`), they are names, qualified like any.

Then (1b, the same day, both front ends): regions and places as binders,
`letregion`, `letfreeze` and `rlambda`, and `letrena` and `letreap`,
which bind their name both as a place and as a value of type `(place r)`:
each rib atom says its namespace (`Atom::Var(n, Ns)`), and a δ `place`
binds both. A macro that makes definitions may make `define-type` and
`define-effect`, in `let*` order within its `begin`, as its values are,
and declared ahead with the program's types when expanded. A pattern
variable that is a name placed in a template never fits a list's shape
(so `(define-type t …)`, `t` a `dvar`, is the plain form, not a family's).

Left for the second stage: `define-datatype` and `define-generative`
(`define-datatype` since done as `define-data`, `datatype-macro.md`), a
`subr`'s named parameters and specification (since built, 2026-11-08:
`docs/fx26.md`), `moduleof`, a file's macro's descriptions with its own binders, a use's
type placed in the scope of a use's `dvar` without saying so, and typed
macros' description parts. Tests: `macros/desc-*.fx`,
`import-with-syntax/main-poly.fx`.

## Ellipsis (2026-11-08, built)

Primitive repetition in patterns and templates, both front ends
(`datatype-macro.md`, §4 and §8; `docs/fx26.md`, "Ellipsis"). For
Herman's checking, an ellipsis's element is aligned once, with the list's
element type (`Macros::seq_of`: a `mu` of `()` and pairs of an element and
itself, binding no more than each element exports, all together), and a
sequence's binders are one atom; each node an ellipsis follows is
repeated, and the walk counts the ellipses each part is under, which a
pattern variable's placing is held to.

## Inferred signatures, and `syntax-rules` (2026-11-08, built)

The user's question: why not a `syntax-rules` that infers its macro type,
since in practice the analysis is local? Pombrio, Krishnamurthi and Wand,
"Inferring Scope through Syntactic Sugar" (ICFP 2017), does it for scope
alone: per-constructor binding facts, a least fixpoint over all the sugar
at once. Built here for Herman's whole signatures, the user's design
choices (2026-11-08):

- **Written** `(define-syntax name [σ] (syntax-rules (literal …) clause
  …))`, the signature optional; `(define-syntax-rec (name [σ]
  (syntax-rules …)) …)` for macros whose templates use each other, as
  `define-rec` is for values. The clauses are always a transformer's (the
  user: "we need to distinguish our different macro forms"): the form
  without one, `(define-syntax name σ clause …)`, is refused, and every
  program was moved. A `syntax-rules`' literals are the names its
  signature writes as they are, `(literal name)`, held to each other where
  the signature is written (a form's name matches itself either way).
- **`many` is inferred** where a template places a part with an
  expression in it more than once (the user's choice, against keeping it
  an opt-out to write).
- **Overlapping clauses are refused** (the user's choice): a `union`'s
  members are told apart by their shapes, as `syntax-rules`' order would
  not.
- **Sound by construction**: what is inferred is a signature, checked by
  the unchanged checker as a written one is; inference only decides which
  macros need none written. A refusal says the signature inferred, to copy
  and change.

How (`macros/infer.rs`, `macros-infer.fx` and `macros-solve.fx`, alike in
each step so that both front ends infer the same, which
`macros_both::both_expanders_infer_alike` holds them to on every program
in `tests/programs/macros` with its signatures left out):

1. **Shape**, from the patterns: where they differ, a `union` of their
   shapes, each member a region its addresses are from; a list by ellipsis
   takes in `()` and the patterns that write its elements one by one where
   one of them is a list by ellipsis (`()`, `(e)`, `(e r ...)` are
   `(expr ...)`, which the template's `(or* r ...)` needs), unless their
   elements turn out of more than one syntax type (then not, the next
   time). `()` and `((x e) . rest)` stay a `union`, whose `rest` may be in
   the scope of what the first clause binds: Herman's let*-cl.
2. **What it makes**, from the templates' heads: a definition's form or
   such a macro's use, definitions; a type form's (`type-forms` in the
   kernel file, `parse.rs`'s `TYPE_FORMS`), a description; an
   expression's form, an expression. A clause that says nothing, a name,
   takes another's; none, an expression.
3. **Each pattern variable's syntax type**, from where the template places
   it, aligned with the kernel's forms' signatures and the macros' (the
   group's, as inferred so far): a binder over the references to it, a tag
   over an application's head it looked like, a variable over an
   expression, an expression over a lambda. Not known yet, taken for a
   name where a form takes a name or a list, else for anything.
4. **Scopes**: the environment each part is placed in, said on the part
   by addresses where its binders are in its region, else on the part
   around it whose region they are outside of; a binder inside a list's
   element or a `union`'s member reached through what that exports (a rib,
   or for a run of levels inside one member, a ribcage). A clause whose
   member has none of what another's exports exports an empty one. A macro
   that makes definitions exports what its template defines of what a use
   gives, so that a template using it sees them.
5. **Recursion**: the group's signatures so far are what a template's use
   of one is aligned with, again, until each says the same twice (at most
   16 times; then the last, which the checker judges).

Of the 125 macros in `tests/programs/macros` with written signatures, the
signature inferred from the clauses alone is the written one for 72
(`macros::infer::tests::inferred_against_written`); most of the rest are
refusal tests, or differ by saying more: a `defn` macro's export, `(many
expr)` where `id` was written, the kernel's whole `formals`. Not inferred,
to be written: typed holes; a part in a list by ellipsis whose elements are
each in the scope of those before (a pattern's binders through a template's
`let*` of them by ellipsis); what a template that names only a pattern
variable makes, `((_ f) f)`; a tag placed only at an application's head,
`(t e)`. Tests: `macros/infer-*.fx`, `macros/syntax-rules-unsaid.fx`.

## Decided: signatures as contracts, named, outside the code (2026-11-08; its notation reopened, "Three notations", below)

Not built. The user's direction, after the inference above, and the
choices made with them the same day:

- **Types outside the code.** Nothing is written in a `syntax-rules`'
  patterns or templates; a signature is a part of the `define-syntax` of
  its own.
- **A signature says what it is**, as a transformer does: `(syntax-contract
  …)`, in the notation below; `(syntax-contract/addressed …)`, Herman's,
  as written today, kept. A bare signature is refused, as a bare clause
  list is, its message naming both. "Contract" in Findler and Felleisen's
  sense: for `syntax-rules` it is discharged once, where the macro is
  defined; for a procedural transformer it is checked at each expansion,
  at the boundary between the transformer and what it makes, the macro
  blamed ("Proposed: procedural macros", below). The expander's own word
  for a typed hole's `(the T e)` wrapper (`Clause::contracts`) is renamed.
- **Readable**: labels and contexts, not chains of `A` and `D`, which stay
  what a contract elaborates to; the checker is unchanged.

```scheme
(define-syntax let1
  (syntax-contract ((x : bvar) (e : expr)) (body : expr (in (x hole))))
  (syntax-rules ()
    ((_ (y v) b) (let ((y v)) b))))
```

### The notation

```text
part  ::= (x : σ)                       labelled x, of syntax type σ
        | (x : σ (in C))                in the scope C, the part in its hole
σ     ::= expr | bvar | id | data | type | label | lambda | dvar | kind
        | place                         a binder of a description and a
                                        value both (`letrena`'s)
        | () | (σ-or-part … σ-or-part ...) | (σ-or-part … . σ-or-part)
        | (offers σ C)                  σ offers the scope C to what brings
                                        it into scope
        | (union σ …) | (mu t σ) | t | (many σ) | (literal name)
        | (expr #:type T #:effect E) …  typed holes, as written today
        | _                             inferred (`syntax-rules` only)
C     ::= hole                          where the part (or the importer) goes
        | (L C)                         L's scope, C inside it
L     ::= x                             what the part labelled x offers: a
                                        binder, itself; a part that offers, its C
        | (x …)                         several, one level, none shadowing
                                        another (a rib)
```

A scope is a context, written as it nests: no order to remember. What a
part sees and what it offers are both contexts, so `in` and `offers` read
alike; naming a label whose part offers a context plugs that context in
there. A `let` is one level, a `let*` levels nested:

```scheme
let:   (body : expr (in ((x1 x2 x3) hole)))
let*:  (body : expr (in (x1 (x2 (x3 hole)))))
```

The contracts of the kernel's examples:

```scheme
;; let, by ellipsis: each element offers its binder; the list, all of them,
;; one level.
(syntax-contract ((bindings : ((offers ((x : bvar) (e : expr)) (x hole)) ...))
                  (body : expr (in (bindings hole)))))

;; let*, by recursion: Herman's let*-cl, which inference finds. Each later
;; clause is in the hole of x's scope; each clause offers x's scope with the
;; later ones' inside it.
(syntax-contract
  ((cs : (mu clauses
           (union ()
                  (offers (((x : bvar) (e : expr)) . (rest : clauses (in (x hole))))
                          (x (rest hole))))))
   (body : expr (in (cs hole)))))

;; A macro that makes a definition, and says what it defines.
(syntax-contract #:makes defn (offers ((n : bvar) (e : expr)) (n hole)))
```

Whole contracts: `#:makes defn` for what makes definitions, `#:makes type`
a description, an expression's by default (`(-> σ defn)` today: `->` reads
as a procedure's type, which this is not); `#:poly ((t type) …)` for the
binders typed holes may name.

### Labels and their scopes

A label is the contract's, not a pattern variable: the contract is the
interface, each clause matched against it by shape as today, so clauses
may name a part differently, or not at all, and renaming a pattern
variable changes no type. A label is in scope in the region it is in (the
contract, a list's element, a `union`'s member, a `mu`'s body: what an
address is from today) and the regions inside it; two of one name in a
region are refused. Inside a `mu` body a label means its own unfolding's
part (`x` is this clause's binder, each time the `mu` unrolls), never an
outer one's, which the inherited scopes bring in already: an `in` flows
down, pushing its unfolding's binder onto what the parts around inherited,
and an `offers` flows up, each unfolding's scope with its `rest`'s plugged
in (an inherited and a synthesized attribute). A part may be in the scope
of a label of a region around it; it may not name a part inside a list's
element or a `union`'s member from outside, which reaches it only by what
that region `offers`, written (the user's: each binding's way from binder
to scope is in the contract, self-documenting).

### Elaboration, and printing

Each label becomes its part's address from its region's root; each `in`'s
context an `import` (one level a `rho`, levels a `cage` of them, innermost
first); each `offers` an `export`; δ from what the part offers (`var` for a
`bvar`, `dvar`, `place`, a part's `rib`, or `(at ℓ)` for nested levels). A
contract is a way of writing a signature the checker already checks; it
adds no rule.

An inferred signature is printed as a contract, each part labelled by the
first clause's pattern variable there, or `p1`, `p2`, … where none is,
which written back elaborates to the same signature (a property to test,
over `tests/programs/macros`). A `_` leaves a part to inference within the
shape and scopes written around it; what is inferred must agree with what
is written, else refused, saying both.

The tests' signatures move to contracts, their "As named:" comments the
start (each checked to elaborate to the addressed signature it replaces);
some stay `/addressed`, for Herman's notation itself.

## Three notations, side by side (2026-11-08)

For the user to judge by reading, before any is built: the contract
notation decided above was settled one confusion at a time (which context
is offered, which order a ribcage is written in), and the user asked
whether a step was wrong. Four macros, each in:

- **A**, Herman's addresses, as written today (`syntax-contract/addressed`);
- **B**, the contexts with a `hole` decided above, with `offers` made a
  clause of a labelled part, as `in` is;
- **C**, *shapes and facts* (after Pombrio, Krishnamurthi and Wand). Each
  node is `(NAME SHAPE FACT …)`: a name for the node (not syntax), its
  shape (a pattern-like tree of labelled parts, exactly what a use
  writes), and its facts, each
  naming only labels of the node's region: `(bind a in b)`, `b`'s insides
  see what `a` provides (flowing down); `(export a …)`, the node provides
  what each `a` does, at one level, two of one name colliding (flowing up,
  `let`'s); `(export* a …)`, the same nested, each inside those before
  it, a later one shadowing an earlier (`let*`'s). Named shapes, recursive or not, are
  bound by `(letrec-shape ((name node-or-union) …) top-node)`, a `union`'s
  members each a node; a shape's name and its node's are distinct, `(b
  (binding …))`. The macro's node is named for the macro, and its shape is
  written as a `syntax-rules` pattern is, the keyword's place first, `_`
  (or the macro's name, no other), so that a contract reads against the
  clauses beside it (the user's): `(my-let (_ ((bs : b) ...) (body :
  expr)) …)`. A `bvar` provides itself; a part of a named shape, what
  its node's facts export. Ellipses follow `syntax-rules`' rules, the
  user's choice (2026-11-08): `p ...` repeats the part before it, as in a
  pattern, and a label under *k* ellipses is named in a fact under exactly
  *k*, as a pattern variable is in a template (a repeated label named bare
  from outside its ellipsis is refused); `(bs ...)` in a fact is every
  repetition's, at one level, as `let`'s `((x e) ...)` is one rib.

### `let1`

```scheme
;; A
((bvar expr) (import expr (rho (AA var))))

;; B
(syntax-contract ((x : bvar) (e : expr)) (body : expr (in (x hole))))

;; C
(syntax-contract
  (let1 (_ ((x : bvar) (e : expr)) (body : expr))
    (bind x in body)))
```

### `let`, by ellipsis

```scheme
;; A
(((export (bvar expr) (rho (A var))) ...) . (import (expr) (rho (A rib))))

;; B
(syntax-contract
  ((b : ((x : bvar) (e : expr)) (offers (x hole))) ...)
  (body : expr (in (b hole))))

;; C
(syntax-contract
  (letrec-shape ((b (binding ((x : bvar) (e : expr)) (export x))))
    (my-let (_ ((bs : b) ...) (body : expr))
      (bind (bs ...) in body))))
```

### `let*`, by recursion

```scheme
;; A
((mu c (union (export () (cage))
              (export ((bvar expr) . (import c (rho (AA var))))
                      (cage (at D) (rho (AA var))))))
 (import expr (cage (at A))))

;; B
(syntax-contract
  ((cs : (mu clauses
           (union ()
                  (clause : (((x : bvar) (e : expr)) . (rest : clauses (in (x hole))))
                            (offers (x (rest hole)))))))
   (body : expr (in (cs hole)))))

;; C
(syntax-contract
  (letrec-shape ((clauses
                   (union (end ())
                          (clause (((x : bvar) (e : expr)) . (rest : clauses))
                            (bind x in rest)
                            (export* x rest)))))
    (my-let* (_ (cs : clauses) (body : expr))
      (bind cs in body))))
```

### `define-data`, with a constructor procedure per variant

What a use defines: the type's name, and each variant's constructor.

```scheme
;; A
(-> (export (dvar (export (bvar label type ...) (rho (A var))) ...)
            (rho (A dvar) (D rib)))
    defn)

;; B
(syntax-contract #:makes defn
  ((name : dvar)
   (v : ((c : bvar) (t : label) (fields : type) ...) (offers (c hole))) ...)
  (offers ((name v) hole)))

;; C
(syntax-contract #:makes defn
  (letrec-shape ((v (variant ((c : bvar) (t : label) (fields : type) ...) (export c))))
    (define-data (_ (name : dvar) (vs : v) ...)
      (export name (vs ...)))))
```

### What each shows

- **A** says everything, in a form for machines: no names, and the reader
  works out `AA`, `(at D)` and `(D rib)` by counting.
- **B** puts scopes inside types: what a part sees and what it provides
  sit within its shape, among its sub-parts' own, and a ribcage's order is
  a written convention (the hole says it, but the reader must still find
  which context is whose).
- **C** separates the two. The shape reads as a pattern (the macro's node
  as its clauses' patterns are, `(_ (cs : clauses) (body : expr))`); each node's scoping is
  a few one-line facts after it, about its own parts alone, so each named
  shape is read, and could be reused, by itself (the kernel's
  `formals`, `let-bindings`, `let*-clauses` are such shapes already:
  `(cs : let*-clauses)`). Shadowing is written, `export*` against
  `export`, and is not read off `bind`: a `lambda`'s parameters each see
  those before (a type may name an earlier one) and yet export one level,
  two of one name colliding, while `let*`'s clauses see those before and
  export nested levels (found writing the tests' signatures in C, below).
  `bind` and `export` are distinct because forms combine them
  differently: `let` exports without binding the later initializers,
  `let*` does both, a part may bind a local without exporting it.

### Leaning: C, to test before deciding

- **Expressiveness.** Pombrio et al. show their four facts (`import`,
  `export`, `bind i in j`, re-export) cover `let`, `let*`, named `let`,
  Pyret's `for` and Haskell's list comprehensions, and that they are a
  little weaker than Romeo (no two binders that shadow each other in
  different parts). To check: every signature in `tests/programs/macros`
  written in C, and elaborated back to A. Their failure, Scheme's `do` (a
  variable seen by every element's `step` and no element's `init`), is the
  case to try first: `(bind bs in step)` names a part inside the list's
  elements, which C's locality forbids, and A says it today only by an
  import on the list.
- **Elaboration.** C's facts give each part the environment it is in;
  turning environments into Herman's imports and exports is what
  inference's solving already does (`macros/infer.rs`'s `sites`, `rings`,
  `merge_rings`), so C elaborates through code we have.
- **Printing what is inferred.** Inference finds environments by region,
  which print as C's facts, a few named shapes each with its own, rather
  than one deep signature.
- **Supersedes B** if chosen: the decisions above stand (contracts outside
  the code, headers, exports written, `#:makes`/`#:poly`, `place`), the
  context notation replaced by facts.

### C against the tests' signatures (2026-11-08)

The tests' written signatures (`tests/programs/macros`, and the files of
`import-with-syntax`): 62 distinct. 42 have no scopes (no `import`,
`export`): in C a shape alone, no facts (a `union`'s members named, as
`define-data`'s `(union dvar (dvar (dvar kind) ...))`, a `(many σ)` or a
typed hole a part's kind). The other 20, each in C (the `syntax-contract`
around each left out; a defn's `#:makes defn` written):

```scheme
;; let1, ((bvar expr) (import expr (rho (AA var))))
(let1 (_ ((x : bvar) (e : expr)) (body : expr)) (bind x in body))
;; where, ((import expr (rho (AAD var))) (bvar expr)): the binder after its scope
(where (_ (body : expr) ((x : bvar) (e : expr))) (bind x in body))
;; call-rec, (bvar (import expr (rho (A var)))); also with `lambda` for `expr`
(call-rec (_ (f : bvar) (e : expr)) (bind f in e))
;; with typed parts: each kind as written, `(e : (lambda #:type fn))`,
;; `#:poly ((t type) …)` before the node; the facts as above
(let1 (_ ((x : (bvar #:type t)) (e : (expr #:type t #:effect e1)))
         (body : (expr #:type u #:effect e2)))
  (bind x in body))
;; a description's binder, (dvar (import expr (rho (A dvar)))); a place's,
;; (dvar (import expr (rho (A place)))), the part's kind `place`
(pfun (_ (t : dvar) (e : expr)) (bind t in e))
(with-arena (_ (r : place) (e : expr)) (bind r in e))
;; defns: (-> (export (bvar expr) (rho (A var))) defn), and two names
(define-const (_ (n : bvar) (e : expr)) (export n))
(define-and-double (_ (a : bvar) (b : bvar) (e : expr)) (export a b))
;; (-> (bvar expr bvar (import expr (rho (A var)))) defn)
(define-both (_ (a : bvar) (e1 : expr) (b : bvar) (e2 : expr)) (bind a in e2))
;; each element's part its own element's binder, ((bvar (import expr …)) ...)
(letrec-shape ((p (pair ((v : bvar) (e : expr)) (bind v in e))))
  (m (_ (ps : p) ...)))
;; let by ellipsis, and let* by recursion: above
;; fun's formals, each parameter's type in the scope of those before,
;; exported at one level, a lambda's: (mu f (union (export () (rho))
;; (export ((bvar type) . (import f (rho (AA var)))) (rho (AA var) (D rib)))))
(letrec-shape ((f (union (none ())
                         (param (((x : bvar) (t : type)) . (rest : f))
                           (bind x in rest)
                           (export x rest)))))
  (fun (_ (fs : f) (body : expr)) (bind fs in body)))
```

Found:
1. **Shadowing is written** (`export*`), not read off `bind`: `fun`'s
   formals and `let*`'s clauses have the same `bind x in rest` and export
   one level and nested levels.
2. **Not writable, and rightly**: `desc-delta-mismatch.fx`'s `(dvar (import
   expr (rho (A var))))`, a description's binder brought in as a value's,
   which the checker refuses. C reads δ off the part's kind, so the
   mismatch cannot be written; that test stays `/addressed`, as a test of
   Herman's notation.
3. **`do`** is said by neither (`TODO.md` §223): named scopes.

So C says what the tests' signatures say. Elaboration to A, and a test
that it gives each of these back, is for the build.

## Syntactic closures: what an expansion means (2026-11-08)

The user's question, reading Clinger and Rees: since a signature already
gives what their deferred renaming was for, should syntactic closures be
our reference? Leaning: yes, as the meaning of an expansion, with
Herman's signatures the static discipline and renaming the
implementation. Not built; nothing changes yet but what we argue from.

**The line of work.** Bawden and Rees's syntactic closure is a form, a
syntactic environment, and a list of names left free: every name in the
form means what it means in the environment, but those, whose meaning the
context gives ("call-by-context"). An expander closes each piece of a use
in the use's environment, leaving free what the expansion will bind
around it, and closes its own text in its own. Clinger and Rees objected
that a pattern language cannot choose the environments and free lists,
since "the syntactic role of an identifier" is not known before
expansion; their algorithm renames as expansion goes, to defer the
choice. The objection is to closures as first proposed, whose names were
symbols. The two lines then met rather than one refuting the other:
Clinger and Rees's algorithm "unifies and extends" both, its renaming
done over syntactic environments ("Rees married syntactic closures to the
modified Kohlbecker's algorithm"); Hanson's 1991 facility, which does not
discuss the objection, adds an identifier type with *aliases* (Bawden's
"synthetic names"), a name closed in the transformer's environment that
may yet be bound, much as a renamed identifier is, so that a
`syntax-rules` template's names become aliases and the output is left in
the use's, which "is hygienic, without requiring the transformer to know
the syntactic roles of the substituted input subforms".

**Herman, on it.** The ESOP paper: "Our work shares a common observation
with the syntactic closures macro system, namely that macro programmers
know the binding structure of macros a priori; their work provides an API
rather than a theory." The dissertation, §8.1: expansion algorithms
"must generally perform provisional variable renamings, since [they do]
not discover the actual syntactic roles of identifiers until quite late
… By contrast, our system provides all of this information up front." He
relates neither his α-equivalence to closing nor his types to free lists;
his semantics is substitution and renaming, chosen to connect hygiene to
α-equivalence. §7.3.3 blames macro-defining macros' troubles on expansion
"defined as simple textual substitution, without regard for binding
structure".

**What a signature is, in closures.** Hanson's `let1`:

```scheme
`((lambda (,id) ,(make-syntactic-closure env (list id) exp))
  ,(make-syntactic-closure env '() init))
```

leaves free in the body the name the use gave, `(list id)`: Herman's
`(body (in expr x))`. His `loop` leaves free `exit`, a name its own
expansion binds: the capture Herman's types refuse. Hanson remarks the two
differ only in "the source of the identifier being left free". So:

> **An import is a free list drawn only from the binders the use gave.**

Syntactic closures are the larger system; a signature picks out the
hygienic part of it, the part that can be checked once, where the macro is
defined, and that keeps α-equivalence of programs not yet expanded
(Herman's theorem), which aliases alone, hygienic only of each expansion
made, do not.

**Ours, read so.** The expander is Hanson's alias scheme compiled to
names: a template's binder made fresh (`%t:3`) is an alias bound by the
expansion; a template's free name, `(with #%toplevel n)` or `(with
%shared:key n)`, an alias closed in the top level's or a file's
environment, as FX-26's `with` closes a body in a module's (`(with m body)`
is a closure in `m`, leaving free what `m` does not give; "First-class
modules as environments", above); a use's part goes in as it is, open in
the use's environment, which the signature has said its free names reach.
The claim to argue, for soundness by construction: for a macro whose
templates the checker accepts, renaming yields what closing yields.

**Where we differ from the closures' meaning, to settle:**
1. *Literals.* A `syntax-rules`' literal is matched by name; Hanson's
   `cond` matches `else` by `identifier=?`, the same meaning in the use's
   environment as in the transformer's, since a macro's output may hold an
   alias of `else`. Reserved words are safe (nothing binds them); a
   literal like `for-sum`'s `in` matches a use's local variable `in`. A
   hygiene gap (`TODO.md` §222).
2. *A template's free names.* Ours mean the top level's where the macro is
   used (item 5, the user's), so a later redefinition is seen; a closure
   in the transformer's environment would mean the definition's. The same
   for any local binding at the use, which neither sees.
3. *Local macros*, `let-syntax`: closures' environments are what they
   need ("Leaning: narrower macros by `let-syntax`", below).

## Proposed: procedural macros, checked by their contracts (2026-11-08)

The user's question: can there be procedural macros at all, with the
contract (above, "signatures as contracts") made an expansion-time
wrapper that holds each expansion to its binding shapes and types? Not
built; a direction.

**Yes, by the same rules, applied to each expansion instead of once to a
template.** A `syntax-rules` macro is a transformer whose output's shape
is known when it is defined, so the checker can align the template with
the kernel's signatures and hold each pattern variable's placing to the
signature, for every use at once. A procedural transformer's output is
known only when it runs; the same check runs then, on the output:

1. The use is parsed by the contract, as today (`Mode::Use`), before the
   transformer runs: each part with its syntax type and the scope the
   contract declares, evaluated over the use.
2. The transformer is given the parts as *handles* (a use's part, closed
   in the use's environment, free in it only what the contract imports:
   Hanson's closures, made from the contract), and builds the output with
   them, its own names aliases in its environment by default, hygienic as
   Hanson's `syntax-rules` is.
3. The output is aligned with the kernel's signatures as a template is
   (`Aligner`, `Mode::Template`), each handle in it a pattern variable of
   the contract's type, and held to the rules a template is
   (`Aligner::placed`: its syntax type where it is placed, the scope there
   the one its contract declares, no more and no fewer; the shadow
   restriction; placed once unless `many`; what a macro that makes
   definitions defines, what its contract exports). Refused there, the
   macro blamed at the use: "`m`'s expansion places `body` where …, and
   its contract says …".

So the wrapper is the template checker, run per expansion; a
`syntax-rules` macro is the case checked once for all. It is the two tiers
already decided for typed holes ("Typed holes": an untyped part promises
nothing and each expansion is checked; a typed one is checked once), one
level up. What a procedural macro gives up is checking where it is
defined: a use may be refused that another is not. What it keeps is
Herman's α-equivalence of programs as written, which the contract alone
gives (a use is parsed by it before anything runs).

**Which procedural system.** Of the four in the literature:
- *Explicit renaming* (Clinger): `rename` and `compare`; simplest, but
  hygiene is opt-in, a name not renamed captures: against "sound by
  construction".
- *Syntax-case* (Dybvig), and Racket's sets of scopes: hygienic by
  default, but syntax objects carry marks or scope sets, an expander's
  representation a transformer sees (Herman's §7.3.3 complaint).
- *Syntactic closures* (Bawden, Rees, Hanson): closures and aliases,
  `identifier=?`; a free list says, at each piece, what may bind in it,
  which is what the contract says, so a contract can *make* the closures
  rather than check what a programmer wrote.

Leaning: syntactic closures made from the contract. The transformer never
writes a free list: a handle is closed as the contract imports, a name
the transformer writes is an alias, and the only way to leave a name free
for its own binder (`loop`'s `exit`) is not offered, since the contract
could not say it.

**Open:**
1. *When transformers run, in both front ends.* A transformer is FX-26
   code, run by each expander (the Rust one's evaluator, the FX-26 one's),
   the two to agree; `pure` (FX-26's effects say so, and it keeps
   expansion deterministic, which both front ends' agreement needs).
2. *What a transformer may name.* Phase separation (Flatt's "composable
   and compilable macros"): the standard environment, and modules imported
   for expansion; not the program's own definitions, not yet run.
3. *Inspecting handles.* Destructuring a use's part (counting, a
   literal's test by `identifier=?`) without reaching into its scope.
4. *Names computed from a use's* (`make-point` of `point`): a binder the
   contract cannot address, against "signatures depend on their operands
   by address alone"; a design of its own, as decided then.
5. *The syntax datatype* a transformer sees: FX-26's `syn` (the reader's),
   or a type of handles and forms of its own.
6. *The macro's own keyword.* `syntax-rules` ignores a pattern's head (R7RS:
   neither a pattern variable nor a literal); `syntax-case` binds it, so
   that `#'foo` is the keyword with the use's context, which a transformer
   recursing through itself may rely on. Whether a transformer is given a
   handle on its keyword, and with whose context.

## Procedural macros, prototyped (2026-11-09)

Built in both front ends, so that writing a macro each of three ways can be
compared (the user's request): `syntax-rules`, explicit renaming (Clinger),
and syntactic closures (Bawden and Rees, as Hanson's facility gives them).
No contracts yet (the section above): a procedural macro has no signature,
its expansion is checked as any code is, and its hygiene is enforced as it
runs. `TODO.md` §228; tests `tests/programs/procedural/`, the same macros
each way (`twice-*.fx`, `aif-*.fx`).

```
(define-syntax name (er-macro-transformer  (lambda (form rename compare) …)))
(define-syntax name (sc-macro-transformer  (lambda (form use-env) …)))
(define-syntax name (rsc-macro-transformer (lambda (form macro-env) …)))
```

**A transformer is FX-26 code over `datum`s**, checked where the macro is
defined at its style's type:
- ER: `(subr spin (datum (subr pure (symbol) symbol) (subr spin (symbol
  symbol) bool)) datum)`, the use's whole form, `rename` and `compare`.
- SC and RSC: `(subr spin (datum symbol) datum)`, the form and an
  environment. Around it, as locals, are `make-syntactic-closure (env free
  form)`, `identifier?` and `identifier=?`.

It sees the standard environment and those alone: nothing the program
defines (phases apart). It is checked and run by an FX-26 session of its
own, the same for both front ends (`macros/procedural.rs`'s `run`; the
expander written in FX-26 reaches it through the standard
`%macros:expand-procedural`), and what it gives comes back as text, read at
the use's place.

**Hygiene by aliases, one spelling for both systems.** `%~N:x` is `x` as
where the macro was defined, made by expansion `N`:
- ER's `rename` makes them; `compare` compares names, an alias as its
  name.
- A syntactic closure is a list, `(%sc env (free …) form)`; once the
  transformer has given its answer, every name closed in the macro's
  environment is made an alias, and every name closed in the use's is left
  as written, a closure's free names closed in the environment around it.
  `sc-macro-transformer`'s answer is closed in the macro's, `rsc-`'s in the
  use's. So syntactic closures are explicit renaming of every name the
  macro writes, as this note's "Syntactic closures" section found.
- What an alias means is decided where its role is known: a keyword's name
  (a form's, a description's word, a macro's), which nothing binds, is the
  keyword, by the expander; a quoted one is its name; a label is its name
  (both labels' readers); a type or effect name nothing in scope binds is
  the top level's (`read_qualified`, `k-qualified?`); and a value's that
  nothing in scope binds, nor the top level defined, the top level's,
  `(with #%toplevel x)` (`aliases.rs`; in FX-26, on the parser's trees,
  `parser-top.fx`'s `unalias`, which both its checker and its compiler
  read). One the expansion binds is a name of its own, which nothing the
  use wrote can capture.

**Not built.** `capture-syntactic-environment`; names compared by what
they mean, not as written (`compare` and `identifier=?` are by name, as
`syntax-rules`' literals are, §222); a procedural macro in a
`syntax-rules` template (refused: no signature says what it binds); and
the contracts.

## Leaning: narrower macros by `let-syntax`, not in module types (2026-11-08)

Today `define-syntax` is allowed at a program's top level and a module
file's, nowhere else (a `lambda`'s body, a `let`, an inline `(module …)`:
both checkers say "unbound variable `define-syntax`", a message to be
improved). So a template's free name only ever reaches a top-level
environment: the program's, a file's module, the standard bindings.

When macros get a narrower scope, the user and Claude lean (2026-11-08)
towards **expression-scoped macros, `let-syntax` and its kin, first**, and
against macros in the types of first-class modules:
- `let-syntax` is the general case. A macro private to an inline module is
  one scoped to the module's body, a lexical scope, so it follows.
- It forces the general mechanism: a template may name a local in scope
  where the macro is defined, which must stay that local where a use
  rebinds the name, so marks must name any scope. `#%toplevel:n` is then
  the outermost case of that.
- A macro exported through a module would have to be in the module's type
  (`moduleof`), and a use would depend on which module value reaches it:
  the signatures that compute (above) this design keeps out. A library as
  a file, `import-with-syntax` and `hide`, already covers the common need.

Not a firm statement: the user means to re-read Bawden, *First-Class
Macros Have Types* (POPL 2000; summarized in `modules.md`, item 7 and §5)
first. The user's reading of it, which Claude shares from that summary:
what is first-class there is **environments**, not macros. A macro value
is an environment frame at run time; its expander is fixed by its static
type where it is used as an operator, so expansion stays entirely static.
That continues Bawden and Rees's syntactic closures (LFP 1988), a form
paired with the environment to read it in.

Read so, a file's macros are already that shape: their expanders fixed at
compile time, their expansions indexing into one module value, `(with
%shared:key name)`. Bawden's generalization would let that environment be
any module value of a given `moduleof`, the template's free names typed by
it and the expansion naming `(with m name)` for whatever `m` reaches it:
macros typed over environments, rather than macros inside module values.
Recorded as a possibility, not planned.

## Questions for the user

Answered 2026-11-06 (the user):
- **Signatures**: Herman's tree addresses to start, each signature with a
  comment beside it saying how it would read in the names of "Binding
  signatures" above, the more readable system to move to.
- **Item 5**: a template's reference to a global is to the global as it is
  where the macro is used, as FX-26's redefinition re-runs definitions.
  Only the top level is redefined: a module's definitions never are, and
  a local binding a template names is its own, hygienically.
- **Repetition**: recursion through syntax types, as Herman's chapter 7
  writes `let*` and `cond`; ellipsis later, as sugar for it. Revised
  2026-11-08 (the user): ellipsis is primitive repetition in transcription,
  since recursion cannot splice into one form (`datatype-macro.md`).
- **Scopes as regions**: Herman's annotations first ("Where to build").
- **Labels in templates**: keywords, or `label` pattern variables; a bare
  label in a template is refused. Ordinary code is unchanged.

Open:
- Keywords (decided: `#:tag`): a sum's tag at run time a keyword, as
  proposed, or still a symbol with keywords only in the source? And flat
  products, `(product #:n n #:reply c)`, or keep the pairs?
