# FX-26: a grammar

A reference grammar for FX-26 as the front ends accept it today
(2026-10-05). It is written from the Rust parser, which is the reference
(`crates/fixpt-fx26/src/parse.rs` for types and expressions,
`kinds.rs` for description functions, `modules.rs` for what a module's
types are checked as, `top.rs` for top-level forms). The parser written in
FX-26 (`parser.fx`, `parser-load.fx`) agrees with it on the forms below,
bar a few corners at the edges. `docs/fx26.md` says what the forms mean.

It is not context-free, and does not try to be. FX-26 is read as
S-expressions first, and a name means what its binding makes it: the same
symbol can be a type, a region, an effect, a size or a convention. Where a
production depends on that, it says so with a side condition in `{ … }`.

## Notation

```
x ::= a | b        alternatives
x*  x+  [x]        zero or more, one or more, optional
( … )              a list, as written in FX-26 source
"lambda"           that symbol, literally
{ … }              a side condition, which the grammar alone cannot say
```

Everything else in a production is a nonterminal. `name` is any symbol
that is not `@`-prefixed. Where the parser expects a symbol bound in a
particular way (a type variable, a region variable, …), the production
says `type-var`, `region-var` and so on: lexically each is a `name`.

## Lexical syntax

FX-26 is read with the reader's FX-26 profile
(`crates/fixpt-read/src/profile.rs`, `SyntaxProfile::FX26`):

```
datum      ::= list | atom
list       ::= "(" datum* ")"
atom       ::= integer | real | string | char | boolean | unit | symbol
boolean    ::= "#t" | "#f"
unit       ::= "#u"
quoted     ::= "'" symbol                      ; sugar for (quote symbol)
region-constant ::= "@" name                   ; a symbol beginning with @
```

- Case matters (no case folding).
- `[` and `]` are reserved: they are not parentheses.
- Comments: `;` to the end of the line, `#| … |#` (nestable), and `#;`
  before a datum.
- No datum labels (`#0=`): nothing in FX-26 is a cyclic datum.
- Integers are exact, in any radix the Scheme reader takes (`#x`, `#b`,
  …). Past the fixnum range (±2^60) a literal stands for arithmetic on
  fixnums that makes the bignum.
- A real literal is an `f64`.

## Programs

A program is a sequence of top-level forms. Definitions may come in any
order (they are declared ahead), and at the REPL may wait for what they
mention (`,pending`).

```
program    ::= top-form*

top-form   ::= definition
             | "(" "define-type" name type ")"
             | "(" "define-type" "(" name param+ ")" type ")"        ; a type family
             | "(" "define-type" name dlambda ")"                    ; a description function
             | "(" "define-generative" name type ")"
             | "(" "define-generative" "(" name gen-param+ ")" type ")"
             | "(" "define-datatype" dt-head variant+ ")"
             | "(" "define-effect" name effect ")"
             | "(" "private-regions" region-constant* ")"
             | expression

definition ::= "(" "define" name expression ")"
             | "(" "define" name type expression ")"
             | "(" "define*" name type lambda ")"     ; latent `(read (globals …))` found
             | "(" "define-rec" rec-binding+ ")"

rec-binding ::= "(" name type lambda ")"

param      ::= "(" name kind ")"
gen-param  ::= "(" name kind ")" | "(" name kind "+" ")" | "(" name kind "-" ")"
               { a region or place parameter takes no variance }

dt-head    ::= name | "(" name param+ ")"
variant    ::= "(" name type* ")"
```

- `define-generative` also defines `up-name` and `down-name`, the
  conversions between the new type and its representation.
- `define-datatype` is sugar, expanded as it is read: a `define-type` of a
  `sumof` of `productof`s, whose members are labelled `1`, `2`, …, and one
  constructor `define` per variant, `(tag e …)`.
- In `define name type expression`, the `poly` binders at the top of
  `type` are in scope in `expression`.
- A `define`d `lambda` is in scope in its own body.

## Kinds and binders

```
kind       ::= "region" | "place" | "effect" | "type" | "data" | "size" | "conv"
             | "(" "=>" "(" kind+ ")" kind ")"   ; a description function's: what it takes, what it gives
               { at least one kind in the list, each any kind, an arrow kind included;
                 it gives a type, data, an effect, or another function;
                 one that gives an effect takes no types, data or functions }

binders    ::= "(" binder* ")"
binder     ::= "(" name kind ")"
             | "(" name "region" place ")"      ; a region that won't outlive the place
             | "(" name "data" place ")"        ; data at the place, or the heap
```

## Descriptions

A *description* is whatever a binder can be bound to: a type, a region, an
effect, a size or a convention.

```
description ::= type | region | effect | size | convention | function

function   ::= fun-var                                 { bound with an arrow kind }
             | fun-name                                { define-type of a dlambda }
             | family-name | generative-name          { with parameters, not applied }
             | "ref" | "icell" | "pairof" | "listof" | "arrayof" | "mark-key"
             | dlambda
             | "(" "select" module-var name ")"       { a module's type constructor }
             | "(" fun-var-or-name description+ ")"  { one that gives a function }

dlambda    ::= "(" "dlambda" binders description ")"  { at least one binder }

fun-var-or-name ::= fun-var | fun-name                { a name bound to a function }
```

A description function is applied where a type or an effect is written,
`(function description …)`: a `dlambda` applied is reduced, one that only
applies a function to its parameters in order is that function, and a
variable applied stays an application, equal only to one of the same
function to equal descriptions (`docs/research/higher-kinds.md`).

Which one is meant shows in its shape (`@x` is a region, `(read …)` an
effect, a natural literal a size), or for a bare name, in how the name is
bound.

### Types

```
type       ::= base-type
             | "void"
             | "nat"                                   { when `nat` is not bound }
             | type-var                                { bound with kind type or data }
             | type-name                               { define-type, dletrec, mu }
             | generative-name                         { define-generative with no parameters }
             | "(" family-name description+ ")"        { define-type with parameters }
             | "(" generative-name description+ ")"    { define-generative with parameters }
             | "(" "subr" [conv-form] effect "(" subr-param* ")" type ")"
             | "(" "poly" binders type ")"
             | "(" "proves" proposition ")"
             | "(" "nat" size ")"
             | "(" "nlist" type size [place] ")"
             | "(" "ref" type region ")"
             | "(" "icell" type region ")"
             | "(" "place" place ")"
             | "(" "pairof" type type region ")"
             | "(" "listof" type region ")"
             | "(" "arrayof" type region ")"
             | "(" "mark-key" type region ")"
             | "(" "prompt-tag" type type effect region ")"     ; answer payload effect region
             | "(" "composable" type type effect region ")"     ; argument answer effect region
             | "(" "bloblet" "(" ("fields" | "frozen") type* ")" region ")"
             | "(" "productof" ("(" label type ")")* ")"
             | "(" "sumof" ("(" label type ")")* ")"
             | "(" "dletrec" "(" ("(" name type ")")* ")" type ")"
             | "(" "mu" name type ")"
             | "(" "moduleof" module-component* ")"
             | "(" "select" module-var name ")"        { module-var: a variable bound to a module;
                                                         name: its `abs` or `desc` component }
             | "(" function description+ ")"          { a function to a type, applied }

base-type  ::= "int" | "bool" | "char" | "string" | "unit" | "symbol" | "datum"
             | "i32" | "u32" | "i64" | "u64" | "f64" | "f32"
             | "tword" | "wcell" | "wglobal"            ; the compiler written in FX-26's

subr-param ::= type
             | "(" name type ")"     { name is no type, type form or keyword:
                                       a named parameter, which later types may
                                       `select` from (a dependent procedure) }

conv-form  ::= "(" "conv" convention ")"

proposition ::= "(" "<=" type type ")"
              | "(" "poly" binders "(" "<=" type type ")" ("(" "<=" type type ")")* ")"

module-component ::= "(" "abs" (name | "(" name+ ")") abs-kind ")"   ; abstract; in scope after
                   | "(" "desc" name (type | dlambda) ")"             ; transparent; in scope after
                   | "(" "val" name type ")"                          ; a value; not in scope in types
                   { each name once, across all three }

abs-kind   ::= "type"                             ; an abstract type
             | "(" "=>" "(" kind+ ")" "type" ")"  ; an abstract type constructor

label      ::= name | positive-integer
```

- `moduleof`'s components may come in any order, but a type in one may
  mention only the `abs` and `desc` names before it. A `desc` is a type or
  a `dlambda`, not a function's bare name (`(desc f listof)` is refused).
  An `abs` is a `type` or a constructor to `type`: no `data`, and no
  function that gives a function.
- A module's type fits another's that has fewer values, or the same in
  another order, or `abs` where it has `desc`; not the reverse, nor a
  constructor for a type (`docs/fx26.md`, Modules).
- `(select m n)` is read where a type is written; `m` must be a variable
  that is bound to a module there, and `n` one of its `abs` or `desc`
  names, or it is refused. A procedure type's parameter written `(name
  type)` may be selected from by the types after it in the `subr`, its
  result included; the checkers show that as `(select $1 t)`, which is
  not input.
- A recursive type (`dletrec`, `mu`, a self-mentioning `define-type`) must
  go through a constructor, not only through names.
- A type family may mention itself only with the same descriptions.
- A recursive type may not go through applications alone: `(define-type
  (fix (f (=> (type) type))) (f (fix f)))` is refused.
- A module's `define-generative` with parameters is an abstract type
  constructor: its `up-name` and `down-name` are polymorphic in them.
- The standard environment defines these generative types, used as
  `(name description …)`: `(vsubr effect type type)` (a variadic
  procedure: its effect, each argument's type, its result), `(flatlayout
  type)`, `(flatarrayof type region)`, `(identity type region)` and
  `(eqtable type type region region)`.

### Regions and places

```
region     ::= region-constant                     ; @name: private if `private-regions` said so
             | "heap"
             | "const" | "acyclic"                 ; frozen data, anywhere
             | "(" "const" place ")"               ; frozen into place
             | "(" "acyclic" place ")"             ; frozen and never written: no cycles
             | region-var                          { bound with kind region or place }

place      ::= region                              { one that is a place: bound with kind
                                                     place, or by letrena or letreap }
```

### Effects

```
effect     ::= "pure"
             | "spin"                                     ; may not terminate
             | effect-var                                 { bound with kind effect }
             | effect-name                                { define-effect }
             | "(" ("read" | "write") (region | globals) ")"
             | "(" ("alloc" | "goto" | "comefrom" | "await") region ")"
             | "(" "maxeff" effect* ")"                   ; union
             | "(" effect-function description+ ")"       { applied; the description's kind is its parameter's }

effect-function ::= fun-var | fun-name | dlambda      { one that gives an effect; not a `select` }

globals    ::= "@globals"                                 ; every global
             | "(" "globals" name+ ")"                    ; those globals
```

### Sizes

```
size       ::= natural-integer
             | "finite"                         ; some number, not known
             | size-var                         { bound with kind size }
             | "(" "+" size+ ")"
             | "(" "-" size natural-integer ")"
```

### Conventions

```
convention ::= "cellular" | "native" | "fx"
             | conv-var                         { bound with kind conv }
```

## Expressions

```
expression ::= integer | real | string | char | boolean | unit
             | name                                    ; a variable
             | "(" "quote" name ")"                    ; a symbol; also 'name
             | lambda
             | "(" "vlambda" (name | "(" name type ")") body ")"
             | "(" "rlambda" expression params body ")"       ; a closure made in a region
             | "(" "plambda" binders body ")"
             | "(" "proj" expression description+ ")"
             | "(" "the" type expression ")"
             | "(" "convention" convention expression ")"
             | "(" "if" expression expression expression ")"
             | "(" "cond" ("(" expression body ")")* "(" "else" body ")" ")"
             | "(" "and" expression* ")"
             | "(" "or" expression* ")"
             | "(" "begin" body ")"
             | "(" "let" "(" ("(" name expression ")")* ")" body ")"
             | "(" "let*" "(" ("(" name expression ")")* ")" body ")"
             | "(" "letrec" "(" ("(" name type expression ")")* ")" body ")"
             | "(" region-form name body ")"
             | "(" "letfreeze" "(" name place ")" body ")"
             | "(" "product" ("(" label expression ")")* ")"
             | "(" "extract" expression label ")"
             | "(" "sum" label expression ")"
             | "(" "tagcase" expression arm* [else-arm] ")"
             | "(" "acyclic" expression "(" name expression ")" expression ")"
             | "(" "confirm-nat" expression "(" name expression ")" expression ")"
             | "(" "confirm-length" expression (natural-integer | name)
                   "(" name expression ")" expression ")"
             | "(" "prompt" expression expression expression ")"   ; tag body handler
             | "(" "module" module-item* ")"
             | "(" "load-module" string ")"
             | "(" "with" module-var body ")"
             | bloblet-form
             | "(" expression expression* ")"          ; an application

lambda     ::= "(" "lambda" params body ")"
params     ::= "(" param-decl* ")"
param-decl ::= name                     { only where the lambda is checked against
                                          a type that says the parameter's }
             | "(" name type ")"

body       ::= expression+              ; an implicit begin

region-form ::= "letregion"             ; a region for typing; its data is the heap's
              | "letfreeze"             ; a region, its data frozen into the heap at the end
              | "letrena"               ; a place: an arena, reclaimed when the body ends
              | "letreap"               ; a place: a heap of its own, also collected
               { the name is written without @ }

arm        ::= "(" label name body ")"                  ; binds the payload
             | "(" label "(" name* ")" body ")"         ; binds a product's members, in order
else-arm   ::= "(" "else" name body ")"                 { last }

module-item ::= "(" "define-generative" name type ")"
              | "(" "define-generative" "(" name binder+ ")" type ")"  ; a type constructor
              | "(" "define-type" name (type | dlambda) ")"
              | "(" "define" name [type] expression ")"
              | "(" "define-rec" rec-binding+ ")"

bloblet-form ::= "(" "make-bloblet" expression expression* ")"           ; bytes field …
               | "(" "rmake-bloblet" expression expression expression* ")" ; region bytes field …
               | "(" "bloblet-ref" expression natural-integer ")"
               | "(" "bloblet-set!" expression natural-integer expression ")"
               | "(" "bloblet-freeze" expression ")"
               | "(" "bloblet-byte" expression expression ")"
               | "(" "bloblet-set-byte!" expression expression expression ")"
               | "(" "bloblet-bytes" expression ")"
```

- A `module` holds only the five items above, and `define*`, as at the
  top level: the globals the procedure reads found, a module's own names
  not among them (it may not be in a recursive group with others, as at
  the top level, where it is in no `define-rec`). Its types each see those
  before them; its values see each other, as a `letrec*`'s: a typed
  lambda (a `define` with a type, or a `define-rec` member) may name any
  of them, but any other value, made as its item is, may not reach one
  not made yet, through the lambdas it names (refused, naming the chain).
  Not `define*`, `define-effect`, `private-regions`, `define-datatype`, a
  type family `(define-type (f p) …)`, a bare expression, or a variance
  mark (`(a type +)`) on a `define-generative`'s parameter.
- A module's `define-generative` makes `up-name` and `down-name` for the
  items after it, and for them alone: `with` does not bring them out. A
  `define-rec` binds only `lambda`s. A `module` is an expression, and may
  be an item's value.
- `(with m body)`: `m` is a variable bound to a module, not an
  expression. It puts the module's `val` names in scope in `body`, which
  is one or more expressions (no definitions); its types are named with
  `select`, not by name.
- `(load-module "file")`: the file is a string literal, and its forms are
  `module-item`s, as if written in a `module`, and also a
  `define-datatype` with no parameters. A file with any other top-level
  form or a bare expression is refused. It sees only the standard
  environment. A relative path is from the program's directory (the
  current one at the REPL); an error in the file is said at the
  `load-module`, with where in the file.

Derived forms, as the parser expands them:

| form                              | stands for                                                                    |
| --------------------------------- | ----------------------------------------------------------------------------- |
| `(and a b …)`                     | `(if a (and b …) #f)`; `(and)` is `#t`                                        |
| `(or a b …)`                      | `(if a #t (or b …))`; `(or)` is `#f`                                          |
| `(let* ((x e) …) body)`           | nested one-binding `let`s                                                     |
| `(cond (t e …) … (else e …))`     | nested `if`s; the `else` is required (FX has no unspecified value)            |
| `(vlambda (xs T) body)`           | `(%vlambda (lambda ((xs (listof T acyclic))) body))`, a `vsubr`               |
| `(acyclic e (x b) else)`          | `(let ((v e)) (if (acyclic? v) (let ((x (certify-acyclic v))) b) else))`      |
| `(confirm-nat e (n b) else)`      | `(let ((v e)) (if (nat? v) (let ((n (certify-nat v))) b) else))`              |
| `(confirm-length e k (x b) else)` | `(let ((v e)) (if (length-is? v k) (let ((x (certify-length v k))) b) else))` |
| `'name`                           | `(quote name)`; only a symbol can be quoted                                   |

## What is not syntax

Most of what a program calls is not grammar but the standard environment
(`crates/fixpt-fx26/src/standard.rs`): references (`new`, `get`, `set`),
pairs and lists (`cons`, `car`, `list`, …), arrays, strings, arithmetic,
control (`cwcc`, `abort-current-continuation`, `call-with-composable-
continuation`, marks), `apply`, and the rest. Each is an ordinary variable
with a type, applied like any procedure; `,apropos` and `,help` at the
REPL list them.

The keywords, which no `subr` parameter may be named for (so that `(name
type)` reads as a named parameter only when it cannot be anything else),
are listed in `top.rs` as `KEYWORDS`, and the type forms in `parse.rs` as
`TYPE_FORMS`.
