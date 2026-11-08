# `define-datatype` as a macro: the spike goal

Research note, 2026-11-08, from the user's question: can `define-datatype`
now be written as a macro? Not yet. This note says what it needs, and
proposes it as the macro system's next *spike goal*: an acceptance test
that a typed hygienic macro system able to express `define-datatype` has
the capabilities a language's library needs. Status: **proposed, not
built**; the two choices made (the user, 2026-11-08, §6).

## 1. The goal

A user-written macro whose uses expand to exactly what the built-in
`define-datatype` expands to (`Checker::expand_datatype`, `top.rs`), so that
the built-in could become a library macro. For the monomorphic form:

```scheme
(define-datatype shape (circle int) (rect int int))
;; is
(define-type shape (sumof (circle (productof (1 int)))
                          (rect (productof (1 int) (2 int)))))
(define circle (subr pure (int) shape)
  (lambda ((%1 int)) (sum circle (product (1 %1)))))
(define rect (subr pure (int int) shape)
  (lambda ((%1 int) (%2 int)) (sum rect (product (1 %1) (2 %2)))))
```

The family form, `(define-datatype (name (param kind) …) …)`, with
constructors `poly` in the parameters, is the stretch goal (§7).

## 2. What the macro system has now

As of stage 1b of binders of descriptions (`typed-macros.md`):
- macros that make definitions, `(-> σ defn)`, including `define-type`;
- a template's descriptions read name by name, its own binders made fresh,
  a use's types placed inside them;
- repetition only as recursion through syntax types (`mu`, Herman's
  chapter 7), each step of which makes a whole form.

## 3. What is missing

**3.1 Repetition that splices into one form.** The variants make *one*
`sumof`, and a constructor's fields make *one* parameter list.
- A macro that makes definitions can recurse to make one `define` per
  variant, but nothing can gather the variants into one `sumof`: a type is
  not where a macro's use expands.
- A constructor needs one fresh parameter per field in one `lambda`, and a
  template binds only the names it writes.

So the plan recorded so far, "ellipsis later, as sugar for recursion"
(`typed-macros.md`, "Questions for the user"), does not reach this case:
repetition has to be primitive in transcription.

**3.2 One name as a label and a value's binder.** The tag `circle` is a
label in the `sumof` and the `sum`, and the name of the constructor. A
pattern variable is one or the other today: a `bvar` placed where a label
goes is refused ("placed where its syntax type is not one the form takes
there").

**3.3 Positional labels.** The fields are labelled `1`, `2`, …, which a
template cannot count. This one needs nothing new: `(tupleof T …)` and
`(tuple e …)` are the numbered `productof` and `product`, so the macro
writes those.

## 4. Repetition: ellipsis in patterns and templates

**Proposed**: Racket's `...`, in patterns and templates, as transcription
repetition, not sugar for recursion.

**In a pattern**, `p ...` matches the rest of a list, each element by `p`.
A pattern variable under `k` ellipses has *depth* `k`, and binds a
sequence (of sequences …) of what the use gave.

**In a template**, `t ...` is `t` transcribed once for each element of the
sequences of the depth-1 pattern variables in `t`, which must be of one
length (else the use is refused, saying which). A pattern variable is
placed at its depth; one of no effect (a name, a type, a label, a `pure`
typed hole) may also be placed deeper, copied into each repetition, as
Racket's are. An expression part may not, since it would run once per
repetition (the affinity rule, as now).

**In a signature**, `(σ ...)` is sugar for the list type
`(mu l (union () (σ . l)))`, so that a signature reads as its pattern does.
Binding structure is said as for that `mu`:
- `let`'s bindings, all in the body's scope: `(export (((bvar expr) ...))
  (rho (… rib)))`, as `let-bindings` says it now;
- `let*`'s, each in the next's scope: a ribcage, as `let*-clauses` does.

The new rule is one for checking: a sequence's binders are *one* atom, the
pattern variable at depth 1, so the environments Herman's rules compare
stay finite; a reference to it under the ellipsis is to "this
repetition's", which the shadow restriction treats as one binder.

**A template's own binders under an ellipsis are made fresh per
repetition**: `(lambda ((x field) ...) (sum tag (tuple x ...)))` makes
`%x:5`, `%x:6`, … one per field. Each binder's fresh name is keyed by its
path and the repetition's indices (today by its path alone).

**Why ellipsis, not macros in description positions.** Letting a macro's
use expand where a type is would make the recursive route reach the
`sumof` (§3.1, first bullet), but not the constructor's parameters (second
bullet). It would also make descriptions an expansion target, with a
macro namespace of their own. Ellipsis reaches both, and stays within
the decided rule that a signature computes nothing: repetition follows the
shape of the use, as a `mu` does.

## 5. Tags: two routes

**(A) A syntax type `tag`**: a name the use gives that is both a label
and a value's binder, its own label. Placed where a label goes, it is
written as given (a bare label, which the core forms take); placed as a
binder, it binds the constructor under the use's name, as a name a use
gives always is. It exports a value's binder (`(rho (ℓ var))`) like a
`bvar`. Small, and local to macros.

**(B) Keyword constructors** (`typed-macros.md`, "A hypothetical
extension: a keyword as a sum's constructor", the user's, 2026-10-30, not
decided): `(#:circle 1)` constructs the sum, so a datatype needs no
constructor procedures, and the macro takes only `label` parts. No dual
role at all; the macro is a `define-type` and nothing else. But it is the
larger language change sketched there: tags as keywords at run time, flat
products, a transition for every program that writes tags bare, and the
arity rule (one member, the value itself), which a macro would need
clauses by shape for.

## 6. The user's choices

Decided (the user, 2026-11-08):
1. **Ellipsis is primitive repetition** in patterns and templates (§4),
   replacing "ellipsis as sugar for recursion".
2. **Tags by (B), keyword constructors**: `(#:circle 1)` constructs the
   sum, and the macro takes `label` parts; the spike waits for them, and
   their design settles what `typed-macros.md`'s "hypothetical extension"
   left open. Route (A), a `tag` syntax type, is not taken.

## 7. The spike

The macro, with (A):

```scheme
;; As named: ((name dvar) (variants ((t tag) (fields type …)) …)), defining
;; `name` and each `t`.
(define-syntax define-data
  (-> (export (dvar ((tag type ...) ...)) (rho (A dvar) (… each tag var)))
      defn)
  ((_ name (t field ...) ...)
   (begin
     (define-type name (sumof (t (tupleof field ...)) ...))
     (define t (subr pure (field ...) name)
       (lambda ((x field) ...) (sum t (tuple x ...))))
     ...)))
```

How the export of every repetition's tag is written is open: the
signature language needs a way to say "each of these", `(rho (… var))`
above, which §4's sequence atoms give a meaning to.

**Acceptance**:
- the expansion of each `define-datatype` test program's datatypes by
  `define-data` checks as the built-in's does (by both checkers, which
  agree), and runs to the same values on every machine;
- a datatype whose fields name it (a recursive one: `define-type`'s name
  is in scope in itself), and one whose tag is the name of a top-level
  value elsewhere (hygiene: the constructor is the use's, the template's
  `x`s are fresh);
- refused alike by both front ends: variants of different shapes than the
  signature says, and a template placing `field ...` at the wrong depth.

**Stretch**: the family form, its constructors
`(poly ((p k) …) (subr pure (field …) (name p …)))` with `plambda`, the
parameters a `dvar` sequence in scope in the fields' types.

## 8. Steps

1. Ellipsis in patterns and templates, both front ends: matching,
   depth checking, transcription, fresh names per repetition; `(σ ...)`
   in signatures; sequence atoms in Herman's checking. Tests: a `my-let`,
   a `my-let*`, a `my-cond` written with ellipsis, the existing recursive
   ones unchanged.
2. Tags, as chosen (§6).
3. `define-data`, the acceptance tests of §7.
4. If it passes, `define-datatype` in `top.rs` and the FX-26 front end
   could become that macro, in a standard library of macros (which wants
   the `#%fx` module of `lang-items.md`).

## 9. Open questions

- How a signature says the binders of each repetition (§7).
- A use whose sequences differ in length where one template ellipsis
  joins them: refused at the use, or also where the macro is defined when
  the signature says the lengths agree? Racket refuses at the use.
- Ellipsis depth greater than one in signatures, `((σ ...) ...)`: needed
  by `define-data` (variants, then fields). Fine for matching and
  transcription; for binding, a sequence of sequences is still one atom.
- Typed holes under an ellipsis (the typed tier): each repetition's hole
  of the one type the signature says; a template check per clause still,
  not per repetition. Later.
