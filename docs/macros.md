# Macros: what to build for M9, and why

## Status (2026-09-24)

Steps 1 and 2 of §5 are done: `define-syntax`, `let-syntax`, `letrec-syntax`
and R7RS `syntax-rules` (`crates/fixpt-scheme/src/macros.rs`), hygienic by
renaming (`expand.rs`, "Hygiene"). The built-in derived forms are hygienic too,
so the bug in §0 is fixed. `crates/fixpt-scheme/tests/macros.rs` holds the §0
cases as regressions, the classic hygiene cases, and R7RS §7.3's own
`syntax-rules` definitions of `cond`, `case`, `and`, `or`, `let`, `let*` and
`do`, checked against the built-ins.

Step 3 is done too: SRFI 211's `er-macro-transformer` and
`ir-macro-transformer` (`crates/fixpt-scheme/src/procmacro.rs`), with
`begin-for-syntax` for helpers that transformers need. And step 4: SRFI 139's
`define-syntax-parameter` and `syntax-parameterize`, with `identifier-syntax`
and R7RS's `syntax-error`. The whole plan of §5 is implemented.

Choices made, and behaviour worth knowing:

- **An alias is an uninterned symbol with its original's name.** No source
  text can produce it, even written with `|…|` and escapes. And everything
  that works by name — `quote`, globals, error messages, procedure names —
  sees the original without a stripping pass.
- **A top-level definition that a macro introduces binds the plain name.**
  `(define-syntax d (syntax-rules () ((_ v) (define helper v))))` makes a
  global `helper` that the program can refer to. That is Twobit's behaviour,
  not fully hygienic; Racket would make the binding unreachable. Inside a body,
  an introduced definition *is* hygienic.
- **Nesting limit.** Macro uses may nest 2 000 deep; a macro whose expansion
  always contains another use of itself stops there with an error, not a stack
  overflow. The expander recurses on the Rust stack — about 3.5 KB a level in a
  debug build, 0.6 KB in release — so `fixpt` runs its command on a 256 MB
  stack. A program that embeds `Session` on a smaller thread should do the
  same.
- **A transformer runs during expansion**, before anything in its input has
  run. Its expression is expanded against the top-level environment only, so
  it can use the prelude, earlier inputs, and whatever `begin-for-syntax`
  defined, but not locals around the `define-syntax`, which don't exist yet.
  There is one global environment, not separate phases: what
  `begin-for-syntax` defines is also there at run time.
- **Collection is held off while a transformer runs**, because the expander
  holds heap values outside any root set: the constants of the program it is
  building. The heap grows instead, which never moves anything.
- **`rename`, `inject` and `compare` pause the machine.** They call `%host`,
  which suspends the engine mid-call and hands the request to the expander,
  which answers and resumes it. No primitive calls back into the expander.
- **Identifiers cross as symbols, so `symbol?`, `eq?` and `case` work on a
  transformer's input.** One whose identity is more than its name (an alias
  from an enclosing macro, a renamed identifier, and every IR input
  identifier) crosses as an uninterned symbol. That makes it `eq?` only to
  itself, and it maps back to exactly the identifier it came from. So a
  procedural macro's input keeps its hygiene when another macro produced it,
  which is the case the R7RS-large draft's ER and IR get wrong. IR
  authors who want plain names use `strip-syntax`, as in CHICKEN.
- **A syntax parameter is overridden by binding, not by name.** Inside a
  `syntax-parameterize` body, every identifier that *resolves to* the
  parameter uses the new transformer, whether it is a template's alias or the
  user's plain `it`. A user's own local binding of the name is lexical and
  wins. The override is dynamic over the body's expansion, as SRFI 139
  specifies, so a macro used in the body whose template mentions the
  parameter sees it too.
- **Identifier macros are an extension.** A `syntax-rules` rule whose pattern
  is a bare identifier matches a use of the keyword on its own.
  `identifier-syntax` (R6RS, and the R7RS-large draft) is built on it; it is
  what lets `it` stand for a hidden variable.
- **Bodies are scanned one form at a time.** A macro use, a `begin` or a
  `define-values` may produce definitions, each name is bound when it is
  found, and a `define-syntax` in a body is in scope for the rest of it.

---

Written 2026-09-24, before any of it was implemented. It surveys the design
space, says what is wrong today, and recommends a plan. Everything claimed about
another system was checked against a source (cited at the end), or run in Racket
9.3 where Racket has the feature.

## 0. Something is already wrong

The expander's built-in derived forms are not hygienic. `cond`, `delay`,
`guard`, `do`, `with-continuation-mark` and friends rewrite to syntax built from
*raw symbols* — `if`, `lambda`, `call-with-current-continuation` — and
re-expand it in the *user's* environment:

```text
> (let ((if list)) (cond (#t 'one) (else 'two)))
(#t one two)                                  ; should be one
> (let ((lambda 5)) (delay 1))
error: attempt to call a non-procedure: 5     ; should be a promise
```

So the first thing any macro work has to deliver is a way for *the expander's
own* rewrites to say "this `if` means the core `if`". Whatever mechanism does
that is also the mechanism `syntax-rules` needs. The two are the same problem.

## 1. Two questions, usually conflated

"syntax-rules vs. syntax-case vs. explicit renaming" mixes two separate
choices. Keeping them apart matters here, because the complaint that
`syntax-case` code is a bear to work with is about the second, and the choice
that is hard to change later is the first.

**A. The hygiene mechanism** — how the expander decides what an identifier
refers to after macros have moved it around. It is internal, it is the hard
part, and it is expensive to change once built.

| Mechanism | Idea | Who uses it |
|---|---|---|
| Timestamps / renaming by expansion history | Kohlbecker et al. 1986: rename everything introduced by a step | historical |
| **Renaming with aliases** | Clinger & Rees, *Macros That Work* (POPL '91): each expansion renames the identifiers its template inserts to fresh, unforgeable names, and binds each fresh name to what the original meant *where the macro was defined* | Twobit/Larceny (`src/Compiler/syntaxenv.sch`, `lowlevel.sch`), CHICKEN |
| Syntactic closures | Bawden & Rees 1988; Hanson 1991: a closure pairs a form with the environment to expand it in | MIT Scheme, Chibi |
| Marks and substitutions ("wraps") | Dybvig, Hieb & Bruggeman 1992: identifiers carry marks and pending renames; `psyntax` | Chez, Guile, R6RS systems |
| **Sets of scopes** | Flatt, POPL 2016: an identifier carries a *set* of scopes, and a binding is found by subset | Racket (since 2015), Klister |

**B. The macro-writer's interface** — what a macro author writes. Any of these
can sit on (almost) any mechanism above.

| Interface | Input is | Hygiene | Breaking hygiene |
|---|---|---|---|
| `syntax-rules` | patterns and templates | automatic | cannot, except by taking the name as an argument |
| explicit renaming (ER) | plain lists; `rename`, `compare` | **opt-in**: rename every identifier you insert | don't rename it |
| implicit renaming (IR) | plain lists; `inject`, `compare` | **automatic**: everything inserted is renamed | `inject` it |
| syntactic closures (`sc-`/`rsc-`) | forms plus environments | by closing forms over an environment | close in the use environment |
| `syntax-case` | opaque syntax objects | automatic | `datum->syntax` with a chosen context identifier |
| `syntax-parse` | syntax objects, with *syntax classes* | automatic | as `syntax-case`; or syntax parameters |
| binding specifications | a grammar annotated with what binds what | checked statically | (the point is that you don't) |

## 2. Why `syntax-case` is a bear, precisely

The same anaphoric `aif` — a macro that captures `it` on purpose — in each
interface. The `syntax-case` and `syntax-parse` versions were run in Racket 9.3;
the ER and IR versions are written to SRFI 211's definitions.

```scheme
;; syntax-case: capture by manufacturing `it` with the use site's context.
(define-syntax (aif stx)
  (syntax-case stx ()
    [(k test then else)
     (with-syntax ([it (datum->syntax #'k 'it)])
       #'(let ([it test]) (if it then else)))]))

;; explicit renaming: everything inserted is renamed by hand, except `it`.
(define-syntax aif
  (er-macro-transformer
   (lambda (form rename compare)
     `(,(rename 'let) ((it ,(cadr form)))
        (,(rename 'if) it ,(caddr form) ,(cadddr form))))))

;; implicit renaming: everything inserted is renamed automatically;
;; `it` is injected.
(define-syntax aif
  (ir-macro-transformer
   (lambda (form inject compare)
     `(let ((,(inject 'it) ,(cadr form)))
        (if ,(inject 'it) ,(caddr form) ,(cadddr form))))))
```

The costs of `syntax-case` are specific:

1. **Two kinds of variable.** Pattern variables live inside `#'…` templates and
   Scheme variables outside them. Computing a piece of output means crossing
   between the two with `with-syntax`, `quasisyntax`/`unsyntax`, or
   `syntax->datum`.
2. **Opaque input.** A syntax object is not a list. `car`, `symbol?` and `eq?`
   do not work on it, so ordinary list code has to go through `syntax-case`
   itself, or through `syntax->list`, to take input apart.
3. **Breaking hygiene means picking a context.** `(datum->syntax #'k 'it)`
   gives `it` the lexical context of the macro keyword at the use site. Choose
   another identifier and `it` means something else. This is the subtle part,
   and the reason the R7RS-large draft devotes a section to identifiers.
4. **Validation is left to you.** A malformed use either matches no clause
   ("bad syntax") or matches the wrong one. Culpepper & Felleisen's
   `syntax-parse` exists because of this. Their diagnosis is that authors must
   choose between a clear specification and a robust one. Declared shapes buy
   error messages for free — the `aif` above with `test:expr then:expr
   else:expr`, given `(aif 1 2)`, reports "expected more terms starting with
   expression".

ER and IR avoid 1 and 2 entirely, because input and output are plain lists.
They trade 3 for something simpler: *don't rename* (ER) or *`inject`* (IR),
which always means "as the macro's user wrote it". Their cost is on the other
side. ER's hygiene is by discipline: forget to rename one inserted `if` and the
macro silently captures, which is exactly the bug `cond` has today. IR inverts
that default, which is why it is the more comfortable of the two.

**IR is harder to implement than it looks.** It promises that whatever the
template inserts is renamed and whatever came from the input is left as the
user wrote it. But the transformer's output is a list of symbols, and a user's
`if` and a template's `if` are the same interned symbol. A correct IR therefore
has to *mark the input* before the transformer sees it. Afterwards it renames
the unmarked symbols in the output, as template-inserted, and strips the marks
from the rest. That is `syntax-case`'s mark-and-flip, done on plain lists. The
fascicle's non-normative IR skips the marking: it unwraps the input to bare
datums and gives `inject` the use-site context. That goes wrong when the input
itself came from another macro's expansion, since an identifier that meant
something at *that* macro's definition site is re-read at the use site. Under
the alias design of §5, identifiers inserted by an enclosing macro are already
distinct aliases and survive untouched. Only the user's plain symbols need
marking, as use-site aliases that resolve to themselves. The cost is a walk
over the input and a walk over the output per expansion: linear, but more than
ER pays, and the honest price of hygiene by default.

Racket's own answer to `aif` is neither form of capture. It is a *syntax
parameter* (SRFI 139): `it` is defined once, and `aif` rebinds its meaning
for the extent of the body. Nothing is captured, so there is nothing to get
wrong. That also ran, and gave the same answer.

## 3. Where the world has gone

* **R7RS-small** has only `syntax-rules`. That is what M9 must deliver.
* **R7RS-large** voted in 2023 to adopt `syntax-case`. The draft *Macrological
  Fascicle* builds on "syntax objects" and specifies `syntax-case`,
  `syntax-rules`, identifier operations, `identifier-syntax` and syntax
  parameters. It carries ER and IR only in a *non-normative* section, which
  defines `rename` as `datum->syntax` on the macro keyword and `compare` as
  `free-identifier=?`. It lists its own caveats: macros that test with
  `symbol?` or compare with `eq?` break, and it blames "the under-specified
  nature of the explicit renaming system itself".
* **SRFI 211** gives the low-level systems standard library names, so portable
  code can ask for `er-macro-transformer`, `ir-macro-transformer`,
  `sc-macro-transformer` or `syntax-case`.
* **Practice is split.** Chez and Guile are `psyntax`. MIT and Chibi use
  syntactic closures, and Chibi also has ER, built on them, and a `syntax-case`.
  CHICKEN uses ER and IR. Racket uses sets of scopes under `syntax-case` and
  `syntax-parse`. "Converged on `syntax-case`" is true of standards, and of
  anything that wants R6RS code to run; it is not true of implementations.

## 4. What research has added since *Macros That Work*

* **Sets of scopes** (Flatt 2016) is the simplest model known to handle what
  broke older expanders: definition contexts where a macro's meaning depends on
  definitions later in the same body, modules, and phases. Racket rewrote its
  expander around it. It is a *mechanism*, and `syntax-case`, `syntax-parse` or
  ER can sit on top of it.
* **A definition of hygiene** (Adams, POPL 2015). Earlier work defined hygiene
  by algorithm. Adams defines it as preserving α-equivalence, given the binding
  structure of the output, which finally makes "is this expander hygienic?" a
  question with an answer.
* **Declared binding structure.** Herman & Wand (ESOP 2008) proposed that a
  macro declare what binds what, so that hygiene can be checked, and macro
  *definitions* reasoned about, statically. Stansifer & Wand's Romeo (ICFP 2014)
  generalised it. Ballantyne, Gamburg & Hemann's `syntax-spec` (ICFP 2024) made
  it practical: a DSL is a grammar annotated with binding specifications, and
  the implementation gets hygiene, macro extensibility and a compiler pass for
  free.
* **Validation as a first-class concern** (Culpepper & Felleisen, ICFP 2010):
  `syntax-parse`'s syntax classes describe input shapes and produce the error
  messages.
* **Macros that know types.** Klister (Barrett, Christiansen & Gélineau, TyDe
  2020) lets a macro ask for the *type* it is expected to produce. Expansion
  "gets stuck" until type inference can answer, in an order that cannot change
  the result. This is the one directly relevant to the FX front ends. A
  type-and-effect-directed macro could ask what effect is permitted where it
  expands, which fits the facts channel the FX front ends already use.
* **Not macros at all.** Kernel's fexprs (Shutt 2010) drop the compile-time
  phase and give operators first-class environments. Staging (MetaOCaml, Typed
  Template Haskell) generates code whose hygiene comes from lexical scope of
  quotations. Both are coherent answers to a different question, and both
  would give up this project's compile-then-run pipeline.

## 5. Recommendation for fixpt

**Mechanism: renaming with aliases (Clinger & Rees), extended to record which
expansion introduced each alias.**

* **It fits what exists.** The environment is already a scope chain from
  symbol to `Binding`, with keywords as bindings (`env.rs` was written
  expecting this). An alias is a fresh, unforgeable `Sym` plus a side-table
  entry: *(original symbol, where it was introduced)*. Resolving an alias that
  nothing in the expansion rebound means looking the original up in the
  environment of the macro's definition.
* **Output stays plain Scheme.** `Datum::Symbol(Sym)` is unchanged, and `quote`
  strips aliases back to their originals, as `m-strip` does in Twobit. That
  keeps the property the metadata work relied on: every stage is a legal
  Scheme expression. It also leaves `fixpt-read` and both FX front ends
  untouched. Sets of scopes would put a scope set on every identifier in the
  shared reader's `Syntax` type.
* **It fixes §0 directly.** The built-in forms insert aliases resolved in a
  fixed *core* environment, where `if` is always the special form, so a user's
  local `if` no longer interferes.
* **ER is its native low-level interface.** ER is 44 lines in Twobit, and IR is
  a thin wrapper over it.
* **It leaves the door open.** Recording provenance — which expansion step
  made an alias — is what `datum->syntax` needs. A later `syntax-case`, if the
  project wants R7RS-large, can be built on it: an alias's provenance plays
  the part of a mark.

The case for sets of scopes instead is real: definition contexts, and
`define-library` with phases if it ever comes. It is recorded as the thing to
revisit if and when libraries arrive, rather than paid for now.

**Interfaces, in order:**

1. `define-syntax`, `let-syntax`, `letrec-syntax` and R7RS `syntax-rules`,
   complete. That means ellipsis followed by more patterns, tail patterns,
   vector patterns, `_`, a custom ellipsis (`(syntax-rules ::: (lits) …)`), and
   `(... ...)` escapes. It runs entirely inside the expander, in Rust, with no
   evaluation at expansion time. Error messages should say which rule came
   closest and where the use failed to match, with a source span. That is the
   cheap part of what `syntax-parse` buys.
2. Re-express the built-in derived forms on the alias mechanism, and add
   tests for the capture bugs in §0.
3. `er-macro-transformer` and `ir-macro-transformer` under their SRFI 211
   names. Recommend IR to macro authors: hygienic by default, input and output
   plain lists, capture spelled out. These need **a Scheme procedure to run at
   expansion time**, which the expander does not do today. It needs the engine
   callable from inside expansion, and `rename`/`compare` exposed as procedures
   that can reach the expander's environment. This is the main new engineering
   in M9, and why it comes third.
4. Syntax parameters (SRFI 139): the way to write `aif` with no capture at all.
5. *Not planned:* `syntax-case`. Revisit it with sets of scopes if R7RS-large
   compatibility becomes a goal.

**For the FX front ends:** no macros in M9. FX-87 and FX-91 have their own
sugar, which their references define. Klister's type-directed expansion is the
experiment worth doing there later, and it belongs next to the facts channel,
not in M9.

## References

- W. Clinger, J. Rees. *Macros That Work.* POPL 1991.
- W. Clinger. *Hygienic Macros Through Explicit Renaming.* Lisp Pointers IV(4), 1991.
- W. Clinger, M. Wand. *Hygienic Macro Technology.* PACMPL 4 (HOPL IV), 2020. The history, from the people who made much of it.
- E. Kohlbecker, D. Friedman, M. Felleisen, B. Duba. *Hygienic Macro Expansion.* LFP 1986.
- A. Bawden, J. Rees. *Syntactic Closures.* LFP 1988.
- R. K. Dybvig, R. Hieb, C. Bruggeman. *Syntactic Abstraction in Scheme.* LASC 5(4), 1993.
- M. Flatt. *Binding as Sets of Scopes.* POPL 2016. <https://users.cs.utah.edu/plt/scope-sets/>
- M. D. Adams. *Towards the Essence of Hygiene.* POPL 2015. <https://michaeldadams.org/papers/hygiene/>
- D. Herman, M. Wand. *A Theory of Hygienic Macros.* ESOP 2008.
- P. Stansifer, M. Wand. *Romeo: A System for More Flexible Binding-Safe Programming.* ICFP 2014.
- M. Ballantyne, M. Gamburg, J. Hemann. *Compiled, Extensible, Multi-language DSLs.* ICFP 2024.
- R. Culpepper, M. Felleisen. *Fortifying Macros.* ICFP 2010; JFP 22(4–5), 2012.
- L. Barrett, D. T. Christiansen, S. Gélineau. *Predictable Macros for Hindley-Milner.* TyDe 2020. <https://github.com/gelisam/klister>
- J. Shutt. *Fexprs as the Basis of Lisp Function Application.* PhD thesis, WPI, 2010.
- R7RS-large, *The Macrological Fascicle* (draft). <https://r7rs.org/large/fascicles/macro/1/>
- SRFI 211, *Scheme Macro Libraries*; SRFI 139, *Syntax Parameters*; SRFI 149, *Basic Syntax-rules Template Extensions*.
- Larceny's Twobit: `src/Compiler/{syntaxenv,syntaxrules,expand,lowlevel,usual}.sch`.
