# Intentional divergences from the reference implementations

This project's rule, chosen deliberately, is the opposite of the Racket ports'
in [`GiffordHistory`](https://github.com/pnkfelix/GiffordHistory): those
preserve the original behaviour *including its bugs*, because their value is as
a trustworthy reference. `fixpt` implements the correct behaviour instead — and
records every difference here, with evidence, so that "conformance" means
something precise rather than "mostly agrees".

Each entry says what the reference does, what `fixpt` does, and why.

---

## Which reference?

Worth stating plainly, because "the reference" is ambiguous and the answer
differs in kind from "the original".

Every golden in `tests/conformance/` is generated from the **Racket ports** in
[`GiffordHistory`](https://github.com/pnkfelix/GiffordHistory) —
`fx-lang/fx91/private/impl.rkt` and `fx-lang/fx87/private/impl.rkt` — and each
`.expected` file records that in its header. The checking rules implemented here
were read from those same files. So goldens and implementation are consistent
with each other by construction.

The ports are not the originals. Those are also in the archive —
`extracted/fx91/*.scm` for 1991 and `mit-psrg-fx/fx87/old-impl/*.lisp` for 1987
— and they cannot be run here: the 1987 sources are Symbolics Common Lisp over
Pseudoscheme. So **"conformant" in this project means "agrees with the port"**,
which is a weaker claim than agreeing with the 1987 or 1991 system, and it is
the strongest claim anything runnable can support.

Where the two are known to differ, it is recorded below and attributed. The
clearest case is FX-87's `'()`, which types as `symbol` because of the port's
NIL emulation; whether the original behaved the same under Pseudoscheme is a
question about `pseudo.lisp` that this corpus cannot answer, and the entry says
so rather than implying it was checked.

Where a detail has been checked against the original, the entry says that too.
FX-87's checking-failure messages are an example: the port reports
`Cannot type-check` for a rule that declines and a specific message —
`Subtyping rule violation`, `Uncomparable types`, `Wrong arguments types` — for
one that raises, and all four strings appear in `old-impl/type-check.lisp`, so
that behaviour is original rather than introduced.

## FX-91

### `[e dx1 … dxn]` projection sugar is implemented

*Report §2.4.9 documents `[e dx1 … dxn]` as sugar for `(proj e dx1 … dxn)`.*

The reader macro that implemented it is **not in the recovered archive** —
`sugar.scm:7` only refers to it ("The sugar for `[` is dealt with in the
reader"), and `utils.scm:257` confirms `[` was reserved for it. The Racket port
cannot reach the feature at all, because Racket's own reader gives `[e d]` and
`(e d)` the identical datum, so `parse-exp` never sees the symbol `proj`.

`fixpt` owns its reader, so it implements the sugar per the published grammar
(`SyntaxProfile::FX91`, `Brackets::ProjSugar`). This is the one place where
`fixpt` genuinely exceeds what the reference can check; the authority is the
report, not the archive.

### Multi-segment dot notation is recursive

*Report §2.4.7 defines `id1.id2.….idn` recursively: `a.b.c` rewrites to
`(with a (with b c))`.*

The original `parse-sugar-symbol` gets this right, splitting at the first dot
only and letting `parse-exp`'s recursion split the rest. The `#lang
fx91-hashlang` translator does not — it treats everything after the first dot as
one literal field name, so `a.b.c` looks for a field called `b.c` and fails at
run time. `fixpt` follows the report.

### `cons~` and `nil~` are bound

`sexp-module` (`standard.scm:566+`) *declares* `cons~` and `nil~` in the `fx`
module's signature but never gives them an `add-run-time` entry. The generated
Scheme therefore references an unbound variable, and evaluating any program that
uses them fails — which is why the unmodified reference dies on form 168 of its
own `tests.fx`.

This is an authentic 1991 archive bug, not a porting artifact (`fx91-hashlang`'s
own runtime supplies the same two shims). `fixpt` binds them. The golden file
records **both** outcomes for the affected form: `#value-error` for what the
unmodified reference produces, `#value-aug` for the value with the shims in
place.

### Real stream I/O

`input-stream` and `output-stream` are declared by the reference but left
unimplemented in the Racket ports (`fx91-hashlang`'s runtime says so
explicitly). `fixpt` implements them against real files, so the two corpus
cases that read `tests.fx` and `tests.list.fx` actually run.

An input port holds the whole file as a heap string with a cursor, rather than
an OS file handle. That is deliberate: a port is then an ordinary heap object,
so it survives collection and will survive being written into a heap image
without carrying a dangling descriptor.

One small extension while implementing it: `quoted-to-sexp` has no case for
`'()` and would call `fatal` on it, since `(pair? '())` and `(symbol? '())` are
both false. `fixpt` converts it to an empty `list->sexp`. No corpus case
reaches the difference.

### Reference bugs deliberately *reproduced*

A separate category, and the one place this project's rule inverts.

For a *checker*, the reference implementation is what defines which programs
FX-91 accepts. Correcting a bug in it would produce disagreements with the
182-case corpus that are indistinguishable from our own mistakes, and would
destroy the only independent signal the project has. So these are reproduced —
but with the intended behaviour named, a test pinning the actual behaviour
(`reference_bugs_are_reproduced_deliberately`), and an entry here. Reproducing
a bug knowingly and in writing is not the same as conforming to one silently.

| where                            | what it does                                                                                                                                             | what was intended                     |
| -------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------- |
| `unify-poly?` (`unify.scm:2532`) | compares `(poly-body dexp1)` with **itself**, so two `poly` types unify whenever arity and kinds agree, whatever their bodies say                        | compare `dexp1`'s body with `dexp2`'s |
| `dlambda<=?`                     | recurses with `dlambda<=?` on the bodies; a body is a type, not a dlambda, so the recursion fails immediately and two dlambdas essentially never compare | recurse with `description<=-1?`       |
| `expression=-1?`                 | dispatches `sum=?` and `product=?` with `(exp1 exp1)` — each compares a node with itself                                                                 | `(exp1 exp2)`                         |
| `product=?`                      | tests `(sum? exp2)` rather than `(product? exp2)`                                                                                                        | `product?`                            |
| `begin=?`                        | uses `map` rather than `every?`, so it returns a non-empty list — always true — and compares nothing                                                     | `every?`                              |

Three *other* bugs in the same file the Racket port already corrected, and this
follows the port: `unify.scm:102` reads `exp1` for `dexp1`, and `plambda=?` and
`proj=?` both read `dexp2` for `exp2` — in each case the correct form is visible
on the adjacent line.

---

## FX-87

### `1.0` really does read as an `int` — and we keep it

`literal-int?` (`standard.lisp:34`) tests Scheme's `integer?`, which is true of
`1.0`, and `literal-standard?` checks it *before* `literal-float?`. So `(fl+ 1.0
2.0)` is a type error in the reference — actuals `(int int)`, formals `(float
float)` — even though `complex.fx` in the original library is written with
`0.0`, `1.0`, `2.0` throughout.

This is a property of Scheme's `integer?`, not of the Racket port, so it is
faithful to the original. The conformance corpus keeps a case pinning it
(`kernel.fx`, marked `QUIRK`), and `fixpt` reproduces it. Deviating would make
the corpus meaningless; it is recorded here so nobody "fixes" it by accident.

### `floor`, `ceiling`, `truncate` and `round` give an exact integer — a divergence

All four are typed `(float) int` (`standard.lisp:114`), and FX-91 types them
the same way (`standard.scm:155`). FX-87's own host was Common Lisp, whose
`floor` of a float returns an exact integer, so the type was true there. The
Racket port runs on Scheme, whose `floor` keeps its argument's exactness:
`(floor 3.7)` is `3.0`, typed `int`. That is unsound, not only cosmetic: an
`int` that is `3.0` fails where an exact integer is needed, such as an index
(`(vector-ref v (floor 1.5))` is an error in Scheme).

`fixpt` gives the exact integer, in both FX-87 and FX-91 (each dialect's
`runtime.scm` defines the four so); an infinity or a NaN, no integer, is an
error. Case 81 (`(floor 3.7)`) carries the reference's `3.0` as `#value` and
`fixpt`'s `3` as `#value-aug`, which `reference/fx87-golden.rkt` writes for
exactly these four when the port's integer is inexact. FX-91's corpus does
not call them.

FX-87 also claimed every standard name integrable, so the bytecode engine
compiled `floor` as Scheme's primitive and bypassed the runtime's definition.
A standard name the runtime defines is no longer claimed integrable
(`Fx87Session::with_backend`).

The literal `1.0`, typed `int` by the rule above, is the same kind of
unsoundness, but a separate, earlier decision, and is left as it is.

### `'()` types as `symbol`, not `null`

`literal-null?` tests `(eqv? (caddr node) '())`, but under the port's NIL
emulation the quoted empty list reaches the checker as a symbol, so `(cons 1
(cons 2 '()))` gets type `(pairof int (pairof int symbol @=) @=)`.

**Not, in fact, a divergence — `fixpt` reproduces it.** This was marked "under
review" pending M6. The goldens settle it: case 9 is `(quote ())` with
`#type symbol`, so the behaviour *is* the reference's, and matching it is
conformance rather than bug-compatibility. Whether the 1987 original behaved the
same way under Pseudoscheme is a separate question about `pseudo.lisp`, and one
this corpus cannot answer; it is recorded here so the distinction is not lost.

### One recursive type prints differently, because cycles are found over
### different objects

Corpus case 155 —
`(lambda ((l (dletrec ((il (oneof ((nil unit) (cons (pairof int il @=))) @=))) il))) l)`
— is the single case in 155 where `fixpt`'s printed type differs from the
reference's. The reference gives two bindings and refers to them by name:

```text
(dletrec ((|#1| (oneof …)) (|#2| (oneof …))) (subr pure (|#1|) |#2|))
```

`fixpt` gives one binding and expands it in place.

The cause is representational rather than a bug in the printer.
`create-finite-dexp` finds cycles by walking **cons cells** and testing `memv`
against a trail of them, so what counts as "the same object" is a pair. Here a
type is one arena node: `(pairof int X @=)` is a single `Desc::Con`, where the
reference has a chain of four cells. The two therefore disagree about which
occurrences are shared, and about how many distinct cycles a type contains.

Matching it exactly would mean giving descriptions a cons-cell representation
purely so that cycle detection agrees — paying for the 1987 memory layout in
order to reproduce an artifact of it. The type is the same type either way, and
both renderings denote it; only the choice of where to unroll differs. Recorded
here rather than chased, and pinned by the conformance floor so it cannot
silently become two cases.

### The dynamic reference does not reach every form

FX-87's value goldens come from `#lang fx87-hashlang`, because `impl.rkt` — the
source of every other FX-87 answer here — installs no evaluator at all
(`machdep.rkt`'s `FX-EVAL-HOOK` errors by design). That path covers **120 of the
155** corpus forms. The other 25 are not skipped for convenience; the archive
cannot produce answers for them:

* **The standard forms are unimplemented there.** `record`, `select`, `one`,
  `tagcase`, `one-set!`, `delay` and `vlambda` are unbound identifiers in the
  hashlang, which never grew them.
* **A recursive type hangs it.** `(list 1 2 3)` does not finish: its type
  contains itself, and the hashlang's display path does not re-finitise it the
  way `create-finite-dexp` does for `impl.rkt`. The golden generator gives each
  case its own process and a deadline, so this shows up as a missing value
  rather than as a wedged run.

`fixpt` runs all 25. They are checked in
`crates/fixpt-fx87/tests/beyond_reference.rs`, and that file is explicit that
its expected values are **this implementation's own**, recorded to catch a
regression — not evidence of agreement with anything. The distinction matters:
120/155 is the conformance figure, and the remaining 25 are covered by a weaker
claim that is labelled as weaker.

### The ADT cluster stays stubbed

Nine identifiers in the `struct`/`structof`/`convert`/`abstract`/`extract`
cluster are called but never defined in BETA-0, consistent with
`*support-adts*` defaulting to `#f`. `fixpt` will error on them with a message
saying so, rather than inventing a design the archive does not contain.

---

## Scheme

### Mutable pairs

R7RS dropped `set-car!` and `set-cdr!`. `fixpt` keeps them, as an R5RS-compatible
extension, because **FX-91's `listof` is genuinely mutable-pair-based** and the
reference implementation depends on it.

### The Core IR lives in the heap, and per-node spans do not

`fixpt`'s Core IR is encoded as heap objects rather than held in a Rust arena,
so that a dumped image is self-contained and can be resumed. The cost is that
per-node source spans are not carried: an image would pay for them on every
node, to improve a message that is rarely better for it.

Nothing is lost where it matters. Expansion-time errors — the ones that want a
precise span — still have full spans, because the expander works on `Syntax`
and runs before lowering. What a *run-time* error needs is the procedure's
name, and that is on the `Code` object.

### `syntax-rules` is deferred

Derived forms (`let`, `cond`, `case`, `do`, `when`, `and`, `or`, `guard`, …) are
native expander forms rather than library macros. Hygienic `syntax-rules` is
scheduled for M9; the expander already has the binding class it will occupy.

### The two engines differ in closure representation, and that is visible

The AST engine's closures are `[code, env]` over a chain of environment
vectors; the bytecode engine's are `[code, v₀ … vₙ₋₁]`, flat. Both are
`ObjType::Closure` and both print the same way, so nothing user-visible depends
on it — but one consequence is worth stating plainly: **a heap holds code for
one engine or the other.** `Session::compiled()` compiles the prelude too, and
`fixpt run-image` reads which engine an image was made with rather than being
told. There is no mixed mode, and no attempt to make a compiled closure
callable from the AST engine.

This is a deliberate simplification, not a limitation discovered late. Larceny
supports mixing because it loads compiled `.fasl` files into an interpreted
heap; `fixpt` has no separate load step, because the heap *is* the program.

### Compiled `letrec` boxes more than `set!` requires

Assignment conversion boxes every assigned variable, which is standard. `fixpt`
also boxes every binding of a `letrec*` whose own initialisers capture one of
them — including bindings that are never assigned, and including the ones in
that group that are not themselves captured.

The first part is forced: a flat closure captures *values*, so
`(letrec ((f (lambda (n) (f (- n 1))))) …)` would capture `f`'s slot while it is
still unbound. The second part — taking the whole group rather than just the
captured members — is to preserve evaluation order. `letrec*` runs its
initialisers left to right, and FX-91's own test suite depends on it (Peano
numbers, where `one`'s initialiser reads the already-computed `zero`), so
`code.scm`'s `letrec` output makes that order a conformance requirement. Boxing
only some of a group would move the others' initialisers past them.

The cost is one indirection per recursive call. Patching the closures' capture
slots after building them all would remove it for the common case where every
initialiser is syntactically a lambda; that is a real optimisation to make
later, and nothing in the encoding stands in its way.

### `call-with-values` is not a tail call in either engine

R7RS calls the consumer in the tail position of `call-with-values`. Neither
`fixpt` engine does: both push a frame that holds the consumer while the
producer runs, and return through it. A loop written as a tail-recursive
`call-with-values` therefore grows the control stack.

Both engines behaving the same way is the point — it is what lets the
differential tests treat a disagreement as a bug rather than as a known
difference — and no corpus in `tests/conformance/` exercises the shape. Making
it properly tail-recursive means giving the consumer call the *enclosing*
frame's continuation, which both engines are structured to allow; it is
unfinished work, not a design decision.
