# Intentional divergences from the reference implementations

This project's rule, chosen deliberately, is the opposite of the Racket ports'
in [`GiffordHistory`](https://github.com/pnkfelix/GiffordHistory): those
preserve the original behaviour *including its bugs*, because their value is as
a trustworthy reference. `fixpt` implements the correct behaviour instead — and
records every difference here, with evidence, so that "conformance" means
something precise rather than "mostly agrees".

Each entry says what the reference does, what `fixpt` does, and why.

---

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

`input-stream` and `output-stream` are declared by the reference but not
implemented in either port. `fixpt` will implement them against real files.

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

### `'()` types as `symbol`, not `null`

`literal-null?` tests `(eqv? (caddr node) '())`, but under the port's NIL
emulation the quoted empty list reaches the checker as a symbol, so `(cons 1
(cons 2 '()))` gets type `(pairof int (pairof int symbol @=) @=)`. Pinned in the
corpus; under review for whether the 1987 original behaved the same way under
Pseudoscheme.

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

### `syntax-rules` is deferred

Derived forms (`let`, `cond`, `case`, `do`, `when`, `and`, `or`, `guard`, …) are
native expander forms rather than library macros. Hygienic `syntax-rules` is
scheduled for M9; the expander already has the binding class it will occupy.
