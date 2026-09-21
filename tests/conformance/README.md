# Conformance corpora

Each language's goldens are generated from the recovered original
implementation running under Racket, never written by hand. They are committed
so the Rust test suite needs neither Racket nor the archive; regenerate with
`reference/regenerate.sh`, which produces a reviewable diff.

## Record format

```
#case N
#src <the source datum, as read>
#type <type, unparsed>            |  #static-error "<message>"
#effect <effect, unparsed>
#value "<printed value>"          |  #value-error "<message>"
#value-aug "<printed value>"      -- only where it differs; see below
#end
```

## `fx91/`

`cases/tests.fx`, `cases/tests.list.fx` and `cases/tests.load.fx` are Pierre
Jouvelot's own 1991–92 test suite, unmodified, from the recovered `fx91.tar`
(MIT PSRG). 182 top-level forms.

`tests.expected` carries a type, an effect and an evaluated value for every one
of them. The reference's own `fx91-check` stops at form 168 — `sexp-module`
declares `cons~` and `nil~` but never binds them, so evaluation hits an unbound
variable. That is an authentic archive bug; the generator resets per form and
guards evaluation, so nothing truncates the run, and the affected form records
**both** outcomes: `#value-error` for the unmodified reference and `#value-aug`
for the value once the two missing primitives are supplied.

## `fx87/`

`cases/kernel.fx` is authored for this project — FX-87 has no surviving test
suite — covering the kernel, regions, subtyping and subeffecting, effect
masking, `poly`/`proj`, records, oneofs, the standard types, and recursive types
re-finitised through `create-finite-dexp`. Ten cases are deliberately ill-typed
or pin down a documented quirk; they are marked in the source.

Every expected answer still comes from the reference implementation, so these
are conformance cases rather than assertions about what FX-87 ought to do.

`kernel.expected` carries a type and an effect per case, and no values: the
FX-87 port installs no evaluator (`machdep.rkt`'s `fx-eval-hook` errors by
design). `#lang fx87-hashlang` is the archive's evaluating path and will be
driven separately when the FX-87 front end needs value conformance.

## Provenance

The FX-91 test suite is MIT Programming Systems Research Group source,
recovered in `~/Dev/LangPlay/GiffordHistory` and included here unmodified for
conformance testing.
