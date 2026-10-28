# Claude's choices

Decisions made while working without asking (the user's, 2026-10-10:
"whenever you have to make a decision, use your best judgement, and log
your choice"). Newest last; each says what was chosen, over what, and why.

## TODO.md §69: `with` shadows applied description functions (2026-10-10)

1. **What is read.** In a `with` body, `(f d …)` is read as `((select m f)
   d …)` for the innermost `with`'s `m`, falling back to the next `with`'s,
   then to what `(f d …)` means outside. Same shape as bare names
   (`with_selected`), so the two read alike.
2. **What falls back.** When `m` does not give `f`, the *application* node
   is linked to the outer reading, not the `select` node. Rejected: making
   the fallback a constant `dlambda` ignoring its arguments, because the
   `select` map is keyed by `(m, f)`, and two applications of one `f`
   (`(pairof (f int) (f bool))`) would then share one fallback.
3. **What is not shadowed.** Heads that are type forms (`listof`, `subr`,
   `pairof`, … : `TYPE_FORMS`, FX's `k-type-forms`) are never shadowed, as
   base types are not for names alone.
4. **Arguments read by shape.** Each `with` level reads the arguments
   again with `parse_d` (by their shape, kinds checked once `f` is known,
   `check_apps`), as `((select m f) d …)` written out already is.
5. **The outer reading's errors.** If `f` is bound outside, the outer
   reading is made eagerly and its errors are reported even where `m`'s
   `f` would have fit; the same as for bare names today. Simpler, and the
   case (an outer `f` of a different kind shadowed by `m`'s) is rare.
6. **Error wording** where neither `m` nor the outside gives `f`: "`f` is
   not a description function, nor one a module opened by `with` gives",
   parallel to the names' "`n` is not a type, nor one …".
7. **Effect functions applied, `(e d …)` in an effect, are not shadowed.**
   A module's effect function cannot be selected at all yet (`effect_app`
   reads a name or a `dlambda` head, no `select`), so there is nothing for
   `with` to put first; left for when that exists.

## TODO.md §69: `include` and `extend` of modules with abstract types not named (2026-10-10)

1. **Types, not text.** The TODO suggested splicing a literal module's
   items (`(module …)`, `(load-module "f")`) into the including one, as
   OCaml's `include struct … end`. Chosen instead: at the type level, a
   module that is not a name (literal, loaded, made by a call) has its
   abstract types taken in as the new module's own abstract types (an
   existential unpacked and packed again), its values by path as before.
   This covers every such expression, not just literal text, needs no
   change at run time, and keeps one way of combining (the reshape).
   Splicing would also have had to re-check the items in the new scope.
2. **Fresh variables.** Each taken-in abstract type gets a fresh variable
   (`abs_taken`, `k-abs-own`), with one substitution over all the sides
   and the module's own items. A procedure's result type is parsed once,
   so two calls share its variables; without this, two modules including
   `(make 1)` and `(make 2)` could share a type. (Binding to a name
   renames them anyway, so this is belt and braces, but it costs little.)
3. **`extend` replacing an abstract type.** `e1`'s names, abstract or not,
   replace `e0`'s. If something kept (a value of `e0` not replaced, or a
   description) still mentions the replaced abstract type, refused:
   "`x`'s type mentions the first module's `t`, which the second's `t`
   replaces". Rejected: keeping it under a hidden name (an existential
   that can't be named outside), which FX-91 does not describe.
4. **Order of the abstract types.** `include`: the included modules' own,
   in order, then the module's own. `extend`: `e0`'s kept, then `e1`'s.
5. **Name clashes in `include`.** An abstract type taken in is "defined
   twice" if the module or an earlier include already has that name as an
   abstract type or a description. The Rust checker missed the case of
   the module's own description against an included abstract type; fixed
   in both.
6. **`(hide (include …))` hides the abstract types too.** They are names
   the include brings in, so they are marked hidden, as its values and
   descriptions are. An exported type mentioning one is then refused, as
   for any hidden abstract type (TODO.md §69's remaining item).
7. **The old refusal tests** (`include-abstract.fx`, `extend-abstract.fx`)
   now run; I rewrote them as programs giving answers rather than keep
   tests for an error that no longer exists.

## `(abs (f (a type)) type)`, an abstract constructor by its parameters (2026-10-10)

The user's `okasaki.fx` wrote this, and it was read as `(abs f type)`: a
list after `abs` was names, and what was not a name was passed over.

1. **Accepted, not only refused.** `(abs (f (a kind) …) type)` is `(abs f
   (=> (kind …) type))`, as `define-generative` writes its parameters; it
   is what one reaches for first. Refusing it alone would have been the
   smaller change.
2. **Telling the two lists apart.** A list of names only is several
   abstract types, as before; a name then `(name kind)`s is a
   constructor; anything else (a name among parameters, a parameter
   first, a `(name kind)` of three) is refused: "an abstract type
   constructor is `(abs (f (name kind) …) type)`". `(abs (f) type)` stays
   one abstract type `f`.
3. **The result is `type`.** As `(abs f (=> … type))` must give a type;
   `(abs (f (a type)) (=> (type) type))` (curried) is refused rather than
   read as `(=> (type) (=> (type) type))`.
4. **No variance marks.** `define-generative`'s `(a type +)` is not taken:
   what a description function is given counts as invariant
   (`docs/fx26.md`, Higher kinds), so a mark would say nothing.
5. **Parameter names are not checked** for repeats: they name nothing, as
   in `(=> (type type) type)`.
6. **When it is checked.** The list's shape with the names (before "appears
   twice"), the kinds with the component, in both checkers, so they fail
   alike.

## A name applied in a type that is none, said by name (2026-10-10)

1. **Wording.** `(queueuof a)` is refused with "`queueuof` is not a
   description function", in the words of `docs/fx26.md` and of `with`'s
   "`f` is not a description function, nor one …". Rejected: "is not a
   type constructor", plainer but a second name for one thing.
2. **One message for unbound and bound.** `(int int)` says the same: `int`
   is bound, as a type, and is no function either; telling the two apart
   would need a second lookup for no better advice.
3. **A head that is no name** (`(5 int)`, `()`) still says "expected a
   type".

## Two variables of one name, told apart in a mismatch (2026-10-10)

The user's okasaki.fx met "a (moduleof …) is expected here, and this is a
(moduleof …)", the two alike: `(the sig e)` inside `(plambda ((f effect))
…)`, `sig` a `poly` over its own `f`.

1. **Primes.** The first free variable of a name, in the order the
   message is read, keeps it; the next is `a'`, then `a''`. A prime
   cannot be in a name (the reader reads it as `quote`), so it is never
   mistaken for one. Rejected: `a.1`, which looks like the fresh regions'
   `@r.1`, real names of their own.
2. **A line saying so**: "`a` and `a'` are different variables, each
   named `a`", after the effect's delta, so the first line still stands
   alone and what rewrites it (`expected_and_found`, `k-rewriting`)
   keeps the line.
3. **Bound ones left alone.** A `poly`'s and a `dlambda`'s binders, and a
   `moduleof`'s abstract types, are printed where they are bound; two
   types each binding `a` are not a clash.
4. **Where.** Only the "a W is expected here, and this is a G" message
   (`Checker::expect`, `k-expect`), where the two types meet. Other
   messages show one type, or name variables by themselves.
5. **How, in two checkers alike.** Each printer prints a variable as a
   mark (`\u{1}`, how, its number, `\u{1}`) while the flag is on, and the
   marks are named after, from the text: the two printers build strings
   in different orders (Rust's `subr` prints its parameters before its
   effect), so naming as printed could disagree. The FX printer only
   reads the flag, so no printer's effect changed.

## Suffix refs, the runtime (TODO.md §77, 2026-10-10)

1. **The owner is an index from the heap's start, not what a tag-`100`
   word holds.** The spec said both "exactly what a tag-100 value holds"
   and "a word index that fits 34 bits"; a tag-`100` word holds the
   address over 8 (`Heap::ix` subtracts the heap's base), ~44 bits. The
   index fits, matches the spec's address formula (base + 8 × owner +
   offset), and needs no relocation in an image.
2. **One conversion in `copy_out`, not a case at every site.** A suffix
   ref is forwarded as its owner's bloblet pointer and rebuilt; every
   root and field reaches the collector through `copy_out`, so roots, the
   scan, minor collections, cards, arenas, reaps and the code area follow.
   `Value::index()` is left meaning a pair's or bloblet's address; sites
   that read an index after `is_ref` (the barrier, the remembered-set
   check, weak references, images, the verifier) were each given a case.
3. **Writes only into a program's own bloblets and flat arrays**, as
   `%bloblet-set-byte!` allows only plain bloblets: otherwise a ref into a
   string, a bignum or code would write where nothing else may. Reads from
   any bloblet.
4. **Reads and writes at any alignment**, byte by byte in the runtime; the
   in-line native path, when it comes, can require alignment by type.
5. **Weak references to suffix refs work** (follow or die with the owner)
   rather than being refused: it cost four lines in `weak_moved`.
6. **A read must fit**: offset + width ≤ B, beyond the spec's offset < B
   for making one.
7. **Native code untouched.** Its write barrier marks the card whatever is
   stored; nothing compiled dereferences a suffix ref until the language
   types them, so the in-line `ubfx`/`lsr #37` path waits (TODO.md §77).
8. **Names** `%suffix-ref…`, after `%bloblet-…`: runtime-level, a `%`
   prefix, not yet FX-26 names.

## Bloblet types by width (TODO.md §77, 2026-10-10)

1. **Today's syntax is the lower bound** (the user's plan); no exact form
   until something needs one.
2. **What may be forgotten**, one rule (`forgettable`): of a frozen
   bloblet, data at its place (`is_data_at`), so a frozen bloblet type
   that is data stays so; of one not frozen, a walk that allows base types,
   data variables near `R`, refs/arrays/i-cells/mutable pairs and bloblets
   only at `R`, frozen pairs, bloblets and nlists in the heap or `R`'s
   place, products, sums and unions of those; nothing else (procedures,
   type variables of kind `type`, generative types, modules, prompt tags…
   refused, conservatively).
3. **`@heap` storage hidden is refused**; frozen heap data is allowed.
   `storage_regions` would not see heap storage behind a hidden field;
   refusing costs little and can be relaxed.
4. **One walk of its own**, not `regions_in` and `storage_regions` reused:
   the FX-26 subtype test runs before `check-resolve.fx` and
   `check-holds.fx`, which have those walks.
5. **The data walk moved from `check-data.fx` to `check-sub-env.fx`**, so
   the subtype test (given `check-sub-env`) reaches it; `check-data` is
   given `check-sub-env` and imports it back, its exports unchanged.
   Rejected: a new module file, which would need the conductor's wiring
   and a types file for four functions; `check-sub-env` already had what
   the walk uses (`check-types`, `check-effects`).
6. **Inference matches the pattern's fields** against an actual bloblet
   of at least as many, both checkers.
7. **No message of its own** for a refused widening yet: it says "a W is
   expected here, and this is a G", as any mismatch. A line saying which
   field could not be forgotten, and why, would help; for later.

## The kind `flat` and `(blobref B F)`, types (TODO.md §77, 2026-10-10)

1. **`flat` as a kind beside `data`**, its descriptions types (`D::Type`)
   that are flats: a scalar's base type, or a variable of kind `flat`.
   Unlike `data`, not a subkind of `type`: a flat variable, or a family's
   flat parameter given one, is refused where a type is wanted.
2. **The scalars' names are both**: `f64` as a flat is the type `f64`, the
   type its bytes are read as. So a family's flat parameter given `f64`
   may stand as a type (harmless: it is one); given a flat variable, not.
3. **`blobref` a standard generative type**, `(blobref (b type +) (f
   flat)) b`, number 5, declared in one text for both checkers, as
   `flatarrayof` is: to the safety analyses it is its owner, so escape,
   masking, storage and knots see what they should, with no new type
   form. `b` covariant: the owner is only given out. `f` invariant.
   Rejected: a new type form (`Ty::BlobRef`), a case in every walk of
   both checkers for what a generative type gets for free.
4. **The owner is any type here**: binders have no subtype bounds, so a
   primitive's type cannot say "`b`, a bloblet at `r`". The operations
   will be syntax (as `bloblet-ref` is, for its literal index), reading
   the owner's type, its region from it.
5. **FX-26 kind code 7**; a variable's kind kept in `k-flats`, reset as
   `k-datas` is. `k-try-kind` and its kin moved from `check-read-descs.fx`
   (1003 lines with the change) to `check-read-helpers.fx`.
6. **The name `blobref`**, the user's; `flatref` named the kind instead.

## The `blobref` operations (TODO.md §77, 2026-10-10)

1. **Syntax, not primitives**: `blobref-at`, `blobref+`, `blobref-owner`,
   `blobref-offset`, `blobref-get`, `blobref-set!`, kept as the bloblet
   forms are (`BlobletOp`, `e-bloblet`), so they read the owner's own type
   and its region, which no primitive's type could name without bounds.
2. **A new blobref's flat from the type checked against**, as
   `make-bloblet`'s region is, not a flat written in the form: no type
   syntax in the FX-26 parser's expression trees. Without one: "which flat
   a new `blobref` points to is said by the type it is checked against".
3. **Read and write only scalars, named**: a blobref to a flat variable is
   not read ("only a scalar's bytes are read or written"); generic code
   over flats passes refs, and the code that knows the scalar reads.
4. **The layout reaches the compilers as a fact at the form's span**, the
   way an `extract`'s field index does (`Facts::field_index`, `k-extracts`,
   `c-field-at`), since the runtime cannot tell an owner's scalar.
5. **Runtime primitives** `%fx26-suffix-ref-get` and `-set!`, taking the
   layout code and reading or writing as a flat array's element is
   (`flat_value`, `flat_bits_of`); the others are the runtime's own
   `%suffix-ref…`.
6. **`blobref-at` masked** in the Rust checker as every other form is (its
   first draft returned before masking).
7. **The evaluator written in FX-26 refuses blobrefs** for now: it keeps a
   suffix as an array of bytes, and would need a value form of its own.
8. **Size debts kept**: `k-bloblet-op` moved from `check-rules.fx` to
   `check-synth.fx`, and `r-bloblet` from `regcode-core.fx` to
   `regcode-helpers.fx`, each given the knot's procedures (`k-synth`,
   `k-check`; `r-exp`, `r-prim`) as arguments; both files shrank, and
   their debts were lowered.

## Flat products and arrays (TODO.md §77, 2026-10-10)

The user chose natural alignment and `extract` on blobrefs, products and
fixed-length arrays before sums; and set a rule: no operation copies more
than a word unless its name says so.

1. **A flat product is the product type node**, read where a flat is
   wanted, as the scalars are their value types; fields laid out in the
   order written (the reader keeps it).
2. **A flat array is standard generative type 6**, `(flat-arrayof (f flat)
   (n size)) int`, not a new type form; written `(arrayof F n)` where a
   flat is wanted, or in a type when `n` is a literal (a region never is),
   so `define-type` can name one. Its length a literal for now.
3. **Natural alignment**, C's: scalars at their size, products padded to
   their widest member (`flat_layout`, `k-flat-layout`).
4. **`extract` of a blobref** to a flat product gives a blobref to the
   field; the offset reaches the compilers as the extract's field fact past
   `BLOBREF_FIELD` (2^40), as `RESHAPE_PATH` marks reshape paths: one
   channel, no new fact kind.
5. **`(blobref-index r i)`**, a new form, since an index is an expression;
   its fact is `n << 32 | size`, and the run time checks `0 ≤ i < n`.
6. **No copy larger than a word**: projections give blobrefs; only a
   scalar is read out, so the user's rule holds with nothing more.
7. **Moves to keep sizes**: the type-level blobref helpers from
   `check-synth.fx` to `check-read-helpers.fx` (which `check-synth` is now
   given), `r-extract` to `regcode-helpers.fx`; the projection rule in
   `check-rules.fx` is one line, `k-extract-blobref`.
8. **Run-time failures in `bloblet-errors/`**: each machine says a run-time
   error its own way, which the compilers' tests would count as a
   disagreement.

## Blobrefs in the evaluator written in FX-26 (TODO.md §77, 2026-10-10)

1. **A value form `o-bref`**, an owner (an `o-blob`) and an offset, over
   the evaluator's own bloblets, whose suffixes are arrays of bytes; not a
   host suffix ref, so the evaluator stays in its own values.
2. **The checker's facts copied in at the start** (`ev-begin!`, as the
   reshapes and `with`s are), so `eval` reads only the evaluator's store
   and its effect stays `evals`; looked up by span, as the compilers do.
3. **Four standard primitives**, `f64->bits`, `bits->f64`, `f32->bits`,
   `bits->f32`: the evaluator, reading a scalar from bytes by hand, needs
   them, and a program may too. Rejected: an evaluator-only primitive.
4. **Equality of two blobrefs** compares their owners' field arrays
   directly (`ev-same-blob?`): `ev-other-eq?` is a `define*`, which may
   not be in a recursive group with `ev-eq?`.
5. **The evaluator's test now runs `bloblet/`**, every program agreeing
   with the lowering.

## Blobrefs in native code (TODO.md §77, 2026-10-10)

1. **In `direct.rs` only**, the compiler of register code to arm64, where
   flat arrays are in line too; the cells' assemblers (`native.fx`, the
   Rust one) call out, as they do for flat arrays.
2. **In line: read, write, step, owner, offset.** `blobref-at` and
   `blobref-index` stay call-outs (made less often than used).
3. **Bounds from the owner's header, found through its trailer**: a read or
   write must lie within `B`, so that the inline path refuses what the
   primitive refuses (an unaligned 4-byte read at `B - 1` reads padding
   otherwise). An owner without a trailer, or with a large header, goes to
   the primitive. Every bloblet FX-26 makes has a trailer.
4. **A read's layout a compile-time constant** (`prim2imm`), so each read is
   one specialised sequence; a write is a call-out instruction with three
   registers, dispatching on the layout at run time, as `flat_set` does.
5. **Writes check the owner's kind** (a program's bloblet or a flat array)
   and its suffix-frozen bit, as the primitive does.
6. **Never collects**: the read, owner, offset and step join the
   primitives register code calls with values in registers, in both
   register-code generators' lists; an `f64` read boxes from the free
   space, or calls the primitive when there is no room.
7. **Measured** (10 million elements, fill then sum by stepping): 1.09 s
   against 0.92 s for the same loop over a flat array, whose elements stay
   raw `f64`s; a blobref's `f64` is boxed on the way out. Unboxing it as
   `reps` does for flat arrays is a follow-up.

## Flat sums (TODO.md §77, 2026-10-10)

1. **A key written as a bare first item**, `(sumof u8 (0 f64) (7 i32))`,
   not `(key u8)` as the TODO had it: a list first could be a variant
   named `key` (of type `u32`, a type too); a bare symbol cannot be a
   variant. No key: the tag indexes the owner's fields.
2. **A label may be 0, everywhere** (both readers, both checkers): Rust's
   discriminants start at 0; a positional label 0 was refused before for
   no reason I found.
3. **`(blobref-variant! r 'l)`: the label a literal**, a quoted name, or a
   number where the sum has a key; the result a blobref to the variant, so
   one form writes the tag and reaches the payload. The FX checker's
   resolved expressions keep no symbol's name, so the resolver keeps this
   one operand as a constant whose type holds the name and whose value is
   -1 (`k-label-const`, `k-variant-label`).
4. **Layout**: the tag at offset 0, `w` bytes (1 without a key); the
   variant at `w` rounded up to the widest variant's alignment; the size
   padded to the larger of the two alignments. The variants' order does
   not matter (a tag is a label, not a position).
5. **The compilers' fact**: `w + 8 * numeric + 256 * p`, on the `tagcase`
   or the `blobref-variant!`, through the field-index channel.
6. **`tagcase` on a flat sum**: each arm binds one name, a blobref to its
   variant; a product's fields are not taken apart (that would copy), the
   message the one a product arm already gets. Coverage is checked as for
   a value sum, and the tag again at run time. `else` binds the blobref as
   it is. Effects: reading the owner's region; `blobref-variant!` reads
   and writes it.
7. **Messages**: "has no tag" shows the sum of blobrefs the arms see, in
   both checkers (the FX one sees that sum).
8. **Owner fields compared by `eq?`** (a word compare), the first match
   written; a tag naming no field, and a numeric label too wide for its
   key, are run-time errors.
9. **Register code calls out**, so a flat `tagcase` declines in a leaf;
   native code calls the primitives. Reading the tag in line is a
   follow-up (TODO §77), as is an index wider than a byte.
10. **Size debts**: `check-rules.fx` lowered to 1331 by moving
    `k-in-scope-check` to `check-read-helpers.fx` (given the knot's
    `k-synth-as`); `regcode-core.fx` kept at 1403 by moving `r-bloblet`'s
    fact lookup and `r-done` into it.

## Opt-in distinct regions, a prototype (2026-10-11)

1. **Per binder, `(r region distinct)`, not pairs `(distinct r1 r2)`**: a
   distinct binder aliases nothing else its procedure sees, which is what
   `&mut` says, and needs no new form in a `poly`'s binder list. Lucassen's
   rule (§3.6.3) for that binder: distinct from every other binder's region
   and from every region the `poly`'s type mentions besides its binders
   (frozen regions exempt, as nothing may write them).
2. **Known distinct**: different constants, the heap or globals (not
   `@globals` against a global); a fresh region; a `letregion`'s region
   (Lucassen's `PRIVATE`, marked distinct when made); a `distinct` binder
   of an enclosing procedure. Two other region variables are not known
   distinct.
3. **Stored beside the variable** (`Arena::set_distinct`, FX-26's
   `k-distincts`), as a region bound is, so `poly`'s shape is unchanged.
4. **Subtyping**: a `distinct` binder of `a`'s must be one of `b`'s for
   `a ≤ b`.
5. **Messages** say which binder and region, but not which region the
   type mentions, so that both checkers, which order regions differently,
   say the same thing.
6. **The survey's diagnostic stays on its branch**; its report is in
   `docs/research/anti-aliasing-survey.md`, marked with the commit it
   measured.

## The FX-26 machines by name (TODO.md §78, 2026-10-11)

1. **The old flags keep their old defaults when given one by one**: a name
   (or nothing, the fastest) sets all three; any of `--fx26-run`,
   `--cellular-machine`, `--calling-convention` given means the rest
   default as before (`rs-scheme-vm`'s parts), so every existing script
   and test means what it meant. A name and the parts together are refused.
2. **The banner says the machine's name**, worked out from the parts too,
   and the parts' flags when they name no machine.
3. **bench accepts its old column names** in `--machines`.
4. **The Emacs mode** now passes no machine flags, the default being the
   machine it named.
5. **The native machine's step-limit trap** now reads "evaluation step
   limit exceeded", as the other machines say it, not "out of fuel".

## The import pass, `(hide (include m))` (TODO.md §69, 2026-10-11)

1. **Only the modules a file is given** (its `lambda`'s parameters), not
   the types files it loads: including whole types files collides on
   about 2,000 re-exported type names (each types file re-exports others'
   types for its signatures) and on the module values they bind
   (`check-types-types` in each), which `include`'s "a name given twice is
   refused" forbids. Relaxing that rule for "the same thing twice" is a
   language change kept for later; the given modules alone carry most of
   the lines.
2. **A file whose signature gives on something it imports from a module
   keeps all of that module's import lines**, and does not include it: the
   re-export must stay a definition, and an include of the module would
   give the name twice.
3. **Files with clashes**, 15 of 59 (a name two given modules both give,
   `k-union` and `k-one` through `check-read`'s re-export, or one the file
   defines itself): every given module included but those that clash,
   whose import lines stay.
4. **Measured back to back** against the commit before (peval's front-end
   phases, old and new builds alternated): no difference past noise.
5. **A type or effect name two `include`s give is one name when it is the
   same both times** (each a subtype of the other), a value still refused:
   the types files re-export each other's types for their signatures, the
   same type under the same name. A different type under one name is still
   "defined twice". The module's own `define-type` against an included one
   likewise.
6. **The types files hide their module bindings** (`(hide (define m
   (load-module …)))`): each binds the modules it names types from, the
   same loads in most of them, which an include of two would give twice as
   values; nothing selected them through a types file.
7. **Hidden marks per kind**: `%hidden:name` for a type, `%hiddenv:name`
   for a value (an abstract type's `up-`/`down-` values), since a module
   may have a type and a value of one name (`check-read`'s `k-items`).
8. **What the types pass keeps**: a types module whose type family a file
   uses (an included family is not applied in a declared type yet), and a
   module of which the file's own signature gives on a value; a re-exported
   *type* keeps only its own line, the module included still.
9. **Committed with a possible 3–5 % cost** in the FX-26 compiler's phases
   (measured under load, back to back; see TODO.md §69), the pass being
   the user's priority; the likely cause and a remedy are in the TODO.

## §77 native follow-ups (2026-10-11, autonomous)

1. **An inlined body's facts go with it** (`c-resolved-at`): the FX-26
   compiler, keeping a body to inline, made every `extract` it had a fact
   for a `bloblet-ref`, a blobref's field (`%suffix-ref+`) too, and left a
   flat `tagcase`'s layout and a `blobref-get`'s where the next form's
   table could not find them. Found because `fixpt compile` said the two
   compilers disagree on the shapes benchmark; `direct.rs` declined the
   bad `field` (too far), which is why nothing ran wrong. Now a fact is
   kept in the node, as a span below -1 that `c-field-at` reads back,
   rather than a new node kind: no other pass changes.
2. **A never-collecting primitive on a value and a constant is
   `prim2imm`**, in both register compilers' `r_prim` / `r-prim-imm`, not a
   call-out: a blobref's step (`%suffix-ref+` of an `extract`'s offset, a
   flat sum's variant), its read (`%fx26-suffix-ref-get`) and a flat sum's
   tag (`%fx26-flat-tag`, now counted as never collecting). No new op.
3. **In line natively** (`direct.rs`): a step by a constant (by 0, only
   the tag checked), a numeric key's tag (`ldurb`/`ldurh`/`ldur w`, encoders
   added), an `f64` read that only `f64` operations use (raw, as a flat
   array's element already was), and `blobref-index` inside the general
   call-out (as `blobref-set!` already was). An index-key tag (labels in
   the owner's fields) still calls the primitive.
4. **A new register-code op, `prim3imm p x k`** (`RESULT := p(RESULT, x,
   REGk)`), rather than a fast path in the call-out only: a call-out
   keeps the procedure from being a leaf, so a loop's `f64` stays boxed
   in the frame. The constant in the middle fits `blobref-set!` and
   `blobref-variant!` as their primitives are; `blobref-index` got a twin
   primitive with its operands in that order (`%fx26-blobref-index`)
   rather than a reordered original, which the lowering and the cellular
   compilers use.
5. **`r-prim3`'s operands simply**: `a` made and kept in its place, `b`
   made into a fresh register, `a` reloaded; not `r_operands`' cleverer
   orders, which the FX-26 helpers file cannot reach (it is in the
   knot of `regcode-core.fx`, which is at its size limit).
6. **A flat `tagcase` arm reuses the blobref's and tag's places** for its
   ref, and a scrutinee variable is used where it is: a leaf has eight
   registers, and the shapes sum's fast version ran out without both.
7. **A self-call's argument that is its own parameter stays put**
   (`r-self-temp`, both compilers): general, it changes every loop that
   passes a parameter on unchanged; measured no slower (peval's phases
   re-run back to back: `fx arm64` 16.6 ms, as before).
8. **Arrays of a length not literal left for the user**: a size variable
   in `(arrayof T n)` is a type-system extension (my notes: optimize from
   what the type system proves; extensions discussed first). Done instead:
   an index key's tag and variant in line natively (a field read, and a
   short loop over the owner's fields by identity), which needed nothing
   new of the types.

## §69's cost, measured (2026-10-11, autonomous)

1. **Measured the import pass against the commit before it**, built side
   by side, alternated: peval's phases ~3 % (as feared, small), but the
   front end's own checking 33 % (Rust) and 64 % (FX-26) slower, which
   the earlier peval-only measurement missed. Fixed the cause found by
   profiling (the bucket made quadratically) rather than revert the pass.
2. **Kept only what measured**: a constant-time `free_into` (a counted
   bound set) and a memo of `k-with-used`'s scan were tried and changed
   nothing measurable; both reverted, the diff kept to the fix.
3. **Left**: `fx check` still ~14 % above before the pass; the per-call
   `with` cost (~3 % when the compiler runs) and its remedy as TODO §69
   says.

## §73, and what waits (2026-10-11, autonomous)

1. **§75 (`string->int`) left for the user**: wanted as FX-26 in §22's
   library, whose prelude design (how a program gets it) is still open
   with the user; a Rust primitive would go against "no Rust at all".
2. **§73's errors placed at the load's start, zero width, in both**: the
   FX-26 parser keeps only where a load starts; Rust's spans were the
   whole load form. Agreeing on less was simpler than carrying the end
   through the loaded files' list.
3. **A file loaded more than once is placed at its first load** (where
   Rust read it), in both: the walk out then always reaches the program.
4. **A blobref's bounds by its type, proposed, not done**: checking that
   all of `F` fits where a ref is made would let every step and read skip
   the owner's header (TODO §77); but `blobref-at` would then fail where
   it makes a ref that today fails only where read. A change of meaning,
   so written up for the user instead.

## Native profiling of the front end (2026-10-11, autonomous)

1. **Profiled natively, not by cells**: `FIXPT_SYMBOLS` + `fixpt-symbolize`
   on `sample`. The cell counts (`FIXPT_PROFILE_PHASE`) pointed at
   `k-has-name?`; natively it was under 1 %, and the real top was the
   FX-26 assembler's `arm-times-pow2`. Recorded both in TODO §43.
2. **`arithmetic-shift` counted as never collecting** (a bignum it makes
   only allocates), so register code calls it in line; and the cellular
   convention's register compiler (where the front end runs) got the
   fixnum fast paths `direct.rs` already had (`int_fast`), rather than
   moving the front end to the native convention.
3. **The Rust checker's `env` as `Bindings`** (a slice to read, an index
   by name beside it, changed only by methods), not a `HashMap` beside a
   public `Vec`: the compiler found every place that changed it.
4. **Not done: a memo of free names for `mask`** (about a fifth of the
   Rust `check`): a stale memo would mask too much, which is unsound, and
   `with`'s facts are set as checking goes; for the user (TODO §43).
5. **Not done: path compression in `k-resolve`**: it would make a read a
   write, changing an effect many signatures name.
6. **Native returns by `br x30` instead of `ret`: committed, then
   undone.** The eight per-commit benchmarks favored it (`closures`
   21.4 → 9.2 ms: a recursion 1000 deep overflowed the return stack
   predictor; `fib` 2.8 → 3.1). The MLton ports, timed both ways, were
   about 3 % worse (`fib`, `peek` +10 %; `merge` −24 %): the broader set
   decided. Data in docs/performance.md; ideas in TODO §52.
7. **Native run time, by sampling the ports** (after the `br` lesson,
   each change timed on the programs it was for and the MLton set):
   only changes that remove work were kept (sums and products in line, a
   kept call-out vector, constant kinds, `string-append`/`char-in?` in
   place, `array-length` by `prim1`); `fixpt-heap`'s ban on `unsafe` kept
   (`string-append` shifts words rather than viewing them as `u32`s).
8. **kayak's two reports (2026-10-11).** Shift counts: a fixed-width
   shift takes any count, a bignum's too, modulo its width, as
   `docs/fx26.md` already said and the FX-26 evaluator did;
   `arithmetic-shift` by a count past a fixnum is 0 or -1 rightwards and
   fails leftwards (unless of 0) rather than trying to allocate it.
   Self-application through a type binder (F17): marked at instantiation,
   not by making calls through any type variable `spin` (which would mark
   every `map`); only procedures in positive positions it can rebuild
   (procedure, result, `poly`, product, sum), since a pair's or a
   reference's type may be written and cannot change; that the rest is
   closed is argued, not proved.
9. **kayak's I/O (TODO §84), the choices not asked about (2026-10-12).**
   Made while building the five stages; each easy to change.
   - `bytevectorof` a new generative type (heap bytevector at run time,
     an array of `u8` to the safety analyses), not `(arrayof u8 r)` nor
     a flat array of `u8`; a reader's `bytevector` in a `datum` left
     opaque, so a quoted bytevector is still refused.
   - `u8` and `i8` made last among the base types in both checkers, so
     no existing type id moved.
   - `io` not a reserved word: a program may still name a variable `io`.
   - `io-error`'s kinds: the eight Rust's `ErrorKind` maps onto most
     usefully, `other` for the rest.
   - `read-line` strips `\n` and `\r\n`; a line not UTF-8 is a failure
     and reading goes on after it.
   - `clock`'s zero is near the run's start (the first time asked), so
     its nanoseconds stay a fixnum.
   - `fixpt run FILE… -- ARG…` for the program's arguments; `fixpt run`
     gives a program no step budget unless `--step-limit` is given (the
     REPL's budget stopped a 4 MB loop).
   - `fixpt eval` keeps its "exit 1 if the program fails"; only `run`
     exits 70, though both honour `exit`.
   - The cellular machines' traps say themselves in the native machine's
     words (`Trap`'s `Display`), not Rust's debug form; the run's word is
     no longer an irritant of the message.
   - Not done, for the user: whether a failing `pure` call may be dropped
     (`rs-scheme-vm` drops `(error …)` when its value is unused; native
     code does not): TODO §85.

## An x86_64 back end: the hand-encoded cellular machine first (2026-10-11)

The user's: "work autonomously on a native backend for x86_64 Linux, to
eventually be in FX26 itself".

1. **The hand-encoded cellular machine first**, and the words Rust compiles
   into it (`cellular::x64`: `generate`, `routine_body`, `assemble_word`),
   over register code or the native convention: its only contract is
   `State` and the `callout` hook, all control is already Rust's
   (`control.rs`, `round_trip`), and the differential tests
   (`tests/cellular.rs`, `frames.rs`, `code_gc.rs`) check it against the
   Rust machine unchanged. `native.fx` compiles for this machine, so it is
   also the one an FX-26 port follows.
2. **A module beside the arm64 code, not a trait over both.** The arm64
   routines are written in its idioms (post-increment loads, `stp`, `csel`,
   `cbz`); a trait of ~60 operations would have meant rewriting upstream's
   most-edited file. The x86_64 routines follow the arm64 ones in order and
   in the names of their steps (`save`, `push_return`, `enter_cur`, …), so
   a change to one is made to the other by reading them side by side.
3. **No BASE register; the fuel in the state.** BASE is always 0 (values
   are addresses); x86_64 has 15 registers to the 19 the arm64 machine
   names, and `sub qword [st + fuel], 1` costs about what `subs` does.
   Only `ST` (r15) must survive a call into Rust; the rest are saved and
   loaded as on arm64.
4. **`#t`/`#f` from the state** (`cmov` from `[st + tru]`), which already
   held them, rather than 10-byte immediates.
5. **Every branch to a label 32 bits**, and a jump to the next instruction
   dropped when its label is bound: no `long_branches` retry, no
   relaxation. Trap stubs go after the whole word, so each cell's code
   falls into the next.
6. **Code counted in bytes in `NativeMachine`**: `install_bytes` and
   `reserve_bytes`, with `install` and `reserve` kept for arm64's `u32`s
   (the FX-26 compiler's `place_code`, tests), so no caller changed.
7. **Encodings checked as arm64's are**, against GNU `as`
   (`tests/x86_64.rs`), each instruction assembled alone (a symbol per
   line, so lengths come from `nm`), and the disassembler reading each back;
   chosen to be the assembler's own encodings (the `rax` short forms, REX
   only where needed), so that the test needs no exceptions.
8. **What "available" means is split**: `AVAILABLE` stays "every machine
   here" (arm64), and `CELLULAR_AVAILABLE` is the hand-encoded machine and
   its compiled words (arm64 or x86_64). `DirectMachine::new` now refuses
   off arm64 itself, since a code space can be made on x86_64.
9. **`fast` on x86_64 is `fx-cells-rsjit-cellcc`**, the fastest there on
   every program `fixpt bench` times (fib 254 → 27 ms against the Rust
   interpreter, tak 87 → 10), and the front end runs on it too.

## x86_64 in FX-26: `x86_64.fx` and `native-x64.fx` (2026-10-11)

1. **The cellular compiler first**, as for arm64 (`native.fx`, step 11c):
   `native-x64.fx` makes exactly the bytes `cellular::x64::assemble_word`
   does, over `x86_64.fx`, which makes exactly `x86_64.rs`'s; each tested
   against its Rust oracle (`tests/x86_64.rs`: 15 061 encodings;
   `tests/native_x64.rs`: every word of the front end). Register code and
   the native convention in FX-26 wait on TODO §81, as for arm64.
2. **A file beside `native.fx`, not one over both instruction sets**, for
   the reason the Rust machine is (above, item 2); and since `native.fx`
   is upstream's and still moving. The two share `layout.fx` and the
   generator of their layouts (`fx26_module_of`).
3. **Both compilers in the front end**, the conductor applying each, and
   Rust choosing by the machine it runs on (`syn::assemble_reachable_by_fx26`):
   the front end cannot know which machine runs it, and one more module
   costs it little beside the 135 it has.
4. **A complete layout for x86_64** (`native-x64-layout.fx`, generated
   with the arm64 one's shared part), not the arm64 one plus registers:
   both define `n-ip` and the rest, and a module cannot include both.
5. **`place_code` takes bytes** (`PlaceCode`, starts in bytes): arm64's
   words become bytes where FX-26's ints are read (`syn.rs`), so
   `place_word` serves both machines.
6. **Lists of bytes, not ints of instructions**: each encoder gives its
   instruction's bytes as a list (`x86-bytes`), made with `cons` at the
   encoders' region; `(list …)` would make one at a region of its own.

## Register code on x86_64 (2026-10-11)

The user, asked which `REG`s should live in memory: "go right ahead"
(to choose them from counts).

1. **REG1–REG3 in registers, REG4–REG8 in the state** (`State::regs`).
   `fixpt regcode-survey --front-end` now counts each `REG`'s uses as an
   operand: of the front end's 129 801, REG1 has 61 289, REG2 48 724,
   REG3 9 137, REG4 4 608, and REG5–REG8 fewer than 3 000 each, so three
   in registers keep 92% of them there. Larceny's x86 back ends kept about
   four. `RESULT` is `rax`, `REG0` stays `CLO`.
2. **No pool pointer.** arm64 keeps `IP` at the word's last field because
   its loads reach only 32 KB up; a 32-bit displacement from `CUR`
   reaches every field, so `IP`'s register (`r14`) is a fourth scratch
   register, beside `rcx`, `rdx` and `r11`, and the machine's other
   registers keep their roles. That is what lets the code share the
   hand-encoded machine's sequences (`save`, `load`, the return stack).
3. **The link on the machine stack, at most one deep.** A call is a
   `call`; `save` pops its return address into the frame's link slot
   (where arm64 stores `x30`), `pop` pushes it back, and `return` is
   `ret`; a leaf keeps it on the machine stack, and in `leaf_link` around
   a call-out, as arm64 keeps `x30`. Return points are 8-aligned (no-ops
   before the `call`) so a link in a frame reads as a fixnum, as on
   arm64; the adapter pushes 0. The assembler checks that every path
   agrees on where the link is, and refuses code where they do not.
4. **The machine's exit restores `rsp`** from the state (`machine_sp`,
   stored by its entry), so a trap or an exit with a link pushed leaves
   cleanly.
5. **`ret`, for now.** arm64 returns by `br`, since a deep recursion
   overflows the return predictor (CLAUDES_CHOICES, "Native profiling").
   On x86 `call` pushes onto the predictor anyway, so `ret` keeps calls
   and returns paired; not yet measured against `pop`/`jmp`.
6. **`fast` on x86_64 is register code** (`fx-regs-rsjit-cellcc`); the
   front end runs on it (`register_machine`), and the bootstrap reaches
   its fixpoint so. Against the compiled cellular words, in ms: fib 27.5 →
   12.5, tak 10.0 → 3.6, loop 76.6 → 26.0, helpers 123.1 → 14.9,
   lists-region 129.2 → 13.4, closures 123.4 → 29.7, captures 23.1 → 18.4.

## The native convention on x86_64 (2026-10-11)

The user: "Go for it" (TODO §112's next item, `direct.rs`).

1. **A file of its own, `direct/x64.rs`, step for step**, as the cellular
   machine's and register code's x86 forms are: the trampoline, the common
   routines and `procedure`, each beside its arm64 original's name. The
   Rust side (call-outs, the stack cache, continuations, stack maps,
   `place`, `restore`) is shared unchanged, since the frames are laid out
   alike. `direct.rs` now keeps code as bytes (`Proc::code`,
   `Compiled::len`), and chooses by `X86`.
2. **The same frame**: `[fp]` the link, `[fp + 8]` the return address,
   `[fp + 16]` the map, slots from `[fp + 24]`, the same sizes. `save`
   moves the return address `call` pushed (the frame's top word) to
   `[fp + 8]`; `pop` pushes it back, so `return` is `ret` and a tail
   call's callee finds it where a `call` leaves it; a leaf keeps it where
   the `call` left it. Calls and returns stay paired for the return
   predictor.
3. **REG1–REG3 in registers, REG4–REG8 in the state**, as register code
   has them (the same counts decide), and the eight scratch registers
   named for arm64's (`X9`, `X11`–`X17`), so that each helper reads as its
   original. Fuel, the stack's limit and code's run address, pinned on
   arm64, are the state's (`sub qword [st + fuel], 1`; `cmp rsp, [st +
   stack_limit]`; `add r9, [st + delta]`): x86 has the memory operands, and
   not the registers.
4. **A code bloblet's fields `rip`-relatively** (`mov r, [rip + d]`), as
   arm64 reads them `pc`-relatively; every label a 32-bit displacement, so
   no code is too long (arm64's `too_far` has no counterpart).
5. **Raw `f64`s in `xmm0`/`xmm1`**, `ucomisd` read so that a NaN compares
   false as arm64's `fcmp` conditions do (`<` and `<=` the other way
   round, `=` without parity); rounding by SSE4.1's `roundsd` (a procedure
   that rounds declines on a processor without it); `abs` and `neg` on the
   bits. `i64::MIN / -1` is itself, as `sdiv` has it (`idiv` would fault).
6. **Where a REG in the state meets a helper that uses every scratch
   register** (a blobref's element, write or variant in `prim3imm`), the
   primitive is called instead: arm64 never meets it, its REGs being
   registers.

## Stencils on x86_64 (2026-10-12)

1. **The routines in LLVM's `preserve_none` convention** (`extern
   "rust-preserve-none"`, nightly's `rust_preserve_none_cc`), not SysV's
   C: C passes six integer arguments in registers, the routines take
   eight, and keeps five registers for the caller, which every stencil
   then pushes and pops. `preserve_none` passes all eight in registers
   and keeps none: `-O2`'s `dup` is a load, a store and the inlined
   dispatch. Rejected: two of the machine's registers moved into the
   state (a load and store more in most routines, and the two machines'
   sources would differ beyond a signature).
2. **`st_start` stays C, and calls the first routine** where arm64's
   `become`s it: its prologue keeps the host's registers, which no
   routine keeps, and a routine that returns (a trap, the end) returns
   through it, as on arm64 it returns to the host.
3. **Branches checked in the assembly LLVM writes beside the object**
   (`--emit obj=…,asm=…`), not in the bytes: an x86 instruction's length
   needs a decoder of every form LLVM may use, and the assembly names each
   branch's target, a label inside the stencil or an indirect one. The
   relocation check is the same ELF reader's, for `EM_X86_64`.
4. Measured (ms, `fixpt bench`): within 1.06–1.55 of the hand-encoded
   machine (`fib` 52.7 against 36.7, 1.44; arm64's README has 21.8
   against 16.1, 1.35), as on arm64 the cost of Rust's code for the same
   routines.

## Register code compiled by FX-26 on x86_64 (2026-10-12)

1. **`native-x64-regs.fx`, a module of its own over `native-x64.fx`'s
   assembler** (its bytes, labels, trap stubs and the machine sequences
   the two share, through `native-x64-asm-sig`), not more of
   `native-x64.fx`: that file would pass the thousand lines `fx_size`
   allows, and the two compilers share the assembler as the Rust ones share
   `Asm`. It is two files for the same reason: `native-x64-regs-ops.fx`, of
   no state, its fast paths and what it does inline (`int_fast`,
   `shape_test`, `bump_words`, `inline_op`) and the helpers they share;
   `native-x64-regs.fx`, the rest, with the compile's state. Its steps are
   `regcode.rs`'s, named `rg-` and the Rust name.
2. **What it knows of the machine, generated**
   (`native-x64-regs-layout.fx`, `fx26_regs_module`, kept so by
   `tests/layout.rs`): its registers, the state's fields, each
   instruction's operand count, the primitives register code names (by
   number and by name), which never collect, and the kinds a shape test
   takes. FX-26 compares primitives by name, as the Rust compiler does.
3. **A primitive, `tword-bits`, and the `tword-…` ones taking register
   words**: a constant operand goes in an instruction as its bits, which
   only fixnums could be read as before.
4. **Placed where `fx-compiled` places words** (`syn::assemble_reachable_by_fx26`):
   a word with register code has it compiled by FX-26 and placed, and the
   adapter into it, also FX-26's, as its entry, as `compile_register_word`
   does; a variadic one, or one of more than `REGS` arguments, stays
   stack code. The machine is `--cellular-machine fx-registers`,
   `fx-regs-fxjit-cellcc`, x86_64 only (refused on arm64, which has no
   FX-26 compiler of register code yet, §81).
5. **Checked byte for byte** (`tests/native_x64.rs`): every register word
   of the front end compiled with register code, 4,014 words and 18 MB,
   the same bytes and resume points as `assemble_register_word`, and the
   adapters for every count; every test program runs alike on the machine
   (`tests/compiler.rs`). Where Rust returns an error, FX-26 notes the
   first and returns it.

## The x86_64 back end rebased onto main (2026-10-17)

The user: "I suspect we need to rebase our branch atop main", then "lets
move with steps 1 2" (step 1: each commit building, the native convention
off on x86_64 until step 2 re-ports it; the push is the user's).

1. **Our section of `TODO.md` renumbered §84 → §105**: main's §84 is I/O.
   (Renumbered again on 2026-10-19 to §112, and the memory test §106 to
   §113: main had filed its own §105–111 by then.)
   Our fix of `knot-spin.fx` under the native convention dropped: main
   fixed it its own way (`check-hold-breaks!`, `DONE.md` §90).
2. **The x86_64 cellular machine, register code and their FX-26 ports
   follow main's arm64 ones** (time slices, preemption, `TODO.md` §92,
   §93, §97): the entry goes on from the state when `start` is 0; a word's
   poll at its first cell, a call's before anything (detail 1); register
   code takes its next slice in line, and its entry's and loops' polls may
   leave the machine (detail 2), keeping the live registers on the data
   stack (`regcode::liveness`, ported to FX-26 too); a leaf's link, on the
   machine stack, which the machine's exit leaves, moves there with them;
   a call of a native closure goes to the Rust machine's `call`; a
   `lambda`'s routine may be `nclosure`. `ricell` is no longer done in
   line: an I-cell is not two `#f` fields now (`TODO.md` §92).
3. **The slice in the state (`State::slice`)**, which x86_64's register
   code reads as it takes its next one, where arm64's moves it as a
   constant: `FIXPT_SLICE` sets it at run time, and the compiler written in
   FX-26 must make the same bytes as Rust's whatever it says.
4. **`NATIVE_CONVENTION_AVAILABLE`**, the one gate for the native
   convention on a machine (`DirectMachine::new`, the CLI's refusal,
   `fixpt bench`, the tests); off on x86_64 until step 2.
5. **Main's new tests on x86_64**: those of `io`, `one_shot`, `preempt` and
   `processes` run the native convention where it runs (`processes`'s
   `native` way, elsewhere, its lowered run); `made_code`'s that run the
   arm64 code a program writes are arm64's (`ignore` elsewhere), the rest
   expecting each program's fallback.
6. **The native convention re-ported onto main's frames (step 2)**:
   `direct/x64.rs` was `direct.rs` step for step as it was; main changed
   the frames under it (`TODO.md` §91: a header word below the link, frames
   as bloblets, raw `f64` slots after the values) and much besides. Ported
   as before, step for step:
   - **A frame's region is S bytes, as arm64's, and the word the `call`
     pushed is its top one**: `push_frame_ret` pops the return address, takes
     S, and stores it as the frame's second word; `pop_frame_ret` puts the
     second word (which a restore may have made the underflow) back where it
     was, for `ret` or a tail call's callee. Stubs' frames (32), control
     frames (64) and polls' (208) the same.
   - **A raw `f64` return's mark is an eight-byte `nop` whose displacement
     nothing else emits** (`0f 1f 84 00 4f f6 4f f6`), and the jump after it
     skipped: 13 bytes past the return address, where arm64's is 8.
   - **A raw entry's length by the parameters' mask** (`raw_entry_skip`),
     not by their count: unboxing REG1 to REG3 differs in length from REG4
     to REG8, which are in the state.
   - **A poll's frame holds REG4…REG8 too**, copied from the state and back,
     so that a collection there sees and moves them.
   - The polls, the common poll, cons and bloblet, the trap's `Failed`
     call-out, calls by the callee's convention, `ncallcc` and `callone`,
     `%fx26-adapted`, and main's new fast paths (`remainder`,
     bytevectors, the 8-bit widths, `suffix-fits`, `blobref-length`).
     Every test of `tests/direct.rs` passes on x86_64; the every-program
     report runs 731 programs, 470 expressions as machine code, its only
     differences 4 forms where the cellular machine runs out of stack or
     steps and native code does not (`deep.fx`, `deep-control.fx`,
     `quiet-boxes.fx`), as on arm64.
   - **`native-code?` and `seal-code` say no off arm64**: the code a
     program makes is arm64's (`programs/made-code/`), and the convention
     `native-convention` declares is arm64's, so on x86_64 each program
     takes its fallback rather than run arm64 bytes. (No longer: "Code a
     program makes, on x86_64", 2026-10-18.)
   - `fast` on x86_64 stays register code: the native convention is fastest
     there on every program of `fixpt bench` but `captures` (42.8 ms
     against 36.9), as before the rebase.

## The native convention compiled by FX-26 on x86_64 (2026-10-18)

The user: "Can you add x86_64 support for fx-regs-fxjit-native? You can
make an appropriately named branch for it" (branch `x86_64-fxjit-nativecc`;
TODO §112, item 4).

1. **Rust keeps the driver, FX-26 makes each procedure's code**, as for
   register code (`syn::assemble_reachable_by_fx26`): `compile`'s finding
   of the procedures a closure reaches, the binding of their globals
   (`global_value`), refusals, and the code bloblets (`install`) stay
   Rust's; `procedure_x64` is FX-26's (`native-direct-x64.fx` and the files
   beside it). The trampoline and common routines are the machine's, in
   Rust, as the cellular machine's are.
2. **The protocol** (`direct/fx.rs`): before each procedure the driver asks
   what `procedure_x64` asks it as it goes (`prepare_x64`: the callees'
   raw parameters, then, instruction by instruction, the procedure each
   `const` of a word or closure, each `global` and each `lambda` names, and
   the continuation procedure), in the same order, so that every procedure
   has the same number; an error after the first code is noted at its
   instruction, for FX-26 to stop there, its message as Rust's. FX-26 is
   given the cells as integers (bits, and the number of each heap value
   among them), and gives back bytes, the fields (by those numbers) and
   the call-outs it numbered from the machine's count, those before a
   failure too.
3. **What FX-26 knows of the machine, generated**
   (`native-direct-x64-layout.fx` and its signature, `fx26_direct_layout`):
   registers, the state's fields, frames, traps, tags, kinds, the
   call-outs' kinds, and the primitives, routines and instructions by
   number. The encoder written in FX-26 gained what the native convention
   uses (`rip`-relative, narrow and indexed memory, `div`, `not`, SSE),
   each against the Rust encoder.
4. **Seven files, each the Rust's step for step**: the assembler and shared
   sequences (`-asm`), where raw values are kept (`native-reps.fx`, of no
   machine's: `reps.rs`), raw values' pieces (`-raw`), the heap's fast
   paths (`-flat`), the procedure's state and analysis (`-proc`), its
   instructions (`-ops`, `-prims`) and the loop (`native-direct-x64.fx`).
   The pieces were ported in parallel and each checked against its Rust
   piece by name (`direct::oracle_x64`, `reps_oracle`; the tests
   `native_direct_x64*.rs`, `native_reps.rs`); a conversion is
   `128 kind + 8 r + rep` (64 collided at REG8).
5. **Collection held off across a compile, but while FX-26 runs**: the
   driver's values are unrooted; between procedures they are parked in one
   heap list under one root (`fx_park`) and taken back where a collection
   moved them (`fx_unpark`), what is keyed by bits made again. The heap's
   roots are the session's handles too, so the root is cleared, not
   popped. (Held off throughout, each allocation FX-26 made called in, and
   its garbage stayed until the compile ended.)
6. **The machine, `fx-regs-fxjit-nativecc`**: `--calling-convention
   fx-native`, x86_64 only. The session's hook `native_fx`, the CLI's
   `compile_by_fx26`, compiles the native runner's thunks and each global's
   procedure; what it declines runs as cellular code, said so as under
   Rust (an adapter, `nclosure`'s, is a decline: it runs cellular code).
7. **Checked byte for byte**: with `FIXPT_FX_NATIVE_ORACLE`, every closure
   is compiled by the Rust compiler too, on a machine of its own, and the
   two described alike (`direct::describe`) after; `fixpt-cli`'s
   `fx_native.rs` runs every test program (698) on both machines: the same
   output, and no difference the oracle sees (a one-byte change in the
   FX-26 code makes 504 differ). `tests/native_x64.rs` compares every
   register word of the front end, each as a closure, its own procedure
   only (`compile_each`, `fx_begin_each`): 4,892 procedures, 11.3 MB, the
   same (77 refused by both).

## Code a program makes, on x86_64 (2026-10-18)

kayak's request: §97 (`seal-code`, `native-procedure`, `native-code?`,
`native-convention`, `define-convention`) on x86_64 Linux. The machinery
needed nothing new: x86_64's native convention (`direct/x64.rs`) already
had a trampoline and every routine the declaration names (`foreign`,
`overflow`, `poll`, `cons`, `bloblet` and the trap), and every machine
there already called native closures. What was missing was the contract
and the programs. `native-x86_64.conv` is the contract, generated like
arm64's (`declare.rs`, from `x64.rs`'s constants and `DState`'s offsets),
and the same test checks both files (`fixpt-native/tests/convention.rs`).
`native-arm64.conv` is byte for byte what it was: no clause it shares
had to change.

1. **The same roles, in the same order, with x86_64's places.** Every
   clause of arm64's is there, with the same sub-clauses where the
   machine allows. `values`, `closures` and `barrier` are word for word
   the same, and so is every `state` offset, because the state is the one
   `DState`. Where they differ, the difference is the machine's.
2. **Registers are `x64.rs`'s, by their names**: `result` rax, `closure`
   rbx, `frame` rbp, `count` r10 (arm64's x9), state r15. Arguments are
   rdi, rsi and r8, then `(state reg4)` … `(state reg8)`, because `x64.rs`
   keeps REG4–REG8 in the state (`DState::regs`). For that, the `state`
   clause gains `reg4`…`reg8` (616–648) after arm64's fields. `rest-in`
   is `(state reg8)`. The overflow routine takes the code in r9 and the
   info in r14, `x64.rs`'s X16 and X17. The made programs use r11, r9
   and r14 as scratch.
3. **Of the four registers arm64 pins, x86_64 pins only the state**
   (r15). The fuel, the stack's limit and the code distance are words of
   the state, `(state fuel)`, `(state stack-limit)` and `(state delta)`,
   as `x64.rs` keeps them; `cellular/x64.rs` keeps fuel there too. x86_64
   has no callee-saved register to spare for them. So
   `(pinned (state r15) (fuel (state fuel)) …)`, `(code (runs-at reference
   plus (state delta)) …)`, `(overflow (when rsp below (state
   stack-limit) after-frame-made) …)`. The `fuel` clause says
   `(fuel (state fuel) …)` where arm64's says `(register x28)`: a place,
   not a register.
4. **The return address is `pushed`**, on the stack's top as a routine
   or procedure is entered, where arm64 has it in `x30`: `(link pushed)`.
   Every routine is entered by `call [r15 + entry]`, and `overflow` says
   `by call` where arm64's says `by x30`. A frame is made as
   `push_frame_ret` makes one: the return popped into r11, `sub rsp`, the
   link and return stored at `[rsp+8]` and `[rsp+16]`, `lea rbp,
   [rsp+8]`. The `made` clause spells that out. The frame then reads as
   arm64's (header `rbp -8`, link `rbp 0`, return `rbp 8`, map `rbp 16`,
   values from `rbp 24`). It is undone in reverse, with the return pushed
   back for `ret`. The trap's stub is entered by `jmp` with the site's
   return address on the stack, as the machine's own code does; arm64's
   declaration says nothing of how its trap is entered, so neither does
   this one.
5. **`target` is `x86_64`**, as `fx26:x86_64.fx` and the Rust target
   name spell it, and the program's convention name is `x86_64-native`.
6. **`native-convention` gives the declaration of the machine it runs
   on** (`fixpt_runtime::NATIVE_CONVENTION`, chosen by `cfg`; both files
   are also there by name). Both checkers compare with it, so a program
   that declares the other machine's convention is refused at its
   `define-convention`, on its first differing clause by role, `code`
   (`tests/checker.rs`). `runs_made_code` is now true on x86_64 too,
   wherever the machine calls native code.
7. **The programs are twins**, in `programs/made-code-x86_64/`, rather
   than one program per test picking its encoding from `target`. Five of
   the seven declare their convention, and a declaration is checked
   against the machine's before the program runs, so an arm64 program
   with one cannot even check on x86_64. Twins keep arm64's programs
   unchanged too. The two that declare nothing (`leaves.fx`,
   `typed-calls.fx`) now test `target` (a `here` beside `native-code?`)
   on both machines, because `native-code?` is true on both and neither
   should run the other's bytes. `frames.fx`'s bytes are written one
   instruction to a line, with the instruction beside them. They were made
   by `generated.fx`, which reads the declaration and encodes with
   `fx26:x86_64.fx`, and checked with `objdump`. The test says the two
   agree byte for byte, as on arm64. x86_64's jumps are all rel32, so
   the generators place the instructions in a first pass and make them
   again with each displacement. The checker's sweep reads both
   directories and expects the other machine's declared programs to be
   refused. `modules/convention-read.fx` now says "a register" where it
   said `x10`, so that it holds on both machines.
8. **`fx26:convention.fx` reads both.** A place is a register's number
   (arm64's `xN`, x86_64's as the hardware numbers them), `cv-in-state`
   (4096) plus a field's offset for `(state field)`, or -2 for `pushed`.
   The reader accepts either machine's names; the printer uses
   `target`'s. A declaration that mixes them does not print back, so it
   is refused. `cv-state` gains `reg4`, 0 on arm64. A test reads both
   files on whichever machine runs it (`made_code.rs`,
   `both_declarations_read_as_data`).
9. **Failures unwind as on arm64; panics do not unwind on either.** A
   trap (a refused bloblet, `car` of `'()` or division by zero in a
   procedure made code calls, even 5,000 made frames deep) goes through
   the common trap, and back to Rust by the saved stack pointer. The REPL
   then goes on, made code and all. A Rust panic in a call-out aborts on
   both machines, because the call-out is `extern "C"`. That is not new,
   and not x86_64's.

Tested on x86_64: `made_code.rs`, all eight tests (the four arm64-only
ones no longer ignored there), on every machine. That means 11 machines:
x86_64 adds `fx-regs-fxjit-cellcc` and `fx-regs-fxjit-nativecc`, and the
stencils run where the build found nightly. They include the stressed
runs, with time slices of 3, a 4 KB nursery and a 1 KB stack cache.


## The command line, FX-26 first (2026-10-22)

The user: "I clearly never remember the right commands, and in any case
its too awkward to have to pass so many parameters to get into the
default mode that I actually care about." Their shell history showed
`cargo run --bin fixpt -- --dialect fx26 --fx26-machine NAME repl`,
`--fix26-machine` misspelt (refused as an unknown command, with the
whole help after it), and a bare `cargo run` failing on three binaries.
Asked, the user chose FX-26 as the default language, and the three part
options removed, not hidden.

1. **A bare `fixpt` is the FX-26 REPL on `fast`.** FX-26 is the default
   language everywhere. Scheme is said with `--dialect scheme`, `fixpt
   scheme` (its REPL, as `fixpt fx26` was FX-26's), a `.scm` or `.ss`
   file given to `run` or `eval`, or the Scheme-only `dump-heap` and
   `build`. Inferring from the file's name was not asked for; it keeps
   `fixpt run greet.scm` (the README's) working without a flag.
2. **`cargo run` finds one binary.** `sexp-edit` and `fixpt-symbolize`
   moved from `fixpt-tidy` to a crate of their own, `fixpt-tools`, which
   `default-members` leaves out. The other way, `default-run`, does not
   apply in a virtual workspace, and `required-features` on the two
   binaries still leaves them in `cargo run`'s choice (tried). The tools
   have no tests, so a bare `cargo test` runs all it ran before; `cargo
   run -p fixpt-tools --bin sexp-edit` runs one.
3. **A machine only by its name**, `--machine NAME` (`--fx26-machine` is
   kept, the same option). `--fx26-run`, `--cellular-machine` and
   `--calling-convention` are refused, saying to name the machine. Given
   alone, a part had reset the others to `rs-scheme-vm`'s, so
   `--cellular-machine fx-registers` alone ran the lowered Scheme: the
   pause the user felt was in fact the default's, its first form loading
   the front end (fixed apart, `4caffc2e`). One combination the tests
   used had no name: cellular words interpreted by Rust, procedures in
   the native convention. It is now `fx-cells-rsinterp-nativecc`, so the
   tests keep it.
4. **`fixpt machines`** lists the machines, marks the default, and says
   which cannot run here and why (the same check that refuses them, now
   one function, `unavailable`). The main help names none of them. Their
   descriptions say "machine code" where they said "arm64" but compile
   for x86_64 too.
5. **An unknown option is refused with the nearest known one**:
   "unknown option `--fix26-machine`; did you mean `--fx26-machine`?".
   Before, an unknown option fell through as a command. Options are read
   from anywhere before a `--`; after it, the words are the program's,
   so `fixpt run p.fx -- --step-limit` gives the program `--step-limit`.
   An unknown command says so in two lines, not with the whole help.
6. **`fixpt FILE [ARG...]`** runs a file, as `fixpt run FILE -- ARG...`
   does, when the first word is no command and names a file; every word
   after it is the program's, one that looks like an option too. Not
   asked for; added because `run`'s `--` was one more thing to remember.
   Scheme, FX-87 and FX-91 take no arguments, so they are given the
   files before a `--`.

The dated records (`DONE.md`, `PLAN.md`, `TODO.md`, the measurements in
`docs/performance.md`) keep the part options as they were run. The
README, the benches' READMEs, the debugging recipe and the native
conventions' notes now name machines.

## The suite's time, back down (2026-10-22)

The user: "it seems clear that something has regressed terribly here.
Either we have added too much test load, or one or more of the tests has
become unbearably slow", and, of the two targets found: "see about
addressing both". The checked suite took 6,400 s on x86_64, with
`native_reps` killed after 36 minutes. Baselines before the x86_64 work
(`3e1229fe`) and before its FX-26 native convention (`35c59a35`) showed
where. `native_x64` (2,039 s) and `native_reps` (hours) are the FX-26
native convention's. `compiler`'s 688 s came from
`every_program_on_every_machine`, which ran on arm64 already and was
turned on for x86_64 (`3376646c`). The tests that compile the whole front
end grew 22–28%, as the front end did (40.8k → 51.1k lines).

1. **The tests run the front end as register code, as the REPL does.**
   They ran it lowered, on the bytecode VM. In `native_reps`, compiling
   the front end alone took 186 s before a word was compared. The FX-26
   pass's words came after: one word ran past 100 s. `tests/common` makes
   the session (`session`, `front_end_session`): the front end as
   register code on the hand register machine, read back from its cache.
   `with_own`, the sessions that call the FX-26 compilers, and the
   bootstrap's stages now use it. Lowered, the front end is still run by
   `the_front_end_compiled_checks_alike` (which compares the two), by
   `FIXPT_FRONT_END_LOWERED=1`, and by the bootstrap's timing report,
   which times each machine's stage 1 on purpose. Stage 1 is the FX-26
   compiler's output however that compiler runs, so the fixpoint means
   what it did.
2. **A program as register code** (`Fx26Session::program_as_register_code`):
   what the front end does for itself, for any program and entries,
   uncached. `native_reps` runs its pass (`tests/native-direct/reps.fx`)
   so. The front end's own loading is now the same code.
3. **`compile-forget-globals!` was missing from `FRONT_ENTRIES`.** The
   session calls it for a whole program (`compile_with_own_compiler`)
   since `b544769b` (2026-10-04), so the register-code front end could
   not compile a whole program. Nothing ran that way until now.
4. **Native slots are no longer lost.** Each thread has one native
   machine, which outlives the sessions that compile into it. Its code
   collection kept every word of a heap other than the current one, so a
   dropped session's words stayed installed, and the 65,536 slot numbers
   ran out after a few sessions. The heap keeps the serials of the heaps
   alive (`Heap::serial_live`); the collection lets go of words whose heap
   is gone; a dropped machine gives its slots back to the process. And
   `NATIVE_SLOTS` is 2^18: `every_program_on_every_machine` keeps six
   sessions alive on one thread, each with the front end installed. Slot
   numbers already reach the code by register or a 32-bit displacement,
   past 16 bits, on both machines.
5. **`webs` is left quadratic.** For each slot read, both the Rust pass
   (`reps.rs`) and the FX-26 one (`native-reps.fx`) clear an
   instruction-long array and search back. On register code the whole
   of `native_reps`, every one of the front end's 4,898 register words
   included, takes 84 s, so it is filed (`TODO.md` §114), not changed
   with this. (Since done, the same day: "`webs` by basic block", below.)

## `webs` by basic block (2026-10-22)

The user: "Can you address that quadratic algorithm?" (`TODO.md` §114,
now `DONE.md` §114).

1. **The same webs, not better ones.** The representation pass could
   find webs some other way (SSA, or not splitting a slot at all), but
   what it decides from them, which slots are raw and which are split,
   is compared word for word between the Rust and FX-26 versions, and
   the native code made from it is tested. So the change keeps the
   partition exactly, and was checked against the old search on every
   word before the search was removed.
2. **By basic block, not by instruction.** Done by instruction, a slot
   at a time costs the slot's live range, and the front end's module
   bodies are 8,000 straight instructions with hundreds of slots live
   at once: lowered, 120 s for one word, three times the search. By
   block, a straight body is one block, and a slot costs its own
   accesses.
3. **The FX-26 version in a file of its own**, `native-reps-webs.fx`, a
   module file of no state that `native-reps.fx` loads, as
   `native-reps.fx` would have passed 1000 lines. It has the blocks
   (`nr-blocks`), a slot's webs (`nr-slot-webs`) and the union-find
   (`nr-find`).
4. **`native_reps` compares the webs themselves** (`Facts::webs`,
   `nr-web-names`, exported for it). What it compared before rests on
   webs only where a slot holds an `f64` and something else, which the
   front end rarely does. The webs are named canonically (the first
   instruction of each), as the two versions' union-finds pick
   different roots.


## `fast` on x86_64 is native (2026-10-22)

The user: "Go ahead and make fx-regs-rsjit-native the default", after
the 46 ports were timed on x86_64, one run each, alone, with
`eval --step-limit none` (wall clock, start-up included):

- `fx-regs-rsjit-nativecc` 91 s in all, `fx-regs-rsjit-cellcc` (the
  default since 2026-10-11, choice 6 of "Register code on x86_64") 206 s,
  `fx-regs-fxjit-nativecc` 94 s, over the 44 ports both ran.
- The `f64` ports 15–20 times as fast (`nbody` 22.3 → 1.5 s,
  `spectralnorm2` 31.1 → 2.6 s); `fib`, `tak`, `even-odd` about twice.
- `merge` and `sieve` fail on `fx-regs-rsjit-cellcc` (a stack overflow)
  and run natively.
- Slower natively on 15 of the 44, most `boyer` (1.45 → 1.97 s, both
  ports) and `string-concat` (1.67 → 2.45 s); then `merge`, `mpuz`,
  `logic`, `hamming`, `sorts`, `fannkuchredux` by 10–30%. Not looked
  into yet.
- At the REPL, alike: a form 0.55 s on each, start-up included.

1. **`FASTEST` is `fx-regs-rsjit-nativecc` wherever the native
   convention runs** (`NATIVE_CONVENTION_AVAILABLE`), so arm64 and
   x86_64 alike; `fx-regs-rsjit-cellcc` where only the hand cellular
   machine would run, which is nowhere today.

## Typed cellular code, begun (2026-10-22)

The user: "See about making a typed cellular code. Try to make it capable
of be fed into a Hoare logic system (ie I'd like it's propositions to
start with type assertions as the baseline, but be extensible to include
more general expressions)." The design is
`docs/research/typed-cellular-code.md`, after
`type-and-effect-directions.md` §4(b).

1. **Assertions over places, propositions over terms.** A certificate's
   assertions name the machine's places at a cell boundary (`(slot i)`,
   `(free i)`); the verifier's terms also name values it made and the
   logic's functions applied (`(car t)`, `(+ a b)`). `Prop` has the
   general forms now (relations, `not`, `and`, `or`, `implies`), though
   only `(: t T)` is stated by the compilers yet, so that what comes
   later is an addition, not a change of form.
2. **The join rule does no inference.** Where ways meet, a place keeps
   what every way agrees on, or its term at the type it was made with;
   a place made since they parted needs the certificate's assertion. No
   least upper bound is computed.
3. **Instantiations given, not found.** The checker keeps each call's
   instantiation of a polymorphic operator binder by binder; the
   verifier substitutes. A `plambda`'s word carries its binders, so a
   closure over it is of a `poly` type.
4. **The certificate is not trusted.** Where the compiler cannot find a
   free value's or added parameter's type by its lambda, it takes one by
   name from elsewhere: a wrong guess can only make a word fail.
5. **A `car` of a list that may be `nil` is a debt, not a failure.** The
   checker accepts it, and every machine checks the pair's tag and fails
   safely (`regcode.rs`'s `trap_if`), so it is a precondition checked at
   run time (`TODO.md` §86), counted apart.
6. **The Rust compiler first.** It makes the same words as `compile.fx`
   (PLAN 13a), and the verifier needs the checker's types, which the
   Rust checker has at hand; the FX-26 compiler's certificates are TC6.
7. **Recording is off unless asked** (`Checker::record_types`,
   `Compiler::certs`): it costs every check, as `record_operands` does.

## Typed cellular code, every word verified (2026-10-23)

The user: finish the type VCs first ("a system we believe to be sound
and complete"), and "If you get stuck, switch to a different class of
VC." The last classes, and what was chosen in them:

1. **The checker's rule, shared.** Where the verifier needs a typing rule
   the checker has, the checker's is made a function of types and both
   call it: `Checker::renamed` (one `poly`'s body under another's
   binders), `Checker::blobref_rule` (flat data). `synth_blobref` keeps
   its error messages, each with which part it blames (`Blame`).
2. **What checking chose freely, the certificate says, and it is
   checked.** A new blobref's flat comes from the type it was checked
   against, which no cell shows: the certificate says it (`%flat`) and
   the rule checks it, as it checks a `%make`'s type. Likewise the list
   type `apply`'s or `list`'s copy is made at (`%copy`).
3. **A new blobref's fit is checked at run time, and the verifier
   requires the check.** Its bytes must lie in the suffix; the compiler
   follows it with `%fx26-suffix-fits`, and the verifier takes the two
   as one, refusing it without the check or with a branch between.
4. **A flat sum's variant is a fact of the way, not a narrowed type.** A
   `tagcase` on a flat sum tests a tag read from the suffix; the way
   where it names a variant keeps that as a fact about the blobref's
   term (`State::variants`, joined as every way in has it), because
   narrowing the sum's type would change its layout.
5. **`%fx26-flat-no-arm` gives nothing.** It fails at run time; its
   result is typed `void`, so the way after it is unreachable. A tag no
   arm has is a safe failure, as `car` of `nil` is.
6. **Thunks the compiler makes are signed by their body.** A `prompt`'s
   body becomes a word of no parameters that checking never saw as a
   lambda: its signature is the body's type and effect as checked.
7. **A `vsubr`'s word is signed by its type unfolded**, in
   `Certs::settle`, which now takes the checker mutably to make the
   unfolding: the compiler holds the checker immutably.
8. **The test now requires every word**, not a count: a word that stops,
   a VC failing or open, fails it. The scheduler's 13 assumptions stay
   assumptions (the note's §7), said, not refused.

## `requires` and `ensures` (2026-10-23)

The user: "let's attack requires and ensures next" (the design note's
§8, decided with the user 2026-10-22). What was chosen in building it:

1. **The result is named in its clause, `(ensures r q)`**, not as the
   note sketched it, `(subr E (…) (r int) …)`: a result written `(r
   int)` reads as a type applied, `(listof int)`. `(requires p)` comes
   first, each clause at most once; `->` takes them too.
2. **The checker carries specifications; the verifier proves them.** The
   checker reads a specification, sees that it speaks of the procedure's
   own `int`s, `nat`s and `bool`s, keeps it in the `subr` type (and in a
   lambda's signature, for the certificate), and compares two. Whether a
   body ensures what it says, and whether a call establishes what its
   callee requires, is the cells' verifier's: Hoare logic once, on the
   code that runs, as the note's design has it. A program whose
   specification does not hold checks, runs, and has words that do not
   verify, each with its VC left open.
3. **Behavioural subtyping by the same prover.** One procedure type is
   within another when its own `subr` rule holds and the other's
   `requires` entails its own, and, with that, its `ensures` entails the
   other's (Liskov and Wing). What the prover cannot show is not within:
   conservative. No specification is `true` on both sides, so a
   procedure with none does not fit where one ensuring something is
   expected.
4. **The proposition language**: linear integer relations (`<`, `<=`,
   `=`, `>`, `>=`) over literals, `+`, `-`, `*`, of names of `int`s and
   `nat`s; names of `bool`s; `not`, `and`, `or`, `implies`, `#t`, `#f`.
   A product of two unknowns is allowed and opaque to the prover (an atom
   of its own): `square.fx` is true and left open, for a prover outside.
5. **One prover, `logic.rs`**, generic in its atoms: the connectives
   taken apart, a disjunction case by case, each case's integers by
   Fourier–Motzkin. The FM is `sizes.rs`'s, moved there and generalized
   (equalities rewritten away first, for the verifier's), and kept step
   for step with the FX-26 checker's for what `sizes.rs` asks: no
   tightening of the constraints given, only of the sums.
6. **No control-effect rule in the checker.** The note's point 4
   suggested a procedure with a specification have no control effect.
   Instead the verifier does not assume a callee's `ensures` after a call
   whose latent effect may `goto`, `comefrom`, or is a variable: such a
   call may return again, with a value its `return` never saw. A body's
   own `ensures` is proved on every way to a `return`, whatever it calls.
7. **A join keeps each way's case.** The note's join keeps only the
   propositions every way has. A value made on the ways (an `if`'s, at an
   assertion of the certificate's) now also gets the disjunction of the
   ways: its value there and what that way alone knew. That is the
   strongest postcondition, not a least upper bound found, so not
   inference; without it, `(+ 1 (if …))` cannot be specified.
8. **No `old`.** A specification speaks of parameters, which are values;
   a slot reassigned is a new term, and the entry's term is what `ensures`
   names. `old` waits for propositions about what refs and arrays hold.
9. **Latent propositions not yet folded in.** `(bool (then …) (else …))`
   stays as it is; an `ensures` of a `bool` result says the same with
   `implies` (`predicate.fx`). Making one the other's sugar is next.
10. **Spec programs in `tests/programs/specs`**, each saying on its first
    line `; Verified`, `; Unverified` or `; Refused`; in the two checkers'
    comparison once the FX-26 checker read specifications (the same day).
11. **The FX-26 checker's prover is `logic.rs`'s step for step**
    (`check-logic.fx`): atoms numbered as met, the first formula that
    does not split taken each time, splits on the first left, so that the
    two checkers decide behavioural subtyping alike, even where a budget
    runs out. `ty-subr` got a fifth field, the specification (none or
    one), and each place that makes one keeps it or not as the Rust one
    does.
12. **A composable continuation ensures nothing.** Porting showed the
    Rust rule letting one stand where any `subr` is wanted, a specified
    one too; both checkers now ask that the wanted one ensure nothing.
13. **`k-synth-rlambda` moved out of `check-rules.fx`** (to
    `check-synth.fx`, given the knot's `k-synth` and `k-synth-lambda-as`)
    so that the file, over its line limit already, ends shorter than it
    was; its debt lowered to match.

## The `(bool …)` result as an `ensures` (2026-10-23)

1. **One representation.** `Ty::Proving` (`ty-proving`) is removed: the
   shorthand reads as a plain `bool` result and an `ensures`, `(and
   (implies r (and P …)) (implies (not r) (and Q …)))`. The shapes and
   certifications became atoms of the specification's logic
   (`ast::Named`'s `Shape`, `Acyclic`, `Nat`, `LengthIs`, and `Length` for
   `(length i)`), booleans the prover treats as opaque; size relations
   became its integer relations.
2. **Narrowing reads any `ensures`, syntactically.** What a branch on a
   call learns is each `(implies r p)` (`(implies (not r) p)` where false)
   conjunct's propositions, each that is one of the old forms, wherever
   the `ensures` came from. So an alias of `<` at a written-out `ensures`
   narrows as one at the shorthand does (`specs/latent-ensures.fx`).
   Other forms, `(or (not r) p)`, are not narrowed by.
3. **No `lambda` may claim them.** The rule that refused a `lambda` at a
   `(bool …)` result now refuses one whose `ensures` has such conjuncts,
   with its own message. `specs/predicate.fx` from the day before, a
   `lambda` with `(implies r (< 0 x))`, would have been trusted by the
   checker unproved; it now says `(or (not r) (< 0 x))`, which the
   verifier proves and uses as before, and `specs/predicate-claim.fx`
   shows the refusal.
4. **Printed back as written.** An `ensures` that is the shorthand's
   form (alone, or first of two conjuncts with a written `ensures`)
   prints as `(bool …)`, with the rest as its clause; a parameter's name
   is printed only where a clause remains to use it, so the types printed
   before are printed alike.
5. **Both written.** `(subr … (bool (then …) (else …)) (ensures r q))`
   conjoins the two, the shorthand's first.
6. **Subtyping by the prover.** Two tests' types compare by behavioural
   subtyping like any specifications, which subsumes the old rule (each
   proposition of the wanted one among the given one's) and goes past it:
   `(< i n)` where true fits where `(<= i n)` is wanted.
7. **The verifier: a standard operation's `ensures` is assumed after a
   call of it**, as a word's is (the call rule), and its word as a value
   is certified with its specification, which its own call then shows.
   A call of a word, not only of an operation, now narrows by what its
   `ensures` says a branch on it learns: types, and the size facts its
   relations are, of the arguments' sizes at the call (`sizes::rel_fact`,
   the one rule `Checker::rel_facts` uses too). Before, an alias of `<`
   called as a global narrowed nothing in the cells, which no verified
   program had shown, since `sizes/` is not among the directories the
   verification test covers.
8. **Names in the FX-26 port.** `k-sides` and `k-latent-facts` were taken
   (`check-unions.fx`, `check-test-facts.fx`), so the new ones are
   `k-latents` and `k-ensures-latent`. `check-test-facts.fx` is given
   `check-logic` by the conductor.


## The verifier over every test directory (2026-10-23)

1. **The corpus test takes every directory but `specs`**, with a list of
   the words known not to verify (`KNOWN_GAPS`), which must be exactly
   the words that do not: one fixed fails the test until it is taken off.
   The survey test is kept, ignored by default, for timings and for a
   directory or file at a time.
2. **Rules added to the verifier, each the checkers' own, shared where
   the checker has it as a function:** the scheduler's forms (`spawn`,
   `spawn-monitored`, `par`, `race`) record what they instantiate its
   procedures at, and a process's body passed to it is within its type
   with its own place's effects its own (`Checker::process_effect`, which
   `spawn`'s rule now uses too); a boolean made where ways join narrows a
   branch on it by what each way that may have made it so learned (`and`,
   `or`); the size facts in force are the checker's while a cell is
   verified, so subtyping and a list's tail's size see them; `null?` of a
   `nlist` gives its size facts, read from `null?`'s type; `cons` onto a
   `nlist` by the checker's rule is instantiated so, and a `nlist` one
   longer; a value narrowed on some ways joins at the type holding it on
   all; paths (`(car x)`, a product's field) keep a test's narrowing until
   a step's effect may write what they read (`Checker::path_killed`,
   factored out of `kill_paths`); data made where a union was expected is
   made as its member of that shape; `%fx26-convert`; `append`'s and
   `string-append`'s words, signed as `list`'s is, and their operations;
   `spin` at a cyclic instantiation (`Checker::spin_for_cyclic`); a
   `prompt`'s effect its body's and handler's, the body checked within
   its tag's bound, as `synth_prompt` has it (it had added the bound).
3. **A `proj` of a value in tail position is noted too**: compiled as the
   value, the note, then the return, the same cells; a `proj` of a call
   in tail position stays a tail call, unnoted.
4. **The harness reads each program's loads from its own directory**, so
   `module-files/` programs load their siblings.
5. **Refusals are not counted as gaps**: error tests (`; Rejected`, `;;
   !` and those their own test files expect), fragments whose test binds
   their free variables, module files meant to be loaded, and arm64's
   conventions on x86_64.

## Masking inside a word, in the verifier (2026-10-23)

1. **The certificate says where, not what.** For each expression whose
   effect `Checker::mask` changed (`Facts::masked`), the compiler marks
   its cells (`Item::Mask`, `Cert::masks`), as region scopes are. It does
   not say what was masked: the verifier finds what the cells are given
   from outside (a slot below where they start, a free value, a global)
   and what they give (the value they leave; the word's result where they
   return; the parameters at the loop back to the start), and masks by
   `Checker::mask_keeps`, the filter factored out of `mask`, which the
   word's boundary uses too.
2. **A range the verifier cannot trust is ignored, not refused**: one
   entered other than at its start, left other than at its end (but by a
   `return`, a tail call or the loop back), with a `slot!` below its
   start, a step that takes it below where it started, or one straddling
   its end. Ignoring one only masks less.
3. **Applied after, per atom.** The word's effect is computed as before
   (regions' scopes, `plambda` bodies); an atom of it is then dropped if
   every step that did it lies in a valid range whose mask drops it.
   Masks are per-atom filters, so their order does not matter, and an
   atom no step noted is kept.
4. **The test of it**: each verified word's latent effect made one atom
   smaller must not verify for the ranges alone (it verifies only if it
   also does without them). The latent effect is what the checker's
   masking kept, so a range masking it would be the verifier masking
   more. It found the older gaps of §117 too, which it does not assert
   on: global reads, `spin`, the scheduler's private regions.

## Global reads in the verifier (2026-10-23)

1. **`global` notes `(read (globals g))`**, of a global of the program's
   (one the checker holds a global, and not the built-in scheduler's,
   whose procedures the forms call through `Checker::library_type` and
   which no latent effect names). A load's hidden global is noted: the
   checker names those in latent effects.
2. **The weakening test skips an atom the rest of the effect still says**
   (`(read @globals)` says each global's read): removing it weakens
   nothing. It asserts that no global's read is left out unseen.

## `assert`, `assume` and `fixpt test` (2026-10-23)

1. **Standard procedures, not forms.** `assert` and `assume` are
   `(subr pure ((p bool)) unit …)`, the first `(requires p)`, the second
   `(ensures r p)`: their specifications are what the verifier makes of
   them, by the call rule, so it needs nothing of its own for them but
   proving a standard operation's `requires`, which it now does (none had
   one). Both checkers read them from the standard table; each compiler
   lowers them to a primitive (`%fx26-assert`, `%fx26-assume`), appended
   to the runtime's table so that no primitive's number changes.
2. **No `any`.** The note's `(any T)` would draw a value of a type, but
   types are not there at run time; a harness's parameters, drawn by the
   runner from their types, are the arbitrary values instead, and the
   verifier already treats parameters as arbitrary. So no effect for it
   either (the note's open question 1).
3. **Every procedure the runner can call is tested**, specified or not:
   a call it makes may break a callee's specification
   (`wrong-requires.fx`'s `f`). Not one whose effect another run could
   see (writes, I/O, control).
4. **Specifications checked by rewriting the program's text**, only for
   `fixpt test`: each specified top-level `lambda`'s body checks its
   `requires` and `ensures`, failing with a message that names whose; a
   copy as written, `%plain-NAME`, gives a counterexample's result. The
   program's own expressions are run each apart, after its definitions,
   so that one that breaks a specification is a counterexample too.
5. **Inputs drawn the same way each time**: 13 edge integers first, then
   a fixed-seed generator in [-100, 100]; lists of up to 5.

## `fixpt verify` and the REPL's `,verify` (2026-10-23)

1. **The Rust compiler's words are what is verified**, not the words the
   REPL runs: only the Rust compiler makes certificates. `,verify` replays
   what was defined (each form the checker took, as typed, and each file
   `,load` ran whole) as one program through the Rust checker and
   compiler, then verifies its words: what is verified is the program,
   not the REPL's machine code. Entries held pending, waiting on types,
   are not replayed.
2. **A command, not a mode**: nothing is verified unless asked, so that
   the REPL is as fast as it was; `,verify NAME …` narrows what is said,
   not what is compiled.
3. **"Open", not "false"**: the verifier cannot tell a false obligation
   from one beyond it, so the report says open and points at `fixpt test`.
4. **One driver** (`fixpt_fx26::verifying`) for the CLI, the REPL and the
   tests' survey, which now calls it in place of its own copy.

## Open VCs given to an SMT solver (S2, 2026-10-23)

1. **z3 as a process, SMT-LIB 2 over a pipe**, one per VC with a
   2-second limit; `FIXPT_SMT` names another. No library binding, so no
   build dependency; without a solver, the report says so and keeps
   "open".
2. **Every term a constant of its own**, an `Int` or a `Bool` by where
   it stands. Sound for proofs; a model may then be one no run gives,
   which the replay shows ("the proof does not know what the run does").
3. **Only the report asks the solver**, not `typed_cells::verify`: the
   tests and the corpus stay independent of an external program, and
   what z3 proved is said as such ("N by the SMT solver").
4. **Replayed in a session of its own**, made when first needed, so that
   `,verify` does not redefine the REPL's globals.
5. **"Not inductive" names a global's call**, any (not only a specified
   one): every call's result is recorded with its arguments' terms
   (`Outcome::calls`), and the call is written as source from the
   input's values and the calls before it, then run for its real value.

## Source places in `fixpt verify` (2026-10-23)

1. **Each expression's cells, from where to where, with its span**, in
   the certificate (`Cert::sources`, `Item::Source` in the compiler, as
   `Item::Mask` is): a cell's place is the innermost expression's whose
   cells it is among (the fewest cells, then the shortest span). A
   `return` is its returned expression's, so an `ensures` broken is said
   at what is returned (`x`, `(- 0 x)`).
2. **The verifier notes the cell each message is said at** (`open_at`,
   `failed_at`), filled as it moves from cell to cell, rather than
   changing each of its messages.
3. **Said as `FILE:LINE:COLUMN, `expression``**, the expression's text
   shortened to 48 characters; in the REPL, the expression alone.
4. **The verdicts reworded** (the user found them hard to read): `false:
   with x = -1, the result is -1`; `not proved, as the proof knows too
   little of a call. It holds for …; but for all the proof knows, (f …)
   could be #f, where it is #t.`

## Logic functions in specifications, first step (S4, 2026-10-23)

1. **Admissible: a global, `pure`, of a `bool`, `int` or `nat` result.**
   `pure` gives ending and dependence on the arguments alone (no region
   read), so congruence holds; a result of no identity of its own
   (`eq?`), so equal calls are equal values. A recursive one is written
   as a local `letrec` over unwritten lists, which the checkers already
   show ends; recursion through the global says `spin`, and is refused.
2. **`Named::Call(Sym, Rc<Vec<Expr<Named>>>)`**, so `Named` is `Clone`,
   no longer `Copy`; in FX-26, `(sx-call symbol k-sxs)`. A call is an
   atom of the logic, compared structurally, in both checkers' provers.
3. **Arguments' types not checked as read**, in either checker, as the
   one written in FX-26 reads specifications before it has subtyping:
   sound, as a call is uninterpreted; a mistake shows when `fixpt test`
   checks the instrumented program.
4. **A call in the cells of a logic function gets the call's term**
   (`Term::Call`), not a fresh one: that is what links `(assert (sorted?
   (insert e xs)))` to `insert`'s `ensures`.
5. **Runtime checks bind the functions they call**: `fixpt test`'s
   instrumented body is `(let ((sorted? sorted?)) (letrec ((insert T
   (lambda …))) insert))`, so the check reads no global the procedure's
   effect does not say; its body's value is `(the RESULT …)`, so that
   branches still join at the declared type.
6. **z3: uninterpreted functions over `Int`**, a non-integer value a
   constant all the same; its values are passed to a replay only for an
   integer or boolean parameter.

## Logic functions' definitions for the solver (S4, 2026-10-23)

1. **Translated from the checker's expressions** (`smt_theory`), not from
   the cells: the body of a `lambda`, or of `(letrec ((s T (lambda …)))
   s)`, as `define-fun-rec`. Anything not translated leaves the function
   undefined, uninterpreted as before: never a partial definition.
2. **Totality by the translation**: `car` and `cdr` only of a list a test
   on the way showed a pair (`null?` false, `pair?` true, `not` of
   either), so each equation is what a run gives.
3. **One datatype, finite lists of `Int`**, as the first case; a list
   parameter of another element type leaves the function undefined.
4. **Lists in a VC only of finite, unwritten lists, in a word that
   writes nothing**: the verifier notes each term whose type is a
   `Frozen(_, true)` list (`Outcome::finite`) and whether the word's
   steps write (`Outcome::writes`, before masking); only those terms,
   their tails and `nil` are `L`'s. A cyclic or written list would make
   the solver's well-founded lists prove what does not hold.
5. **What `cons` made is its pair** (`Outcome::conses`), asserted for the
   pairs the VC has as lists: true of data never written.

## Lists of any element sort for the solver (S4, 2026-10-24)

The user asked why only lists of `int`s were the solver's, and to lift it.
- **One datatype of a parameter**, `(List T)`, not one declared for each
  element type: z3 takes `par`, and the sorts are then a tree
  (`Sort::List(Rc<Sort>)`). `nil` is written `(as nil S)`, so the
  translator of a definition is told the sort it wants where it knows it
  (a parameter's, `cons`'s tail, an `if`'s other branch); a `nil` of no
  known sort leaves the function undefined.
- **A list term's sort is its type's**, noted with it in
  `Outcome::finite` (`note_finite`, by `smt_theory::sort_of`), or that of
  a list it is the tail or (a list of lists') head of. Before, any term a
  VC used as a list was one; now a use alone does not make one, as its
  sort would be unknown.
- **No lists of `nat`s**: the solver's `Int` would give a list with a
  negative element, a counterexample of no value of the type. Refused
  (left undefined) rather than asserted, for now (TODO §120).
- **A non-empty pair** (`Ty::Pair(…, false)`, what `cons` gives) whose
  tail is a list is a list of that sort; without it `insert`'s result was
  none, and its proof lost.
- The nested test is of a function counting empty lists, not of
  `flatten` by `len` and `sizes`: a logic function calling another reads
  a global, so is not `pure` to the checkers (TODO §120).

## A perf map, and native definitions named (2026-10-24)

The user asked for perf map support first, for kayak's stage 0
(`docs/kayak-stage0-workload.md`, TODO §121).
- **Beside `FIXPT_SYMBOLS`, not in place of it**: the same notes
  (`symbols::note`) go to both, the perf map's lengths in hex. One switch,
  `FIXPT_PERF_MAP` set to anything, for the path is perf's to choose
  (`/tmp/perf-PID.map`), and the file is left there, as perf expects.
- **The names were the larger gap.** In the native convention a
  definition's value is compiled alone, in a thunk, so its procedure was
  named `lambda@11`, for where its body starts in the thunk's text: every
  procedure of kayak's would be. Now `native_define` queues two names for
  the FX-26 compiler (`compile-name-word!`): the thunk's, `define NAME`,
  and the procedure's, `NAME`. `c-word-name` became a queue, taken one
  per lambda (`c-take-name`); the Rust compiler sets only one, so the two
  compilers still agree.
- **Only a plain `lambda`** (through `the` or a convention) is named so,
  as the compilers' own rule (`name_word_for`, `c-name-for!`).

## Kayak's stage 0: what kept it from native code (2026-10-24)

The user: "Do 1 and 2 please. I suspect we have a big performance gap and
we shouldn't be asking kayak to work around it." About 610 s → 22 s,
by the first two below.
- **`tagcase` loads only the fields its arm uses**, in both register
  compilers, rather than a leaf retried with a frame: the narrower change,
  and the one that makes an accessor of any width a leaf. The retry stays
  in TODO §121.
- **No closure size limit on x86_64**, in both of its native compilers:
  the limit was arm64's (`ldur`, 9 bits) copied over. Arm64's went the
  same day (below).
- **A cellular closure compiled natively as it is made** (`adapt`), not
  the call-out made cheaper: a call then costs a native call's, and
  nothing crosses. Compiled once per word, cached by weak references to
  the word and its code. Weak references into the code area now die
  when a major collection frees what they refer to: they were kept as
  if alive, the area never moving. Only where the thread's own machine
  runs the code (`compile_when_adapting`, which the CLI's native sessions
  set): compiled code names its call-outs by their number in the machine
  that compiled it, and a test or bench that makes a machine of its own
  would run it on the wrong one.
- **A decline's note is kept** when the pass that compiles a definition's
  procedures after compiles none (a module), and replaced by that pass's
  own when it fails; cleared only when it succeeds, as before.


## Frame slots held in registers, native convention on x86_64 (2026-10-24)

The user: "We should absolutely try to keep values in registers in
straight line code." Measured on kayak's stage 0 (`perf stat`, four
alternating runs each): 121.6G instructions to 120.1G, about 3% fewer
cycles (58.9G to 57.4G).
- **A write-through cache, not an allocator**: every slot is still
  stored, so the frame, its stack maps and the collector are as they
  were; a slot's read is a move, or nothing, where `RESULT` or REG1…REG3
  still hold it. REG4…REG8 are words of the state, not registers, and
  scratch registers are any helper's, so those four are all it uses.
- **Forgotten wherever it might be wrong**: at every branch's target and
  every way in from the fixnum version, where an instruction's
  conversions emitted code, and at any instruction but the moves, the
  slot reads and writes, the branches that fall through, and those that
  only make `RESULT` over.
- **Tried and dropped**: carried across a forward branch to a target
  with no other way in (no measurable change); and a copy of a slot just
  written into a register dead until its next read (more instructions,
  more cycles: 123.7G and 57.7G against 119.9G and 56.6G). The copy also
  needed joins to unbox only live registers.

## Raw comparisons branched on the flags, native convention on x86_64 (2026-10-24)

The user, of instruction selection: "finish the fusion work", after it
measured no fewer cycles on kayak's stage 0 (120.9G instructions to
117.5G; pinned to a core, 69.9G cycles before, 70.2G after: stage 0
waits on data cache misses, `TODO.md` §121).
- **Liveness, not "sets `RESULT` first"**: the boolean is dropped where
  `RESULT` is dead on both ways out of the branch (`reps::live_in`), so
  a branch whose next instruction loads an argument for a call (kayak's
  `(and (i64= fp pos) (string=? ff file))`) fuses too. What `RESULT`
  then holds is the raw operand; nothing reads it, and no collection
  traces a dead register (frames by liveness, REG1…REG8 by the entry).
- **`op2`'s test the same**: `branch_on` (`dp-branch-on`) is shared, so
  an `int` comparison fuses where it did before and also where the next
  instruction does not set `RESULT`, in both compilers.
- **`f64` comparisons left as they were**: a NaN's unordered result
  wants a second branch (`ucomis` sets PF), not one condition.
- **`dp-joinable` and `dp-edge` moved** from `-ops.fx` to `-proc.fx`
  (`do-joinable`, `do-edge` before), so that `-prims.fx`, which cannot
  see `-ops.fx`, branches as `-ops.fx` does.

## Slot facts kept across compiles; code installed a word at a time (2026-10-24)

The user asked to dig into stage 0's fixed cost (`TODO.md` §126). Of
it, the native convention's compiler was 20% (`perf`, frame pointers):
8% finding again, at every compile that calls a procedure, which of its
parameters it takes raw (`register_params`: `split_slots` and
`raw_slots`, each a `webs`); 3% `install` writing the code a byte at a
time, the bloblet's header read for each.
- **Kept by the cells, not by the word**: `slot_facts` keeps a register
  word's split cells, raw slots and raw parameters in the
  `DirectMachine`, keyed by its cells' raw values. The facts are a
  function of the cells alone, so a collection that moves a constant
  they name costs a miss, never a wrong answer; nothing need be traced
  or forgotten. About 11 MB more at stage 0's peak (395 MB to 406 MB).
  The register word itself as the key would want it kept still or
  traced.
- **Both procedure compilers** (`procedure`, `procedure_x64`) take
  their own cells and raw slots from it too, so a procedure's analysis
  is done once whether it is compiled or called first. FX-26's driver
  (`direct/fx.rs`) keeps its own, across its procedures.
- **`set_bloblet_bytes`** writes a word at a time, as
  `set_bloblet_byte` of each byte would: the bytes that fit, then the
  first that does not refused, the same errors in the same order.
- Fixed cost 20.6G cycles to 18.1G; stage 0 29.5G to 27.1G (68.4G
  instructions to 60.8G); output the same.

## The front end in the native convention (2026-10-24)

The user: "Native front end sounds good" (`TODO.md` §126: the front
end's register words were 37% of loading kayak's compiler).
- **Where**: only on a native-convention machine whose native code the
  compiler written in Rust makes (`front_end_native`, set by the CLI
  with `compile_when_adapting`). Where FX-26's own compiler makes each
  procedure's code, the front end is that compiler, so it stays
  register code; sessions made otherwise (the tests) keep it so too.
- **How**: the front end checked in the native convention, so the
  closures it makes as it runs are native procedures, compiled as they
  are made (`adapt`); its entry points are native closures, which
  `%run-front-end` calls by the same word it makes for a cellular one,
  and whose code `compile_reachable_as` no longer follows as a word.
- **Its cache apart**: the native one keyed by the convention too, so
  both may be kept for one executable.
- **Not kept: its native code.** Compiling it is now part of every run
  (about 2.9G cycles of the tiny program's, some 5,000 procedures),
  which eats most of what running it natively saves (about 4.2G on
  kayak's compiler, measured with both built fresh). Loading kayak's
  compiler: 17.9G cycles to 17.05G; stage 0 27.0G to 26.35G. Keeping
  the native code between runs would save the rest: images carry no
  code area yet, and code numbers its call-outs into its machine's
  table, which would have to be kept with it.

## Kayak's x86_64 gains, ported to arm64 (2026-10-24)

The user, of the four found not to apply to arm64 (measured on the arm64
Mac, alternating builds: run times the same, only the native compiler
faster): "do them all. work autonously." Each in `direct.rs`, the one
native compiler arm64 has (no FX-26 one, as `native-direct-x64*.fx` is).
- **No closure size limit on arm64.** A closure's value past `ldur`'s
  reach (32 values) is read through its address, `sub` into X16 as
  `"field"` does; past one `sub`'s (about 510), by its offset in X16
  (`ldr` of a register offset). `native_reach.rs` now runs on arm64 too,
  with closures of 40 and 520 values (two procedures' values: a frame
  holds about 500).
- **Raw comparisons branched on the flags, and the test dropped wherever
  `RESULT` is dead on both ways out** (`reps::live_in`, `branch_on`, as
  x86_64's): `op2`'s `int` tests too, which arm64 already fused under the
  old, stricter test (the next instruction and the target each set
  `RESULT` first). `Cond::not` added for `branchf`. Kayak's stage 0 on
  the Mac, alternating builds: about 5.55 s to 5.4 s.
- **Strings read in line**: `string-length` and `string-ref` in
  `pure_fast`, an index past the end or not a fixnum still the
  primitive's to refuse; `string=?` of two in the call-out's path
  (`string_eq`), lengths then characters. The instructions are arm64
  register code's (`regcode.rs`), which already did all three. Kayak's
  stage 0 on the Mac: about 5.4 s to 2.9 s.
- **Frame slots held in registers**, as x86_64's write-through cache,
  forgotten at the same places: but over `RESULT` and all of REG1…REG8,
  which are registers on arm64 (x86_64's REG4…REG8 are words of the
  state). Measured by `/usr/bin/time -l`, three runs each alternating:
  59.91G instructions to 59.83G, 12.31G cycles to 12.13G (about 1.4%);
  little to remove, as arm64's register code keeps more in its eight
  registers and stores and reloads fewer slots.

## The front end's native code kept in the cache (2026-10-24)

The user, of `TODO.md` §126's next step, keeping the front end's native
code between runs: "Let's do it". On the arm64 Mac the native front end
cost a 6-line program 0.3 s of its 0.55 s, compiled again in every run.
- **What is kept: the front end after its first run**, not its word with
  its code beside it: what `%run-front-end` gave (its entry points, native
  closures) and all they reach, saved just after it. Compiling a native
  closure compiles all it calls and makes closures of, so by then the
  front end is native code; read back, it is neither checked, compiled
  nor run (faster than the cellular cache, which runs it every time).
- **Code as ordinary bloblets in the image**, named in a list, made code
  bloblets again as they are copied in (`Heap::copy_graph_with`): the
  image format and the code area are as they were. The code needs no
  relocating: it reads its fields PC-relatively, and the code area's
  place and the heap's from the state.
- **The native adapter's code shared, not copied**: `Heap::adapted` knows
  an adapter by it.
- **The call-outs' table kept with the code**, encoded, and given back
  to a machine that has numbered none of its own (`restore_callouts`);
  where it has, the front end is compiled and run as ever. Not the code's
  numbers patched on reading: the machine is fresh when the front end is
  read, in every session the CLI makes.
- **Hooks, not a dependency**: `fixpt-fx26` reaches `fixpt-native` only
  in its tests; the CLI gives the session `NativeKeeping`, as it gives it
  the native runner.
- **x86_64 not run here.** Its code reads its fields RIP-relatively and
  the code area's place from the state too, so it should read back alike;
  `FIXPT_NO_CACHE=1` turns the cache off.

## Characters, symbols and strings read in line, native convention on x86_64 (2026-10-24)

The user, of kayak's stage 0's 18M call-outs: "1 then 2". Five
primitives in line in both compilers (`pure_fast` and the call-out
path; `dq-pure-fast`, `dq-callouts`), some 10M of the call-outs:
`char->integer`, `%symbol-hash`, `%fx26-string<?`; `char-whitespace?`,
`%fx26-char-in?`.
- **A character's tag tested, a string's or a symbol's not**: as
  `string=?` and `string-ref` already are, the types say what a string
  or a symbol is; a character's bits are tested (one `and` and a `cmp`),
  and anything else is the primitive's to refuse, at the slow path.
- **`char-whitespace?` of ASCII only**: tab to carriage return and space,
  by a mask; a code point past 0x7F is Unicode's, by the primitive
  (`char::is_whitespace`), which the test's `far-spaces` exercises.
- **`string<?` as `Heap::string_cmp`**: code points compared unsigned,
  then the lengths; the other three orders left to the call-out.
- Stage 0 22.2G cycles to 21.1G, 49.7G instructions to 46.6G.

## Who allocates in Rust: a sampling global allocator (2026-10-24)

The user: "we should figure out how to profile more effectively; *we*
are the one's malloc'ing, right?"
- **The global allocator wrapped, in `fixpt-memmgmt`**: an allocator is
  `unsafe` to write, and the CLI denies `unsafe`; `fixpt-memmgmt` is
  where the workspace keeps memory from the system, and allows it. The
  CLI installs it (`#[global_allocator]`); off, it costs a load and a
  test each allocation.
- **Sampled, by the standard library's `Backtrace`**: every `N`th
  allocation's stack, resolved only at the end, so that a run of 10M
  allocations at one in 1,000 takes 10,000 stacks; no crate added. A
  thread-local flag keeps the sampler's own allocations out.
- **Grouped by the first three frames in Fixpt's crates**, past the
  allocator's and the standard library's: where in our code, which is
  what a fix needs.
- Its first findings fixed with it: `reps::successors`' vector for each
  instruction (now none, two in place) and `symbol->string`'s round trip
  through Rust's strings (now a copy in the heap): 14.4M allocations to
  10.3M loading kayak's compiler; that loading 12.45G cycles to 11.93G,
  stage 0 21.05G to 20.6G.
- With them, the call-out's arguments on the stack, not a vector, and
  `collection_due`'s thresholds in integers (three quarters as a
  fraction, the same test): some 0.5% of stage 0.

## Fewer of Rust's allocations loading (2026-10-24)

The user: "see what you can do about all those allocations during
loading". 10.3M to 5.8M loading kayak's compiler, by the sampling
allocator's report, each fix where it pointed:
- **Strings in the heap, not through Rust's**: `string_with` makes a
  string of `n` code points from a function of each, nothing gathered
  first; `make_string`, `string_from_chars`, `substring`,
  `string_search` (code point by code point, as `str::find` found by
  characters), `string`, `list->string`, `string->list` and `reverse`
  (consed as walked) on it; `string->symbol` interns through a buffer the
  heap keeps (`intern_string`). The errors are the old ones, in the old
  order; a cyclic list is still refused (`list_len`, Floyd's, as
  `list_to_vec`'s), which the suite caught missing at first, and which
  `cyclic-list-string.fx` now tests.
- **The native compiler**: `webs`' lists by key in two vectors each
  (`Grouped`), its work lists kept from one slot to the next, a block's
  leader from a count of predecessors; `procedure_x64`'s successors in
  place (`reps::Succ`).
- **The Rust checker**: `each_ty_kid` in place of `ty_kids`' vector where
  a caller only walks them; `cyclic`'s walk of each kid in turn, none
  after one that may loop, as `any` was; `free_into` matching its node by
  reference, not a clone.
- **The parser and reader**: a module's forms borrowed, not copied, onto
  its work list (a `Cow`, what a `hide` expands to owned); an atom with
  no escape read as a slice of the source.
- **Tried and dropped**: skipping `supply_loaded_in`'s reading of a text
  that names no load: forms load implicitly (`spawn`, `send`, `self`, …,
  for the processes' module), so a test of the text is wrong, as the
  suite showed, and for names that short, would rarely skip.
- The report itself: each function counted where first met in a stack,
  so that a recursion of any shape is one frame; `FIXPT_ALLOC_DEPTH` for
  more than three.

## Loading: the reader lowered only when wanted, and no linear searches (2026-10-24)

The user: "keep going", after the allocations. By `perf` on loading:
- **The reader lowered, loaded only for the eager reader**: where the
  front end runs as register code, every session also checked, lowered
  and loaded the reader alone as Scheme (`load_reader_alone`), 4.5% of
  loading, though nothing a batch run does calls it: its globals that
  the register code also gives (`read-text-at`, `parse-program`) were
  replaced by the register code's at once. Now `load_own_reader` loads
  it when an eager reader (the REPL's, `read_with_own_reader`) wants it;
  loaded after the register code, it gives those globals back to the
  register code (`entry_defines`), so that which was loaded first
  changes nothing.
- **An instruction's index by binary search**: `procedure_x64` (and
  `direct.rs`'s, and `prepare_x64`'s) found the index of each
  instruction's start in `starts` by a linear search, for every
  instruction: quadratic in a procedure's length, 3% of loading. `starts`
  is sorted, so `binary_search`; and the two `HashMap`s from a start to
  its index, the same way.
- **The checker's copies of forms**: `expand_generative` and
  `expand_datatype` copied each top-level form whole before looking at
  its head; `parse_exp` each list's items; `top_defining` the form twice,
  for what runs and for the definition kept, now one `Rc` for both.
  Fewer allocations (5.57M to 5.19M), little time.

## The major collections' budget, across every space they reclaim (2026-10-24)

The user: "you need to have your total heap be at least a multiple of
your current live storage, and it's often simplest to have it be a
multiple of your peak live storage"; "make sure you're including the size
of the code space in your heap growth calculations; even though it's a
separate space, it contributes to the so called mark/cons ratio". Then:
"Go for it".

What it was, traced on loading kayak's compiler (five majors): the old
space measured alone, from 64K words, grown to 3 times what one found
live; the heap's code area's allocation measured against a *semispace*
(the first major, the front end's 1M words of code against 64K); and
the cellular machine's code space forcing a major of the whole heap
whenever 8 MB more than was live had been installed (the last two,
copying 5.0M and 6.8M words to let go some 0.5 MB of code each).

What it is:
- **One budget** (`Heap::major_budget`, `major_due`): a major when
  `LIVE_RATIO - 1` (2) times the most one has found live has been
  allocated since the last, across the old space (promoted, or
  allocated there), the code area, the reaps' chunks and the cellular
  machines' code for the heap (`note_outside_code`, `set_outside_code`).
  Live is the old space, the code area and that code. The peak, so the
  heap never shrinks under it, as the semispace never did.
- **At least 4M words** (32 MB), `MIN_MAJOR_BUDGET`: a session's start
  loads some 2.4M words of front end, code and data. A choice; the
  semispaces start at 8M words to hold it (only what is written is
  committed: a small run's peak memory is as it was, 18.6 MB).
- **The old space sized past the budget**, and a nursery's promotion,
  so that its threshold (three quarters) is a backstop, for heaps made
  small; an image loaded counts as live (`budget_from`). A minor that
  overflows the old space leaves room for the next.
- **The cellular machine's code collected after a heap major**, whose
  weak references are fresh, when worth it: `LIVE_RATIO - 1` times what
  was live installed since (it was once what was live), the heap's ratio. A major
  of its own only when its space is half full. Collecting the code at
  any point between runs was already safe (a word's weak reference is
  cleared only by a collection that found it dead).
- **Crowding alone collects the code**, the space past half full with
  8 MB installed since it was last collected, whatever the ratio says:
  the suite (`every_program_on_every_machine`, many sessions compiling
  into one thread's machine) filled the 256 MB space when crowding also
  had to be worth it by the ratio, live code being large.
- `code_gc.rs`'s test of placed code now asks that placed code forces
  no major short of the heap's budget, and one past it;
  `code_area.rs`'s bound is the budget and what is live, over three
  majors; `a_letreap_is_collected_as_it_runs` runs `reap.fx` for 8,000
  rounds, not 300 (16M words through the reap, not 600K): it asked for
  ten collections of a reap in a heap of 64K words, and a reap's chunks
  count toward the budget as the heap's allocation does. `reap.fx`
  itself is unchanged, run by every machine's sweep.

Loading 10.30G cycles to 10.04G (two majors, 45 ms, from five, 136 ms;
one code collection, from two); stage 0 18.32G to 18.0G (three majors,
86 ms, from five, 134 ms), output the same, peak memory the same (398
MB).

## The code area remembered by its cards (2026-10-25)

The user's "look into that" (2026-10-25), of minors scanning the code area
whole.

- **Cards, as the old space has**, not a list of slots: machine code
  already marked the code area's cards (`card_mark` has no range check),
  so only `Heap::set_slot` needed widening, and one remembered set
  serves both.
- **A sorted list of object starts** (`CodeArea::starts`) to find the
  objects on a dirty card, not a crossing map: the area allocates first
  fit into holes, out of address order, which the crossing map's
  encoding assumes away; and it holds few objects (6,000 when loading),
  so an insertion's shift is cheap. Walking the area header to header
  instead, only when a card is dirty, was tried first: 56 of loading's
  135 minors walked, some 0.45 ms each, a cache miss for each header.
- **The regions still scanned whole**: machine code fills what it
  allocates there without marking, and loading has none live.

Loading 9.82G cycles to 9.57G (minors 237 ms to 174 ms); stage 0 18.2G
to 17.6G, output the same. The suite passes with `FIXPT_VERIFY_BARRIER=1`,
whose check now covers the code area too.

## A definition compiled on its own knows itself (2026-10-25)

The user's "go for it", after a profile of stage 0's native code found
kayak's `find-bind` making a full tail call through its global each time
round.

- **The fix in the driver's protocol, not in either register compiler**:
  a new entry, `compile-defining!`, which `native_define` calls beside
  `compile-name-word!`. The lambda whose word is named for the definition
  takes it as `c-defining` (`c-take-defining`), and the thunk's program
  counts the one write the driver makes after it runs (`c-defined-writes`,
  into `c-form-writes`), so each guard expects what the global will hold.
  The alternative, compiling such a definition whole through
  `c-define-lambda`, would change who writes the global and when, which
  the native convention's driver relies on.
- **Matched by name**, the word's name against the definition's: the
  thunk's own lambda (`define NAME`) is compiled first and must not take
  it. `names_its_word` already decides when the lambda is so named.
- Tested by the REPL's `,disassemble` (`native_reach.rs`): a guard of the
  procedure's own global, written once.

Stage 0 17.62G cycles to 16.70G, loading unchanged, output the same.

## The heap in huge pages (2026-10-25)

After the user moved the baseline to kayak `d5840ee` and asked to go on;
`docs/performance.md`, "The heap in huge pages".

- **The whole heap mapping asks**, semispaces, regions, nursery and code
  area alike, not each part: one call where the mapping is made. The code
  area's pages are replaced by a shared mapping when first used (its
  execute view), which the advice does not reach, and needs none.
- **Not the card table or crossing map**: sparse, so a huge page would
  commit 2 MiB for each byte written apart.
- **Peak memory up some 20 MB** (4%) for 5.6% fewer cycles: accepted
  without asking, as a size the heap's growth already allows; tell me if
  memory matters more.
- The measurement scripts now report kernel cycles beside user cycles:
  this cost had been invisible in `cycles:u` alone.

## Syscalls as two definitions (2026-10-26)

Kayak's request (`docs/research/syscalls.md`), whose "Open questions" were
Fixpt's to decide; the rest of what Fixpt chose is in that note's last
section. In short:

- **A declaration expands into ordinary definitions**, the host name and
  canonical type as literals, rather than a new form for every machine to
  compile: three runtime primitives serve all nine machines, and the check
  at load is the declaration's own run. The cost: a check runs when the
  declaration does, not before the program's first form.
- **`syscall-available?` is a hidden global's name**, so that the FX-26
  compiler, which compiles the parser's trees, needs nothing from the
  checker at a use.
- **`(io sys)` one atom; declarations per program; `syscall-available?`
  of declared names only**: the open questions, each the simpler side.
- **`code:exec-view/1` always -1** in Fixpt, rather than pinning arrays
  for it: allowed by the request, and nothing in Fixpt needs a view.
- **At most six arguments**, constant regions and specifications refused:
  limits nothing asked for yet needs past, each easy to lift.
- **The evaluator written in FX-26 gets a table of its own**, the same
  three, so that every machine answers alike.


## Every procedure's code runs (2026-10-26)

Kayak's request (`docs/research/code-stubs.md`), whose open questions were
Fixpt's to decide; the note's last section has the rest. In short:

- **The code area in two parts**, words and the shared stub below native
  code, `code-lo` the native part's start: so the older clause's test
  keeps its meaning exactly, and the machines that tell native closures
  from cellular ones by `code-lo` need no change. The request put
  `code-lo` at the area's start instead, the word's stub then entering
  `foreign`; same result, more change.
- **One shared stub at field 2 for the other kinds**, the VM's closures,
  primitives and continuations and cellular continuations, rather than
  proving they never reach native code: their layouts change by a field,
  which every reader of them takes by name.
- **Words only run stay in the heap; words made again and again alike are
  made once.** Putting every word made in the area would put one there for
  every call from native code.
- **Images carry the code area** (version 8) rather than copying code out
  as ordinary bloblets and back: the bytecode VM's closures hold the stub,
  so every image would need the special case.
- **The convention read as data keeps `native-when-code-at-least`** at
  `code-lo` under the new clause, with a new flag: a generator written
  before keeps making the code it made, which still runs.
- **`foreign` takes a native closure too**, so that the older clause's
  code, wherever its test sends one, never fails.

## Queries in the checker, asked by the REPL and the command line (2026-10-27)

- **One engine, two doors**: `fixpt_fx26::query`, asked by `,query` and by
  `fixpt query`, so a script or an editor gets the REPL's answers.
- **The sources checked again** for each question rather than kept checked
  with their facts: a question is rare, and a checked program kept whole
  would be every session's cost. Heist's editor (15 files, 360 KB)
  is answered in 1.2 s, built for release.
- **`,query KIND ARG`**, one command, not a command for each kind: the
  existing `,returns` (a subtype search of the environment) means
  something else and stays.
- **A `T` given through a callback counts as given**; the toll decides
  `constructs` from `transforms`. The answers are what the types allow, not what
  the code does.

## A file's module type, `load-moduleof` (2026-10-27)

The user chose the form and its names (`load-moduleof`,
`load-input-moduleof`) and that abstract types are binders. Choices of
mine, not asked:

- **The arguments**: descriptions for a `poly`, and for a procedure's
  parameters a module's *name* only, as a dependent call takes one (M5).
  Not general expressions, nor a check that the module named fits the
  parameter's type: a value of the type comes only from a real
  application, which is checked there.
- **What is left must be a module's type**, so neither name promises a
  module that is not there (a `load-input` file of data, say).
- **Type loads before the expressions' loads, in each form**, and in each
  item of a module, so that the two parsers and the driver that reads files
  for the FX-26 front end read files, and number them, alike.
- **A `define-type` naming a file is not declared ahead**: its file's
  hidden global must be defined before it, and declaring it ahead would
  load the file outside any form, its definition never run. So it must
  come before the types that use it.
- **A file of its own for the FX-26 checker's part**, `check-read-made.fx`,
  since `check-read-descs.fx` was full; it is given `k-parse-d` as an
  argument rather than calling it, being before it.
- **`check-program.fx` made room** by using `k-has-name?` and `reverse`
  for its own copies of them, rather than a split.

## A file's abstract types shared by its loads (2026-10-27)

The user decided to share them. How, mine:

- **By strengthening where a load is used**, not by changing what a
  binding does: a load's abstract types become descriptions of the hidden
  global's own, so every binding of one is an alias, as OCaml's `module
  type of struct include M end` is of `M`. A binding of any other module
  is still opaque (Sheldon's `let` rule), and makers still make types of
  their own.
- **Only `load-module`'s modules.** A `load-input` file whose value is a
  module with abstract types is not strengthened: none such is in use, and
  its files are functions, whose modules are made by applying them.
- **Named for the file's base name**, `x.fx..t`, not its whole key: two
  files of one name in two directories print alike, though their types
  stay apart.

## A top-level `include` (2026-10-27)

The user asked for it (Heist's problem F). How, mine:

- **An `import` of every name, made where the module's type is known**,
  rather than a form of its own through both front ends' parsers,
  checkers and compilers: the FX-26 parser, compilers and evaluator work
  from trees made before checking, and `import` already goes through all
  of them.
- **The driver tells the FX-26 parser what each gives**, by position, for
  `fixpt check`, rather than giving it a text with the `import`s written
  in: a text changed so moves every place after it.
- **It ends what is declared ahead.** The Rust checker can make it an
  `import` only once `m` is defined, after the types are declared ahead;
  so both read a type after it in order. The FX-26 one could have
  declared its types ahead too, the driver having told it; the two would
  then disagree.
- **A module's name only**, as `import` takes: `(include (load-module …))`
  would need a hidden binding of its own.
- **A REPL's lines for each definition** (`run_each`), not the last only.

## `restrict` (2026-10-27)

The user named it; the semantics are the research note's. Mine:

- **A type form**, `(restrict T name …)`, not one on a module value: where
  it is wanted is a parameter's type or a `define-type`; a module is
  restricted by `(the (restrict T …) m)`.
- **The unnamed abstract type marked `%hidden:t`** in the binder's name,
  and paired by its name without the mark, rather than a module type with
  a place of its own for unnamed binders: no change to module types'
  shape in either checker.
- **`hide`'s refusal kept**: lifting it is the user's decision of
  2026-10-09 to revisit, not part of this.

## Names and frames for `gdb` and `lldb` (2026-10-27)

The user: "Yeah do 1, 2, and 3" (names, lines, values). Names first.
- **ELF objects, Linux x86_64 only**: the machine at hand; Mach-O for
  macOS left (TODO §26).
- **Frames read from the bytes, not told by the compilers**: one analysis
  for the Rust compiler's code, the FX-26 compiler's (byte-for-byte the
  same) and the hand-written stubs, with no change to either compiler.
- **Frames lazily, on a debugger's breakpoint**: made eagerly they cost
  7% of stage 0 even after a structured decoder took them from 50%; the
  default costs 0.7%. The price: a debugger attached to a running loop
  sees frames only once the program goes on to a time slice.
- **On by default**, `FIXPT_JIT_DEBUG` to change it: a debugger is most
  wanted where nobody planned for it.

## Allocation in line natively, for Heist (2026-10-27)

- **The heap's too, not only the region's**: the benchmark and s7st make
  references and arrays at a region variable, which allocates in the heap
  (`%make-box`, `%make-bloblet-filled`); the region primitives the request
  named would not have changed its numbers. Both are done.
- **16 fields in line**, a loop storing them: s7st's frames are under 8;
  the loop keeps the code short for every length.
- **arm64 left** (TODO §136, since done: `DONE.md` §154): untestable here,
  and a mistake there would corrupt the heap.

## Lines for `gdb` and `lldb` (2026-10-27)

- **Places in the register word's suffix**, which nothing used: no new
  field for both compilers to agree on, and it moves with the word.
- **A source per text compiled, mapped back through the form's written
  text**: each form is written again before it is compiled, often inside
  more; rather than carry spans through the writing, a place is found by
  where the form's text is in the text compiled.
- **No marks for variables and constants**: their code is their parent's,
  and marking them doubled the cost (3.0% to 0.8% of stage 0).

## Values for `gdb` and `lldb` (2026-10-27)

- **The program writes its own values**, called by the debugger, rather
  than DWARF types and formatters: a tagged word's meaning is the runtime's,
  and its printer is already written; DWARF would need the compilers to
  say each slot's type.
- **Commands, not pretty-printers**: no slot or register has a DWARF type
  for a printer to hang on.

## A pure syscall (2026-10-27)

- **The call's effect given by a `the` on its operator**, `%syscallN`
  polymorphic in it: the inner call then has exactly the declared effect,
  so a compiler acting on purity (`lower.rs`'s pure calls) sees the truth.
  Typing `%syscallN` `pure` would have checked too, but a call writing a
  region would then look pure inside the procedure. The `the` is noted
  plain as `(with #%fx n)` is, so no compiler builds a value of
  `%syscallN`, which has no fixed arity.
- **`kayak:string-utf8-length/1` in Fixpt's runtime**, under the name Kayak
  gave it, so its compiler's declaration loads here too; the test's
  runtime that has a pure syscall. Fixpt's strings are not UTF-8, so it
  counts, still without the copy `string->utf8` makes.

## A module's maker in native code (2026-10-28)

- **The two limits lifted, not the items kept in a record** (Heist's
  first choice): with both lifted, typing in the modules' editor is as
  fast as with globals, measured. A record would spare each item's
  closure copying what it captures, once, at start-up, which the
  measurement does not show as what costs: the checker does (TODO §138).
  It stays a choice to make if start-up apart from checking shows it.
- **16 KiB**: a frame is pushed before the stack's limit is checked, and
  the limit leaves `STACK_SLACK` (64 KiB) below it; a quarter of it leaves
  room for the overflow's own frames.

## Strings at a region (2026-10-28)

- **`string` kept as the name, `(stringof const)` made as it**: the user
  chose one type; making the frozen form *as* `string`, rather than
  `string` as an abbreviation expanded everywhere, keeps every rule that
  knows `string` (data, shapes, syscalls' crossing types, the printer) as
  it was, and needs only the matching where a region is still unknown.
  `acyclic` too, since a string holds no cycle.
- **Only the reads that a mutable string needs are generalized**: `length`,
  `ref`, `substring`, `=?`, `->list`, `->utf8`. The comparisons, the
  searches and `string-append` still take `string`; a string at a region
  is frozen or copied first. Generalizing more is a type each, later.
- **`substring` still gives a `string`**: its region would otherwise be a
  new binder nothing solves, and every `(define x (substring …))` would
  change its type.

## `module-parameters` of modules (2026-10-28)

- **Read as a `load-input` file**: a file of module parameters is the
  `lambda` Heist wrote by hand, and is read as one, its key `input:`;
  so the checkers' scoping, already proven by Heist's editor, is unchanged,
  and no rule is new. A file is told by its first form, in both parsers
  and the driver alike, before its key is chosen.
- **Every module parameter included, hidden**: (2) as the default, with no
  way to opt out yet; a file that wants a module's names only by `with`
  can still be written as a `lambda`.
- **A pure expression item refused**: found converting Heist's editor, where
  a `load-input` file loaded by `load-module` became one pure expression
  item, its module empty, silently.
- **(3), a parameter typed by its file alone, not done**: Heist measured
  the parameters' types as costing nothing to check, so it would save only
  writing.

## Interning, and names by structure (2026-10-28)

- **The printer, not interning, changed**: the checkers named a type by its
  node's id, which interning shares; naming by structure (the user's table
  of aliases) leaves interning free. Of the rules for which aliases name,
  "where it abbreviates" (a type with parts) is the user's, as a printing
  rule rather than one about types.
- **Alias nodes, which keep provenance, not done**: every function that
  rebuilds a type would have to keep them, in both checkers.
- **Stage 0's 3% kept for now** (the user's word): to be brought down, by a
  cheaper lookup or fewer nodes looked up.
