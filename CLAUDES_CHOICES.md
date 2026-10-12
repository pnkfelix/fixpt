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

The user: "Go for it" (TODO §105's next item, `direct.rs`).

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
