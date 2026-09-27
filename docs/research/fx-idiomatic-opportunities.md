# Opportunities for `src/fx-idiomatic/`

Research note, 2026-09-27 (PLAN.md "The next queue", item 8). The FX-26
front end (`crates/fixpt-fx26/src/*.fx`) mirrors the Rust front end rule for
rule. This note looks for places where an idiomatic version should differ,
and says what each change would gain. For each opportunity it gives:
- what the code does now, and which invariant is left implicit;
- the change at the level of types;
- whether FX-26 can express the change today;
- what the change costs, and whether it would change anything observable.

"Observable" means the outputs that the planned three-way tests compare:
- the checker's lines and first error (message, span);
- the parser's result or error;
- the compiled words.

Internal representation is free to change. Order is not. The first error
found, fresh region names (`@r.3`), and the order of atoms in a `maxeff` all
depend on the order of traversal and on counters.

Every `file:line` below refers to the sources as they stood on 2026-09-27;
`check.fx` and `parser.fx` were being edited at the time. The ids (Q1, M3,
L1, and so on) are this note's own.

## Method

I read the following:
- `docs/fx26.md`;
- `docs/research/sizes.md`, `gadts.md` and `generative-types.md`;
- PLAN.md item 8;
- all of `parser.fx`, `table.fx` and `layout.fx`;
- about half of `check.fx`: its data, arena, printing, reading of
  descriptions, resolving, masking, substitution, subtyping, instantiation,
  facts, programs and proofs;
- the heads and data definitions of the other files.

I tested the claims marked **(tested)** with small programs under
`$CLAUDE_JOB_DIR/tmp/`, using `fixpt repl --dialect fx26`. A table at the
end lists them. I did not change any source.

Two facts frame the rest:
- **`spin` is everywhere.** `check.fx` has 382 occurrences of `spin`. 109
  signatures are `(maxeff checks spin)`. The checker's entry point is
  `check-program : (subr (maxeff checks spin) …)` (`check.fx:5432`).
- **There is one region.** Almost all state lives in the single region `@t`
  (`check.fx:22-26`): 49 top-level `ref`s, of which `k-reset`
  (`check.fx:1864`) clears 35.

PLAN.md item 8 already sets the direction. The mirror becomes nominal (`TyId`,
`DVar` and `Sym` as generative types). The idiomatic front end becomes
structural where its data is: `syn`, `datum`, trees, and "types as `finite`
data, so that size-change can see a walk of a type shrink". This note tests
that direction and adds to it.

## Ranking at a glance

The **Today?** column says whether FX-26 can express the change:
- **yes**: it can;
- **part**: some of it needs a planned feature;
- **no**: it needs language work.

The **Diverges?** column says whether observable output would change. "no"
means only the internals change.

| Rank | Id  | Opportunity                                                          | Main places                                                   | Today?           | Cost | Diverges?                           |
| ---- | --- | -------------------------------------------------------------------- | ------------------------------------------------------------- | ---------------- | ---- | ----------------------------------- |
| 1    | Q1  | Finite spines for the table's buckets: lookups need no `spin`        | `table.fx:12,27-58`                                           | yes (tested)     | XS   | no                                  |
| 2    | Q2  | Loops bounded by `>=` or by `nat`, not by `=`                        | `check.fx:173-191,565`; `arm64.fx:18`                         | yes (tested)     | XS   | no                                  |
| 3    | Q3  | Effects declared tighter than they need to be                        | `parser.fx:111-125`; `check.fx:800`                           | yes (tested)     | XS   | no                                  |
| 4    | Q4  | Products, not pairs at `@t`, for immutable tuples                    | 57 × `(pairof … @t)` in `check.fx`                            | yes (tested)     | S    | no                                  |
| 5    | Q5  | Named labels, not `(1 …) (2 …)`                                      | 85 × `(productof (1` in `check.fx`                            | yes              | S    | no                                  |
| 6    | Q6  | Sums for integer codes: kinds, variance, `letregion` forms, measures | `check.fx:47,316,1450,1753,3540-3543`; `parser.fx:48`         | yes (tested)     | S    | no                                  |
| 7    | Q7  | An `opt` type in place of `-1` and of "none or one" lists            | about 40 places                                               | yes (tested)     | S-M  | no                                  |
| 8    | Q8  | The compiler's lists `finite` inside their refs                      | `compile.fx:45-47`; `regcode.fx:35,41`                        | yes (tested)     | S    | no                                  |
| 9    | M1  | Structured errors, not error messages parsed back                    | `check.fx:2668-2692`                                          | yes              | S    | no, if rendered the same            |
| 10   | M2  | A node type without `ty-link`, returned by `k-get`                   | `check.fx:58-90,234-241`                                      | yes (tested)     | S    | no                                  |
| 11   | M3  | Generative ids: `ty-id`, `dvar-id`, `gen-id`, `label`                | `check.fx:45-47,92,2291,2347-2359`                            | yes (tested)     | M    | no                                  |
| 12   | M4  | Substitution maps split by kind; dvars carry their kind              | `check.fx:56,92,95-105,2132-2156`                             | yes, phantom; N4 | M    | no                                  |
| 13   | M5  | Spans as one product; each node split from its span                  | `check.fx:1643-1691`; `parser.fx:29-63`                       | yes              | M    | no                                  |
| 14   | M6  | The parser without `spin`: parts, not `nth` and `drop`               | `parser.fx:174-437`                                           | yes (model)      | M    | no                                  |
| 15   | M7  | Regions by role; each analysis's state private and masked            | `check.fx:22-26,264-450,3547-3562`                            | part             | M-L  | no                                  |
| 16   | M8  | Instructions as datatypes; registers and conditions not bare ints    | `regcode.fx:18-64,557`; `native.fx:28-39`; `arm64.fx:14-42`   | part (N5c)       | M    | no                                  |
| 17   | M9  | Primitives and operations as sums, not strings                       | `evaluator.fx:116-228`; `compile.fx:452-484`; `regcode.fx:44` | yes              | M    | no                                  |
| 18   | M10 | Zips indexed by length, with `nlist` and `confirm-length`            | `check.fx:1234,2261,2389,3309,1505`                           | yes (tested)     | M    | no                                  |
| 19   | M11 | The reader's state and cursor as sums                                | `eager-reader.fx:74-89,103-146`                               | yes              | M    | no; the Rust callers use procedures |
| 20   | M12 | One tree family for `exp` and `kx` ("trees that grow")               | `parser.fx:29`; `check.fx:111`                                | yes              | M    | no                                  |
| 21   | L1  | Types as `finite` data (`mu`, back-references): walks end, no epochs | the whole arena, `check.fx:211-262`                           | part (tested)    | XL   | risk: names in printing             |
| 22   | L2  | Walks of graphs without `spin`: fuel, or a measure                   | `check.fx:236,949,1889,3105`                                  | part             | M    | no                                  |
| 23   | L3  | Failure that a handler can discharge: abort-only tags                | `check.fx:152-155`; `parser.fx:80`; `compile.fx:50`           | no               | L    | no                                  |
| 24   | L4  | Invariants kept by smart constructors, with hiding                   | `check.fx:54,490-502,593-620`                                 | no (G4)          | S    | no                                  |
| 25   | L5  | Bounded naturals: registers, arena indices, array bounds             | `arm64.fx:14`; `check.fx:213-262`                             | no (N5c)         | M    | no                                  |
| 26   | L6  | Kind-indexed descriptions, a tree indexed by phase                   | `check.fx:56,92,111`                                          | no (N4)          | L    | no                                  |

## Quick wins

These are local changes. FX-26 can express each of them today, and none
changes what anything prints.

### Q1. Finite spines for buckets, and a table whose lookups end

**Now.** A bucket is `(listof (pairof k v r) r)` (`table.fx:12`). Its
spine is at the table's own region, which can be written, so it may be
cyclic. So `bucket-find` must say `spin` (`table.fx:29`), and with it:
- `table-ref` and `table-has?`;
- every lookup in the checker (`k-lookup`, `check.fx:404`; and
  `k-binding-depth`, `check.fx:2959`), and everything that calls them.

The spine is never written: only an entry's `cdr` is (`set-cdr!`,
`table.fx:111`).

**Change.** Make the bucket `(listof (pairof k v r) finite)`. The spine
becomes finite, and each entry stays a mutable pair at `r`. Consing onto a
finite list allocates into `finite` directly.

**Today.** Yes (tested). With the change:
- `bucket-find` is `(read r)`, with no `spin`;
- `table-ref` and `table-has?` lose `spin`;
- `(table-ref t 'a 0)` is `(read @r)`.

`rehash-array` still needs `spin`. It counts up to `(array-length old)`,
and size-change accepts `string-length` as a bound but not `array-length`
(`terminate.rs:546`). Two gaps close this off:
- rewriting it to count down a `nat` does not help, because `array-length`
  gives an `int`;
- no test turns an `int` into a `nat` (tested). See the language gaps.

So `table-set!` keeps `spin` for now.

**Benefit.** Every name lookup in the checker loses `spin`. That is the
first step towards a checker whose effect shows that it ends. The change is
one line, and `table.fx` has no Rust twin to agree with. There is no
divergence.

### Q2. Loops bounded by `>=` or `nat`

**Now.** Several loops say `spin` only because their test is `=`:
- `k-starts-at?`, `k-find-sub` and `k-str-cmp` (`check.fx:173-191`), and so
  `k-mentions-token?` and `k-expected-split` (`check.fx:565,2670`);
- `arm-pow2` (`arm64.fx:18`), and so every arm64 encoder that calls it;
- the evaluator's `occurs?` (`evaluator.fx:120`) is likely another.

Size-change rightly refuses these. `(= n 0)` alone does not bound a
count-down, since `(f -1)` loops.

**Change.** Test with `>=` or `<=`, bound the index on its own
(`(> at (- (string-length s) (string-length sub)))`), or make the counter a
`nat`.

**Today.** Yes (tested). The following all check as `pure`:
- `k-starts-at?`, `k-find-sub` and `k-str-cmp` rewritten so;
- `arm-pow2` with `(<= n 0)`;
- a `nat` version, `(subr pure (nat) int)`, whose only test is `(= n 0)`.

**Benefit.** The printing of types (`k-mu-wrap`, `check.fx:718`) and the
whole arm64 encoder lose a `spin` that was never real. There is no
divergence.

### Q3. Effects declared tighter

**Now.** Several helpers declare more effect than they have:
- `parser.fx`'s `syn-nil?`, `len`, `nth` and `drop`
  (`parser.fx:111,120-125`), which declare `(read @s)` or `parses`;
- `check.fx`'s `k-head` (`check.fx:800`), which declares `(read @s)`.

These are walks of `(listof syn finite)`, which are pure. The declarations
date from when `syn` lists lived at `@s`.

**Change.** Declare them `pure`, and make `nth` and `drop` take a `nat`.

**Today.** Yes (tested): `(subr pure ((listof syn finite) nat) syn)` checks.

**Benefit.** A declared effect is a promise to readers and to the licence.
One that is too big costs precision all the way up the call graph. There is
no divergence.

### Q4. Products, not pairs at `@t`, for tuples that never change

**Now.** `check.fx` has 57 `(pairof … @t)` types. Among them:
- bindings, `k-bindings` (`check.fx:390`);
- `k-named` (`check.fx:310`), `k-bounds` and `k-outers` (`:294,297`);
- `k-certified` (`:276`);
- the trail pairs in subtyping (`:2280`);
- `k-benv` (`:2291`).

None is ever written: `check.fx` has no `set-car!` or `set-cdr!`. But
reading any of them is `(read @t)`. That is why `k-find` (`:391`),
`k-named-has?` (`:356`), `k-benv-var` (`:2292`) and about a hundred
signatures say `(read @t)`.

**Change.** Use `(productof (name symbol) (ty ty-id))`, or a pair frozen at
`finite`.

**Today.** Yes (tested): a lookup over a finite list of products is `pure`.

**Benefit.** Pure helpers show what really touches the checker's state
(the arena, the environment), which Q7 and M7 build on. There is no
divergence.

### Q5. Named labels, not positions

**Now.** 85 product types are positional: `(productof (1 int) (2 int))` for
binders, `(extract l 4)` for a lemma's hypotheses, `(extract gen 4)` for a
generative type's representation. Nothing but comments says what each
position means (`check.fx:46,316,330`). `regcode.fx:64` already does
better, with `(productof (items …) (leaf bool) (nreg …) …)`.

**Change.** Use labels:
- `(productof (var dvar-id) (kind kind))`;
- `(productof (name symbol) (params k-binders) (variance …) (rep ty-id))`.

**Today.** Yes. There is no cost at run time: fields are laid out in
label order.

**Benefit.** Readability, and a class of mix-ups (`extract … 2` for `… 3`)
that the checker cannot catch between fields of the same type. There is no
divergence.

### Q6. Sums for integer codes

Several small integer codes appear, each an enumeration with a meaning
kept only in comments:

| Code                   | Where                                                                                             | Values                                                   |
| ---------------------- | ------------------------------------------------------------------------------------------------- | -------------------------------------------------------- |
| kind                   | `check.fx:46-47`, printed by `:530-534`, 59 comparisons such as `(= k 3)`                         | 0 region, 1 effect, 2 type, 3 place, 4 data, 5 size      |
| variance and polarity  | `check.fx:316,1450-1518,2631-2639`                                                                | 0 co-, 1 contra-, 2 invariant                            |
| `letregion` form       | `parser.fx:48,225`; `check.fx:119-123,1753,4442-4451`                                             | 0 `letregion`, 1 `letrena`, 2 `letreap`, 3 `letfreeze`   |
| guard                  | `check.fx:3540`                                                                                   | 0 below, 1 above                                         |
| size-change slot       | `check.fx:3542,3822-3828`                                                                         | `parameter × 3 + measure`, measure 0 parts, 1 down, 2 up |
| atom rank as predicate | `check.fx:472-478,2033,2100,3420`                                                                 | `(> rank 1) (< rank 5)` means alloc, goto or comefrom    |
| type rank              | `check.fx:2160-2166,3022-3030`                                                                    | `(= p 6) (= a 18)` means a pair pattern and a `nlist`    |
| argument handling      | `regcode.fx:557-575`                                                                              | -1 simple, -2 in its register, otherwise a slot          |
| base type ids          | `check.fx:376-382`, fixed by the order of the `k-basic` calls in `k-reset` (`check.fx:1873-1875`) | 0 int … 6 symbol, 10 void                                |

Two of these hide real hazards:
- **Two codes share one function.** At `check.fx:1753`,
  `(kind (if (or (= k 0) (= k 3)) 0 3))` maps a *form* code to a *kind*
  code. In both spaces, 3 means something (`letfreeze` in one, `place` in
  the other).
- **The base type ids depend on call order.** `k-symbol` is 6 only because
  `k-basic "datum"` is called fifth. Nothing checks that.

**Change.** Use datatypes:
- `(define-datatype kind (k-region) (k-effect) (k-type) (k-place) (k-data) (k-size))`;
- `(sumof (co) (contra) (inv))`;
- `(sumof (letregion) (letrena) (letreap) (letfreeze place))`, whose
  `letfreeze` carries its place, which today is a symbol that means nothing
  for the other three (`parser.fx:52`);
- a size-change slot as `(productof (param nat) (measure measure))`;
- predicates written as `tagcase`, not rank ranges;
- base types found by name, or held in a product built by `k-reset`, not
  fixed integers.

**Today.** Yes (tested: a `kind` datatype, and a narrower sum
`(sumof (k-region …) (k-place …))` that widens to `kind`). One limit: a
constructor of `define-datatype` returns the whole datatype, so `(k-place)`
does not fit the narrower sum. You must write `(sum k-place (product))`
(see the language gaps).

**Benefit.** `tagcase` without an `else` must cover every tag, so adding a
kind (as `size` was added) becomes an error at every place that must
handle it. Today it silently falls into the `else "type"` of `k-kind-name`
(`check.fx:531`). There is no divergence: each code prints as before.

### Q7. An `opt` type in place of sentinels

**Now.** "None" is written in two ways:
- **`-1` in an `int`.** Examples:
  - `k-find` and `k-lookup` (`check.fx:393,405`);
  - `k-knot-of`, `k-memo-find` and `k-part-find` (`:1139,2158,2285`);
  - `k-upper-bound` (`:3292`), `k-sc-member` (`:3572`) and `k-take-inside`
    (`:5282`);
  - the "no expected type" argument of the synthesis procedures
    (`:4366-4470`, `(k-synth-app x f args -1)`);
  - `r-frozen -1` for the heap (`:35,838-844`);
  - `a-spin`'s region `(r-var -1)` (`:477`);
  - `e-bloblet`'s field index (`parser.fx:57`);
  - `confirm-length`'s "a variable, not a literal" (`parser.fx:257`);
  - `syn-int` (`parser.fx:118`);
  - `c-this-params` (`compile.fx:143`) and `c-arity` (`compile.fx:452`);
  - `n-cont` and `n-target` (`native.fx:36-39`);
  - every arm64 field that does not fit (`arm64.fx:11-42`).

  `k-label` adds a third kind: labels are negative numbers from -1000 down
  (`check.fx:2358`), and 0 means "not found" (`:2351`).
- **A list of none or one.** Examples:
  - `ty-link` (`check.fx:79`);
  - `k-lookup-desc` (`:430`);
  - `k-as-subr` (`:1830`);
  - the facts at `:4199-4299`;
  - `k-place-of` (`:5105`);
  - `t-define`'s type (`parser.fx:65`);
  - `parse-else` (`parser.fx:425`);
  - a cursor's lookahead and `pending`, and the reader state's `ks`
    (`eager-reader.fx:84,103`).

A sentinel can be used as a value by mistake. `(array-ref marks -1)`, or a
`-1` type id passed to `k-get`, is a failure at run time. `k-ty-known`
(`check.fx:3599`) exists only to guard against that.

**Change.** Use `(define-datatype (opt (t type)) (none) (some t))`. The
arm64 encoders get `(opt int)`, or better, fields that are shown to fit
(L5). Checking against an expected type becomes
`(sumof (synth) (check ty-id))`, or two entry points.

**Today.** Yes (tested: `find` returning `(opt int)`, matched by
`tagcase`). This needs one parametric datatype in a shared prelude.

**Benefit.** A lookup's result can no longer be used without checking it,
and `-1` stops being a type id, a label and a region at once. The cost is
some extra `tagcase`, and an allocation per `some`: a frozen bloblet, where
`-1` costs nothing. It is worth measuring in the arena's hot paths. There
is no divergence.

### Q8. The compiler's lists `finite` inside their refs

**Now.** `compile.fx` and `regcode.fx` keep their code, environments and
symbol sets as lists at `@k` (89 occurrences), for example:
- `items`, `code` and `cenv` (`compile.fx:45-47,133`);
- `syms` (`:195`);
- `renv` and `rargs` (`regcode.fx:35,41`).

So every walk of them says `spin`: `c-reverse`, `c-member?`, `c-find`,
`c-where`, `r-reverse`, `r-last-hard`, and more. What changes is the `ref`
that holds each list, not the lists themselves.

**Change.** Make these lists `(listof item finite)` inside a `(ref … @k)`.

**Today.** Yes (tested). A model of `c-emit` and `c-reverse` gives `c-emit`
as `(maxeff (read @k) (write @k))`, with no `alloc`, and `c-reverse` as
`pure`.

**Benefit.** The compiler's walks end by their types. `compile-program`
would still say `spin` for the walk of the tree (see M6), but far less
would. There is no divergence.

## Medium

These are larger rewrites of one area. Most are expressible today.

### M1. Structured errors, not error messages parsed back

**Now.** `k-rewriting` (`check.fx:2674-2684`) catches a failure. It then:
1. splits the failure's *message string* on `" is expected here, and this is a "` (`k-sep`, `:2672`);
2. takes the prefix `"a "` off with `k-expected-split` (`:2670`);
3. rebuilds a different message from the pieces.

The Rust does the same (`infer.rs:546`, `check.rs:1887,1911`), so this is
the mirror's inheritance. `k-result` (`check.fx:147-150`) mixes a program's
result (`k-ok`) with an inner computation's (`k-done`). So every catcher
has a `(k-ok (xs) (k-fail "k-ok inside" a b))` arm that cannot happen
(`:2684,2692`).

**Change.** Give the error a structure:
- `(define-datatype k-error (e-mismatch ty-id ty-id) (e-say string))`,
  carried with its span;
- render it to the same string only at the top;
- rewriting matches `e-mismatch` and needs no string search.

Using a separate answer type for inner catches removes the impossible arm.
That runs into the fixed answer type of a prompt tag (L3). Until then, one
tag can carry an error payload, and the handler can build the answer.

**Today.** Yes.

**Benefit.** A type whose printed form contained the separator would break
the split. More important, the error becomes data, which `,help` and a
future structured diagnostic (a path, as `gadts.md` describes for
"unknown") can use. There is no divergence if it renders byte for byte.
This is also worth doing in the Rust.

### M2. A node type without `ty-link`

**Now.** An arena slot is a `k-ty`, which includes `(ty-link k-ids)`: a
forwarding slot of none or one (`check.fx:79`). `k-get` (`:238`) follows
the links, but its type still includes `ty-link`. So every `tagcase` of
`(k-get t)` either ends in an `else`, or has a `ty-link` arm that cannot
happen: `(ty-link (x) "?")` in printing (`:752`), `(ty-link (x) t)` in
substitution (`:2194`), and `ty-link`'s rank 14 in `k-ty-rank` (`:2165`).

**Change.** Declare `k-node` as the sum without `ty-link`, and `k-ty` as
`k-node` plus the link. `k-get` returns `k-node` from
`(tagcase … (ty-link (to) …) (else x x))`, whose `else` binding has the
narrower type.

**Today.** Yes (tested: `k-get : (subr … (int) node)` checks, and a
`tagcase` of its result needs no link arm). A GADT is not needed; width
subtyping on sums does it. Stating the sum twice is clumsy (see the gaps).

**Benefit.** The "unfilled or unfollowed link" state becomes impossible
where it is impossible. There is no divergence.

### M3. Generative ids

**Now.** Many kinds of number share the one type `int`:
- type ids, description variables and generative indices (`k-gen-of`);
- binder labels (negative, `check.fx:2358`);
- epochs, and slots;
- size-change parameter indices.

`k-benv` maps dvars to labels, and both are ints (`:2291-2302`), so a
confusion would type-check. `k-map` keys are dvars and `dt` payloads are
type ids, all `int` (`:92`).

**Change.** Use `define-generative` for `ty-id`, `dvar-id`, `gen-id` and
`label`, each with its `up-` and `down-` at the arena boundary. PLAN.md
already plans this for the *mirror*. For the idiomatic front end it
matters only as long as the arena stays (L1 would remove `ty-id`).

**Today.** Yes (tested): passing a `dvar-id` where a `ty-id` is wanted is
refused with "argument 1 is a dvar-id, where a ty-id is expected". The
conversions cost nothing at run time, and size-change sees them as the
identity.

**Benefit.** Mix-ups between the id spaces become type errors. The cost is
a `down-` at each array access. There is no divergence.

### M4. Substitution maps split by kind

**Now.** A `k-map` is a list of `(dvar . k-desc)`, where `k-desc` is
`dr | de | dt | dz` (`check.fx:56,92`). Each lookup therefore ends with an
arm that should not happen:
- `k-subst-region` has `(tagcase (cdr (car f)) (dr (x) x) (else y r))`
  (`:2135`);
- so do `k-subst-effect` and `k-subst-size` (`:2154,694`) and
  `k-match-region` (`:2504`).

`ds-var int int` (`:100`) carries the kind as an integer beside the dvar,
and `k-proj-map` (`:2789`) checks at run time that a description fits its
binder's kind.

**Change.** Make it `(productof (regions …) (effects …) (types …) (sizes …))`,
each with its own payload type. The dvar id can carry its kind as a phantom
parameter, `(define-generative (dvar (k type)) int)` instantiated at empty
marker types, so that a region variable's id is a different type from an
effect variable's.

**Today.** The split and the phantom parameter: yes. A single
heterogeneous map whose entries are kind-indexed needs existentials (N4).

**Benefit.** No impossible fallbacks, and a wrong-kind substitution becomes
a type error. There is no divergence.

### M5. Spans as one product; each node split from its span

**Now.** Every variant of `exp` and `kx` ends with `int int` for start and
end (`parser.fx:29-63`; `check.fx:111-138`). So four procedures are
tagcases with one arm per variant, only to fetch those two fields:
`k-start`, `k-end`, `exp-start` and `exp-end` (`check.fx:1643-1691`).
Adding a form means adding four arms.

**Change.** Use `(define-type span (productof (start nat) (end nat)))`, and
make a node a `(productof (node exp-node) (span span))`. With N5c the span
could also state `start ≤ end`.

**Today.** Yes, apart from `start ≤ end`. `syn` (`eager-reader.fx:53`) is
read field by field by Rust (`syn.rs:311-330`), so leave it as it is, or
change it together with `syn.rs`.

**Benefit.** Less boilerplate, and a node that has no span cannot be built.
There is no divergence. The idiomatic trees are internal: the parser's
comparison with Rust goes through `sexp.rs`, which prints the mirror's
trees.

### M6. The parser without `spin`

**Now.** `parse-exp`, `parse-form` and the rest must say `spin`
(`parser.fx:174-437`). Taking the `spin` off shows why: "nothing smaller,
or related, is passed by the call of `parse-exp` in `parse-form`, …"
(tested). `parse-form` hands `(nth items 1)` and `(drop items 2)` to
`parse-exp`. The results of `nth` and `drop` *are* parts of `items`, but
they are the results of other procedures, which size-change cannot see
through (`docs/fx26.md`, "a part reached through another procedure's
parameter").

**Change.** Take `items` apart with `car` and `cdr`, which are parts of a
finite list. The other route is language work: a summary for a known
procedure saying "its result is a part of argument 1" (see the gaps).

**Today.** Yes, by rewriting. A model shows the two cases:
- a tree walk that recurses on `(car (cdr items))` checks as `pure`;
- the same walk recursing on `(nth items 0)` needs `spin`.

**Benefit.** Parsing becomes a walk that ends, so `parse-program` loses
`spin`. There is no divergence.

### M7. Regions by role, and each analysis's state private

**Now.** Everything is at `@t`: the arena, the environment table, the
scope of descriptions, facts, lemmas, and the termination analysis's nine
refs (`check.fx:3547-3562`). So:
- every helper that touches any of it has `kstate`;
- the size-change analysis, which only reads the arena and builds graphs
  of its own, looks like a writer of the checker's state;
- `k-writes-in` reports two flags through globals as side outputs
  (`k-wrote-param`, `k-given`, `:3359-3360,3435`);
- a program's check starts with `k-reset`, which must clear 35 refs by
  hand (`:1864-1876`). Fourteen other refs are cleared elsewhere, or never.

**Change.** Split `@t` by role (`@ty`, `@env`, `@scope`, `@facts`), and
give each analysis its own region:
- **`k-termination`** (`:4132`): state in a bloblet allocated in a
  `letregion`, so the analysis's writes are masked;
- **`k-writes-in`**: the two flags returned in a product;
- **the trails of `k-subtype`** (`:2659`): at a region the call binds with
  `letregion`, so that comparing types is at most `(read @ty)` plus the
  arena's growth;
- **the whole check**: `check-program` could then run in a `letreap` and be
  masked to `(read @s)`.

**Today.** Part:
- `letregion` and region polymorphism exist, but each affected procedure
  must take the state's region and the state itself as parameters;
- the arena grows during subtyping (`k-slot` in lemma instantiation). So
  "arena writes" would stay `(write @ty)`, not something finer (see the
  gaps: append-only effects);
- the error tag's `goto` on `@z` cannot be masked (L3).

**Benefit.** This is what PLAN.md means by "regions by role, per-procedure
effects". The effects become true descriptions, `k-reset` goes, and
running two checks at once becomes safe. The cost is large, spread over
hundreds of signatures. There is no divergence.

### M8. Instructions as datatypes

**Now.**
- **Arity lives in comments.** Register code instructions are `rop-`
  integers whose operand counts appear only in the comments of
  `layout.fx:140-167` ("2: REGk := frame slot n"). `r-op1`, `r-op2` and
  `r-opnn` (`regcode.fx:75-85`) trust the caller to pick the right one.
- **Registers are bare ints.** They are bounded by `register-regs` (8)
  only through the global flag `r-declined` (`regcode.fx:69,88-91`).
- **`n-fix` fields are positional ints** (`native.fx:28`).
- **arm64 registers and conditions are ints.** Registers run 0–31 and the
  conditions are listed in a comment (`arm64.fx:14-16`). A value out of
  range becomes `-1`, which "whoever places the code checks"
  (`arm64.fx:11`).

**Change.**
- A `(define-datatype rinstr (ri-load reg slot) (ri-op2 routine reg) …)`
  with typed operands, encoded to cells in one procedure.
- `reg` as a `nat` bounded by N5c, or, today, a generative `reg` made only
  by a checking constructor.
- Declining through a prompt, or a result sum, not a flag.
- For arm64, conditions as a datatype, and encoders over `(opt int)` (Q7)
  now and over bounded fields later.

**Today.** Part. The datatypes and the declining: yes. Bounds on
registers and immediates need N5c.

**Benefit.** The encoder's oracle tests (`tests/arm64.rs`,
`tests/native.rs`) would catch fewer bugs, because fewer can be written.
The layout tables stay integers at the boundary, since they are generated
from Rust. There is no divergence.

### M9. Primitives and operations as sums, not strings

**Now.** Primitives are looked up by string at run time:
- **the evaluator** finds a primitive with `occurs?` in a string of names
  separated by spaces (`evaluator.fx:116-120`), then dispatches through a
  chain of `string=?` (`evaluator.fx:227-228`);
- **the compiler** (`compile.fx:452-484`), **the register compiler**
  (`regcode.fx:216`) and `standard-primitive` (`standard.fx:7`) each
  dispatch on the name again;
- **the size-change analysis** marks "not an operation" with the empty
  string (`check.fx:3573`, `k-sc-op`);
- **`k-termination`** returns "" for "ends", or a reason (`check.fx:4132`,
  used at `:5364,5399`).

**Change.**
- A `prim` datatype, resolved once when a name is resolved.
- `(opt string)` or a `why` datatype for the analysis.

**Today.** Yes.

**Benefit.** A misspelt primitive can no longer fall through silently.
Dispatch becomes one `tagcase`. There is no divergence.

### M10. Zips indexed by length

**Now.** Several places zip two lists after an arity check, or trust that
they have the same length:
- `k-sub-callable` (`check.fx:2389`) and `k-gen-args` (`:1234`);
- `k-zip-fields` (`:3309`), called after "cannot be taken apart";
- `k-rename`, whose `(car as)` assumes a length check made earlier (`:2261`);
- `k-polarity-descs`, which walks `ds` and `ws` together (`:1505`).

**Change.** Confirm the length once, then zip at one size variable:
```
(poly ((n size)) (subr pure ((nlist a n) (nlist b n)) (nlist c n)))
```

**Today.** Yes (tested):
- `zip-sum` over `(nlist int n)` twice checks as `pure`;
- `confirm-length` with a run-time `(length …)` confirms both lists.

There are two awkward points:
- `length` of a `(listof T finite)` needs a `(the (nlist T finite) …)`,
  because inference does not match `listof` with `nlist`;
- getting from `(nlist T finite)` to a fresh `n` takes a `confirm-length`
  on the list itself. That is really an existential (N5c).

**Benefit.** A mismatched zip cannot be written. The cost is one confirm
per zip site. There is no divergence.

### M11. The reader's state and cursor as sums

**Now.** A `state` is five nested pairs (`eager-reader.fx:74-77,103-108`):
- a `bool` for "waiting";
- a list of continuations that has one element exactly when waiting;
- a position;
- the data;
- a message, which is "" unless stopped.

A `cursor` is four nested pairs, with a lookahead and a `pending`, each a
list of none or one (`:84,138-143`).

**Change.** Use `(sumof (waiting (productof (k cont) (pos nat) (done syns)))
(stopped (productof (pos nat) (done syns) (message string))))`, and a
cursor product with `(opt char)` and `(opt cursor)`.

**Today.** Yes. The Rust drives the reader through its procedures
(`eager-status`, `eager-state-position` and the rest), not through the
layout of a state, so the change stays inside the reader. `syn`, which
Rust walks, is untouched.

**Benefit.** "Waiting with no continuation" and "stopped with one" become
impossible. There is no divergence.

### M12. One tree family for `exp` and `kx`

**Now.** `kx` (`check.fx:111-138`) is `exp` (`parser.fx:29-63`) with its
descriptions read: `syn` becomes `int` or `k-binders`, and `syns-a`
becomes `k-ids` or `(listof k-desc)`. Its constants are also re-coded
(`x-const int int int int`: a type id, and a value that is 1 or 0 for a
boolean and 0 for a string, `check.fx:113-115`). The two definitions and
their walks are kept in step by hand.

**Change.** Make one parametric datatype, with the representation of
descriptions as parameters:
```
(define-datatype (tree (ty type) (descs type) (binders type)) …)
```
This is Najd and Peyton Jones's "trees that grow", from memory.
`k-resolve-exp` becomes a map from `(tree syn syns-a syn)` to
`(tree ty-id (listof k-desc finite) k-binders)`. Literals become a sum,
not a type id and a code.

**Today.** Yes: parametric datatypes are done.

**Benefit.** One definition, shared walks such as the span of a node, and
`letregion`'s form typed once. There is no divergence.

## Needs language work

These need language work, or a redesign large enough to be one.

### L1. Types as `finite` data

**Now.** A type is an index into a growing arena (`check.fx:211-262`). A
recursive type is a cycle through forwarding links. This has several
consequences:
- **every walk needs a visited set.** Walks such as `k-regions-walk`,
  `k-storage-walk`, `k-data-walk` and `k-vars-walk` use epoch marks
  (`k-marks`, `k-epoch`, `k-visit?`, `:245-262`), or a path list
  (`k-show-body`, `k-cyclic-from?`, `k-polarity`'s `seen`);
- **every such walk must say `spin`**, as must `k-resolve` itself (`:236`);
- **it rests on a check made at run time.** It ends only because
  `k-grounded` (`:1075-1092`) has checked that no cycle runs through
  links alone.

PLAN.md item 8 already names this ("today `k-check-mode` peels `poly`s off
a type held as an `int`, and must say `spin`"; `k-check-mode`,
`check.fx:4755`).

**Change.** Make a type a `finite` tree. A recursive type is a `t-mu`,
whose body refers back to it by depth. That is the form the checker
already *prints*: `(mu %d …)`, `%d` being the cycle's depth
(`check.fx:734-747`). With this:
- a walk that needs to see each node once stops at a back-reference, which
  names an ancestor it has already passed through;
- walks end by size-change, with no marks and no `spin`;
- inserting a closed type under other `mu`s needs no shifting, since its
  back-references are internal.

**Today.** Part. A model is in `fty.fx`: a regions walk over `t-mu` and
`t-back` checks as `pure` (tested), and gives `(@r)` for
`(mu %1 (pairof int %1 @r))`. But the rest of the checker does not follow
so easily:
- **Some questions still need a trail.** Subtyping, matching and
  unification of equi-recursive types unfold `mu`s, which makes terms
  larger. They end because the pairs of subterms met are finitely many:
  Amadio and Cardelli's trail. That is not size-change. Those procedures
  keep `spin`, or take fuel (L2).
- **Walking a generative type's representation is not a descent.** It is
  a lookup in the table of generative types (`(extract (k-gen-of g) 4)`),
  and the representation may mention the name again. It needs a visited
  set of gens, with a `nat` measure of the unvisited ones.
- **Sharing is lost.** `k-regions-memo` (`:1862`) memoises by id, and a
  tree has no id. That costs memory and time, and wants measuring.
- **Printing may diverge.** `k-abbrev-in` (`:541-551`) prints a type as
  the `define-type` name whose *slot is the same node*. Compared
  structurally instead, a type that inference builds and that is equal to
  an abbreviation's body would print as the name, where the Rust prints it
  written out. The idiomatic front end would need a transparent label
  node, made where the abbreviation is expanded and lost on substitution,
  as the arena loses the id.

**Benefit.** This is the largest single cut of `spin` and of global state
in the checker. The cost is very large: it rewrites the core. It also
carries a real risk to message agreement through printing. Do it last, and
behind the three-way tests.

### L2. Walks of graphs without `spin`

**Now.** While the arena stays, (L1 not done), the walks end for a reason
the checker cannot see: the arena is finite, and each node is visited
once.

**Change.** Pass fuel down, a `nat` that starts at the arena's size and
falls by one per level. Any path through the walk has distinct nodes, so
its depth is bounded by the number of nodes, and running out of fuel is
an internal error. Better: a measure the checker accepts on the state, as
a `decreasing` clause over (nodes − visited).

**Today.** Part. Fuel works with `nat` today, but it is noise in every
signature, and `array-length` gives an `int` (Q1).

**Benefit.** Only as good as the fuel is honest. It would let
`check-program` say it ends, which matters to the licence: "a step budget,
since running early may not terminate" (`docs/fx26.md`, step 7).

### L3. Failure that a handler discharges

**Now.** The parser, the checker and the compiler each fail by aborting to
a *global* tag: `parse-tag` at `@p`, `k-tag` at `@z`, `c-tag` at `@y`
(`parser.fx:80`, `check.fx:152`, `compile.fx:50`). Every failing procedure
closes over the tag, so no prompt can delimit it. That is why
`bootstrap`'s type carries `(comefrom @p) (comefrom @z) (comefrom @y)`
(`bootstrap.fx:24`), and why `parser.fx:624-627` explains that this is
"still licensed". In addition, a tag fixes its answer type, so a nested
catch must share the outer answer type. That produces `k-done` and its
impossible `k-ok` arms (M1).

**Change.** Either:
- **an exception tag** that fixes only the payload `H` and the effect bound
  `D`, not the answer type (abort only, no capture), whose prompt delimits
  every abort to it; or
- **a named effect that a handler discharges** (`fails`, masked by its
  `prompt`), where `define-effect` today is only an abbreviation.

**Today.** No. Writing every procedure region-polymorphically over the
tag's region would work, as `docs/fx26.md` "Control, typed" notes, but at
a prohibitive cost in signatures.

**Benefit.** `check-program` would lose `goto`/`comefrom` on `@z`, and
nested catches would be typed exactly. There is no divergence.

### L4. Invariants kept by smart constructors

**Now.** Some invariants hold only because every value is built by the
right procedure:
- **effects** are sorted lists without duplicates, built by `k-insert` and
  `k-union` (`check.fx:490-502`);
- **sizes** are linear forms whose terms are sorted by variable, with no
  zero coefficient (`k-terms-add`, `:593-606`);
- **facts** are normalised when they are recorded.

**Change.** Make `eff` and `lin` generative, and let only the operations
that keep the invariant see inside.

**Today.** No. `define-generative` makes `up-`/`down-` ordinary
definitions that anyone can call, so this only documents. Real hiding is
G4 (`docs/research/generative-types.md`, "conversions made
program-private").

**Benefit.** `k-eff=?` and `k-size=?` are correct only if the lists are
normal. With hiding, that becomes a theorem. There is no divergence.

### L5. Bounded naturals

**Now.** Several integers carry bounds kept only by checks at run time:
- arm64 registers must be 0–31 (`arm-reg`, `arm64.fx:38`);
- immediates must fit their field (`arm-simm`);
- register-code registers must be at most `register-regs` (`regcode.fx:88`);
- array indices must be below the length: the arena (`k-tys`, `k-marks`,
  `k-regions-memo`) and `native.fx`'s label arrays;
- the growth checks (`:226,256,1883`) keep them so, by hand.

**Change.** Use `(nat i)` with facts `i < n` (N5c; `sizes.md` "array index
`(nat i)` with the fact `i < n`, CF4"). Registers become `(nat r)` with
`r ≤ 30`.

**Today.** No. `nat` and its facts exist (N5d), but there are no
inequality facts against a bound, and no array bounds.

**Benefit.** Moderate. The arena would still need its growth checks unless
array types carried sizes.

### L6. Kind-indexed descriptions; a tree indexed by phase

**Now.** Descriptions of different kinds live together in one
heterogeneous list: the entries of M4's map, `proj`'s arguments (checked
by `k-proj-map`, `check.fx:2780-2794`), and a generative type's arguments.
The phase of an expression tree (resolved or not) is a second type (M12).

**Change.** Two GADTs:
- `(desc k)` indexed by kind, with binder lists as existential pairs
  `(exists k (pair (dvar k) (desc k)))`;
- a `tree` indexed by phase, so that one procedure can require resolved
  trees.

**Today.** No: this is N4 (constructor result types, existentials,
refinement in `tagcase`).

**Benefit.** It removes the run-time kind checks that remain after M4. It
is the natural first client of N4 inside the front end.

## Language gaps and awkward spots

This exercise brought these to light, as feedback for the language. Each
names the opportunity that runs into it.

1. **`array-length` and `string-length` give `int`, and no test turns an
   `int` into a `nat`.** `(if (< x 0) 0 x)` is refused as a `nat`
   (tested). Size-change accepts `string-length` as a bound but not
   `array-length` (`terminate.rs:546`), though an array's length never
   changes. The fix is small, in the N5d/N5c area:
   - `array-length : (arrayof T r) → nat`;
   - facts from `(>= x 0)` on an `int`;
   - `array-length` as a bound.

   It would remove the `spin` from `rehash-array`, the three `copy`
   helpers and `n-copy-*` (Q1, L2).
2. **Size-change cannot see through a helper's result.** `nth`, `drop` and
   `syn-items` return parts of their argument, but a caller cannot know
   that. Either of two would fix it (M6):
   - summaries for known non-recursive procedures ("the result is a part of
     argument 1"), as "known procedures" are already tracked;
   - sized types for trees, indexed by depth, not length.
3. **You cannot name "a datatype without one variant", and a constructor
   returns the whole datatype.** `k-ty` minus `ty-link` has to be written
   out in full (M2), and `(k-place)` does not fit
   `(sumof (k-region …) (k-place …))`. You must write
   `(sum k-place (product))` (tested). Two things would help:
   - an operator such as `(sum-without T tag …)`;
   - constructors whose result type is the variant's own singleton sum,
     which widens to the datatype.
4. **No option type in the prelude, and families print expanded.**
   `(opt region-kind)` prints as `(sumof (none (productof)) (some
   (productof (1 region-kind))))` (tested). Printing an application of a
   family by name, as `define-type` names print, would make messages about
   idiomatic code readable (Q7).
5. **`length` on a `(listof T finite)` is not inferred** (it needs a
   `the`), and **no form opens an existential size**. Going from
   `(nlist T finite)` to a fresh `n` and `(nlist T n)` takes a
   `confirm-length` of the list against its own length (M10; N5c).
6. **No identity for mutable objects.** There is no `eq?`, and no
   identity hash for refs or bloblets. So a graph must be an arena of
   integers, since a visited set needs identities. With identity,
   recursive types could be a graph of I-cells: an I-cell *is* the
   forwarding slot (`check.fx:79`), and it cannot be linked to another
   cell, which is what `k-grounded` checks today (L1, M3).
7. **No way to ask whether an I-cell is full.** Printing a slot not yet
   filled (`"?"`, `check.fx:752`) needs that probe. It might be a `read`
   rather than an `await` effect.
8. **No append-only effect.** Adding a node to an arena is `(write @t)`,
   the same as changing one. An "allocation into a user arena" effect,
   which commutes with reads of old entries, would let the construction of
   types (`k-ty-new`, `k-slot`) be `alloc`-like. Subtyping, which grows the
   arena, could then be shown not to disturb what callers read (M7).
9. **Exception tags, or handlers for named effects.** A global failure tag
   blocks delimiting everywhere it is used, and the fixed answer type
   forces impossible arms (L3, M1).
10. **Region-polymorphic state is too verbose to use at scale.** Making the
    checker's state per invocation means threading a region and a state
    through about 400 signatures. Two things would make it practical:
    - a module that is polymorphic in its regions (FX-91 had first-class
      modules), instantiated per use;
    - `private-regions` per *invocation*, not per program (M7).
11. **No productivity.** The eager reader says `spin`
    (`eager-reader.fx:131-628`), though it does finite work per character
    between suspensions. An effect or check for "finite work between
    `comefrom`s" would describe it truthfully.
12. **Measures over state.** A walk over an arena with a visited set ends
    by a measure (nodes not yet visited), not by size-change. A
    `decreasing` clause proved as a lemma, or fuel with less noise, is
    missing (L2).
13. **Not needed: a top effect.** Nothing in the front end asked for
    `any`, not even the evaluator, whose effects are all on its own `@v`
    and `@x`. The `c-register-code` hook (`compile.fx:153-155`) is a knot
    through the store, and wants an I-cell (set once), not a larger effect.

## Which file to port first

1. **`table.fx` (111 lines).** It has no Rust twin, so there is nothing to
   agree with. Its idiomatic form is ready and tested (Q1, plus Q5 for the
   bloblet's positional fields). It pays off at once: every lookup in the
   checker loses `spin`, whichever checker uses it. It is also the right
   place to settle the shared prelude that later files need:
   - `opt`;
   - the `nat` helpers;
   - `array-length` as a `nat`, once gap 1 is closed.
2. **`arm64.fx` (151 lines).** It is pure encoders, checked against the
   Rust encoder instruction by instruction (`tests/arm64.rs`), so "agree on
   outputs only" is easy to test. It shows Q2 (every `spin` goes), Q7
   (`-1` becomes `opt`), and later L5 (registers and immediates as bounded
   naturals). It is small enough to finish in a sitting.
3. **`parser.fx`, which PLAN.md stages first** ("the reader and parser
   first; they change rarely"). It gains the most visible structure:
   - M5, spans;
   - Q6, a sum for the form of `letregion`, carrying `letfreeze`'s place;
   - Q7, options for `t-define`'s type, `parse-else`, a bloblet's field
     index and `confirm-length`;
   - Q3;
   - M6, no `spin`;
   - M12, the tree family `kx` will share.

   Two cautions. It was being edited while this note was written, so wait
   for that work to land. And its trees feed `evaluator.fx`, `compile.fx`,
   `regcode.fx` and `check.fx`. An idiomatic parser therefore needs either
   those consumers ported, or an adapter to the mirror's `exp`, so do it
   after the prelude settles.

**`eager-reader.fx` next, with care.** M11 is safe, but `syn` is read by
Rust field by field (`syn.rs:311-330`), so leave it as it is.

**`check.fx` last**, after N1–N3 as PLAN.md says. Port it in the order Q →
M1–M4 → M7, with L1 decided separately behind the three-way tests.

## Prototypes run

In `/Users/pnkfelix/.claude/jobs/c41da332/tmp/`, each checked with
`target/{debug,release}/fixpt repl --dialect fx26 < FILE`:

| File                | What it shows                                                                                                                                    |
| ------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------ |
| `table2.fx`         | With a finite bucket spine, `bucket-find` is `(read r)`, with no `spin`.                                                                         |
| `table3.fx`         | `table-ref` and `table-has?` lose `spin`, and `(table-ref t 'a 0)` is `(read @r)`. `rehash-array` still needs `spin` (the `array-length` bound). |
| `table4.fx`         | Counting down a `nat` is refused, because `array-length` is an `int`.                                                                            |
| `tonat.fx`          | `(if (< x 0) 0 x)` is not accepted as a `nat`.                                                                                                   |
| `strs.fx`           | `k-starts-at?`, `k-find-sub` and `k-str-cmp` rewritten with `>=` are `pure`. An array copy bounded by `array-length` still needs `spin`.         |
| `pow.fx`            | `arm-pow2` over a `nat` with `(= n 0)` is `pure`.                                                                                                |
| `ep2.fx`            | The parser's `len`, `nth` and `drop` (with `nat`), and a `k-head`, are `pure`.                                                                   |
| `ep.fx`, `tree.fx`  | Why the parser needs `spin` (`nth` hides a part), and that `car`/`cdr` of `items` fixes it.                                                      |
| `narrow.fx`         | `k-get` returning the sum without `ty-link`; a `tagcase` of it needs no link arm.                                                                |
| `gen.fx`            | Generative `ty-id` and `dvar-id`: mixing them is refused.                                                                                        |
| `opt.fx`            | A parametric `opt`; a `kind` datatype; a narrower sum widening to `kind`; a constructor does not fit the narrower sum; families print expanded.  |
| `code.fx`           | A code buffer as a finite list in a `ref`: `c-emit` needs no `alloc`, and `c-reverse` is `pure`.                                                 |
| `zip.fx`, `zip2.fx` | A zip over `(nlist int n)` twice is `pure`. `confirm-length` with a run-time `length` confirms both lists. `length` of a `listof` needs a `the`. |
| `fty.fx`            | Types as finite data with `t-mu` and `t-back`: a regions walk is `pure`.                                                                         |
