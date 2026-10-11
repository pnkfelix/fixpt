# Re-introducing FX-87's anti-aliasing rule: a survey

> **Measured at `4670769`** (2026-10-11, by a survey agent in its own
> worktree, branch `worktree-agent-a8c0a6397d5bda01c`, commit `d873019`,
> which holds the diagnostic, `FIXPT_ANTI_ALIAS`, and its scripts; not
> merged). That commit predates the blobref operations and flat data
> (`DONE.md` §77), so §5's item 7 ("no suffix view or `RefAt`") is out of
> date: `blobref-at` and kin exist now, and the split form of
> `region-anti-aliasing.md` §5.1 is what would make two views of one
> bloblet disjoint. The standard procedures' types, which nearly all the
> counts come from, are unchanged since.

What would break if FX-26 brought back the region anti-aliasing rule that
the PLDI '89 paper assumed away (`docs/fx26.md`, line 68), and what would
make the breakage go away. A measurement, not a change: the rule is a
diagnostic behind an environment variable, and nothing in the code base
was changed to satisfy it.

## 1. The rule, and the three variants measured

Lucassen's thesis (MIT/LCS/TR-408, 1987), §3.6.3 "Abstract Regions",
pp. 46-47:

> Restriction. In a polymorphic application (PROJ e p), where e has type
> τ, no region constant or variable may appear free in both τ and p; in
> other words, FRC(τ) ∩ FRC(p) and FDV(τ) ∩ FDV(p) must be empty.

It applies only when the operand is a region description; its purpose is
"to maintain the invariant that effects on distinct region constants
and/or variables in any scope do not interfere", so that an effect analysis
may treat distinct region variables as distinct constants (§8.2.2). Two
further remarks bear on the proposals below: a PRIVATE region (fresh,
FX-26's `letregion`/`letrena`/`letreap`/`letfreeze`) introduces no
aliasing (§5.3.6, p. 70); and Lucassen himself calls the general rule
"rather restrictive in practice" and suggests instead saying explicitly
which region variables may alias which (§9.2.3, p. 144), having already
mentioned "constrained quantification over regions" as the alternative he
did not pursue (p. 46).

FX-26's `poly`/`proj` are n-ary, and calls instantiate implicitly, so the
variants are stated over all the region (and place) binders of one
instantiation, `r1 … rk` given `p1 … pk`:

| Variant           | Refused when                                                                              |
|-------------------|-------------------------------------------------------------------------------------------|
| (A) strict        | `pi = pj` for some `i ≠ j` (same `Region` after resolution)                                |
| (B) write-excl.   | `pi = pj`, `i ≠ j`, and `ri` or `rj` is written (a `write` atom on it) in the `poly`'s type |
| (L) Lucassen      | (A), or (a): some `pi` is a region free in the `poly`'s type itself (outside its binders)  |

(A) is Lucassen's rule restricted to its part (b) (after `r1 := p1`, `p1`
is free in what remains, so `p2 = p1` is refused). (L) is the faithful
n-ary reading.

How regions are compared. Every `Region` value counts, with no exemption,
so that the counts can be split afterwards (§4):

* `heap` (`Region::Heap`) and the named constant `@heap` are different
  regions to the checker (`(ref int @heap)` is not a `(ref int heap)`;
  checked), and each is one region: two binders given `@heap` alias.
  Every `@heap` hit in the corpus is the named constant; no hit is `heap`.
* Frozen regions, `(const p)`/`(acyclic p)`/`const`/`acyclic`, are regions
  like any other for (A) and (L). (B) never fires on them, since nothing
  may write frozen data.
* A region variable of an enclosing scope (an outer binder, or a
  `letregion` variable) is one region; two different variables are
  different regions (the rule, applied in the outer scope, is what makes
  that so).
* `(globals g)`/`@globals` regions are compared the same way; none was
  ever given to a region binder.
* Fresh regions (inference's default for a binder nothing solves,
  `@r.N`) are distinct from every other region by construction; no hit.

## 2. The diagnostic

`FIXPT_ANTI_ALIAS=strict|writes|lucassen` makes a violation an error at
the instantiation, naming the binders and the region; `FIXPT_ANTI_ALIAS=log`
makes nothing an error and prints one line per violation on the standard
error, saying which variants it breaks. Unset, nothing runs (one
`OnceLock` read per instantiation).

```
ANTI-ALIAS file=0 off=443 variants=A,B,L site=call who=[mv user] reason=dup
  binders=a,b region=heap rclass=heap bounded=0 written=1 written_inst=1 open=0
! t1.fx:6:40: anti-aliasing (Writes): site=call who=[mv user] reason=dup binders=a,b region=heap ...
```

The check sits where every instantiation of region binders ends in the
Rust checker, after the map is complete and the instance made:

| Site                 | Where                                                     | What                                            |
|----------------------|-----------------------------------------------------------|-------------------------------------------------|
| `call`               | `crates/fixpt-fx26/src/infer.rs:1024` (`instantiate`)     | a call of a polymorphic operator, inferred      |
| `value`              | `crates/fixpt-fx26/src/infer.rs:1087` (`instantiate_against`) | a polymorphic value where a type is expected |
| `proj`               | `crates/fixpt-fx26/src/check.rs:1494` (`Exp::Proj`)       | explicit `proj` (and a module file's parameters) |
| `family`             | `crates/fixpt-fx26/src/kinds.rs:152` (`apply_fun`)        | a `dlambda` applied; logged only, never an error |

All three of the first sites come right after `check_bounds`
(`infer.rs:1196`), which is the natural home for a real implementation.
The code is `crates/fixpt-fx26/src/antialias.rs`. Module signatures need no
site of their own: a module's abstract types are type variables only
(`modules.rs`, `Ty::Module { abs, … }`), and a module file's region
parameters (`module-parameters`) are a `plambda`, instantiated by `proj`.
Generative types' region arguments (`(eqtable k v kr r)`) are not checked
apart: they are only ever made by instantiating a procedure, which is.

For the measurement, `FIXPT_RUST_CHECK_ONLY` (in
`crates/fixpt-fx26/src/compare.rs`, `both_checkers`) makes `fixpt check`
run the Rust checker alone and report its verdict as both, so that the
FX-26 checker, which knows nothing of the rule, neither slows the survey
nor turns every hit into "the checkers disagree".

Where the FX-26-written checker would need the same check (not touched):
`k-check-bounds` (`check-binders.fx:270`) is reached from
`k-subst-checked` (`check-synth.fx:297`; calls at `check-synth.fx:670`, and
`proj`) and from `k-instantiate-plain` (`check-infer.fx:718`, used by
`k-instantiate-against`, `check-infer.fx:735`). The pieces it would use:
`k-unify-region` (`check-infer.fx:473`), `k-default-regions`
(`check-binders.fx:197`), `k-finish` (`check-infer.fx:244`), `k-subst`
(`check-subst.fx:363`), `k-subst-region` (`check-subst.fx:131`).

To reproduce: `cargo build --release --offline`, then
`scripts/anti-alias-survey/survey.py OUT.jsonl FILE… | @LISTFILE` (log mode
on each file, then each error mode on the files with hits, each run under
`scripts/conductor/t 120`) and `scripts/anti-alias-survey/classify.py`
(which reads `fe.jsonl`, `tests.jsonl`, `bench.jsonl` in the current
directory). The front end is checked as `fecheck.sh` does: the
non-module files of `fixpt front-end-files` concatenated, with its 135
module files loaded by `load-module`.

## 3. What was measured

| Corpus                                                      | Files | Rust-checked OK |
|-------------------------------------------------------------|------:|----------------:|
| Front end (one program: 546 lines + 135 module files)       |     1 |               1 |
| Tests: `crates/fixpt-fx26/tests/programs/**`, `crates/fixpt-cli/tests/programs` |   461 |             261 |
| Benches: `scheme-bench/`, `mllang-bench/` (`.fx`)           |    95 |              94 |

The tests' 200 rejected files are expected rejections, and module files
that are not programs alone; `tests/programs/bench/` (8 files) is counted
with the tests. A "site" is one instantiation in the source (deduplicated
by file and offset); a file "breaks" when it checked before and the
variant's error mode now rejects it. In every case the error modes
rejected exactly the files the log said they would: no hit came from an
instantiation that inference tried and then threw away.

### 3.1 Files broken

| Corpus    | OK before | (A) strict | (B) writes | (L) Lucassen |
|-----------|----------:|-----------:|-----------:|-------------:|
| Front end |         1 |          1 |          0 |            1 |
| Tests     |       261 |         16 |          1 |           30 |
| Benches   |        94 |         10 |          1 |           15 |

The front end is one program; under (A) 17 of its module files have hits
(4 once frozen data and bounded binders are exempt, §4).

### 3.2 Sites, by class

Each cell is A/B/L. Classes as asked: (i) a standard procedure over two
regions given one; (ii) a user procedure over two regions given one;
(iii) a region given for two binders by inference defaulting; (iv)/(v)
modules and module parameters; (vi) false positives; (vii) other. Class
(i) is split by whether the shared region is frozen data, and (L)'s
extra part (a) is its own row.

| Class                                        | Front end | Tests   | Benches | Total    |
|----------------------------------------------|-----------|---------|---------|----------|
| (i) std, two regions given one (mutable)     | 7/0/7     | 9/0/9   | 30/8/30 | 46/8/46  |
| (i′) std, two regions given one (`acyclic`)  | 30/0/30   | 2/0/2   | 0/0/0   | 32/0/32  |
| (ii) user procedure                          | 0/0/0     | 0/0/0   | 0/0/0   | 0/0/0    |
| (iii) bounded binder defaulted to its bound  | 2/0/2     | 15/0/15 | 0/0/0   | 17/0/17  |
| (iv)/(v) module-file parameters              | 0/0/0     | 1/1/1   | 0/0/0   | 1/1/1    |
| (L-a) region free in the `poly`'s type       | 0/0/66    | 0/0/28  | 0/0/84  | 0/0/178  |
| (vi) false positive                          | 0         | 0       | 0       | 0        |
| (vii) other                                  | 0         | 0       | 0       | 0        |
| All                                          | 39/0/105  | 27/1/55 | 30/8/114| 96/9/274 |

By procedure, the 96 (A) sites: `reverse` 38, `append` 18, `rcons` 13,
`eqtable-set!` 5, `current-marks` 4, `list->array` 3, `eqtable-ref` 3,
`marks-of` 3, `array->list` 2, `make-eqtable` 2, `rnew` 2, `rmake-array`
1, `rmake-icell` 1, a module file's `proj` 1. The (L-a) sites: `list` 173
(168 calls, 5 as a value), `apply` 3, `parse-number` 1, `datum-dotted` 1 — every one with the region `acyclic`.

### 3.3 Representative examples

(i) Standard procedure, one region for two (the bulk). A list reversed or
appended into the region it is in, the type alias on the result fixing
both sides:

* `crates/fixpt-fx26/src/check-env.fx:388`:
  `(each (the k-with-list (reverse ws)))`, `r1 = r2 = acyclic` (i′).
* `crates/fixpt-fx26/src/native.fx:278`:
  `(the n-stub-list (reverse (get n-stubs)))`, `r1 = r2 = @k`.
* `crates/fixpt-fx26/src/compile-state.fx:272`:
  `(append ws (the c-waits (list …)))`, `r1 = r2 = @k`.
* `crates/fixpt-fx26/src/eager-reader.fx:337`:
  `(list->string (the closers (reverse acc)))`, `r1 = r2 = rc`, a
  module parameter (a region variable of the enclosing scope).
* `crates/fixpt-fx26/src/eval-prims.fx:430,432`: `current-marks` (`r`,
  `l`) and `marks-of` (`q`, `r`, `l`) all at `@x`, the evaluator's one region.
* `scheme-bench/earley.fx:261`, `scheme-bench/matrix.fx:210`,
  `mllang-bench/fx/mlton/count-graphs.fx:217`: `reverse` at `@heap`.
* `scheme-bench/conform.fx:323`: `(list->array …)`/`(array->list …)` at `@heap`.
* `crates/fixpt-fx26/tests/programs/native/standard-ops.fx:20-22`:
  `append`, `list->array`, `array->list`, all at `@l`.
* The only (B) hits of class (i): `scheme-bench/equal.fx:188-229`, the
  union-find tables: `make-eqtable`, `eqtable-ref`, `eqtable-set!` with key
  region `kr` and table region `r` both `@heap`. `eqtable-ref` and
  `eqtable-set!` write `kr` (`standard.rs:358-374`: the operations "write
  the keys' region, so that no table is keyed by frozen data"), and
  `equate!` also `set-cdr!`s the class lists stored in the table, in the
  same region. This is real write aliasing.

(iii) Bounded binder defaulted to its bound. `rcons`, `rnew`,
`rmake-array`, `rmake-icell` are `(poly ((p place) (r region p)) …)`
(`standard.rs:36-39`); when nothing says what `r` is, `default_regions`
(`infer.rs:1167`) gives it its bound, `p` itself. Every call that
allocates "in the place" is then `p = r`:
`crates/fixpt-fx26/tests/programs/bench/lists-region.fx:7`
`(rcons r n acc)`, `run/region-allocators.fx:7-9`, `run/arena.fx:8`,
and in the front end `check-types.fx:215`, `check-print.fx:139`.

(iv)/(v) Module parameters.
`crates/fixpt-fx26/tests/programs/modules/load-parameters.fx:4`:
`(proj (load-module "../module-files/tally-twice.fx") @q @q)`, whose
`module-parameters` are `((r region) (unused region))` and which writes
`r`. The front end's own module parameters
(`(module-parameters ((rs region) (re region) (rm region) (rc region) (rp region)))`,
six files) are always given distinct regions (`@s @e @m @c @p`): no hit.

(L-a) Free in τ. `list` is `(poly ((t type) (r region)) (vsubr (alloc r) t (listof t r)))`
(`standard.rs:262`), and `vsubr`'s representation is
`(subr e ((listof t acyclic)) r)` (`check.rs:35`, `VSUBR`): the rest list
of a variadic call is frozen heap data, so `acyclic` is free in `list`'s
type, and `(list 1 2 3)` made as a constant (`acyclic`) gives `r` that
same region. Likewise `apply`, and `datum` (frozen) in `parse-number` and
`datum-dotted`. Examples: `crates/fixpt-fx26/src/parser.fx:710`,
`crates/fixpt-fx26/src/parser-exps.fx:505`,
`mllang-bench/fx/mlton/smith-normal-form.fx:277-309` (one per row of a
matrix literal), `scheme-bench/triangl.fx:42-54`. No (a) hit involves a
region that can be written, a closure's captured region, or `heap`.

(ii) None. Hardly any code writes a procedure polymorphic in two regions:
26 `poly` headers over regions in all the FX-26 sources, tests and benches,
two with more than one region binder (`tests/programs/run/caller-place.fx`,
`tests/programs/regions/caller-region-outside.fx`), neither aliased.
FX-26's exposure to the rule is the standard environment's 16 procedures
over two or more regions, listed in §5, and module parameters.

(vi) No hit was spurious in the sense of not being an instantiation with
a shared region. Two qualifications: `datum/quote-shadowed.fx:10` is
reported as a user `append` because the program rebinds `append`, but the
call is the quasiquote's `#%fx` `append`, so it is counted in (i); and
whether the (L-a) hits are "real" depends on reading generative types'
representations (`vsubr`, `datum`) as part of τ. Lucassen's τ had no
such types, so these are best read as artifacts of how FX-26 encodes
variadic procedures and data, harmless since the region is frozen.

### 3.4 The family site

`dlambda` applications with region parameters (`(define-type rw (dlambda
((r region)) …))`, `tests/programs/higher-kinds/effect-family.fx`) were
logged and never had two region parameters given one region: 0 sites.

## 4. Exemptions, measured

The log keeps enough to recount with exemptions:

| (A) files broken, exempting…           | Front end module files | Tests | Benches |
|----------------------------------------|-----------------------:|------:|--------:|
| nothing                                |                     17 |    16 |      10 |
| frozen regions                         |                      6 |    14 |      10 |
| frozen regions and bounded binders     |                      4 |     5 |      10 |

The tests left are `diverge/cyclic-reverse.fx`, `native/deep-control.fx`,
`modules/load-parameters.fx`, `native/standard-ops.fx`,
`run/tail-marks.fx`. (L) with frozen regions exempt is exactly (A) with
frozen regions exempt: every (a) hit is frozen.

(B), with no exemptions, leaves 9 sites in 2 files:
`scheme-bench/equal.fx` (8, eqtables) and
`tests/programs/modules/load-parameters.fx` (1, a written module parameter).

A note on (B)'s definition: "written" is a `write` atom on the binder in
the `poly`'s own type (with generative types' representations followed as
`Checker::writes_in`, `check.rs:2650`, does). The log also records whether
the shared region is written anywhere in the *instance* (`written_inst`),
which also counts writes that arrive through an effect argument. That
reading adds 4 front-end sites (`eval-prims.fx:430,432`: `marks-of` is given
a continuation whose effect `d` writes `@x`), and they are wrong to count:
`marks-of` never runs the continuation, and a body cannot rely on an
effect variable's not touching any region anyway. The `poly`-type reading
is the one that matters.

## 5. What would remove each class

The standard procedures over two or more regions, and how each fares:

| Procedure                    | Binders      | Writes a binder | (A) sites | (B) sites |
|------------------------------|--------------|-----------------|----------:|----------:|
| `reverse`                    | `r1 r2`      | no              |        38 |         0 |
| `append`                     | `r1 r2`      | no              |        18 |         0 |
| `list->array`, `array->list` | `r1 r2`      | no              |         5 |         0 |
| `rcons`, `rnew`, `rmake-*`   | `p`, `r ≤ p` | no              |        17 |         0 |
| `current-marks`, `marks-of`  | `r l`, `q r l` | no            |         7 |         0 |
| `make-eqtable`, `eqtable-count` | `kr r`    | no              |         2 |         0 |
| `eqtable-ref`, `eqtable-has?`| `kr r`       | `kr`            |         3 |         3 |
| `eqtable-set!`, `eqtable-delete!` | `kr r`  | `kr`, `r`       |         5 |         5 |

Ranked by how much each fixes:

1. **Variant (B) instead of (A)/(L), plus (a) for written binders only.**
   Fixes 87 of 96 (A) sites and all 178 (L-a) sites; leaves 9 sites in 2
   files. It is also what the checker could use: in a `poly`'s body, a
   `write` to binder `w` cannot touch the region of any other binder `r`
   (if they were one region, `w` being written would have been refused),
   so `kill_paths`'s `may_alias` (`check.rs:1062`) could say "no" for two
   distinct binders of one `poly` when the write is to one of them, which
   is §8.2.2's interference rule with reads commuting. Two read-only
   binders may still alias, and nothing cares, since reads commute. To
   keep the guarantee against regions captured by the value (Lucassen's
   (a)), a written binder must also not be given a region free in τ;
   this costs nothing in this corpus (every (a) hit is frozen, so never
   written). Cost: one walk of τ for `write` atoms per instantiation,
   cacheable per standard procedure; in the FX-26 checker, the same walk
   beside `k-check-bounds`.

2. **Frozen regions exempt.** Data that nothing may write cannot be
   observed to alias; this removes 32 (A) and all 178 (L-a) sites, and
   would let `reverse`/`append` of constant lists stay as they are. (B)
   subsumes it. Needed only if (A) or (L) is chosen.

3. **Bounded binders exempt from their bound (region nesting).**
   `(r region p)` already says `r` lives within `p`'s lifetime; reading
   it also as "`r` may be `p`" (a sub-region, as Lucassen's EXTEND shares
   one name for both, §5.3.6) removes all 17 class-(iii) sites
   (`rcons`, `rnew`, `rmake-array`, `rmake-icell`). Alternatively, the
   defaulting in `default_regions` could give `r` a fresh region within
   `p` instead of `p` itself, which keeps disjointness at the cost of
   types that name a region nobody else does. (B) subsumes this too (they
   only allocate).

4. **Eqtables: a non-conflicting effect for identity stamping, or
   distinct table regions.** The 8 (B) sites are `eqtable-ref`/`-set!`
   writing `kr`, the key region, to forbid frozen keys
   (`standard.rs:358-361`). If that "write" were an effect of its own
   kind (it marks the key as hashed; it does not change what reading the
   key sees), `eqtable-ref` would only read, leaving `eqtable-set!`'s
   genuine write to `r`: `equal.fx` would then still need its tables in a
   region apart from the keys (one `letregion` or one named region in its
   `classes` alias; the class lists it `set-cdr!`s are values in the
   table's region and keys' region both). One-region variants
   (`(eqtable k v r)`, keys and table together) are the other way out.

5. **Explicit distinctness, opt-in: `(distinct r1 r2)` in a `poly`, and in
   `module-parameters`.** Lucassen's own suggestion (§9.2.3) and his
   "constrained quantification" (p. 46). Breaks nothing today: no user
   code would opt in, and the standard procedures that need nothing from
   disjointness (all but the eqtable writers) would not. The front end's
   module parameters could opt in at no cost (always given distinct
   regions). `load-parameters.fx` passes `@q @q` deliberately and would
   either not opt in or pass two regions. Cost: syntax in both parsers and
   both checkers, and the check of §2 restricted to the named pairs. The
   opt-out dual, `(may-alias r1 r2)`, is what (B) infers from effects
   automatically, so it adds little over (B).

6. **One-region standard procedures** (`reverse!`-like,
   Rust's `copy_within`): `reverse1`, `append1`, `list->array1` with one
   region binder. They would remove the remaining (i) sites under (A)
   (46 mutable + 32 frozen) one call at a time, at the cost of a second
   name for every procedure. Unnecessary under (B).

7. **Region splits for flat data** (a `split_at_mut`-like form, or
   allocation in sub-regions seen as the parent by subtyping). No site in
   this corpus needs one: nothing instantiates two binders with one
   array's region to write parts of it. The bloblet operations at this
   commit (`BlobletOp`, `ast.rs:620`: make, ref, set, freeze, byte,
   set-byte, bytes) have no suffix view or `RefAt`; once flat data is
   reached through views into one bloblet, a split form is what would let
   two views be written as disjoint regions. Today it fixes nothing.

## 6. Soundness of today's checker with respect to aliasing

Nothing found unsound. Today nothing in the Rust checker *relies* on
distinct region variables being disjoint, so having no rule costs no
soundness:

* `kill_paths` (`check.rs:1058`) ends a path's facts on a write to any
  region variable, whatever region the path reads through
  (`may_alias`, `check.rs:1062`); region constants are compared by
  identity, which is right since a value has one region and `@heap` and
  `heap` are not interchangeable (checked). It does not relate
  `(globals g)` to `@globals`, but path facts only record pairs' regions
  (`check.rs:1000-1006`), never globals.
* `mask`'s note that a `letfreeze` region was written
  (`check.rs:1794`) matches `(write v)` exactly, not up to aliasing. That
  is sound because a `letfreeze` region is fresh (thesis §5.3.6): no binder
  instantiated before it can be it, and instantiation substitutes the
  actual region into the callee's effect, so a write through a
  polymorphic call is seen as `(write v)` itself.

The rule would matter only once something wants to rely on disjointness:
sharper `kill_paths`, a compiler reordering memory operations by effect,
or running effects in parallel. For each of those, (B) gives the needed
guarantee (a written binder is disjoint from every other binder) at
almost no cost to existing code.

## 7. Measured vs inferred

Measured: every count in §3 and §4 (Rust checker, log and error modes, on
the release build of this branch); the `@heap`/`heap` distinction; the
absence of hits at the `family` site; the count of `poly` headers over
regions (by `grep`). Inferred: the costs and coverage of §5's proposals
other than what §4 recounts (no proposal was implemented); that (B) would
let `kill_paths` sharpen soundly; the reading of (L-a) hits as artifacts of
`vsubr`/`datum` encodings. The FX-26 checker was not run with any variant.
