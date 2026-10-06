# One set of decisions, two back ends

Design note, 2026-10-06, with the user. For review before any code. It
answers the last of the front end's cross-file hook cycles (`TODO.md`
§34): the stack compiler and the register compiler calling each other.

## Where we are

Each compiler of FX-26 to cellular words is written twice, in Rust
(`cellular.rs`, `cellular/regcode.rs`) and in FX-26 (`compile*.fx`,
`regcode*.fx`), and the two must make the same words. Each is two
compilers of the same trees:

- the **stack compiler** makes every lambda's word: cells for the
  interpreting machines;
- the **register compiler** makes, for most of those words, a register
  twin: the same lambda compiled again, from its tree (not from the cells),
  for the machines that compile register code. A closure is of the stack
  word; a machine that runs register code takes its twin, if it has one.

They are not phases. Each time the stack compiler finishes a lambda's word
it calls the register compiler for the twin (`lambda_word_in`;
`c-lambda-word-in`, `c-register-twin!`, through the hook
`c-register-code`), and the register compiler calls the stack compiler back
when it needs a word not made yet (`r_lambda`, `r-made-word`) and for every
specialized copy (`r_specialize`, `r-spec-word`). That cycle is why the FX
files need the hooks `c-register-code` and `c-standard-register-code`.

What is shared is mostly decided already in one place, and asked twice:

| Decision                          | Where decided                                   | How                                    |
| --------------------------------- | ----------------------------------------------- | -------------------------------------- |
| a lambda's shape, free values     | `lambda_of`, `captured`; `c-lambda-of`, `c-lambda-captured` | pure, of the tree and the env |
| where a name lives                | `where_is`; `c-where`                           | the env, and the globals visible       |
| lambda lifting of a `letrec`      | `lift`; `c-lift`                                | the stack walk, on first visit, cached by span |
| joins                             | `r_join_ok`; `c-join-ok?`                       | pure (FX memoizes it)                  |
| an applied lambda as a `let`      | `applied_lambda`; `c-applied-let`               | pure                                   |
| constants, conversions, reshapes  | the checker's facts (`c-set-facts!`)            | tables, up front                       |
| what may be inlined, specialized  | after each definition (`c-record-inline`)       | lists, filled as definitions are made  |
| whether *this call* is inlined    | the register walk (`r_inline`; `r-inline`)      | at the call                            |
| whether *this call* is specialized| the register walk (`r_specialize`; `r-specialized`) | at the call, making a word then    |

The coupling that remains is in four places:

1. **Specialization makes words in the middle of the register walk.** A
   call of a recursive higher-order global at a known lambda argument gets
   a copy of the procedure: its stack word (the body compiled again, under
   the definition's globals, named `f@lambda@N`) and its specialized twin,
   made then, with no memo; so a body whose twin is tried twice (the fast
   and the plain version, a leaf retried as not one) makes its copies
   twice.
2. **The globals a lookup sees move with the walk.** An inlined body, or a
   specialized copy, sees the globals of its definition, not of the call
   site: the register walk sets `genv_limit` / `c-genv` around them. One
   tree node resolves differently at each inlined site.
3. **Order.** The lists of what may be inlined or specialized gain a
   definition only once its word and twin exist; lifting is decided by the
   stack walk's first visit; inner twins are made before the outer word is
   assembled.
4. **Words are matched by key.** The register compiler finds an inner
   lambda's word by span, parameters, own name and free values
   (`made`/`reuse`), so its own env must reproduce the stack env's exactly.

## The proposal

A **middle phase** between the checker and the compilers: one walk that
makes every decision the two compilers share, and writes them down, so
that each compiler is a back end over a decided program and neither calls
the other.

What it produces, for each top-level form:

- **A table of procedures.** Every lambda the form makes (lifted members
  included), every specialized copy, every standard operation used as a
  value: each with its parameters, its body, its own name, its captured
  names and their places, its lift plan, its name for profiles
  (`outer/inner@N`), and the globals its body sees. A procedure is made
  once; a copy is keyed by (procedure specialized, lambda argument), so a
  body tried twice finds it.
- **Decided call sites.** At each call: plain, inlined (with the inlined
  copy of the body, its names resolved for its definition), or specialized
  (naming the copy in the table). The stack back end compiles every call
  as plain, as now; the register back end follows the decision.
- **Resolved names.** Each variable: local slot, free value, loop, global
  `k`, or standard, as `where_is` says, in the context the node is compiled
  in. An inlined copy is a copy of the subtree with its own resolutions, so
  no back end moves the globals limit.
- **The facts**, as now: tables keyed by span.

Then, per form:

1. the stack back end makes each procedure's word, in the table's order;
2. the register back end makes each procedure's twin, attached to its word,
   in the same order;
3. the form's inline and specialization candidates are recorded.

In FX-26 the middle phase is a file (or files) between `compile-lift.fx`
and the back ends; the program driver (`compile-program`, `c-tops`) moves
after `regcode-entry.fx`. The hook `c-register-code` goes, and so does
`c-standard-register-code`: a standard operation's procedure is in the
table like any other. What is left is three hooks inside the register
compiler (`r-module-code`, `r-reshape-code`, `r-leaf-call`), its own
recursion across its files, for the per-file regrouping the other cycles
get.

## What changes, and what must not

**Words.** The agreement tests compare the two implementations' words, so
both change together, step by step, each step keeping them equal. Two
changes of output are expected and wanted:

- specialized copies made once per (procedure, lambda), not per visit:
  fewer words, the same code;
- names that are the same as now (`f@lambda@N`, `outer/inner@N`), assigned
  in the middle phase.

Everything else must come out the same: which words, their cells, their
twins, and the order they are made in (the table is in the order the stack
walk meets lambdas now, post-order, inner first).

**Speed.** One more walk of each form, and copies of inlined bodies made
once instead of re-walked under a moved limit. Measured against
the self-compile's compile phase (0.21 s) and peval's at each step.

## Steps

Each one a commit, both implementations, agreement tests and the suite
green, the self-compile measured.

1. **Memoize specialized copies** by (procedure, lambda span, globals) in
   both compilers. Small, and it settles the one expected change of words
   first, on its own. *Done, 2026-10-06*: keyed by the procedure's word, the
   lambda's span, what it captures and the globals it sees
   (`spec_copies`; `c-spec-made`, reset with the other span-keyed tables).
   The front end's self-compile: time and collections per phase unchanged
   (`tests/bootstrap.rs`'s probe: check 1.081 s and 1.086 s, 34
   collections each; compile 0.254 s and 0.256 s, 45.5 M and 45.4 M words
   allocated). Counted (a temporary counter in `r_specialize`, over every
   test program and both bench suites): 55 copies made and 5 reused, in
   `scheme-bench/matrix.fx` (2), `mllang-bench/fx/ocaml/kb.fx` (2) and
   `mllang-bench/fx/mlton/ratio-regions.fx` (1); the front end makes none,
   having no call it specializes. What the step is for is step 3's: one
   copy per key, for the middle phase to own.
2. **The procedure table, as a pre-pass**: every lambda met, in the order
   the stack walk meets them, with what each needs (captured names, lift
   plan, name); the stack compiler reads it instead of deciding as it
   goes. Words unchanged. *Rust done, 2026-10-06* (`cellular/procs.rs`): before each
   top-level form is compiled, a walk with the stack compiler's scoping,
   arm for arm, in environments whose places are only their kinds, decides
   each lambda's captured names and each `letrec`'s lifting with the
   compiler's own predicates; the stack compiler reads them, and decides
   only for the lambdas register code compiles (an inlined body, a
   specialized copy), whose context is not the tree's. Keyed by node, not
   by place: a `define-datatype`'s constructors share their form's.
   `FIXPT_PLAN_CHECK` re-decides beside the plan and says where they
   differ: none, in 8088 lambdas and `letrec`s of the test programs and
   bench suites and 2841 of the front end. peval's `words` 2.78 → 2.84–
   2.89 ms. *FX-26 done, 2026-10-06* (`compile-plan.fx`; the tables and
   lookups in `compile-lift.fx`, read by `c-lambda-word-in` and `c-lift`):
   the same walk, reusing the compiler's scope builders (`c-own-scope`,
   `c-letrec-own`, `c-module-own`, …). Both key a lambda by where its body
   is and its parameters' names, a `letrec` by where it is: FX-26's trees,
   frozen data, have no identity to key a table by; checked to tell every
   lambda apart. The self-compile, per phase (probe, new/old/new): check
   1.083 → 1.095 s, 34 → 35 collections (the front end has the new file
   to check); compile 0.258 → 0.273 s, 43 → 45 collections, 45.5 → 47.4
   M words (the walk, its tables, the lookups): the price of a second walk
   before anything is taken out; step 3 lets register code read the plan
   instead of finding captures again.
3. **Decided call sites**: inlining and specialization decided in the
   pre-pass (the candidate lists and the call's argument trees are all it
   needs; the callee's register location is whether it is a known global),
   copies of inlined bodies made there with their names resolved. The
   register compiler reads the decisions. Words unchanged. *3a done, both compilers, 2026-10-06*: the plan decides each call
   of a global (Rust `plan_call`; FX-26 `p-call`), and register code reads
   it (`r_inline_of`, `r_special_of`; `r-inline-of`, `r-special-of`) in a
   planned lambda's own code (`r_in_plan`, `c-r-in-plan`, set when its
   register code starts), outside any inlined body or copy, which are
   another form's tree and still decide where they are (3b). The
   candidates (`c-inlines`, `c-specials`, `c-spec-now`) and the size
   measure moved into `compile-plan.fx`, which reads them. Rust's shadow
   check: no difference in 31051 decisions of the programs, 13543 of the
   front end. The self-compile, per phase: compile 0.272 → 0.281 s, 45 →
   46 collections, 47.4 → 47.8 M words; check 1.095 → 1.105 s.
   *3b-0 done, both, 2026-10-06*: a join point's lambdas (its body
   compiled inline in its `letrec`'s procedure) are found among every
   word the form's stack code made (`form_made`, `c-form-made`), not made
   again: 26 over the programs, none in the front end. Register code then
   makes lambdas only inside an inlined body or a copy.
   *3b-1 done, both, 2026-10-06*: an inlined callee's body is planned as
   `r_inline` compiles it there (its parameters local, the globals it saw,
   the names being inlined on the way not inlined again), once per callee
   in each context; it makes no closure (`inline_room`), so only its calls
   are planned. Rust nests the sub-plans (`Plan::inlined`, followed by
   `inlining_ks`); FX-26 numbers the contexts (`c-plan-child`, followed by
   `c-r-plan-ctx`). Shadow check: no difference in 41251 decisions of the
   programs, 14417 of the front end. The self-compile: compile 0.282 s
   both, 47.8 → 48.0 M words.
   *3b-2 done, both, 2026-10-06*: a specialized copy is planned as
   `r_specialize` compiles it, in a context of its own (the procedure's
   body, its parameters local, in the globals it saw), and the lambda's
   body in it as `r_spec_lambda` inlines it (its parameters and what it
   captures local, in the globals it sees at the call); neither has a
   lambda, so neither specializes. Rust's path through the plan is steps
   (`Step`: inlined body, copy, lambda); FX-26 numbers a copy's context
   and the lambda's the next (`c-plan-copies`, `c-plan-copy`), and a copy
   made where the plan's calls are has its twin read them
   (`c-r-copying`). A new test program, `run/map-specialized-inlines.fx`,
   has calls planned in all three. Shadow check: no difference in 41591
   decisions; the front end makes no copy. The self-compile (new/old/new):
   compile 0.284–0.288 s against 0.284–0.285 s, 46 collections each, 48.0
   → 48.1 M words. *Step 3 done*: register code decides no call itself
   where the plan's are.
4. **Twins as a phase**: per form, every word first, then every twin; the
   register compiler no longer calls the stack compiler, and the stack
   compiler no longer calls it. Remove `c-register-code` and
   `c-standard-register-code`; move the driver after register code.
   *Done, both compilers, 2026-10-06*, in four commits:
   - 4a: register code never made a lambda's word itself any more (none,
     counted, since 3b-0); where it would, it declines.
   - 4b: a form's twins are made after all its words, each noted with what
     its stack code knew and made (`Twin`; `c-twin`), before the form's
     procedure is noted to be inlined or specialized.
   - 4c: specialized copies are made from the plan (`CopyAt`,
     `make_copy`; `c-copy-at`, `c-make-copy`), after the form's words and
     before the twins, each copy's twin made in the copy's context: the
     56 copies register code made, no more. A standard operation's word as
     a value is made once per compile and register code looks it up,
     rather than making another beside the stack code's (fewer words: the
     self-compile allocates 48.3 → 47.9 M words, 46 → 45 collections).
     FX-26 planned a lambda definition before pushing its global, Rust
     after; FX-26 now plans after.
   - 4d: FX-26's twin phase is its own file, `compile-twins.fx`, after the
     register compiler, which it calls directly; `compile-programs.fx`
     follows it. The two hooks are gone. 40 of the front end's 50 files
     are modules.
   The self-compile: compile 0.283–0.285 s, 45 collections (0.282 s, 46
   before step 4); check 1.106–1.116 s.
5. The register compiler's own three hooks, regrouped as the checker's
   cycles are. *Done, 2026-10-06*: `r-module-code`, `r-reshape-code` and
   `r-leaf-call` closed one knot with `regcode-core.fx`'s recursive group
   (every one of its 50 members in the recursion around `r-exp`), which
   the module code and a leaf's tail call joined; their helpers stay in
   `regcode-modules.fx`, now before it. The file is 1127 lines, over the
   1000-line limit by the user's decision, to be revisited (`TODO.md`
   §41: pass the recursion, a functor module, or a seam in the group).

## Open

- **The Rust compiler follows the same structure** (the user's,
  2026-10-06), step by step with the FX-26 one, not only the same words:
  two implementations of one design are compared more easily than two
  designs.
- **Step 3's genv.** Whether every place the register walk moves the
  globals limit is an inlined body or a specialized copy (the inventory
  found nothing else: `regcode-core.fx` 379–383, 473–475;
  `regcode-helpers.fx` 117, 148; `regcode-exps.fx` 543; `regcode.rs` 640,
  1554, 1638, 1663) is to be confirmed by reading each.
- **Known divergences** to settle first, harmless or not: only the FX
  compiler resolves `extract`s in recorded bodies (`c-resolve-extracts`)
  and memoizes joins (`c-join-memo`); the two save and restore the register
  compiler's state around a specialization differently.
