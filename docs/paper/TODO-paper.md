# FX-26 paper: what a submission still needs

`fx26.tex` (built: `fx26.pdf`) was drafted from the three repositories
alone, at Fixpt `0585488`, Kayak `f59ac8cd` and Heist `18efce5`. Every
number in it comes from a file in one of them. This list is what a PLDI
paper would normally contain that the repositories do not, so the draft
either says so (§8.5, §9) or leaves it out. Each item is a task for the
Fixpt team; the priority is how much a reviewer would mind.

Build: `pdflatex fx26 && bibtex fx26 && pdflatex fx26 && pdflatex fx26`
(TeX Live with `acmart`, `texlive-science`, `cm-super`).

## A. Evaluation (most of what reviewers will ask for)

1. **Baselines (high).** No benchmark has ever been timed on another
   implementation. Run scheme-bench on Larceny (its home), Chez and
   Racket; mllang-bench on MLton and OCaml; the same machine, same
   inputs. The paper currently makes no cross-system speed claim.
2. **Hardware and OS (high).** No CPU model, core count used, RAM or OS
   version is recorded anywhere ("the development machine", "a 128-core
   shared machine"). The platform also moved from arm64 macOS to x86_64
   Linux without re-baselining; Table 4 is arm64 from 2026-09-28.
3. **Fresh, complete tables (high).** The last full per-machine table
   is 2026-09-28; scheme-bench and mllang-bench were last run in full on
   2026-09-29/10-12 and include 1.8-3.5 s of start-up. Re-run all three
   at one commit, start-up excluded.
4. **Statistics (high).** Everything is best-of-3 or a single run.
   Need at least 10 runs, mean or median, and a dispersion measure, on a
   quiet machine.
5. **Ablation of what effects, types and regions buy (high).** This is
   the paper's thesis and it is supported by one-off before/after
   numbers on eight micro-benchmarks. Needed: switches to turn off typed
   calls, typed primitives, effect-summary versions, inline region
   allocation and checked `%fx-note`s independently, and a table over
   scheme-bench, mllang-bench and the Heist programs.
6. **MLton inputs (medium).** mllang-bench uses our own iteration
   counts because MLton's driver was not fetched, and some inputs were
   shrunk; fetch the driver and use its counts, or the baselines are not
   comparable with published numbers.
7. **Unported benchmarks (medium).** 22 of Larceny's 75 and about 13 ML
   programs were skipped for floats or file I/O, both of which now
   exist. Port them or say why not.
8. **Memory, GC and code size (medium).** No per-benchmark peak memory,
   GC time or code-size figures.
9. **Compile-time table (medium).** Per phase for both front ends
   exists only for the front end itself (2026-10-02, 10-11) and `peval`.
   Wanted: lines per second for check and compile over the suites and
   the Heist programs.
10. **Lockstep, quantified (high; it is a claimed contribution).** How
    many disagreements between the Rust and FX-26 checkers and
    compilers were found, by kind, and which side was wrong? There is
    no catalogue (`docs/divergences.md` is about FX-87/FX-91). A
    script over the commit history, or a log kept from now on.
11. **KFX-as-Rust measurements (medium).** Six micro-benchmarks from
    one day (2026-10-11), no hardware, two folded at compile time by
    rustc. Re-run with larger programs; add rustc compile times.
12. **How often effects choose the Rust (medium).** Count, in `boot/`
    and the other generated crates, functions emitted as plain,
    `Result`-returning, `async`, and `Send + Sync` closures. One table
    would carry §7.
13. **KFX acceptance by reason, current (low).** The refusal survey is
    of 286 programs on 2026-10-11; 194 are accepted now with no
    breakdown of the rest.
14. **Kayak's checker against Fixpt's (low).** 423 same and 88 differ
    of 541; the other 30 are not accounted for in C289.

## B. Case studies (Heist)

15. **Annotation overhead (high).** No measurement of signature
    characters or lines against code, per program. Table 3's counts
    were made for this draft with a script; the team should own and
    check one (and decide how `define-effect` bodies are classified:
    the draft says every named effect of the five programs includes
    `spin`, from inspection, not from a checked count).
16. **Sizes of the originals (high).** Only Yank is sized (13,012
    lines). Line counts for lockpick, shakedown and cahoots would let
    the paper compare a typed port with its source.
17. **Bugs the checker caught (high).** None is recorded as such. Either
    mine the Heist history and FIXPT-CHANGES.md for refusals that were
    real defects, or keep a log. Likewise a count of refusals that were
    the checker's limits (fuel added, `the` added).
18. **Check and compile time per Heist program (medium).** Only two
    data points exist.
19. **More application baselines (medium).** ratfink against shakedown,
    casing against Alloy (time, not only agreement), s7st against a
    second Scheme. combo vs lockpick was measured on a shared machine;
    s7st.md itself says differences under about 25% are noise.
20. **Processes in an application (medium).** No Heist program uses
    `spawn`, `par` or `race`; the determinism guarantee has no
    application evidence. A parallel workload (the CFA or solver
    portfolio) with speedup figures would support §4.2.
21. **Macros in use (low).** 70 `define-syntax` in Heist and a recorded
    saving of 98,871 characters; say how the saving was measured.

## C. Formal development

22. **A formal semantics in the paper (high).** Figure 2 gives five
    rules reconstructed from the prose of `docs/fx26.md` and
    `soundness.md`. The team should check them (in particular the set
    of atoms masking applies to, and whether `send`/`receive` on a
    private region are masked) and supply the dynamic semantics and
    the full rule set, as an appendix.
23. **K26 is behind the language (high).** It predates unions,
    intersections, `io`, processes and the 2026-10-29 masking change.
    Update it, or state exactly which language the theorems are about.
24. **Theorem statuses (high).** T5 (termination of `spin`-free code)
    is conjectured; T3 (effect soundness) is sketched and false as
    stated for composable continuations; T0, T4, G1 sketched; T6 and
    S1-S3 conjectured. `soundness.md`'s status table and its theorem
    text disagree on whether control cases are done.
25. **Mechanisation (medium).** Nothing is mechanised. Heist's proposal
    (sanitiser machine, enumeration of small programs, Rocq/Iris) is
    open. Even a Redex model with random testing would change §9.
26. **Fixes "argued, not proved" (medium).** F17 and F18.
27. **Determinism (medium).** The `par` guarantee is stated in prose;
    no theorem, no proof. Same for the licence rule (that a licensed
    computation is unobservable) and for cancellability.
28. **Macros (medium).** Soundness of signatures, α-equivalence, and
    "full expansion = repeated expand-once" are argued or unproved;
    hygiene is tested.
29. **The KFX translation (medium).** K1 (same answers) is tested, with
    known gaps listed in Kayak's TODO; no statement of type or effect
    preservation.
30. **Termination checker, described precisely (low).** The measures
    and the size-change graph construction, with the 4000-graph budget.

## D. Related work

31. **Citations to verify (high).** Several design notes say their
    literature is cited "from memory" (`soundness.md`,
    `recursive-subtyping.md`, `cellular-compilers.md`, `twobit.md`).
    `fx26.bib` was written for this draft; check every entry against
    the source, especially FX-91's report number, Sheldon's thesis date
    (1989 in one note, 1990 in another), and the unattributed
    "Communication effects for parallel processes" in `fx26.md`.
32. **Comparisons the repositories never make (high).** Koka, Effekt,
    Frank, OCaml 5, Flix, capture checking and reachability types are
    cited in §10 from general knowledge; the docs mention only Koka's
    `div`. Someone who knows FX-26 should write the technical
    comparison (row polymorphism against region-indexed sets; handlers
    against typed prompts; Koka's `div` and Agda/Idris/Liquid Haskell
    termination against `spin`).
33. **Prior work on effects to Rust and regions to lifetimes (medium).**
    Only GhostCell is cited in Kayak. The claim "we know of no prior
    translation that selects Rust's function colours by a source effect
    system" needs a literature search.
34. **Speculative evaluation in REPLs (medium).** The claim of no
    precedent needs checking (live programming, Hazel, eager evaluation
    in browser consoles).

## E. Paper mechanics

35. **Authors, affiliations, acknowledgements, funding.** Placeholders.
36. **Disclosure of AI assistance.** The repositories record that much
    of the code, the design notes and this draft were produced with an
    AI assistant (`CLAUDES_CHOICES.md`). ACM policy requires disclosure;
    the team must write it.
37. **Anonymisation.** PLDI review is double-blind; the draft names the
    repositories. Decide and apply.
38. **Artifact.** No reproduction instructions for the benchmarks, no
    CI configuration, no container. An artifact appendix and a
    `scripts/paper/` that regenerates every table from a commit.
39. **Data availability statement, CCS concepts check, DOI, page
    limit.** The draft is 20 pages in `acmsmall`; PLDI's limit excludes
    references.
40. **Full history for dates and counts.** The clones used were
    shallow (50 commits each), so commit counts and the project's start
    date are taken from the docs (2026-09-24), not from git.

## F. Inconsistencies found in the repositories while drafting

These are not gaps in the paper but would mislead its next author.

41. README says the front end is "about 78,000 lines"; it measures
    87,071 (11,534 of them `*-types.fx`). README says Heist is "about
    39,000 lines"; it measures 38,202.
42. `docs/fx26.md` (near "effect summaries") says "no compiler uses
    them yet"; `docs/performance.md` reports the "versions" optimisation
    built on them.
43. `docs/fx26-grammar.md` (2026-10-05) lacks `oneof`/`anyof`/`allof`,
    `io`, `init`, `send`/`receive`/`nondet`, `typecase`, bounded effect
    binders and `#:seal`/`#:unseal`, and says definitions are declared
    ahead, which `fx26.md` contradicts.
44. `docs/research/typed-macros.md` opens "Nothing here is built" and
    `first-class-modules.md` "Nothing is built yet"; both are built.
45. `docs/fx26.md`'s open questions still list "does FX-26 need
    macros?".
46. Heist `TODO.md` lists `takes_modules_at` as open; its request file
    says done in Fixpt `8202075e`.
47. Kayak's `DONE.md` stops at C212 (2026-10-24); later decisions are
    only in `CLAUDES_CHOICES.md`. `INCR_IMPED.md`, cited by three Fixpt
    commit messages, is in neither repository.
