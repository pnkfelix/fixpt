# Twobit (Larceny's compiler): passes, optimizations, recorded wins

A survey made on 2026-09-26 for the FX-26 optimizing compiler (PLAN.md,
"After M12"). It was written by a research agent that read the Larceny
checkout at `~/Dev/LangPlay/larceny` and its git history, read-only. Paths
are relative to that checkout. They have not all been rechecked by hand,
so confirm a citation before relying on it.

## 1. Passes, and the rule that output stays source language

**The core language.** Passes 1 through 3 take and give the same grammar,
and pass 4 takes it too:

- `lambda`;
- `define`, internal only;
- `quote`;
- variable references, written `(begin I)`;
- calls, `set!`, `if` and `begin`.

The grammar is restated in the headers of `src/Compiler/pass1.sch:11-38`,
`pass2p1.sch:20-47`, `pass3.sch:22-48`, `pass3anormal.sch:17-44` and
`pass4p1.sch:10-35`. Every lambda has the shape
`(lambda args (begin D ...) (quote (R F G <decls> <doc>)) E)`, so the
analysis is a quoted constant inside a legal lambda. The accessors are in
`pass2.aux.sch:264-313`.

- **R**, for each bound variable: its references, assignments and calls,
  as pointers into the tree. Rewriting through them rewrites the tree
  itself (`pass1.sch:46-58`).
- **F**, the variables free in the body. It may hold a few stale extras.
- **G**, the part of F that an escaping inner lambda captures. It is
  approximate.
- **decls**, declarations. `(anf)` asserts the body is in A-normal form,
  and pass 4 trusts it.
- **doc**, the name and source, for debugging.

Each pass's header says which annotations it needs valid and which it
leaves as garbage. `pass3.sch:75-81` is explicit: inlining spoils R and F,
constant propagation keeps both, and commoning and targeting recompute F.
`check-referencing-invariants` checks them after pass 3
(`pass3.sch:162-165`).

**Facts the optimizer finds are kept in two places.** Either they go in an
annotation, or they become *names in the program*:

- Type specialization renames the primitive: `+` becomes `.+:fix:fix`
  (`pass3rep.sch:283-303`, tables at `iasn.imp2.sch:144-190`).
- Register targeting renames temporaries to `.REG1`, `.REG2`, and so on
  (`pass3commoning.sch:24-30`).

Checks are ordinary source too. Inlining `car` gives
`(let ((x x0)) (.check! (pair? x) exn x) (.car:pair x))`
(`common.imp.sch:576-599`). A later pass removes the check by proving its
test true, rewriting it to `'#t`.

The passes:

- **pass0** rewrites what the R6RS/R7RS library expander produces, so that
  libraries get interprocedural optimization.
- **pass1** does macro expansion and alpha-conversion, and makes the
  first R.
  - Block compilation turns top-level definitions that are never assigned
    into locals of one big `let` (`pass1.sch:81-`).
  - Benchmark mode turns self-calls into calls of a known local
    (`expand.sch:146-160`).
- **pass2**, the simplifier:
  - single-assignment elimination;
  - assignments that remain become explicit cells;
  - lambda lifting;
  - let-conversion (a let-bound lambda that is only called becomes a known
    procedure);
  - `if`/`case` algebra;
  - `case` compiled to binary search, a table or hashing;
  - light constant folding.

  Its output invariant: no assignments except to globals, and every
  internal definition is a *known procedure*, a lambda referenced only in
  call position (`pass2p1.sch:67-71`).
- **pass3**, flow analysis:
  1. inlining of known local procedures, guided by a call graph;
  2. interprocedural constant propagation and folding;
  3. A-normal form;
  4. commoning (common subexpressions, copy propagation, dead code),
     representation inference, then commoning again with register
     targeting (`pass3.sch:99-165`).
- **pass4** generates MacScheme-machine assembly. `pass4p3.sch` is a local
  optimizer over it.
- **pass5** is the assembler, with a peephole optimizer per target.

## 2. The optimizations

| optimization                                   | where                                  | notes                                                           |
| ---------------------------------------------- | -------------------------------------- | --------------------------------------------------------------- |
| primitives integrated, with explicit `.check!` | `common.imp.sch:540-600`               |                                                                 |
| self-recursion to a known local                | `expand.sch:146-160`                   | benchmark mode                                                  |
| block compilation                              | `pass1.sch:81-`                        |                                                                 |
| single-assignment elimination                  | `pass2p2.sch:13-75`                    |                                                                 |
| assignments to cells                           | `pass2p2.sch:205-`                     | keeps lambda lifting simple                                     |
| let-conversion, known procedures               | `pass2p1.sch:391-443`                  |                                                                 |
| lambda lifting                                 | `pass2p2.sch:336-472`                  | "not a clear win" (`:341-346`)                                  |
| `if`/`case` control                            | `pass2if.sch`                          | sequential beats binary below about 8 constants (SPARC)         |
| inlining known local procedures                | `pass3inlining.sch:14-57`              | thresholds: tail 10, non-tail 20; a non-tail inline saves a frame |
| constant propagation and folding               | `pass3folding.sch:14-88`               | at most 5 iterations                                            |
| A-normal form                                  | `pass3anormal.sch`                     | abandoned above size 80000                                      |
| CSE, copy propagation, dead code, targeting    | `pass3commoning.sch:14-35`             |                                                                 |
| representation inference                       | `pass3rep.sch`, `*.imp2.sch`           | specializes primitives, removes checks; widens after a budget    |
| known calls                                    | `pass4p2.sch:90-115`                   | a branch to a label instead of `invoke`                          |
| parallel assignment of arguments               | `pass4p2.sch:399-600`                  |                                                                 |
| frame elision                                  | `pass4p1.sch:60-91`, `pass4.aux.sch`   | lazy `save`; unused stores dropped, and then empty frames        |
| local assembly optimization                    | `pass4p3.sch:7-22`                     |                                                                 |

## 3. The peephole optimizer

`src/Asm/<target>/peepopt.sch` is a hand-coded decision tree over the next
two to four instructions, run just before each is assembled. It fuses
sequences into target-only superinstructions:

- **Three-address fusion.** `reg r; op2 p; setreg d` becomes
  `reg/op2/setreg`, for `car`, `cdr`, `+`, `-`, `eq?`, `cons`,
  `vector-ref` and a few more.
- **Branches on tests without a boolean.** `reg r; op1 null?; branchf L`
  becomes one instruction.
- **Check fusion.** `reg; op1 pair?; check` becomes one. Two range checks
  become one unsigned compare.
- **Small allocations unrolled.** `const k; make-vector` for k from 0 to 9.
- **Calls.**
  - `global; invoke` fuses.
  - `setrtn L; branch; L:` becomes a hardware call.
  - `setrtn/invoke` was disabled because it "does not pay off"
    (`Sparc/peepopt.sch:686-700`).
- **x86.** `save` plus stores become pushes.

## 4. What the history records of measured effects

Little. Commit messages are terse, and none quantify the Twobit passes.
What there is:

- `da31d407` (2007-02-14), the A-normal form evaluation-order heuristic:
  "1%-2% overall" on Intel; little on SPARC.
- `2724ea7e` (2007-02-06), stores as x86 pushes: heaps about 52-64 KB
  smaller. `divrec` was 10% faster, but `deriv`, `diviter` and `divrec`
  were 4-6% slower.
- **Negative results:**
  - `setrtn/invoke` did not pay;
  - two peepholes made programs slower
    (`doc/DevManual/nasm-representations.txt:87-96`);
  - lambda lifting is "not a clear win";
  - a type-propagation pass "stalled due to problems with lambda-lifting"
    (`doc/OldDocs/TODO-RAINYDAY:37-38`).

## 5. What the survey recommends for FX-26

This section is the agent's inference, not something it read. For
threaded code, where calls, returns, frames and stack traffic cost the
most:

1. Known procedures and let-conversion: direct calls, and no closure for
   a lambda that does not escape.
2. Inlining small known procedures, favouring non-tail calls.
3. Specializing primitives by type, by renaming them, so the output is
   still FX-26.
4. Superinstruction peepholes on the threaded code, each measured.
5. Frame and store elision.
6. Constant folding, copy propagation and dead code, after inlining.
7. Assignments made explicit cells, which FX-26's effects already make
   visible.

Lambda lifting comes last, since flat closures already spare a known
procedure its closure.
