# Specifications that explain their failures: proof attempts, counterexamples and bounded checking

Design note, 2026-10-23, from a discussion with the user. Research only:
no code was changed. The questions: how FX-26 should let a program carry
specifications and assertions that become proof attempts; what it should
say when an attempt fails, and how it can suggest what to change; and
whether a model checker such as CBMC or Kani belongs in fixpt. No source
was read online for this note: every claim about another system is
*(from memory)*. FX-26 facts cite files in this repository.

## 0. In brief

- **A failed obligation has three possible meanings, and the user
  needs to know which.** It is *false* (inputs exist that break it); it
  is *true but not inductive* (the code is right, but the specification
  is too weak to carry itself through a recursive call); or it is *true
  but beyond the prover* (nonlinear, or it needs a lemma). Each calls
  for a different change: to the code or the specification, to a
  stronger specification, or to a lemma. Today the verifier says the
  same thing for all three.
- **A model checker is how to tell them apart.** A counterexample from
  a solver, replayed by running the real code, sorts the first two: if
  the real run breaks the specification too, it is false; if the real
  run keeps it, the counterexample was made of a value some callee was
  only *assumed* to return, and that is the place the specification is
  too weak. No counterexample and no proof is the third.
- **Add `assert`, `assume` and `any`** (an arbitrary value, for
  harnesses), and let specifications call the program's own procedures
  that are pure, terminating and total. FX-26 already knows all three
  facts of a procedure: its effect, the size-change check, and its proof
  debts (`TODO.md` §86).
- **Bounded model checking is a second mode of the verifier fixpt
  has**, not a new tool: the same forward walk, with calls inlined to a
  depth instead of replaced by their specifications, and the resulting
  formula given to an SMT solver for a model.
- **Kani on kayak's Rust is a cheap experiment; CBMC itself is not the
  way in.** CBMC is bit-precise over C-like programs; FX-26's bignum
  `int`, its sums and its closures fit SMT's integer and datatype theories
  better.

## 1. Where this came from

The user is building acquittal (`~/Dev/LangPlay/acquittal`), a rewrite of
ACL2 in R7RS Scheme on Larceny, and asked how FX-26 might let programs
carry specifications that map to proof attempts, with feedback on where
an attempt failed and how the specification or the assertions might be
changed. Separately, they had been musing about putting a model checker
such as CBMC's or Kani's into fixpt. `typed-cellular-code.md` §11 leaves
open three questions that these answer: whether `(assert P)` inside a
body is wanted (question 1), which prover outside (question 3), and what
the logic's functions are (question 4).

## 2. What there is now

- **Specifications in procedure types** (`typed-cellular-code.md` §8,
  `specs.rs`): `(subr E ((x int) …) T (requires p) (ensures r q))`,
  over the procedure's own `int`s and `nat`s, its `bool`s, shapes,
  certifications, and the connectives. Both checkers read them and
  compare two by behavioural subtyping; neither proves anything of a
  body.
- **The verifier proves them of the cells** (`typed_cells.rs`): the
  `requires` assumed at entry, each branch's condition, each callee's
  `ensures` after a call; the `ensures` a VC at each `return`, a
  callee's `requires` at each call; recursion by partial correctness.
- **The prover** (`logic.rs`, `entails`): connectives taken apart,
  disjunctions case by case, Fourier–Motzkin for each case. It answers
  yes or no, and no means "not shown".
- **What a VC not shown becomes**: `Outcome::open`, the implication
  written out "for a prover outside" (`Verifier::prove`). `failed` is
  for type VCs; a specification's VC is never found false.

So, in `tests/programs/specs`, these two come out the same:

```
;; wrong-ensures.fx: false (abs returns x itself where x < 0)
(define abs (subr pure ((x int)) int (ensures r (<= 0 r)))
  (lambda (x) (if (< x 0) x (- 0 x))))

;; square.fx: true, but x·x is beyond Fourier–Motzkin
(define square (subr pure ((x int)) int (ensures r (<= 0 r)))
  (lambda (x) (* x x)))
```

Both are `; Unverified`, each with an open implication. One is a bug;
the other wants a lemma. Nothing in the output says which.

What specifications cannot yet say: anything about what a program's own
procedures compute. `TODO.md` §116 lists `(length xs)` and a sum's tag as
terms still to come, and `old` for what refs and arrays held.

## 3. Three ways to fail

**False.** `abs` above: `x = -5` gives `-5`. The fix is in the code or
in the specification, and the user wants the input and the path.

**True but not inductive.** A recursive procedure is verified assuming
its own specification at its recursive calls (§8, "Recursion"). If that
specification is true but too weak, the assumption lets the recursive
call return values the real procedure never does:

```
(define k (subr (maxeff (read (globals k)) spin) ((n int)) int
            (requires (<= 0 n))
            (ensures r (<= 0 r)))
  (lambda (n) (if (= n 0) 0 (+ (* 2 (k (- n 1))) (- 2 n)))))
```

`k` is the identity on naturals, so `r ≥ 0` holds. But the VC at the
second `return` is `(k (- n 1)) ≥ 0 ∧ n ≥ 1 ⇒ 2·(k (- n 1)) + 2 − n ≥ 0`,
which fails with `n = 5` and `(k 4)` assumed to be `0`. The real `(k 4)`
is `4`. The fix is a stronger specification, `(= r n)`, which is
inductive. This is the commonest failure in practice and the one users
find hardest to diagnose. ACL2 meets the same thing as a lemma that needs
generalizing, and Dafny as an invariant that needs strengthening *(from
memory)*.

**True but beyond the prover.** `square` above. The fix is a lemma, a
hint, or a weaker claim; the user wants to be told which term was beyond
the prover (here, a product of unknowns, which `logic.rs` takes as an
atom of its own).

## 4. What a program says

Three forms, beside `requires` and `ensures`:

| form | meaning | in a proof | at run time |
| --- | --- | --- | --- |
| `(assert P)` | `P` holds here | a VC here, then assumed | checked; failing safely |
| `(assume P)` | only runs where `P` holds | assumed | checked; the run discarded where it fails (in a harness), else failing safely |
| `(any T)` | an arbitrary value of `T` | a fresh unknown | drawn by the test runner |

`assert` is §11 question 1. Inside a body it is also how a user localizes
a failure: an `assert` halfway down says whether the trouble is before it
or after it, which is how Dafny users debug *(from memory)*.

`any` and `assume` are for **harnesses**: procedures that state a
property of others, as Kani's proof harnesses do *(from memory)*:

```
(define insert-keeps-sorted (subr (choose) () unit)
  (lambda ()
    (let ((x (any (listof int @heap))) (e (any int)))
      (assume (sorted? x))
      (assert (sorted? (insert e x))))))
```

`any` should have an effect of its own (`choose` above, a name to
decide), so that only harnesses use it and nothing else can come to
depend on an arbitrary value: an effect as a licence, as `docs/fx26.md`
puts it. What `choose` licenses is being run three ways: by the test
runner, by the verifier, and by the bounded checker (§7).

**Runtime checking** of `requires`, `ensures` and `assert` is the
loader's `guard` and `contract` answers (`typed-cellular-code.md` §7)
applied to specifications. It is also the cheapest source of
counterexamples: run harnesses on values enumerated or drawn from each
`define-datatype`, with the specifications checked, before anything
symbolic. ACL2s does this before every proof attempt *(from memory)*,
and finds most false conjectures that way. fixpt's engines make it
nearly free.

## 5. The logic's functions

For specifications to say what a program computes (`(sorted? r)`,
`(= (len r) (+ (len a) (len b)))`), they must call the program's own
procedures. A procedure may stand in a specification when it is:

- **pure** (its effect, already checked);
- **terminating**: no `spin` (the size-change check);
- **total**: no proof debt of its own or inherited (§86's analysis), so
  `(car t)` never stands where `t` may be `nil`.

That is ACL2's admissibility test for a definition, made of analyses
FX-26 already does, and it answers §11 question 4 by leaving partial
functions out of the logic, rather than by giving them unknown values
or definedness conditions. Such a procedure is then executable in
specifications (runtime checking, replay in §8) and has a definition the
provers can use (an equation per way through its body).

Its terms need more than integers: `define-datatype`'s sums and products
(constructors, tags, fields), lists, and the logic's functions applied to
them. That is the "terms of more than integers" of `TODO.md` §116.

## 6. Provers, cheapest first

1. **Fourier–Motzkin** (`logic.rs`), as now.
2. **An SMT solver**, through SMT-LIB 2 (§11 question 3, `TODO.md`
   §116): integer arithmetic for `int` (a bignum, so integers, not bit
   vectors), bit vectors for the fixed-width types, algebraic datatypes
   for `define-datatype`, uninterpreted functions with their equations,
   or `define-fun-rec`, for logic functions. Solvers unfold recursive
   definitions incompletely *(from memory)*: enough for many facts,
   never for induction. The solver must be asked for a **model** when it
   finds the VC's negation satisfiable: the model is the counterexample.
3. **An inductive prover** for what needs induction: an ACL2-style
   waterfall (rewriting with lemmas, induction schemes from the logic
   functions' recursion). That is what acquittal is; how FX-26's logic
   functions would reach it is §11's question 4.

What a prover outside proves is a `trust` in §7's terms, unless it
returns a certificate the verifier checks.

## 7. Bounded checking: the verifier's second mode

The verifier walks a word forward, computing what holds, and at a call
assumes the callee's `ensures`. **Bounded mode** walks the same way but
inlines each call, to a depth `k`, and unrolls a loop (a tail call back
to the word's start) `k` times. At the bound, a path either assumes the
callee's `ensures` if it has one, or is cut off (assumed unreachable),
which makes the check an under-approximation: it finds what goes wrong
within `k`, and proves nothing beyond. Kani and CBMC report whether the
bound was enough with an *unwinding assertion* at each cut *(from
memory)*; so should this.

The formula a path gives (its conditions, the operations' results, the
negated `assert`) goes to the SMT solver of §6. A model is a run: the
inputs, the branches, each call's arguments and result. Because the walk
is the verifier's, one encoding of the cells' routines serves both
modes, and a harness is just a word whose inputs are `any`.

Whether bounded mode should walk the cells or the checked source is a
question (§11, 2): the cells are what the verifier trusts nothing above,
but feedback has to speak of the source.

## 8. Feedback that sorts failures

For each VC not shown:

1. **Ask the solver for a counterexample** to the VC: the procedure's
   inputs, and the value each callee was assumed to return.
2. **Replay it.** Run the real procedure on those inputs, specifications
   checked:
   - the real run also breaks the specification: **false** (§3). Report
     the inputs and the path, at source places;
   - the real run keeps it: the counterexample needed a callee to
     return what it never does. **Not inductive** (§3). Report the
     assumed value beside the real one, at the call where they differ:

     ```
     k: the ensures (<= 0 r) is not shown at the second return.
       It is true for n = 5, but not inductive: the proof assumed
       (k 4) could be 0; it is 4. What (k 4) returns needs saying:
       an ensures that relates r to n.
     ```
3. **No counterexample, and no proof**: **beyond the prover** (§3). Name
   what was beyond it: a product of unknowns, a logic function the solver
   would not unfold, a quantifier.

Each VC already knows the place it came from (`what` in
`Verifier::prove`); the report must map it to the source. Suggestions
are kept to what the classification licenses: "the code or the
specification is wrong here, for these inputs"; "strengthen this
`ensures`, or this `requires`: it lets this call return this"; "this
needs a lemma about this term". The inductive prover in §6 can say more
where it fails: ACL2 prints the goals it was stuck at ("checkpoints"),
which are usually the lemma the user should state *(from memory)*.

## 9. CBMC and Kani

What they are *(from memory)*: CBMC is a bounded model checker for C
(and, through its intermediate GOTO programs, more): it unwinds loops and
recursion to a bound, encodes the program and its negated assertions
bit-precisely as SAT or SMT, and reports a trace when it finds one. Kani
compiles Rust's MIR to GOTO programs for CBMC; a proof harness uses
`kani::any()` for arbitrary values and `kani::assume`, and newer Kani has
function contracts (`requires`, `ensures`, `modifies`) that it checks
once and then uses in place of the function.

Two ways they could serve fixpt:

- **Kani on kayak's Rust.** kayak turns KFX, a subset of FX-26, into
  Rust. FX-26 specifications could become Kani contracts and harnesses on
  the generated code, which would show cheaply what bounded checking
  finds in real FX-26 programs. It trusts kayak's translation, covers
  only KFX, and would check `kayak-rt` along with the program. Not tried.
- **CBMC directly**, from cells or source to GOTO programs. Not
  recommended: CBMC's strength is bit-precise C, and FX-26's bignums,
  sums, frozen data and closures are better served by SMT's integers and
  datatypes (§6), with the verifier's own walk (§7) doing the unwinding.

## 10. Stages

- **S1.** `assert`, `assume`, `any` with its effect; runtime checking of
  specifications; a test runner drawing harnesses' inputs from datatypes.
  Counterexamples for false claims, with no solver. Done (2026-10-23),
  but `any`, and inputs of datatypes: `assert` and `assume` standard
  procedures whose specifications say what the verifier makes of them;
  `fixpt test`, which runs the program with each specified `lambda`
  checking its specification and calls each procedure it can on inputs
  drawn from its parameters' types (`int`, `nat`, `bool`, lists of
  those). A harness's parameters are its arbitrary values, so `any` and
  its effect are not needed (types are not there at run time to draw by
  in any case). See `docs/fx26.md`, "Specifications".
- **S2.** SMT-LIB output for open VCs (`TODO.md` §116), with models read
  back, mapped to source, and replayed (§8): the three classes reported.
  Done (2026-10-23), source places too: `fixpt verify`
  and the REPL's `,verify` ask z3 of each open VC (`fixpt_fx26::smt`);
  a refuted one is run on the solver's values of the parameters, and
  said false, with the input, or not inductive, with the call whose
  value the proof took wrongly beside the real one; one neither proved
  nor refuted, beyond the prover. `TODO.md` §119 has what is left.
- **S3.** Bounded mode (§7), with unwinding checks.
- **S4.** Logic functions (§5) and terms over datatypes in
  specifications. Begun (2026-10-23): a specification calls `pure`
  globals of a `bool`, `int` or `nat` result; the solver is given their
  definitions over integers, booleans and finite lists of these (and of
  lists so, 2026-10-24), so
  `insert` is proved to keep a sorted list sorted where its `ensures` is
  inductive (`specs/logic-insert.fx`). What is left is `TODO.md` §120.
- **S5.** An inductive prover for what S2 and S3 leave (§6, 3).
- Beside these, at any time: Kani on kayak's output (§9), as an
  experiment.

## 11. Open questions (the user's)

1. **`any`'s effect**: its name, and whether a harness is a kind of
   definition or just a procedure with that effect.
2. **Cells or source** for bounded mode and for feedback (§7).
3. **Which solver**, and whether fixpt may depend on one being installed
   (a test that needs it, skipped without it, as the stencils' column is
   left out without nightly).
4. **How logic functions reach an inductive prover**: translated to
   ACL2's terms (acquittal's), or a prover over FX-26's own terms.
5. **What a proof outside is worth**: `trust`, or a certificate the
   verifier checks (§7 of `typed-cellular-code.md`).
