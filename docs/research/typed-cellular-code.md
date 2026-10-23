# Typed cellular code, as Hoare logic

The user, 2026-10-22: "See about making a typed cellular code. Try to make
it capable of being fed into a Hoare logic system (ie I'd like its
propositions to start with type assertions as the baseline, but be
extensible to include more general expressions)."

This note is the design. It is `type-and-effect-directions.md` §4's
option (b), "a type and a certificate a small verifier checks", with
the certificate's assertions made propositions, not only stack maps.
`TODO.md` §21 says why compiled code rather than source: inference
proper is under 4% of checking the front end, so a verifier of an
elaborated source would redo nearly all of it. A verifier of compiled
code finds selects, subtyping and regions settled, and stands in for
both the check and the lowered load.

## 1. The machine the assertions speak of

Cellular code (`fixpt_engine::cellular`; `layout.rs`'s `ROUTINES`) is
token-threaded code for a stack machine with MacScheme's frames. Between
two cells of a word, the state a program can see is:
- the frame: slots `0 … d-1` of the data stack above the frame pointer,
  the arguments first, then each `let`'s values;
- the temporaries above it, `stack 0 … stack t-1`, oldest first;
- the running closure's free values, `free 0 … free m-1`;
- the globals' cells;
- the heap.

A **place** is `(slot i)`, `(stack j)`, `(free i)` or `(global g)`. An
assertion holds at a *cell boundary*: before cell `k` of a word.

## 2. Assertions

**Terms** name values:
- a place;
- a literal (`3`, `#f`, `'tag`, `nil`);
- an application of a *pure function of the logic* to terms: `(car t)`,
  `(cdr t)`, `(field k t)`, `(length t)`, `(+ t u)`, `(- t u)`, `(tag t)`.
  These are the logic's, not the program's: a term never runs. Each has a
  meaning on heap values, partial where the program's operation fails.

**Propositions**:
- `(: t T)`: term `t`'s value is of FX-26 type `T`. The baseline: every
  stack map of a JVM-style verifier is a conjunction of these.
- `(= t u)`, `(< t u)`, `(<= t u)`: integer relations, and `(eq t u)`,
  the same value.
- `(shape t s)`: `t`'s shape is `s` (`pair`, `nil`, a sum's tag, …), as
  the checkers' `Prop::Shape` says of arguments.
- `(not p)`, `(and p …)`, `(or p …)`, `(implies p q)`.

So the proposition language contains the four fragments the checkers
have (`DONE.md`, the lemmas' `≤`; `Prop`'s latent propositions; `sizes.rs`'s
linear facts; the certifications), in one syntax, and more: disjunction
and implication, which the checkers' facts cannot say (`sizes.rs`'s
comment at `test_facts`).

An **assertion** is a proposition, in practice a conjunction, over the
places of one cell boundary. Two more components of the state are not
propositions, as Hoare logic for effects keeps them apart:
- the **effect so far**: an `Effect`, the union of what the cells run so
  far may have done;
- for a later stage, the **capabilities**: the regions open, as
  Walker, Crary and Morrisett type them (`TODO.md` §21).

## 3. Routines as triples

Each routine is a triple schema over the stack, as Forth's stack
comments are, with the effect beside it:

| routine | pre | post | effect |
| --- | --- | --- | --- |
| `lit x` | | `(: (stack t) T_x)`, `(eq (stack t) x)` | |
| `slot i` | | `(eq (stack t) (slot i))` | |
| `slot! i` | | `(eq (slot i) old(stack t-1))` | |
| `int-add` | `(: a int)`, `(: b int)` | `(: r int)`, `(= r (+ a b))` | |
| `int-less` | `(: a int)`, `(: b int)` | `(: r bool)`, `(iff r (< a b))` | |
| `pair-car` | `(: p (pairof A B R))` | `(: r A)`, `(eq r (car p))` | `(read R)` |
| `field k` | `(: o T)`, `T` has field `k` at `F` | `(: r F)`, `(eq r (field k o))` | per `T` |
| `eq` | | `(: r bool)`, `(iff r (eq a b))` | |
| `0branch` | `(: f bool)` | taken: `(eq f #f)`; not: `(not (eq f #f))` | |
| `tcall n` | `(: c (subr E (P…) Q))`, each `(: x_i P_i)` | `(: r Q)` | `E` |
| `return` | `(: r Q_word)` | (exits) | |

where `a`, `b`, `p`, `o`, `f`, `c`, `x_i` are the terms the stack held, and
`r` the new top. A runtime primitive (`prim p n`) takes its triple from
its FX-26 type in the standard environment.

The post of `int-add` says more than its type: `(= r (+ a b))`. A
verifier that keeps only types forgets it at once; one that keeps
propositions can prove an index in bounds, or a size exact, from it.

**Narrowing is the `0branch` rule.** After `slot 2; field 2; lit 'some;
eq; 0branch L`, the fall-through knows `(not (eq (eq (field 2 (slot 2))
'some) #f))`, so `(eq (tag (slot 2)) 'some)`, so, with `(: (slot 2) (sumof
(some T) (none unit)))`, `(: (field 3 (slot 2)) T)`. That is the checkers'
narrowing (`props_narrow`, `test_facts`), asked of cells, and stated as
what it is: a consequence of a branch condition.

## 4. The certificate

For each word:
- its **signature**: the precondition at entry, `(: (slot i) P_i)` for
  each parameter and `(: (free j) F_j)` for each free value; the
  postcondition at `return`, `(: result Q)`; and its latent effect `E`.
  For a word made from `(lambda …)` of type `(subr E (P…) Q)`, exactly
  that type, with the free values' types beside it;
- an **assertion at each branch target** (each label) that the verifier
  cannot get by the join rule (§5): the JVM's stack map, as propositions;
- **instantiations** where a polymorphic value is called: the types a
  `poly` is used at, given, so the verifier substitutes and need not
  unify.

Everything else the verifier works out going forward. The certificate is
what inference found and checking would otherwise find again.

## 5. The verifier

One pass over a word's cells, in order, computing the strongest
postcondition of each cell from the state before it (a symbolic state:
each place a term, and a set of propositions about the terms).

- **Straight-line code**: apply the routine's triple. Its precondition
  becomes a *verification condition* (VC): `state ⊨ pre`.
- **A branch** to a later cell: the state, with the branch's own fact,
  is held for the target.
- **A target**: the states that reach it (each branch's, and the
  fall-through's) are *joined*. Each place keeps its declared type, from
  where the place was made, which is the same on every way. The
  propositions kept are those every way holds, compared as written: the
  join of `P` and `Q` is weakened to their common conjuncts, never
  computed as a least upper bound, which would be inference. A place made
  on the ways since they parted (an `if`'s value) needs the target's
  certificate assertion, and each way's state must entail it (a VC).
- **A loop** is a backward branch to a word's start (a self tail call
  made a jump): its assertion is the signature's precondition, the loop
  invariant.
- **Exit**: `return`'s VC is `state ⊨ (: result Q)`, and the effect so
  far, its regions private to the word masked, within `E`.

**Discharging VCs.** A VC is an entailment `Γ ⊨ φ`.
- `(: t T)` with `(: t S)` in `Γ`: subtyping, `S ≤ T`, with the
  checkers' `sub`. Structural, no unknowns to solve: the certificate gave
  every instantiation. (Later, `recursive-subtyping.md`'s R10:
  subtyping's own certificates, checked locally.)
- Linear integer propositions: Fourier–Motzkin over the linear facts
  (`sizes.rs`'s `refuted_below`, sound and incomplete).
- Anything else is **open**: written out as a goal, in the syntax above,
  for a prover outside. A word whose open VCs are all discharged is
  verified; one with open VCs is verified *relative to* them, as a
  Hoare-logic proof with lemmas left to prove.

This is the extensibility the user asked for. Today every VC the
compilers' code raises is a type VC, or (from `sizes.rs`) a linear one.
A program that asserts more (§8) raises more, and the same verifier
passes them on.

## 6. What is trusted

The verifier, each routine's triple, each primitive's type, and the
provers that discharge VCs. Not the checkers or the compilers: a wrong
word is refused, not run. Machine code and register code are made from
verified cells, so they are trusted as their compilers are; register
code typed in its own right is later (`directions` §4(c), C12). Beyond
that, only what a loader's policy trusts (§7), and that shows in types.

## 7. Loading under a policy, and trust as an effect

Decided with the user (2026-10-22): the code that loads a fragment says
how its open VCs are handled, and trusting one is an effect.

**When.** Verification runs at load and link time, before anything of
the fragment runs: everything the verifier discharges is settled then,
once, and so is everything that speaks only of what linking fixes (an
import's type in the host against the type the fragment assumed). What
is left open is the policy's to decide.

**The policy** is the loader's argument: a table by kind of VC, or a
procedure given each open VC as data, in §2's syntax. Its answers:
- `proved`: by a prover the caller supplies (an SMT solver, a proof
  database). Unless the prover returns a certificate the verifier checks
  (a proof term; a solver's proof), this is a `trust` (below): the
  prover joins what the program rests on, as a lemma's proof does.
- `guard`: the VC made a check at its cell, run as the code runs, failing
  safely where it does not hold: a *debt* (`TODO.md` §86). Only a VC a
  check can decide on the values at hand: a tag (a pair, `nil`, a sum's
  arm), an integer relation, `eq`. Some guards the machines make already
  (`pair-car` checks the pair's tag); others the loader would insert.
- `contract`: for a VC about behaviour (a closure's type, its effect),
  the value wrapped and each use checked as it happens (Findler and
  Felleisen's higher-order contracts), a violation found late and
  blamed.
- `trust`: the VC assumed.
- `refuse`: the fragment not loaded.
An answer that cannot be had (a `guard` of a VC no check decides, that a
closure ends) is not given: the policy is told, and goes on to its next
rule.

**Trust is an effect.** Every answer but `trust` keeps the program
safe: each checks, or refuses. `trust` gives the load an effect atom,
`(trust A)`, `A` naming what was assumed. So whatever relies on assumed
code says so in its type, as it says what it reads and writes:
- it propagates as any effect does, and masking cannot hide it: nothing
  private makes an unproven assumption hold;
- a licence asks it: the eager reader's (`licence.rs`), run on every
  keystroke, can refuse what was loaded under `trust`;
- a procedure may be **polymorphic in its trust**, `(poly ((t effect))
  (subr (maxeff t …) …))`: a library that loads plug-ins, say, is as
  trusting as the policy its caller gives it, and a caller that gives a
  policy that never trusts gets a procedure whose type has no `trust` in
  it. The policy's own type carries the effect: one that may answer
  `trust` is a `(subr (trust A) (vc) answer)`.

**What may be trusted, and how far it reaches** (decided with the user,
2026-10-22). The policy may trust a fragment (all its open VCs), a
prover (whatever it says it proved), or a VC alone, a semi-local axiom
(Boogie's `assume`, F*'s `admit`, Lean's axioms). These are one thing at
three grains: a set of VCs assumed, each named by its proposition and the
facts it was asked under, hashed, so that `(trust A)` names the set and
the fragment's report holds each in full; one alone can be discharged
later by proof, the rest still assumed.

The grain says *what* is assumed, not how far it reaches. An assumption
is stated at one cell; what follows from it is not kept there: a false
`(: x T)` lets the word store `x` where code that never runs the word,
and whose type says no trust, reads it at `T`. A false assumption can
break memory safety, and then nothing in the process is safe from it.
So the effect is the load's, whatever the grain, and covers what runs
after it: for now, the whole process. Finer grains buy a smaller set to
audit and to prove, not containment.

Containment needs isolation, not bookkeeping: trusted code in a heap of
its own (an FX-26 process: nothing shared, only sendable, first-order
data across, which a guard can check), where `(trust A)` could be masked
at the boundary, the one place masking it is honest. Not planned (the
user: no isolation within a process for now). Tracking a trusted word's
consequences through the regions it writes (taint) was considered and
left: it needs a soundness argument of its own.

**What a fragment reports.** Loaded, a fragment says what it rests on:
each VC discharged, proved (and by whom), guarded, wrapped, or trusted.
A program, or a later link, can look at those assumptions rather than
only inherit them.

**To decide:** whether a later proof can discharge an assumption while
the program runs (a `certify`-like operation, as `certify-nat` refines
a binding today), and how `contract` blame is said.

## 8. Specifications in procedure types

Decided with the user (2026-10-22): propositions come into a program as
preconditions and postconditions on procedure types. Hoare logic for
procedures (Hoare, "Procedures and parameters: an axiomatic approach",
1971), as design by contract and Dafny, Why3 and Boogie have it:

```
(subr E ((x int) (y int)) (r int)
  (requires (< 0 y))
  (ensures (and (<= 0 r) (< r y))))
```

The parameters and the result are named, so that the propositions can
speak of them; otherwise it is the `subr` type it is now.

**The rules.**
- *Body*: a procedure is verified once, assuming its `requires` at entry;
  its `ensures` is a VC at each `return`.
- *Call*: the callee's `requires`, its parameters the arguments, is a VC
  at the call; after it, its `ensures` is assumed, the result named.
- *Tail call*: the callee's `ensures` must entail the caller's.
- *Recursion*: a body is verified assuming its own specification at its
  recursive calls: partial correctness, what holds if it returns. Total
  correctness is termination as well, which FX-26 has as `spin` and the
  size-change check, and `TODO.md` §21 would make checkable (ranking
  functions as certificates).
- *Loops*: FX-26's loops are tail recursion, compiled to a jump back to
  the word's start, so a loop's invariant is its procedure's `requires`.
  No syntax of its own: the jump back is a tail call, and the rule for
  it is Hoare's loop rule.

**Latent propositions become a special case.** Occurrence typing's
`(bool (then P …) (else Q …))` (`logical-types.md`, L1; `Ty::Proving`)
is a postcondition:

```
(ensures (and (implies r (and P …)) (implies (not r) (and Q …))))
```

The checkers' narrowing after a test (`latent_props`, `props_narrow`) is
the call rule (assume the callee's `ensures`, read from its type, not
its name) with the branch rule (each way knows `r` or `(not r)`).
Subtyping one `Proving` under another when it proves at least as much
(`check.rs`'s `sub`) is the covariant half of behavioural subtyping.
`Prop` (`ast.rs`) is already a language of propositions over parameters
(shape, acyclic, nat, length, integer relations on `Param(i)`,
`Length(i)` and literals). What the general form adds:
- postconditions of any result, and of the result itself (`(< x r)`),
  not only of a `bool`'s, about the arguments;
- preconditions;
- connectives and richer terms (§2): implication, disjunction, the
  result, the logic's functions;
- **bodies checked against them.** Today only the standard predicates
  have latent propositions: axioms of the primitives, by L1's stage 1
  (no latent propositions on user procedures, its question 5). A
  program's own `ensures` is a VC to verify of its body.
`(bool (then …) (else …))` stays, as sugar for the `ensures` it means,
and the cells' verifier narrows at `0branch` by the callee's
`ensures`, not by the patterns it knows now (`null?`, a sum's tag).

**What FX-26 must settle.**
1. *Effects are the frame.* Hoare logic must say what a call leaves
   alone (Dafny's `modifies`). FX-26's effects say which regions a call
   may write: a fact about any other region survives the call, as the
   checker already lets facts survive (`kill_paths`). The frame rule,
   nearly for nothing.
2. *Behavioural subtyping.* A procedure is a value and its specification
   is in its type, so a closure carries its contract. One fits where
   another is expected if it requires no more and ensures no less
   (Liskov and Wing): contravariant `requires`, covariant `ensures`.
   Subtyping then raises VCs, implications between propositions, not
   only structure to compare. This is refinement typing (Liquid
   Haskell's) by another road.
3. *State before.* Most FX-26 data is immutable; refs and arrays are
   not. An `ensures` of their contents needs to name what they held at
   entry: Dafny's `old(e)`.
4. *Control effects pass `return` by.* An abort, an escape, a
   continuation resumed leave without the postcondition. Either they
   have their own (JML's `signals`: an `ensures` for each way out), or,
   first, a procedure with a specification may have no control effect.

**What it needs first:** the verifier's state keeping facts (§9's TC5):
each triple's postcondition kept (`(= r (+ a b))`), each branch's
condition, the facts every way in holds kept at a join, linear facts to
Fourier–Motzkin, and the rest open to the loader's policy (§7). The
checker needs the same at source level, to check a body against its
`ensures`.

## 9. Stages

1. **TC1. The certificate, made.** The Rust checker records each
   expression's type; the Rust cellular compiler (`cellular.rs`) gives
   each word its signature and its targets' assertions, in a side table.
   Measure their size against the words'.
2. **TC2. The verifier, for types.** Straight-line code, branches with
   the join rule, `0branch` narrowing of sums, calls by their callee's
   type, `return`. Over the test programs: how many words verify, which
   stop at a routine it does not know, and none refused that the checker
   accepted. Mutation tests: a word changed (a `pair-car` for an
   `int-add`; a slot's number) is refused.
3. **TC3. The idioms and the primitives**: data construction (`lit`
   plus `prim %make-frozen`), every `prim`'s type, effects confirmed.
4. **TC4. Control and regions**: prompts, marks, continuations, private
   regions masked, capabilities (C8).
5. **TC5. Propositions beyond types**: the post of each triple kept
   (`(= r (+ a b))`), linear VCs to Fourier–Motzkin, open VCs written
   out; then programs that state propositions (§8).
6. **TC6. Kept and loaded**: the certificate in the word (`WORD_TYPE`,
   C2), the FX-26 compiler making the same certificates, fragments
   verified on loading (C10), under the loader's policy (§7).

## 10. Where it stands (2026-10-23)

TC1 and the start of TC2, over the Rust compiler (`cellular.rs`) and
checker:
- The checker keeps, with `Checker::record_types`: each expression's type
  (`NodeFacts::types`); each lambda's signature by its body, its free
  variables' types where it is made, narrowings included
  (`NodeFacts::lambdas`); the binders of a polymorphic value's lambda
  (`generalized`); and each call's instantiation of a polymorphic
  operator, binder by binder (`insts`).
- The compiler, with `Compiler::certs`, gives each word its certificate
  (`typed_cells::Cert`): its signature; an assertion `(: (slot d) T)`
  where ways join in an expression whose value goes on; and, at the cell
  that runs a standard operation, its name and instantiation. Each global
  cell's type beside.
- `typed_cells::verify`: the pass of §5. Triples for `lit`, `slot`,
  `slot!`, the stack routines, `free`, `global`, `global!`, `closure`,
  the calls, `return`, `exit`, `branch`, `0branch` (narrowing `null?` and
  a sum's tag), `int-add` and the rest of the typed routines, `eq`,
  `field`, and `prim` and `cons` where the certificate says which
  standard operation they run (checked against the compilers' table).
  Literals are looked at. A `car` of a list that may be `nil` is a debt:
  the machine checks it, failing safely (`TODO.md` §86).

Over the test programs (`tests/typed_cells.rs`), first: 625 of 1,069
words verified, 243 mutants refused. Then, closing the type VCs class by
class (the user: finish the types first): 976 of 1,094 words verify,
discharging 8,758 VCs; 349 mutants of verified words (an `int-add` made a
`pair-car`, and the reverse) are all refused; 37 type VCs fail, each
pinned with its cause. What is left is `TODO.md` §115.

Rules added since, each in `typed_cells.rs`: conversions checked (an
identity word at a type between a representation and its abstract
type); a `letrec`'s placeholders owed and given; nested `poly`s, and a
`plambda`'s value generalized where its cells add no effect; the
checker's instantiations at calls, at values used at an instance, at a
`proj`; data made against the type the certificate names; idioms;
narrowing by a predicate's latent propositions (the call rule with an
`ensures`), by a value tested, by a sum's tag both ways; unreachable
states (a sum with no arm left); control's operations and prompts.

TC2 to TC4 are met for the types (2026-10-23): every one of the 1,109
words of the test programs verifies, no VC failing or left open, 13
relative to named assumptions (the built-in scheduler's procedures at
their forms' types, §7's trust); 437 mutants are all refused; and
`tests/typed_cells.rs` now requires it. Where the checker has a rule the
verifier needs, it is the checker's, shared, not copied: module layout
as data, size facts asked of `nat_arith`, `Checker::renamed` for two
`poly`s, `Checker::blobref_rule` for flat data. The certificate carries
what checking chose freely and the cells cannot show: a new blobref's
flat (`%flat`), a list copy's type (`%copy`), as it carries
instantiations; each is checked, not trusted. What the stage leaves for
TC5: the facts kept are the checkers' (types, sizes, a flat sum's
variant); propositions beyond them are §8's `requires` and `ensures`.

TC5 begun (2026-10-23, the user: "let's attack requires and ensures
next"): §8's specifications, in the Rust checker and the verifier.
- Written `(subr E ((x int) …) Q (requires p) (ensures r q))`, the
  result named in its clause (a result written `(r int)` would read as a
  type applied). Propositions: linear relations of the procedure's `int`s
  and `nat`s (`+`, `-`, `*` by a literal; a product of unknowns opaque),
  its `bool`s, and the connectives.
- The checker carries a specification in the `subr` type and compares
  two by behavioural subtyping (§8, point 2); it proves nothing of a
  body. The certificate carries a word's.
- The verifier (§5) keeps propositions: the `requires` at entry, each
  `0branch`'s condition (an integer test the relation it tested), each
  call's `ensures`, and at a join each way's case for a value made on the
  ways. Its VCs: the `ensures` at each `return`; a callee's `requires` at
  each call; at a tail call, the callee's `ensures` entailing the word's;
  at a loop's jump back, the `requires` of the values passed, and the
  `ensures` of them entailing the word's (Hoare's rule). A callee's
  `ensures` is not assumed after a call that may capture or jump past its
  continuation (point 4, without restricting the language).
- One prover for both (`logic.rs`): the connectives, disjunctions case by
  case, Fourier–Motzkin for each case (the checkers' own, moved there). A
  VC it cannot show is open, written out as an implication in §2's
  syntax.
- `tests/programs/specs`: 19 programs, each verified, left open, or
  refused as its first line says; mutants of specified words (an `int-add`
  made an `int-sub`, and back) all refused.

## 11. Open questions (the user's)

1. ~~**Where propositions come from in a program.**~~ From `requires`
   and `ensures` in procedure types, loop invariants being `requires`
   (§8, decided 2026-10-22). Left: §8's four points, and whether
   `(assert P)` within a body is wanted too.
2. ~~**What an open VC means at run time.**~~ The loader's policy says,
   and trusting is an effect (§7, decided 2026-10-22); what is left of
   it is §7's "to decide".
3. **Which prover outside.** An SMT solver (SMT-LIB 2 is the natural
   form to write VCs in), a proof assistant, or none yet.
4. **The logic's functions.** `car`, `field`, `length`, `+` are partial;
   a term `(car t)` where `t` may be `nil` means what? (The usual
   answers: a total function with an unknown value there, or definedness
   as a proposition.)
