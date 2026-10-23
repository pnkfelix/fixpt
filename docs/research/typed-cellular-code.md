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
A program that asserts more (§7) raises more, and the same verifier
passes them on.

## 6. What is trusted

The verifier, each routine's triple, each primitive's type, and the
provers that discharge VCs. Not the checkers or the compilers: a wrong
word is refused, not run. Machine code and register code are made from
verified cells, so they are trusted as their compilers are; register
code typed in its own right is later (`directions` §4(c), C12).

## 7. Stages

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
   verified on loading (C10).

## 8. Where it stands (2026-10-22)

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

Over the test programs (`tests/typed_cells.rs`): 625 of 1,069 words
verify, discharging 6,248 VCs. 243 mutants of verified words (an
`int-add` made a `pair-car`, and the reverse) are all refused. Where the
rest stop is `TODO.md` §115.

## 9. Open questions (the user's)

1. **Where propositions come from in a program.** Today only the checker
   makes them. A program could state them: preconditions and
   postconditions on a `subr` type (`(subr E ((x int)) (r int) (requires
   (< 0 x)) (ensures (< x r)))`), loop invariants, `(assert P)`. Which,
   and in what syntax?
2. **What an open VC means at run time.** Refuse the word? Run it, the
   VC a check made at run time (a "debt", `TODO.md` §86)? Run it, the VC
   trusted, as a lemma is?
3. **Which prover outside.** An SMT solver (SMT-LIB 2 is the natural
   form to write VCs in), a proof assistant, or none yet.
4. **The logic's functions.** `car`, `field`, `length`, `+` are partial;
   a term `(car t)` where `t` may be `nil` means what? (The usual
   answers: a total function with an unknown value there, or definedness
   as a proposition.)
