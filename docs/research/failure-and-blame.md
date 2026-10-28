# Failure, proof debt and blame

Design note, 2026-10-12, from a discussion with the user. Research only:
no code was changed. The question: how FX-26 should treat a run that
fails, `(car nil)` and `(error …)` among them; whether "may fail" should
be an effect; and, if it is one, whether it would spread until nothing is
`pure`. Sources marked *(from memory)* were not checked for this note.

## 0. In brief

- **Not every failure belongs in one bucket.** Resource exhaustion is the
  machine's: it depends on the heap, the stack and the compiler, not on
  what the program means. `(car nil)` is the program's: deterministic,
  reproducible, and in principle ruled out by types.
- **Of the program's failures, ask whether the outcome was part of a
  contract.** If it was (a missing file, a closed pipe), it is a value.
  If a contract was broken (`car` given `nil`), it is a **proof debt**
  that was never discharged.
- **A broken contract has a blame site**, and with a sound type system
  there are only two kinds: the consumer that assumed more than the
  producer's type promised, or a trusted assertion that lied.
- **"May fail" then means "carries an undischarged debt".** It is to be
  inferred, not written; written only where a layer promises it away
  (`total`) or exports it as a precondition.
- **The fear that it spreads everywhere is testable** with the checker as
  it is (section 7). Debts a layer owes itself stop at that layer; what
  crosses an API is the caller's preconditions, and FX-26 can already put
  many of those in parameter types.

## 1. Where this came from

Making `fixpt run`'s exit status (`TODO.md` §84) showed the machines
disagree on a failure (`TODO.md` §85):

```
(begin (quotient 1 0) (car (the (listof int @heap) nil)) 3)
rs-scheme-vm:            3
fx-regs-rsjit-nativecc:  ! evaluation failed: division by zero
```

`error`, `car` and `quotient` are typed `pure` (`docs/fx26.md`: "failing
is not an effect"), so the lowering claims the calls `(pure)`, "its
value may be dropped when unused" (`lower.rs`), and the bytecode compiler
under `rs-scheme-vm` drops a non-final `pure` expression of a `begin`
(`crates/fixpt-engine/src/compile.rs`, around line 374). Native code never
drops a call. One proof of `pure`, two behaviours. `pure` is sound for
masking, for reordering reads and for the licence to speculate, but not
as a licence to remove code that may fail: removing it turns "fails" into
"returns 3".

The immediate fix (settled with the user) is narrower than this note:
emit the `(pure)` claim only for code that cannot fail, and perhaps type
`error` as a control effect. This note is about the larger question
behind it.

## 2. Four kinds of failure

The user's list:

- resource exhaustion;
- an internal invariant violated;
- misuse by an end user;
- an exceptional situation arising.

They overlap, especially once there is I/O: exhaustion can make a request
fail, the failure can come back as an empty list where a non-empty one is
usual, and that list can reach `car`. The causal chain runs through every
kind. So the kinds are not where a failure *comes from*; they are where it
*should have been handled*.

## 3. Two questions that sort them

**Is it about the program, or about the machine?** Resource exhaustion
(memory, stack, a step budget) depends on where the program runs. The
same program and input can exhaust on one machine and not another, and no
type system rules it out in general. The other three are about the
program.

**For the program's failures: was the outcome part of the contract, or
was a contract broken?**

- *Part of the contract*: the user's "exceptional situations". A missing
  file, a closed pipe, bytes that are not UTF-8 are anticipated outcomes
  of the domain. They belong in values: `io-error`, `(oneof (data …)
  (failed …))`, `utf8->string`'s `(bad k)`.
- *A contract broken*: an obligation someone was to establish was not.
  `car`'s precondition is "not `nil`"; `quotient`'s is "not zero".

The user's "invariant violation" and "misuse" are one kind seen from the
two sides of a boundary: whose obligation was it? If it was this layer's
own, it is an invariant it failed to keep, a bug here. If it was its
caller's, it is misuse, a bug there. That is blame in Findler and
Felleisen's sense (*Contracts for higher-order functions*, ICFP 2002;
from memory). Misuse by an *end user* is a special case: at the system's
edge, bad input is an anticipated outcome, to be validated into values;
it becomes a broken contract only if it leaks inward unvalidated.

| kind                  | about       | contract               | belongs                                   |
| --------------------- | ----------- | ---------------------- | ----------------------------------------- |
| resource exhaustion   | the machine | none                   | ambient, never in types                   |
| exceptional situation | the program | anticipated            | values (`oneof … (failed …)`)             |
| misuse (by a caller)  | the program | broken: caller's blame | the layer's API, as preconditions         |
| invariant violation   | the program | broken: own blame      | inside the layer, its own debt to vouch   |

## 4. `spin` is the precedent

FX-26 already tracks one semantic non-value outcome in effects:
divergence, as `spin`. Its operational shadow, a stack that overflows,
is left ambient. Failure is the other semantic non-value outcome, and it
is not tracked. If the line between what is tracked and what is ambient
is "semantic or operational", `(car nil)` belongs with `spin`, not with
running out of memory. Koka draws the same line: its effect rows have
`div` and `exn`, `total` below both, all inferred (Leijen, *Koka:
Programming with row-polymorphic effect types*, MSFP 2014; from memory).

## 5. "May fail" as proof debt

Read a failure effect not as an event that happens but as a debt the
code carries: "this relies on a precondition it has not discharged".

- `(car x)` with `x` a `pairof` carries none: since Q7 a `pairof` is
  never `nil`.
- `(car x)` in the branch where `(null? x)` was false carries none: the
  test narrowed `x`.
- `(car x)` with `x` a `listof` and no test carries one.
- `(quotient a 7)` carries none; `(quotient a b)` carries one unless the
  facts in scope show `b` nonzero.
- An index carries one until N5's array bounds can prove it in range
  (`docs/research/gadts.md`, "Stages"); the size facts it would use (`<`,
  `nat`, `nlist` sizes) already exist.
- `(error …)` is a debt stated on purpose: "this cannot happen". Rust's
  `unreachable!` is the same claim.

Integers do not add debts: `int` is a bignum, and the fixed widths wrap.

**Where the debt goes.** A debt is either *owed within* the procedure
(nothing its caller does could discharge it: `car` of a list it built
itself and believes non-empty) or *passed to callers* (it follows from a
parameter: `car` of a `listof` it was given). The first is the layer's
own invariant. The second is a precondition, and the better fix is
usually in the parameter's type: demand a `pairof`, a `nat`, an `nlist`
of a size, and the debt becomes the caller's type error instead of a run
that fails.

## 6. Blame across components

With a sound type system a value always satisfies its static type, so a
`(car nil)` at run time has one of two causes, and each has a site.

1. **The consumer assumed more than the producer promised.** The producer
   said `(listof t)`; the consumer called `car` without narrowing. The
   consumer took the debt and did not discharge it: blame the consumer.
   The fix is there: test, or demand a `pairof` of its own callers.
2. **The producer promised more than it gave.** Its type said non-empty,
   but the value passed somewhere the checker trusts without verifying.
   Blame that assertion. The trusted boundaries are few:
   - the standard operations' own types, which the runtime must keep
     (`standard.rs`; the I/O primitives among them);
   - data from the host: Scheme code calling an `fx:` global, whose
     `datum`s are acyclic by contract only
     (`docs/research/soundness-findings.md`, A3);
   - `error`, the programmer's own claim of unreachability.

   Not `certify-acyclic`, `certify-nat` or `certify-length`: each is
   accepted only on a variable, in the branch where a test has just
   established the fact (`docs/fx26.md`), so each is checked, not
   trusted.

In the user's chain, the exhaustion at the start is nobody's fault. It
was allowed to happen, so long as it surfaced as a value. The fault is
wherever that possibility was first erased: a producer that returned
`nil` for "failed" (conflating two outcomes the I/O primitives keep apart:
`list-dir` gives `(names …)` or `(failed …)`, never an empty list for an
error), or a consumer that took a `listof` for a `pairof`.

**Refusing the link.** A module is checked against the signature it is
linked at, so a consumer whose parameter is a `pairof` cannot be linked to
a producer whose result is a `listof`: the mismatch is refused before any
run. What survives linking is exactly the debts consumers took knowingly,
and the trusted boundaries. Both can be located statically.

## 7. Does it spread? A measurement

The user's instinct: "leave `(car nil)` pure; otherwise the effect will
end up infecting everything." Failure would propagate up the call graph
as `spin` does. But what would spread is debts that cross API boundaries,
and how many those are is a measurable fact about real code. The checker
already knows enough to classify each procedure of the front end written
in FX-26 and of the 42 benchmark ports:

- **failure-free**: every partial operation discharged by types or
  narrowing;
- **internal debt only**: debts owed within the procedure, none from a
  parameter;
- **passes debt to callers**, and through which parameters;
- **states debt** (calls `error`).

With the call graph, the same classification for each procedure's
callers shows how far "may fail" would spread under inference. The
measurement needs no language change and nothing written by anyone.

### Results (2026-10-12)

Measured by `crates/fixpt-fx26/src/debts.rs` (`cargo run --release -p
fixpt-fx26 --example debts`): each definition (a top-level `define`, or a
module's item) of the front end written in FX-26, checked as one program,
and of 94 of the 95 benchmark ports (`mllang-bench/fx`, `scheme-bench`;
`bv2string.fx` does not check, `TODO.md` §88). A definition's debts are
its own; "may fail" spreads to a caller by name, over the call graph.

| class                                           | front end |  ports |
| ----------------------------------------------- | ---------:| ------:|
| definitions                                     |      5549 |   2877 |
| failure-free, and everything it calls           |     62.1% |  52.9% |
| failure-free, but calls a procedure it is given |      0.1% |   3.9% |
| failure-free itself, calls one that may fail    |     29.4% |  26.3% |
| internal debt only (owed)                       |      3.7% |   6.5% |
| passes debt to callers (via a parameter)        |      4.6% |   8.7% |
| states debt (calls `error`)                     |      0.0% |   1.7% |

What it says:
- **"May fail" would not reach everything.** Most definitions stay
  failure-free under inference: 62% of the front end, 53% of the ports.
- **The call graph amplifies.** Only 8% of the front end's definitions,
  and 17% of the ports', have a debt of their own; three times as many
  inherit one by calling. Where the spread comes from is a few sources
  deep in the graph.
- **Types already discharge most of the commonest debt.** Of `car` and
  `cdr`, the front end's 4,685 sites are 84% discharged (a `pairof`, or a
  branch a test narrowed), the ports' 1,697 sites 82%.
- **What is left differs by corpus.** In the front end, `car` and `cdr` of
  a `listof` dominate (770 sites, 471 of them on a parameter): a
  parameter typed `pairof` would move each to its caller's type. In the
  ports, indices dominate (758 sites); were every index proved in bounds
  (N5), the ports' failure-free share would rise from 52.9% to 59.7%,
  the front end's from 62.1% to 64.7%.
- **Stated debt is rare**: one `error` in the front end, 58 in the ports.

Approximations, each toward more debt: a local bound from a parameter is
not followed (its debts count as owed, not passed); a call is linked to
every definition of its name; a call of a procedure given is counted
apart, neither failing nor free.

## 8. A design that follows

1. **Inferred, not written.** The checker infers each expression's and
   procedure's debts. Signatures do not mention them by default, as Rust
   does not mention panics. The compilers may drop or move only code
   inferred debt-free; that alone settles `TODO.md` §85's first item.
2. **Promised where wanted.** A layer that wants totality in its API
   writes it, an assertion such as `total` that the checker verifies;
   callers may rely on it, and a debt from below must then be discharged
   inside the layer. Koka's `total` is the precedent.
3. **Exported as preconditions where a layer cannot discharge them.**
   Preferably in parameter types. Where types are not strong enough, as a
   declared effect at the API: the user's tiers, an effect that is part
   of a layer's interface, beside effects that are internal details.
4. **Abstraction, not masking.** A region is masked because no one
   outside can observe it. A failure is always observable, so a layer
   cannot mask its failures away. It can turn its internal debts into a
   coarser declared effect ("may panic"), or into values at its boundary,
   as `io-error` does. Erlang's "let it crash" is the operational form:
   an invariant violated inside a process is answered by restarting the
   process, not by handling it in place (Armstrong, PhD thesis, 2003;
   from memory). FX-26's actors (`docs/research/actors-and-distribution.md`)
   would be the boundary for that.
5. **Blame reported.** A failure at run time names the site that took the
   debt (the consumer, or the trusted assertion), not only the primitive
   that tripped. A debt is static, so its site can be compiled into the
   failure's message.

## 9. Open questions

- Should `error` be a control effect, `(goto @fail)` on a constant
  region, so a future handler is a prompt that masks it? Or a failure
  atom of its own, beside `spin`, so `goto` keeps one meaning?
- Is a precondition that types cannot state worth an effect at all, or is
  "strengthen the parameter's type" always the better answer once N5
  lands?
- What does `total` promise about resources? Nothing, by section 3; but
  then a `total` procedure can still fail, and the name should say what
  it means ("no debt"), not more.
- Where do the trusted boundaries go as the language grows: a foreign
  function interface, data read from files and parsed into typed
  structures (`confirm`, `docs/research/confirmation.md`)?

Sources, all *(from memory)*: Findler and Felleisen, ICFP 2002
(higher-order contracts, blame); Leijen, MSFP 2014 (Koka's effect rows,
`total`, `exn`, `div`); Peyton Jones, Reid, Hoare, Marlow and Henderson,
*A semantics for imprecise exceptions*, PLDI 1999 (a pure language whose
failing expressions may be reordered); Armstrong, *Making reliable
distributed systems in the presence of software errors*, PhD thesis, 2003
(let it crash).
