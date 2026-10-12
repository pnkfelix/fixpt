# Conditions: a typed way to raise and handle

Design note, 2026-10-12, from a discussion with the user. Research only:
no code of FX-26 was changed. It follows `failure-and-blame.md`, which
sorts failures into values (anticipated outcomes), API-level failures
(broken contracts a layer exports) and panics (invariants violated). The
question here is the middle tier: whether FX-26 should have an exception
or condition system, which kind, and how it would be typed. Sources are
*(from memory)*: none was checked for this note.

## 0. In brief

- **Two kinds of error, not one.** A *panic* (an invariant violated,
  "cannot happen") stays `pure` in types, is never dropped (`TODO.md`
  §85), and is not caught inside the program: today's `error`, and the
  partial primitives (`car` of `nil`). A *raise* is a failure a layer
  exports: typed, a control effect on a region, and handled.
- **FX-26 can already express both designs of the second**, with no new
  machinery: prompts and aborts give escape-only exceptions (design A),
  continuation marks and prompts together give Common Lisp's handlers
  and restarts (design B). Each is written and run below, both checkers
  agreeing and every machine giving the same answers.
- **What strains is the typing's bookkeeping, not its soundness**: a
  raiser must be polymorphic in its handler's region; a prompt tag must
  bound what its body may do though an escape never uses the bound; and
  every operation needs its instantiation written. Each has a remedy,
  section 5.
- **Recommendation: design B, as a standard library with a little
  syntax**, since it subsumes A (a handler that always escapes) and lets
  a policy (retry, substitute, give up) be chosen by the caller without
  the code that raises knowing it. The user's decision, with the
  examples in hand.

## 1. Where this came from

Making `fixpt run`'s exit status (`TODO.md` §84) showed `error` typed
`pure` and dropped as unused on one machine (§85, fixed). The user asked
whether there should be two error procedures, one pure and one with a
control effect, and then whether the better thing is a condition system.
The measurement of `failure-and-blame.md` (section 7) bears on the cost:
`error` is called by 1 definition of the front end and 48 of the
benchmark ports, and an effect on it would reach 0.2% and 5.8% of their
definitions; the front end's own checker already fails by a control
effect, not `error`: `k-sfail` aborts to a prompt, and its effect
`checks` includes `(goto @z)` (`check-types-types.fx`).

## 2. What other languages do

| language    | raise, handle                                     | handler runs             | in types                            |
| ----------- | ------------------------------------------------- | ------------------------ | ----------------------------------- |
| Racket      | `raise`, `with-handlers`; built on marks, prompts | after unwinding (escape) | no                                  |
| Common Lisp | `signal`/`error`, `handler-bind`, `restart-case`  | at the signal, before    | no                                  |
| Standard ML | `raise`, `handle`; `exn` an extensible sum        | after unwinding          | no                                  |
| Java        | `throw`, `try`/`catch`                            | after unwinding          | checked exceptions, no polymorphism |
| Swift 6     | `throw`, `do`/`catch`; typed `throws(E)`          | after unwinding          | yes, and `rethrows`                 |
| Koka        | effect handlers; `exn`, `div`, `total`            | at the operation         | yes, effect rows, inferred          |
| Rust        | `panic!` versus `Result`                          | panics: at a thread      | `Result` only                       |
| Erlang      | crash; supervisors restart                        | a process boundary       | no                                  |

Two lessons. **Java's checked exceptions** became the virality the user
fears, chiefly because generic code could not be polymorphic in what it
throws: lambdas and streams could not carry them. Swift's `rethrows` and
Koka's effect rows are that polymorphism, and FX-26 has it already
(section 4, the second example). **Common Lisp's** handler runs where the
condition is signalled, before anything unwinds; it may decline, return a
value the signaller uses, or invoke a restart, which escapes. Policy is
the caller's, mechanism the callee's. Racket builds its exceptions from
exactly FX-26's parts: a handler in a continuation mark, found by `raise`,
and escape by an abort to a prompt.

## 3. FX-26's parts (`docs/fx26.md`, "Control, typed")

- A prompt tag `(prompt-tag A H D R)`, in region `R`: its prompts deliver
  an `A`, its aborts carry an `H`, its bodies do at most `D` apart from
  control on `R`.
- `abort-current-continuation` has `(goto R)` and returns `void`.
- `(prompt tag body handler)` removes `(goto R)` and `(comefrom R)` from
  the body's effect, when no free variable of the body has a type naming
  `R` but the tag itself: another tag in `R` could be reached past it.
- A mark key `(mark-key T R)` names a place in the dynamic context;
  `with-mark` writes it (`(write R)`), `first-mark` reads it (`(read R)`).
  A private key's marks are masked as a private cell's contents are.

## 4. The examples

In `docs/research/examples/conditions/`, each checked with `fixpt check`
(both checkers agreeing) and run with `fixpt eval` on `rs-scheme-vm`,
native code and the evaluator written in FX-26 (`handlers.fx` on a
cellular machine too), 2026-10-12:

| file                        | design | today's FX-26 says                         | shows                                                   |
| --------------------------- | ------ | ------------------------------------------ | ------------------------------------------------------- |
| `escape-monomorphic.fx`     | A      | refused: `safe-digit` keeps `(goto @fail)` | a raiser fixed to a region cannot be handled            |
| `escape-polymorphic.fx`     | A      | checks; runs, `(7 -1)`                     | a raiser polymorphic in the region is; the handler pure |
| `escape-through-generic.fx` | A      | checks; runs, `(6 -1)`                     | a raise through generic code, its effect inferred       |
| `handlers.fx`               | B      | checks; runs, `(4 6 -1)`                   | a handler at the raise: a value to go on, or a restart  |

**Design A, escape only.** `digit` aborts to a tag it is given. Fixed to a
region, `(goto @fail)`, it cannot be handled: the prompt sees `digit`, a
free variable whose type names `@fail`, and keeps the effect, as it must
(another tag in `@fail` could be the target). Polymorphic in the region,
`(poly ((r region)) (subr (goto r) ((prompt-tag int string D r) char)
int))`, it can: the handler makes a region of its own with `letregion`, a
tag in it, and calls `(proj digit r)`; the body's only free variable
naming `r` is the tag, so the prompt delimits and `safe-digit` is pure but
for reading `digit`. Through `sum-over`, polymorphic in its argument's
effect, the raise's `(goto r)` flows out of the generic call and is
removed by the prompt around it; the checker inferred the instantiation
of `sum-over`'s effect from the lambda given it, with nothing written.

**Design B, handlers at the raise.** `digit` finds a handler in a mark,
`(mark-key (subr e (char) int) k)`, and calls it with the bad character;
its type is polymorphic in the key's region `k` and in the handler's
effect `e`, which its own effect includes: a typed signal. `lenient-sum`
installs a handler that returns 0, so the sum goes on, nothing unwound:
`"1x3"` sums to 4. `strict-sum` installs one that aborts to a prompt
around the whole, a restart: `"1x3"` gives -1. With no handler at all,
`digit` panics (`error`), the default. Both are pure but for reading
globals and `spin`: the key's marks are masked by its `letregion`, the
restart's `(goto r)` by its prompt.

## 5. What strains, and the remedies

1. **The raiser must be polymorphic in the handler's region.** Natural:
   the region names *which* handler, as an effect handler's label does
   (Koka's, from memory); and it is what keeps the masking sound. A
   library makes it routine: raisers take a tag or key whose region is a
   binder, and `handle` makes the region.
2. **A tag must bound its bodies' effect, `D`, though an escape never
   uses it.** `D` exists because a composable continuation returns and
   runs the rest of a body; an escape-only tag has none to capture. In
   the examples it had to be widened to what the bodies do (`(maxeff
   (read (globals …)) spin)`), and `(read @globals)` there leaked out
   through `with-mark`'s instantiation until made precise. Remedies: an
   escape-only kind of tag, whose prompts allow no capture and so need no
   `D`; or a top effect (`PLAN.md`, item 7) for `D` to be, which the
   user has named: should FX-26 get one, it is `yolo` (2026-10-12).
3. **Every operation's instantiation is written.** `(proj (proj
   abort-current-continuation r) int string D)` per abort; implicit
   instantiation found `sum-over`'s, but not the control operations'.
   Remedy: a small syntax, `(handle (r t) body (why expr))` and `(raise t
   v)`, or standard procedures whose types the checker instantiates from
   their arguments.
4. **A restart's key must be made inside the prompt's body**, so that no
   free variable of the body names the tag's region but the tag (the
   key's type names it, through the handler's `(goto r)`). Sugar hides
   the order.
5. **Conditions have one type per tag or key.** Common Lisp's are a
   class hierarchy; ML's `exn` an extensible sum. FX-26's sums and unions
   of shapes could serve (a handler's parameter a union of the condition
   types it takes); not tried here.

## 6. A design that follows

- **Values** for anticipated outcomes in an API, as the I/O primitives
  give `io-error`: the default.
- **Raise and handle, design B**, for failures a layer exports, as a
  standard library: `(handle …)` binding a fresh region, key and tag;
  `(raise key condition)` calling the handler found, whose effect the
  raiser's type carries; restarts as escapes to the handle's prompt;
  design A as the handler that always escapes. Its effect polymorphism is
  what Java lacked; its effects are inferred where instantiation can.
- **Panic** for invariants: `error` as today, `pure`, never dropped,
  ending the run; later caught only at a task or actor boundary
  (`docs/research/async.md`'s nurseries, Erlang's supervisors), never in
  place. The partial primitives' failures are panics, inferred as debts
  (`failure-and-blame.md`), not conditions: making `(car nil)` catchable
  would blur blame.
- **The front end** could move from `k-sfail`'s hand-made abort to the
  library once it exists, its first large user.

## 6a. `yolo` in coopt

coopt (`~/Dev/Rust/coopt`), the asynchronous runtime, gives effects a
run-time form (its R7, `docs/research/effects-scheduling.md`; its
DONE.md, "M9, stage 2" and "stage 3"): an FX-26 effect is lowered to a
descriptor (`coopt-sched/src/effect.rs`: reads, writes and control per
numbered region, `read_all`, `write_all`, and `any`, "assumed to touch
every region"), and `(effect-handle F)` is a run-time handle covering at
least `F`, contravariant in `F`. The top effect fits both with nothing
new:
- **`yolo` lowers to `Effect::any()`**, which interferes with everything
  but `pure`: what "may do anything" must mean to a scheduler.
- **`(effect-handle yolo)` is the handle that covers everything**, and by
  contravariance it stands wherever any handle is wanted; `handle-of`
  gives it the constant `any` descriptor. coopt chose handles over
  evidence passing so that polymorphism stays erased; that is what makes
  `yolo` need no run-time form beyond `any`.
- **Its cost is where it reaches the scheduler.** coopt measured an entry
  beside a loader it does not interfere with answered within 5 of the
  loader's slices, and with either as `any`, 384. Under R7's option (b)
  a loop's tag bound `D` becomes its fibers' descriptor, so a loop whose
  `D` is `yolo` makes every fiber `any`. A condition handler's
  escape-only tag never reaches the scheduler: `yolo` costs nothing as
  its `D`, which is where section 5 wants it.
- **FX-26's `(io k)` atoms** (`TODO.md` §84) have no row in coopt's
  lowering table yet. Under the one ordering rule they all lower to a
  write of one "world" region, so that no two tasks doing I/O
  interleave; `yolo` covers it, as `any` touches every region.

## 6b. The library, built (2026-10-12)

`fx26:conditions.fx` (`crates/fixpt-fx26/src/conditions.fx`), a module
file built in, which a program loads by name, over an escape-only tag
(`(escape-tag A H R)`, no `D`; `docs/fx26.md`, "Control, typed"):

| procedure      | type, in short                                                                    |
| -------------- | --------------------------------------------------------------------------------- |
| `handle`       | `body`, given a fresh region's escape tag (rank 2), and `on-escape`; gives an `a` |
| `with-handler` | `handler`, and `body`, given a fresh region's key whose mark is the handler       |
| `raise`        | the key's handler called with the condition where `raise` is; else a panic        |

A restart is a handler that escapes to a `handle` around the
`with-handler`; the key is then made inside the prompt's body by
construction, so strain 4 of section 5 is gone. The examples of
`handlers.fx`, written with it (`library.fx`, and
`tests/programs/run/conditions.fx`), give `(4 6 -1)` on every machine;
an unhandled raise panics (`unhandled.fx`).

What building it showed:
- **Procedures can make a region**, through rank-2 polymorphism: the
  body is a `plambda` over the region, as Haskell's `runST` is (from
  memory). Both checkers accept a parameter of `poly` type and its
  `proj`.
- **Inference stops at a rank-2 argument.** A `plambda` argument's
  parameters need their types written, and the library procedure's own
  instantiation (`(proj with-handler char int int bodies pure)`) too:
  nothing infers `e` from a polymorphic argument. Syntax, or inference
  into such arguments, would take this away; the user chose procedures
  for now, so it stays visible.
- **Reading globals is bookkeeping** in every signature; `define*`
  infers it for the program's own definitions.

## 7. Questions for the user

1. Decided by the user (2026-10-12): **design B**, handlers at the raise,
   restarts as escapes. R6RS's model (from memory: `with-exception-handler`
   calls its handler where `raise` is, before unwinding;
   `raise-continuable` returns the handler's value; `guard` unwinds, so is
   design A on top of B), with Common Lisp's named restarts, which typed
   prompts give FX-26; R7RS kept R6RS's handlers, and `fixpt`'s Scheme
   implements them (`with-exception-handler`, `raise-continuable`,
   `guard`).
2. Decided (2026-10-12): **standard procedures**, for now.
3. Decided: **an escape-only kind of tag**, which allows no capture and
   so needs no `D`; `yolo` kept for later.
4. The user's answer: **start small**, one condition type per key, and
   find what more is needed by using it.
5. Decided: a panic is caught **only at a task's boundary**, once there
   are tasks; never in place. And `error` stays the panic (`pure`, never
   dropped, ending the run); `raise` is the new, typed one.

Sources, all *(from memory)*: Racket's reference (exceptions,
continuation marks, `with-handlers`); Pitman, *Condition handling in the
Lisp language family* (2001) and the Common Lisp HyperSpec (conditions,
restarts); the Definition of Standard ML (exceptions); Java's checked
exceptions and the difficulty lambdas brought them; Swift's typed
throws (SE-0413, 2024) and `rethrows`; Leijen, Koka (effect handlers,
`exn`, `total`); Rust's `panic!` and `catch_unwind`; Armstrong's thesis,
2003 (supervisors).
