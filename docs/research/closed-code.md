# Closed code: what a process may hold that shares nothing

Research note for the Kayak team, answering §4 of Kayak's INCR_IMPED.md, "A
procedure of a place may not be held by a process" (2026-11-16). It is a
proposal and nothing in it is built. What works today without it is in the
first section. The test programs in it were run with both checkers.

## What Kayak ran into

A process's body may hold, from outside it, only values that are
*transmissible* (`processes.rs`, `synth_spawn` and `untransmissible`;
FX-26's `check-processes.fx`, `k-spawn-holds`). That covers the globals it
names too. The check judges each value by its type, because a procedure's
type doesn't show what its closure captured. So a procedure is transmissible
only if its parameters and result are, and its latent effect stays within
what a process may do (`crossing_effect`). A place is never transmissible,
so this module maker is refused:

```
(define counter-in (poly ((p place)) (subr (maxeff kfx (alloc p)) ((place p)) (cnt p)))
  (lambda (p) (module (define n (ref i64 p) (new 0)) …)))
…
(spawn (box unit p) (let ((x (counter-in p))) …))
;; its body holds `counter-in`: a (place p)
```

`counter-in` captures nothing. Calling it in the process would be the same as
writing its code there, but its type can't say that.

One could make the type rule more lenient: a place at a region the
procedure's `poly` binds would count as transmissible, as a mailbox at one
already does. We decided against it. The result `(cnt p)` is a module, and a
module's abstract types can hide a captured value, such as a reference into a
place outside the process that may end. Judging a module by its type would
need its own rule for abstract types, and that rule would be another
type-based approximation of something types can't see.

## What works today: load the maker in the process

A module file sees only the standard environment, so it captures nothing.
A load is exempt from the check (`shared_globals`: "the hidden globals of
loads, which are the runtime's"). So a maker written as a module file that
takes a place parameter, and loaded inside the body, is accepted:

```
;; counter.fx
(module-parameters ((p place)))
(define-effect kfx (maxeff (read @globals) spin))
(define n (ref i64 p) (new 0))
(define bump (subr (maxeff kfx (read p) (write p)) (i64) i64)
  (lambda (k) (begin (set n (i64+ k (get n))) (get n))))

;; the program
(spawn (box unit p)
  (let ((x ((proj (load-module "counter.fx") p))))
    (begin (with x (bump 3)) (icell-put! out (with x (bump 4))))))
```

It runs to 7, and `fixpt check` reports "both checkers agree". Defining the
maker inside the spawn's body, with `(the maker (plambda ((q place))
(lambda (q) (module …))))`, works too: the check looks only at the body's
free variables.

For Kayak's expander: give each expander file `(module-parameters ((p
place)))`, so that its state is allocated in `p`. Then each REPL front or
worker loads its own instance into its own place, and nothing is shared
between them. Nothing in Fixpt needs to change for this.

## The proposal: closed globals

What the load exemption relies on is that a load is *closed*: it captures
nothing but the standard environment. Every top-level procedure has the same
property if it names only globals that are themselves safe. Recognising such
procedures directly would let Kayak keep a maker as an ordinary `define`.

**Definition.** A global `g` is *closed* if its definition is a `lambda` or a
`plambda` (under any `the`), and each of its free variables is one of:

- a standard binding,
- a load's hidden global (`shared_globals`),
- a closed global, or
- a global whose value is transmissible by type, as today.

The definition is recursive. Globals defined together by `define*` are closed
when the group is: compute the greatest fixed point over the group, assuming
each member closed and taking back any assumption that fails.

**The rule.** When a spawn's body names a closed global, its type is not
checked for transmissibility. Everything else about the spawn stays as it is.

**Why it is sound.** A process that calls a closed global behaves as if the
procedure's code were written in its body. Each value the call can reach is
of one of four kinds:

1. **Its arguments.** The process supplies them, so they are the process's own
   or already transmissible.
2. **What it allocates.** Allocation is an atom of the call's effect, so it
   becomes part of the body's effect. The spawn already refuses any effect
   outside the process's own place that is not a crossing atom (`process_effect`,
   `crossing_atom`), so `(alloc p)` can only be in the caller's place.
3. **The globals it names.** Reading a global's binding is `(read @globals)`,
   a crossing atom. By the definition, the value read is closed or
   transmissible.
4. **Anything else in the call's effects.** This includes writes to a global's
   reference and sends. These are effects of the body and are checked as such.

This is the argument the load exemption already makes, applied to top-level
definitions. No type-based approximation is involved. The only judgments are
"what the code names" and "what the code does", and the checker already
makes both.

**What it depends on.** A global's binding must not change after it is
defined. If one could be reassigned, a closed global's name could later stand
for a closure that captures state. FX-26 refuses a second definition of a
global ("`clamp` is defined already") and has no assignment to a global's
binding. Before building this, check that no form or session operation (a
REPL entry, a module reload) rebinds a global.

**What it does not cover.**
- **A closed procedure as a value inside the process.** The body may pass it
  around or store it, and it still shares nothing. But a *message* is judged
  by its type, so a closed procedure that takes a place cannot be sent. The
  principled way to send one is a type for closed code, `(static T)`, as in
  Cloud Haskell's static pointers or Erlang's sending of a module, function
  and arity. A worker pool that is sent a job maker would need it. It is not
  proposed here: wait until someone needs to send code rather than name it.
- **Moving state into a process.** Handing a worker an instance already built
  elsewhere needs ownership: a linear or unique place that the sender gives
  up. That is a much larger design, and nothing Kayak reported needs it.

## How it would be built

Both front ends, alike:

- **Rust.** After a top-level group is checked, compute its closed members
  as above and record them in a set beside `shared_globals`. In
  `synth_spawn`, skip a free variable that is in the set, as a load's global
  is skipped now.
- **FX-26.** Keep the same set in the checker's session state. Test it in
  `check-processes.fx` where `k-shared-name?` is tested (the free-variable
  loop around `k-spawn-holds`).
- **Refusals.** When a spawn refuses a global that is not closed, the message
  should say why: "its body holds `g`, which is not closed: it names `n`, a
  (ref i64 @g)". Then a user can see what to factor out.
- **Tests.**
  - Kayak's `process-maker.kfx`: accepted.
  - A closed procedure that returns a global's mutable reference: refused,
    because that global is not transmissible.
  - A pair of mutually recursive `define*` procedures, one of which names a
    mutable global: both refused.
  - The load form in the section above, kept as a regression test.
  - A closed global that allocates at a named outside region (`@w`) when
    called in the body: refused by the body's effect, as today.

Until then, the load form above is what to use.
