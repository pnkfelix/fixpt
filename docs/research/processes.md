# Processes and `par`: the design built for kayak's request

Design note, 2026-10-13. kayak asked for concurrency in FX-26 (`TODO.md`
§92): deterministic `par`, and processes sharing only immutable data, in
three stages (Q1; M1, H1, M3 and I-cells that suspend; P4, P5 and P7),
meaning the same under green threads and OS threads. All three stages are
built. The forms and their types are in `docs/fx26.md`, "Processes and
`par`"; this note says what was decided, where the request was changed,
and what is left. It builds on `actors-and-distribution.md`,
`type-and-effect-directions.md` §3, `async.md` and `places-and-regions.md`.

## What was built

| stage | what                                                                                                                                                   |
| ----- | ------------------------------------------------------------------------------------------------------------------------------------------------------ |
| Q1    | each task has its own stack of places (`fixpt-heap`'s `regions.rs`): a handle is a slot of its own, not a position, so tasks' regions end in any order |
| M1    | `(addr M R)`, `(inbox M r)`; `(send R)`, `(receive R)`; `spawn`, `send`, `receive`, in both checkers                                                   |
| H1    | transmissible types, checked on every free variable of a process's body (globals too) and on its messages                                              |
| M3    | `nondet`, an atom no masking removes; `receive` has it, so does a spawn of a body that receives or does I/O                                            |
| Q3/P6 | I-cells that suspend: a read of an empty cell waits for a task to fill it; with none left, a deadlock, said                                            |
| P4    | `(init R)`, an I-cell's fill, within `(write R)`                                                                                                       |
| P5    | the interference relation, FX's table extended to sends, receives and I/O, tested cell by cell in both checkers                                        |
| P7    | `(par ((x e) …) body …)`, checked for interference, run as tasks; the same answer under twenty orders of the run queue                                 |

The runtime is a scheduler written in FX-26 (`fx26:processes.fx`), over
the prompts and composable continuations every machine has, with a small
Rust part (`fixpt_runtime::sched`: the run queue, mailboxes, I-cells'
waiters, the copy of a message). So it runs every way FX-26 runs: lowered
to Scheme, by the evaluator written in FX-26, as cellular code on each
cellular machine, and natively. kayak allowed a green-thread prototype as
long as the rules it fixes are the ones that hold under OS threads; the
rules below do not mention turns.

## Answers to kayak's questions

### The transmissible-type rule

The request: "a message's type must be transmissible: no region except
address regions, and no `ref`, `icell`, `arrayof`, `prompt-tag`,
`composable` or `mark-key`". Four changes were needed.

1. **I-cells must be transmissible**, or the request's own replies ("a
   request carries an I-cell for its reply") could not be sent. An I-cell
   is a capability, as an address is: sent, it is shared, not copied.
   That is sound only if no process can hold one in memory that is given
   back, so every I-cell is now made in the heap, `rmake-icell`'s too
   (an allocation in a place is only ever an optimization: "either is
   sound"). Under separate heaps, a fill from another process would be a
   message to the cell's home.
2. **Procedures must be transmissible.** A process's body calls global
   procedures, and each is a free variable of the body. A procedure is
   transmissible when its parameters and result are, and its latent effect
   has only what a process may do anywhere: send, fill or await an I-cell,
   I/O, `spin`, `nondet`, read globals' bindings or frozen data, allocate
   at a region that is no place, or anything on a binder of its own
   `poly`. A procedure that touches mutable data shows it in its latent
   effect (FX-26's effects are per region, F2 closed the frozen-data case),
   so this needs no closure inspection. It refuses a closure with an
   effect variable in its latent effect, as the actors note asked.
3. **"No region except address regions" is positional.** A region is
   allowed in an `addr`'s or an `icell`'s region position; in a data
   position only `const` or `acyclic` (frozen in the heap) is: a
   `(listof int const)` is a fine message, a `(listof int @l)` is not.
   `(const p)`, data frozen into a place, is refused: the place ends.
4. **Type variables**: only of kind `data` in the heap (already "what may
   be sent", `generative-types.md` §3), or bound by a `poly` inside the
   type. So a server polymorphic in its message type cannot yet be
   written; a `sendable` kind, `data ≤ sendable ≤ type`, would allow it,
   as Rust's `Send` does. Not built: no program needed it yet.

Free variables are checked, not only messages: a process's body is itself
something that crosses. Globals count as free variables. A process may
read a global's binding, since a binding changes only between top-level
forms, and the scheduler runs every task that can run before a form ends
(below).

### A process's heap, `letreap` and places

`(spawn (box M r) body …)` binds `r` as a place: a reap entered for the
process when it starts and ended when it ends. It is a `letreap` whose
body is the process, with the process's extent rather than a lexical one.
Two things make that sound:
- **Q1.** Each task has its own stack of places, so the process's reap,
  and any `letrena` or `letreap` it opens, end in its own order, whatever
  other tasks do meanwhile.
- **Waiting is not `comefrom`.** A process waits in `receive` or
  `icell-get`, whose effects are `(receive r)` and `(await R)`. A region
  binder refuses `comefrom` because such a continuation may be dropped or
  resumed twice; a waiting task is resumed exactly once, by the scheduler,
  so a process may wait inside its own `letreap`
  (`programs/processes/own-place.fx`). The library's own captures are
  internal: what a program's types show is the wait, not the capture.

Plain `cons` in a process allocates in the collected heap, as it does
anywhere. That is indistinguishable from a heap per process, because
nothing a process can write is reachable by another: the transmissible
rule is what makes per-process heaps a free choice for an implementation.
Messages are copied (`Heap::copy_within`), deeply for data, sharing
I-cells, addresses and procedures. Under separate heaps they would be
copied into the receiver's; here into the heap. The process's reap is
where `rcons r …` allocates, and what it holds dies with the process.

### Should `nondet` appear in a procedure's latent effect?

Yes. `receive`'s type has it, so a procedure that receives says so, and a
`spawn` of a body that does carries it. A procedure that spawns a server
privately is therefore not pure, as finding 2 of the actors note asked.
Two refinements:
- A process that does I/O also makes its spawn `nondet`: its output
  interleaves with others' as the schedule has it.
- A procedure that asks a server it did not make (`send`, then await a
  reply cell) shows no `nondet`. It shows an unmasked `(send R)`, which
  already says it talks to the concurrent world. The invariant: **an
  expression whose effect has neither `nondet` nor a send, receive or
  await on a region outside it gives the same answer every run.**

## Where the request was changed, or pushed back on

1. **"The only nondeterminism should be message arrival order."** Not
   quite, as the user pointed out. There are four sources:
   - arrival order;
   - the interleaving of two processes' I/O (tracked: a process that does
     I/O makes its spawn `nondet`);
   - which of two failures is reported first (not tracked: a failure is
     not a value, the same choice as for the `io` effects);
   - which of two fills of one I-cell from two processes wins (the other
     traps; not tracked).

   What the types promise is the invariant above. Deterministic programs
   in this model exist and keep `pure`: a worker that only computes and
   fills a reply cell receives nothing, so its spawn has no `nondet`;
   `par` is deterministic by construction.
2. **P4 moved into stage 2.** A process that fills a reply's cell must not
   be said to write the region, or no process could reply: `(write R)` is
   not something a process may do outside itself, `(init R)` is.
3. **`par`'s shape.** `(par ((x e) …) body …)`, as `let` binds, rather
   than `(par e1 … en)`, so that the branches' values come back;
   `(par ((_ e1) (_ e2)) #u)` is the statement form. A branch may not
   escape (`goto` or `comefrom` out of it).
4. **When a top-level form ends.** The request did not say. A form ends
   when every task that can run has run (here: the program's own
   computation runs the others when it waits, and after each `spawn`,
   `send` and `icell-put!` it makes). That keeps a definition, which
   assigns a global between forms, from racing a process that reads it.
   Under OS threads this is a barrier at the end of each form. A process
   still waiting then is no error: servers wait for ever.
5. **Deadlock** is the program waiting with nothing left that can run.
   Processes waiting on each other while the program goes on are not
   detected (no more than Erlang does).
6. **Failure.** With links and monitors out of scope, a trap in any
   process fails the form it ran in; the processes are then forgotten
   (the scheduler begins again). Erlang would let an unlinked process die
   alone; that needs F1 and F2 (signals to a top prompt).
7. **Fairness.** The semantics is fair, Clinger's: every message sent is
   received by a process that keeps receiving. The prototype does not
   preempt: a task runs until it waits, ends, or (the program's) sends.
   So a process that spins for ever starves the others, where OS threads
   would not; but its form never ends either way, so the difference shows
   only in I/O made before. Preemption at fuel polls (the actors note's
   Q2) closes it.
8. **`spawn`, `send`, `receive`, `par`, `icell-get` and `icell-put!` are
   forms**, so their names are keywords: one benchmark port's `send`
   became `send-to`. `icell-get` and `icell-put!` were procedures; they
   are forms now so that the waiting one reaches the scheduler.
9. **No `self`.** A process learns its own address from a message (the
   program introduces peers: `programs/processes/exchange.fx`). Binding it
   in `spawn` needs the address's region inside the body, which is the
   spawner's choice; later, with a `sendable` kind.
10. **Two senders, one mailbox**: FIFO per sender (a sender's messages
    arrive in the order sent), any order between senders. The test
    `arrival_order_varies_with_the_schedule` sees both orders.

## How it is built, briefly

- **Forms** are derived, in both parsers (`processes.rs`'s
  `parse_process_form`, `parser-forms.fx`): each a call of a procedure of
  the scheduler's through the hidden global of its load, so no compiler
  and no machine needed a new construct. Each node the expansion makes has
  a place of its own, since the FX-26 compiler finds what its checker says
  of an expression by where it is.
- **Typing** is the checkers': the library's procedures are typed by the
  standard table's `%processes:` entries where the forms name them
  (`library_type`); `spawn` and `par` are rules of their own
  (`synth_spawn`, `synth_par`; `check-processes.fx`). The library and its
  runtime primitive, `%sched`, are visible only to module files built in.
- **Natively**, the library is defined from its text in the program's
  convention: loaded apart it would be cellular code, and a capture in it
  could not cross the call into native code (`built_in_load`); the session
  then tells the FX-26 parser it is made (`syn::set_shared_made`).
- **The evaluator** written in FX-26 runs the library as it runs any
  program, with `%sched` among its primitives and the machines' I-cells.

## Next: `select` and `race` (decided with the user, 2026-10-13)

Two operations async programs reach for, in this order:

1. **`select` over waits**: the first of several I-cells to be filled, or
   a message, or (with a clock event) a deadline. One waker registered
   with several cells or mailboxes, the first to fire winning (a fired
   flag, so later wakes do nothing: `async.md`'s one-shot waker). Its
   effect is its arms' `await`s and `receive`s, and `nondet`: which arm
   wins is the schedule's.
2. **`race`, best effort**: `(race e1 … en)` gives the value of a branch
   that finished. The contract, which an implementation may strengthen
   but not change:
   - *Value*: some branch's, the implementation's choice, so `nondet`
     (unless every branch gives the same answer).
   - *Losers*: an implementation may stop them at once, at their next
     wait, or never (FX-26's first version joins them, so no task
     outlives the form). So that no program can tell which, a branch's
     effect must be **cancellable**: it may read, allocate, await,
     receive, spin, and do anything on regions of its own, but not write,
     fill a visible I-cell, send, or do I/O outside itself. A branch
     stopped half way and one run to its end then look the same.
   - *Termination* is what is best effort: `race` may fail to end if any
     branch does; an implementation that cancels promptly ends whenever
     any branch does. Every program's possible answers are the same under
     both; the stronger one (kayak's, an async runtime whose programs are
     FX-26 programs) only ends more often. The same relation as fairness
     under preemption (Q2).

## What is left

- **H3**: measure copying against sharing, for messages of 1 to 10,000
  words (`fixpt_runtime::sched::words_copied` counts them).
- **Q2**: preemption at fuel polls, for fairness.
- **A `sendable` kind**, for servers polymorphic in their messages; and
  `self`.
- **The cost of a switch** (the actors note's A4): a capture and an abort
  per wait; one-shot stack segments if it matters.
- **Links, monitors, supervisors** (F1–F4), session types (P9–P11), and
  distribution (N1–N6), out of scope as asked.
- **Transfer of mutable data**, as kayak suggests, by consuming a whole
  place's handle; after H3.
