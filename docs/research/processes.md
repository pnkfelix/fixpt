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
   received by a process that keeps receiving. Built (2026-10-14, Q2):
   preemption at fuel polls on every machine, so a process that spins
   for ever starves no other. Each machine's fuel is given out in time
   slices; at a slice's end the runtime decides (`sched::preempt_due`)
   and the machine calls the scheduler's `preempt` where it is: the
   bytecode machine at an instruction boundary, the cellular machines at
   a cell boundary (through a trampoline word, `call 0`, `drop`, `exit`),
   register code at its entry and loops (the registers live pushed, by a
   liveness pass), native code from a frame of the poll's own, mapped as
   a procedure's, and the evaluator written in FX-26 from a poll of its
   own. Preemption made the scheduler's check-then-act sequences races,
   all fixed: a waker given for what was already ready (a message arrived
   between the check and the wait) now runs at once; `race`'s winner
   fills its cell in one step; the first task looks again before it says
   deadlock; and a task is not preempted until its `preempt` has returned,
   nor from its wait's capture until it is resumed, nor again until it
   has had a slice.
8. **`spawn`, `send`, `receive`, `par`, `icell-get` and `icell-put!` are
   forms**, so their names are keywords: one benchmark port's `send`
   became `send-to`. `icell-get` and `icell-put!` were procedures; they
   are forms now so that the waiting one reaches the scheduler.
9. **`self` at the process's place** (2026-10-14). `(self box)` is the
   process's address as `(addr M r)`, `r` its own place, not the region
   the spawner chose for it, which the body cannot name. So it serves
   messages to itself and to processes it spawns, but cannot leave the
   place; a peer elsewhere still learns it from a message
   (`programs/processes/exchange.fx`).
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

## Next: `pselect` and `race` (decided with the user, 2026-10-13)

Two operations async programs reach for, in this order. Together they are
Tokio's `select!`: `pselect` its use over futures that only wait, `race`
its use over futures that compute.

1. **`pselect` over waits** (built; `docs/fx26.md`, "`pselect`"): the
   first of several I-cells to be filled, a message, or a deadline (a
   clock event, built 2026-10-14; the scheduler sleeps until the earliest
   when no task can run). One waker registered with several cells or
   mailboxes, the first to fire winning (a fired flag, so later wakes do
   nothing: `async.md`'s one-shot waker). Its effect is its arms'
   `await`s and `receive`s, and `nondet`: which arm wins is the
   schedule's. Named `pselect` because `select` is a module's component
   in types and effects. Once fired, the waker is taken back from every
   event (`undo`), so no I-cell, mailbox or timer keeps one.
2. **`race`, best effort** (built 2026-10-14; `docs/fx26.md`, "`race`"):
   `(race e1 … en)` gives the value of a branch
   that finished. The contract, which an implementation may strengthen
   but not change:
   - *Value*: some branch's, the implementation's choice, so `nondet`
     (unless every branch gives the same answer).
   - *Losers*: an implementation may stop them at once, at their next
     wait, or never. FX-26's stops each at its next wait, or before it
     starts: a cancelled task ends, its places with it, instead of
     resuming; one that computes without waiting is stopped where it is
     next preempted (Q2), its waker the same. So that no program can tell which, a branch's
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

## H3: copying against sharing (measured 2026-10-14)

`processes-h3.fx`: a process takes messages, each a frozen list of `n`
ints (a list cell is two words), and the first task sends it many; beside
each, what building the list once costs, which is what sharing it would
leave. Nanoseconds per message, on the REPL's machine
(`fx-regs-rsjit-nativecc`), before and after the copier's map stopped
hashing with SipHash (`Heap::copy_within`, `WordHasher`):

| n      | send, SipHash | send, now | build  |
| -----: | ------------: | --------: | -----: |
|      0 |           877 |       867 |      2 |
|      1 |           889 |       875 |      3 |
|     10 |         1,353 |     1,194 |     18 |
|    100 |         5,362 |     3,084 |    200 |
|  1,000 |        48,650 |    21,156 |  1,950 |
| 10,000 |       442,548 |   179,156 | 19,600 |

So a message costs about 0.87 µs whatever its size (a switch to the
receiver and back: "The cost of a switch", below), and about 18 ns a list
cell copied, 9 a word: nine times what building it costs. The two are
equal at about 50 cells. **Decision: copy.** Below a few hundred words
the copy is lost in the switch; above, sharing frozen data would save up
to nine tenths of a large message, but would tie the meaning of a message
to one heap shared by every process, which an implementation with a heap
for each (OS threads, distribution) would not have. Revisit if a client sends messages
of thousands of words often; a size above which frozen data is shared is
then the shape of it.

## The cost of a switch (measured 2026-10-14)

The actors note's A4. A message to a process that waits for it is two
switches: the receiver resumed (its continuation reinstated), and, once
it waits again, suspended (the rest of it captured, and an abort to the
scheduler). `processes-h3.fx` at `n` 0 measures the pair with the
message: 890 ns on the REPL's machine. A profile found a third of it in
the runtime's bookkeeping, not in the switch: each of `%sched`'s
operations interned `#u` and its state's global's name (SipHash, a
string's), and the prompt tag's sum its kind by name. Now the heap finds
such names by where they are kept (`Heap::intern_static`) and hashes the
rest with `WordHasher`, and the kinds are constants: **585 ns**. What is
left is the switch itself: the call-out from native code to the runtime
(a third), and walking and copying native frames to capture and
reinstate (a sixth). One-shot stack segments, a task's own stack switched
to rather than its frames copied, would take most of that; not done.

## What is left

- **The cost of a switch** (the actors note's A4): measured, 585 ns a
  message's two (above); one-shot stack segments if it matters.
- **Links, monitors, supervisors** (F1–F4), session types (P9–P11), and
  distribution (N1–N6), out of scope as asked.
- **Transfer of mutable data**, as kayak suggests, by consuming a whole
  place's handle; after H3.
