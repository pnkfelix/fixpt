> **Where this stands (2026-09-27).** Since this note was written, regions
> are being split into places (for allocation) and regions (for analysis):
> `docs/research/places-and-regions.md`. Read "a reap owned by a process"
> below as a place with the process's extent, and "transmissible" as
> mentioning no place but `heap` and no region but `const` (frozen data)
> and addresses. Q1 below is that note's per-thread stack of places.

# Actors, Erlang and distribution: inspiration for FX-26's processes

Research note for section 3 of `docs/research/type-and-effect-directions.md`.
No network was used. **Every citation below is from memory** (none of these
papers is in `~/Dev/LangPlay/GiffordHistory/papers/`): authors, titles,
venues and years are as I recall them and should be checked. Claims about
FX-26 are from the repo (`docs/fx26.md`, `PLAN.md`,
`crates/fixpt-heap/src/heap/regions.rs`).

## Two findings first

1. **Green threads and regions do not mix yet.** Regions end newest first:
   "a handle is a position in a stack of live regions, and ending one ends
   any newer" (`regions.rs`, `region_exit`). Interleaved threads break that
   order: A enters `r1`, yields; B enters `r2`, yields; A leaves `r1`, which
   ends B's `r2`. The checker stops the cooperative case today (a yield
   inside a `letrena` body is a `comefrom` on the scheduler's region, which
   the rule forbids). But preemption at a fuel poll is invisible to the
   checker. So per-thread region stacks must come **before** any preemption
   and before "a process owns a reap". This is task Q1.
2. **Actors are nondeterministic, and masking must not hide that.** With
   two senders, a mailbox's arrival order is a choice. That choice is
   Clinger's point, below. A function that uses actors privately is
   deterministic only in the special cases the draft relies on (tree
   topology, one sender per channel). Otherwise its result can differ from
   run to run, and masking would call it `pure`. The fix mirrors `spin`: an
   atom `nondet` with no region, which masking never removes (task M3).

## 1. The Actor model: lineage and what is essential

- **Hewitt, Bishop & Steiger, "A Universal Modular ACTOR Formalism for
  Artificial Intelligence", IJCAI 1973.** Everything is an actor, and
  computation is message passing. Sussman and Steele wrote Scheme in 1975
  to understand actors ("Scheme: An Interpreter for Extended Lambda
  Calculus", MIT AI Memo 349). They found that sequential actors are
  closures and message sends are calls in CPS. So FX-26 inherits the model
  at one remove.
- **Greif, "Semantics of Communicating Parallel Processes", MIT PhD thesis,
  1975.** Behaviours are given as causal orderings of events.
- **Hewitt & Baker, "Laws for Communicating Parallel Processes", IFIP 1977.**
  Axioms on events:
  - each actor's *arrival ordering* is total, so one actor handles one
    message at a time;
  - the *combined ordering* (activation plus arrival) is well-founded, so
    only finitely many events precede any event;
  - creation gives a new actor a fresh address that nobody else knows.
- **Clinger, "Foundations of Actor Semantics", MIT PhD thesis (AI-TR-633),
  1981.** A power-domain semantics. Its central points:
  - Delivery is guaranteed: every message sent is eventually received.
    This is fairness at the level of the model.
  - Guaranteed delivery gives **unbounded nondeterminism**. A counter
    actor that stops on a `stop` message always halts, yet it can return
    any integer. Dijkstra's bounded-nondeterminism models cannot express
    this.
  - Arrival order is where the nondeterminism lives. Sending is
    deterministic; which message arrives first is not.
- **Agha, "Actors: A Model of Concurrent Computation in Distributed Systems",
  MIT Press, 1986** (his 1985 Michigan thesis). It gives three primitives:
  - `create`: a new actor with a behaviour;
  - `send`: asynchronous, to an address;
  - `become`: the behaviour for the *next* message, which makes an actor's
    state a sequence of behaviours with no assignment.

  A *configuration* is the actors, a multiset of messages in transit,
  *receptionists* (actors outsiders may address) and *external actors*
  (addresses of the outside world). Configurations compose. Later, **Agha,
  Mason, Smith & Talcott, "A Foundation for Actor Computation", JFP 1997**
  gave an actor λ-calculus and observational equivalence under fairness.
- **Addresses as capabilities.** You can send only to an address you were
  given, created, or received in a message. That is the object-capability
  rule of Dennis & Van Horn (CACM 1966). Rees's W7 ("A Security Kernel
  Based on the Lambda-Calculus", MIT AI Memo 1564, 1996) showed it for
  Scheme closures.

**Essential:** asynchronous send with no reply implied; per-actor
sequential handling (a total arrival order); addresses as unforgeable
capabilities; `create` with a fresh address; `become`; fairness of
delivery.

**Incidental:** FIFO between a pair of actors (Erlang promises it, the
model does not); blocking or selective receive (Erlang, not Agha); "every
value is an actor"; futures and continuations as actors; the exact message
representation.

## 2. Erlang

These points come from Armstrong's thesis, "Making reliable distributed
systems in the presence of software errors" (KTH, 2003), from Armstrong's
"A History of Erlang" (HOPL III, 2007), and from general knowledge of
BEAM/OTP.

- **Processes and mailboxes.**
  - `spawn` returns a pid, and `Pid ! Msg` is asynchronous and never
    fails, even to a dead pid.
  - `receive` takes the *first* message in the mailbox matching *any*
    clause and leaves the others, optionally with `after T`.
  - Selective receive is what makes a process a state machine with many
    states. Its cost is that a receive scans the whole mailbox, O(n). Since
    about R14 (from memory), a receive on a freshly made `make_ref()` skips
    the messages that were already there, which makes `gen_server:call`'s
    wait for its reply cheap.
- **Links and monitors.**
  - `link` is bidirectional: a process that dies sends an exit signal
    along its links, which kills the other end unless it `trap_exit`s,
    in which case the signal arrives as an `{'EXIT', Pid, Reason}`
    message.
  - `monitor` is one-way and stackable: the watcher gets
    `{'DOWN', Ref, process, Pid, Reason}`.
  - Both work across nodes, and a lost node connection is reported as
    `noconnection`.
- **"Let it crash", supervision and OTP.**
  - Workers do not program defensively. A supervisor restarts them from a
    known state.
  - A supervisor's restart strategy is one of `one_for_one`,
    `one_for_all`, `rest_for_one` or `simple_one_for_one`. Its restart
    intensity is at most MaxR restarts in MaxT seconds, and beyond that
    the supervisor itself dies and escalates.
  - `gen_server` splits a server into generic code (the loop, `call` with
    a monitor, a ref and a 5 s default timeout, and `cast`) and callbacks
    (`init`, `handle_call`, `handle_cast`, `handle_info`, `code_change`).
    A callback returns the next state: Agha's `become`, in effect.
- **Distribution.**
  - Nodes are named `name@host` and found through `epmd` (port 4369).
    They authenticate with a shared *cookie*: a guard against accidents,
    not a security boundary. Once connected, a node has full trust.
  - The default topology is a full mesh (`net_kernel`). `global` offers
    cluster-wide names.
  - A pid carries its node, and `!` is the same locally and remotely: this
    is location transparency.
  - Order is guaranteed only between one pair of processes.
- **Hot code loading.**
  - A module has at most two versions, *current* and *old*. A fully
    qualified call (`?MODULE:loop(S)`) enters the current version, and a
    local call stays in the version it is running.
  - Loading a third version kills the processes still in the oldest.
  - A fun sent to another node travels as its module, an index, the
    module version's checksum and its free variables. It fails with
    `badfun` if the receiver has another version (from memory).
- **Memory.**
  - Each process has its own heap, collected by its own generational
    copying collector. A process's death frees its heap at once.
  - Messages are *copied* into the receiver's heap. The exceptions are
    large binaries (over 64 bytes), which are reference-counted off-heap
    and shared, and the literal area.
  - The design space (private, shared and hybrid heaps, where the hybrid
    has a shared message area found by escape analysis) is measured in
    **Johansson, Sagonas & Wilhelmsson, "Heap Architectures for Concurrent
    Languages using Message Passing", ISMM 2002.**
- **Scheduling: reductions.**
  - A process runs for a budget of reductions: about 2000, or 4000 in
    later releases (from memory). One reduction is roughly one function
    call, and BIFs, GC and I/O charge more.
  - Erlang has no loops, only calls, so counting calls bounds every
    cycle. That is exactly FX-26's fuel poll at word entries and backward
    branches.
  - When the budget is spent, the process is switched out. A receive on a
    mailbox with nothing matching switches it out too.
  - There is one scheduler per core, and they steal work from each other.
- **Weaknesses.**
  - Messages are untyped. Dialyzer (**Lindahl & Sagonas, "Practical Type
    Inference Based on Success Typings", PPDP 2006**) finds only definite
    errors and cannot type a mailbox.
  - Mailboxes are unbounded, with no backpressure, so a slow consumer's
    mailbox grows until memory runs out, and selective receive gets slower
    as it grows.
  - Transparency hides latency and partial failure: a `call` that times
    out may still have taken effect.
  - Cookies are all-or-nothing, and the full mesh does not scale past
    some tens of nodes.
  - **Marlow & Wadler, "A Practical Subtyping System for Erlang", ICFP
    1997**, and later Gleam (below), are the attempts to type Erlang.

## 3. Typed descendants and relatives

- **Akka Typed** (Scala; Roland Kuhn's design, around 2016–2019):
  - An actor is a `Behavior[T]`, and handling a message returns the next
    `Behavior[T]`: `become`, typed.
  - An address is an `ActorRef[T]`, contravariant in `T`.
  - Request/response is a request that carries a `replyTo: ActorRef[R]`,
    the "ask" pattern.
  - Lifecycle events (`Terminated`, `PostStop`) are *signals*, handled
    apart from `T`. The earlier `TypedActor` proxies (RPC-style) were
    abandoned.
  - Background: **Haller & Odersky, "Scala Actors: Unifying Thread-Based
    and Event-Based Programming", TCS 2009**. Its `react` never returns,
    and the closure passed to it *is* the continuation: an event-based
    actor has no stack to save.
- **Pony**:
  - Sources: **Clebsch, Drossopoulou, Blessing & McNeil, "Deny
    Capabilities for Safe, Fast Actors", AGERE 2015**, and **Clebsch et
    al., "Orca: GC and Type System Co-Design for Actor Languages", OOPSLA
    2017**.
  - Reference capabilities are `iso`, `trn`, `ref`, `val`, `box` and
    `tag`. Only `iso` (unique), `val` (deeply immutable) and `tag`
    (address only, no read or write) are *sendable*. So messages are
    passed by pointer with no copy, and the types guarantee there are no
    races.
  - Behaviours (`be`) are asynchronous and run to completion. There is no
    receive and no blocking, so the only deadlock possible is a lack of
    progress.
  - Each actor has its own heap. ORCA counts references between actors,
    so there is no global pause, and actors themselves are collected.
  - Pony has no preemption: a long behaviour holds its scheduler thread.
- **E, and the object-capability model**:
  - Sources: **Miller, "Robust Composition", PhD thesis, Johns Hopkins,
    2006**, and **Miller, Tribble & Shapiro, "Concurrency Among
    Strangers", TGC 2005**.
  - A *vat* is one heap with one event loop. Near references allow
    immediate calls; eventual references allow only `x <- m(args)`, which
    queues the message and returns a *promise* at once.
  - `when (p) -> {…}` reacts to resolution. A promise resolves or is
    *broken*, and a broken promise carries the failure (for example, a
    partition).
  - **Promise pipelining** sends a message to an unresolved promise's
    eventual target, which saves round trips. It comes from **Liskov &
    Shrira, "Promises: Linguistic Support for Efficient Asynchronous
    Procedure Calls in Distributed Systems", PLDI 1988**, and from Joule.
  - A vat never blocks, so there is no lock-style deadlock. Live
    references break on partition and are not silently reconnected;
    persistent "sturdy refs" are separate. The wire protocol is CapTP.
- **Joule** (Tribble, Miller, Hardy & Krieger, Agorics, about 1995):
  channels, everything concurrent, capability security. E's ancestor.
- **Cloud Haskell**:
  - Source: **Epstein, Black & Peyton Jones, "Towards Haskell in the
    Cloud", Haskell Symposium 2011**.
  - It has both Erlang-style mailboxes (`send`/`expect`/`match`) and typed
    channels (`SendPort a`, `ReceivePort a`). A message must be
    `Serializable` (`Binary` + `Typeable`), whose type fingerprint is
    checked on arrival.
  - Code cannot be serialized, so a closure travels as a `static` code
    pointer plus a serialized environment (GHC's `StaticPointers`, 7.10).
    That requires every node to run *the same binary*.
- **Session types**:
  - Binary sessions: **Honda, "Types for Dyadic Interaction", CONCUR
    1993**, and **Honda, Vasconcelos & Kubo, ESOP 1998**.
  - Multiparty sessions: **Honda, Yoshida & Carbone, "Multiparty
    Asynchronous Session Types", POPL 2008** (JACM 2016). A global
    protocol is projected onto local types.
  - Logical foundations: **Caires & Pfenning, CONCUR 2010**, and
    **Wadler, "Propositions as Sessions", ICFP 2012**.
  - For actors:
    - **Mostrous & Vasconcelos, "Session Typing for a Featherweight
      Erlang", COORDINATION 2011**, which uses refs to tag sessions over
      one mailbox;
    - **Neykova & Yoshida, "Multiparty Session Actors", COORDINATION
      2014**;
    - **Fowler, "An Erlang Implementation of Multiparty Session Actors",
      ICE 2016**, which checks at run time.
  - Failure:
    - **Mostrous & Vasconcelos, "Affine Sessions", COORDINATION 2014**;
    - **Fowler, Lindley, Morris & Decova, "Exceptional Asynchronous
      Session Types", POPL 2019**.
  - **Fowler, Lindley & Wadler, "Mixing Metaphors: Actors as Channels and
    Channels as Actors", ECOOP 2017**, translates each model into the
    other. Actors need a sum type over all of a mailbox's messages.
  - **Mailbox types**, closest to Erlang: **de'Liguoro & Padovani,
    "Mailbox Types for Unordered Interactions", ECOOP 2018**, and **Fowler
    et al., "Special Delivery: Programming with Mailbox Types", ICFP
    2023** (the Pat language). These type many-to-one mailboxes with
    selective receive by commutative regular expressions over message
    tags.
- **Gleam** (Louis Pilfold, from about 2019): Hindley–Milner on BEAM.
  - Its `Subject(msg)` pairs a pid with a ref, so each subject is a typed
    channel into one untyped mailbox.
  - Selective receive becomes a `Selector` over subjects.
  - Supervision is ported but typed loosely.
- **Orleans**:
  - Sources: **Bykov et al., "Orleans: Cloud Computing for Everyone",
    SoCC 2011**, and **Bernstein et al., "Orleans: Distributed Virtual
    Actors for Programmability and Scalability", MSR tech report, 2014**.
  - A *virtual actor* (grain) always exists logically. It is activated on
    demand where a directory says, deactivated when idle, and handles one
    turn at a time.
  - Its address is its identity, not its location, so it survives node
    loss.
- **Mozart/Oz**:
  - Sources: **Van Roy & Haridi, "Concepts, Techniques, and Models of
    Computer Programming", MIT Press 2004**, and **Haridi, Van Roy, Brand
    & Schulte, "Programming Languages for Distributed Applications", New
    Generation Computing 1998**.
  - Dataflow variables are single-assignment and suspend on read: FX-26's
    I-cells. Threads over them give *declarative concurrency*, which is
    deterministic. That is the `par`/init/await layer exactly.
  - Distributed Oz is "network-transparent but network-aware": an entity's
    *kind* fixes its distribution protocol.
    - Stateless values are copied.
    - A dataflow variable is bound by a distributed binding protocol.
    - A cell's state migrates (the mobile-state protocol).
    - Ports are many-to-one channels, which are where nondeterminism
      enters.
  - This is the model for letting a value's type decide what crossing a
    node boundary does.
- **Distribution in general.**
  - **Waldo, Wyant, Wollrath & Kendall, "A Note on Distributed
    Computing", Sun Labs SMLI TR-94-29, 1994.** Local and remote differ
    in latency, in memory access (no shared address space, so pointers
    are meaningless), in partial failure and in concurrency. A unified
    object model that hides these is wrong: the difference must show in
    the interface.
  - **The eight Fallacies of Distributed Computing** (Deutsch, about 1994;
    the eighth added by Gosling): the network is reliable, latency is
    zero, bandwidth is infinite, the network is secure, the topology
    doesn't change, there is one administrator, transport cost is zero,
    and the network is homogeneous.
  - **CAP**: Brewer's PODC 2000 keynote, and **Gilbert & Lynch, SIGACT
    News 2002**.
  - **FLP**: **Fischer, Lynch & Paterson, JACM 1985**. In an asynchronous
    system, a slow node cannot be told from a dead one, so timeouts are
    part of the semantics, not an implementation detail.
  - **The end-to-end argument**: **Saltzer, Reed & Clark, ACM TOCS 1984**.
    Reliable delivery below does not give correctness above. Erlang's
    "sends never fail, check replies with monitors" is an end-to-end
    design.

## 4. Mapping onto FX-26

| Idea                      | Where it lands in FX-26                                           |
| ------------------------- | ----------------------------------------------------------------- |
| actor = closure + mailbox | a handler `(subr F (M) beh)`, a recursive type by `define-type`   |
| `become`                  | the handler returns the next handler                              |
| address as capability     | `(addr M R)`: send right only; receive right never leaves         |
| per-process heap          | a reap owned by a process, not in the LIFO region stack           |
| copied message            | a Cheney copy of the message's graph; on the wire, a mini image   |
| reductions                | fuel polls at word entries and backward branches                  |
| `gen_server:call` + ref   | a request carrying a fresh I-cell, the reply awaited              |
| broken promise (E)        | an I-cell that can be *broken*: `await` aborts                    |
| links/monitors            | signals from a process's top prompt, delivered as a separate sum  |
| hot code, two versions    | FX-26's "second define is a new binding" + `become` a new handler |
| dataflow variable (Oz)    | I-cell, unchanged                                                 |
| Cloud Haskell `static`    | closures that carry their types (C1–C12), verified on arrival     |

**Effects of a behaviour.** Keep the draft's single communication effect,
but split it by direction on the mailbox's region:
- `(send R)` goes on `send` to an `(addr M R)`;
- `(receive R)` goes on taking from one's own mailbox.

The receive right is not a value that can be passed around. It is bound
only inside the process body, as a `letreap`'s `(region r)` is, so no one
else can receive from the mailbox. The address is the capability to
send, and it is transmissible.

For `par`'s table, send against send on one region is X unless the
region's mailboxes have one sender each: two branches sending to one
mailbox make its arrival order a choice. Receive masks like `read`. A
function whose effect had `(receive R)` with more than one sender carries
`nondet` after masking (finding 2). Whether a mailbox has one sender is
what session types, or the draft's tree rule, establish, so the
deterministic special case keeps its `pure`.

A behaviour's other effects:
- on its own state region: masked at the process boundary;
- alloc anywhere;
- control: allowed only on tags delimited inside the handler, so an abort
  cannot jump into another thread;
- `spin`: optional. A handler with no `spin` needs no preemption, which is
  Pony's model. A handler that may spin relies on the polls.

**Per-process state as a masked region.** "A process's private heap ≈
`letreap`" is right in the type rule. The body's value and escapes may not
mention the region, and what it does there is masked. It is wrong in the
runtime twice over:
- regions end LIFO (finding 1);
- `letreap` forbids `comefrom` in its masked body, and a process that
  blocks in `receive` or `call` captures up to the scheduler.

The fix is a region form with process extent, `spawn`'s own. Its chunks
already stand alone (`regions.rs`: "each region is chunks of its own"), so
only the handle stack and `REGION_SLOTS`' positional table need to become
per thread. Collecting one reap from "the stacks and the regions nested in
it" becomes collecting from *that thread's* stack: Erlang's per-process GC,
justified by types rather than by copying everything.

**One heap, several heaps, copying.** FX-26 has one semispace heap plus
region chunks, and values are word offsets. Three stages follow:
- *One heap, messages by reference.* Correct only if a message cannot
  carry mutable state into another actor. So the message type must have
  no region in it except address regions.
- *Reap per process, messages copied* (Erlang). Copy the message's graph
  into the receiver's reap, as the collector already copies a reap's live
  objects. Large immutable bloblets could be shared in the common heap,
  like Erlang's refc binaries, since the heap outlives every process.
- *Across OS processes.* A message is a small heap image: a Cheney copy
  from one root, base-relative (PLAN §3.4: "dump = write"). Loading it into
  a *live* heap needs a relocation pass (add a base), which whole images
  never needed. Symbols are sent by name and re-interned. Words (code)
  travel as cells, never machine code, as images already do.

**Transmissible types.** Say that `T` is transmissible when:
- its free region set is empty, or holds only address regions, where
  addresses become remote addresses; and
- it contains no `ref`, `icell`, `arrayof`, `prompt-tag`, `composable` or
  `mark-key`.

That region check comes nearly free. A region in a type *is* a claim
about a store, so a region-free type is location-independent: Waldo's
"pointers are meaningless" becomes a check. Immutable products, sums,
strings, symbols and bloblets are transmissible, and so are lists of
them, since their region is only their allocation site.

A `subr` is transmissible only with closures that carry their types:
- the receiver runs the C-direction verifier over the words (C5–C8);
- it links imports by name and type (C10);
- it renames regions fresh, which is what `private-regions` does.

This is safer than Cloud Haskell's `static` pointers, which need an
identical binary. It is also safer than Erlang's module checksum, which
fails at run time with `badfun`. An effect variable in a sent closure's
latent effect is a hazard, because it may stand for a local region, so
at first sent closures must have closed effects.

**Typed mailboxes first, session types second.** Recommendation: build
`(addr M R)` with `M` a sum type, handler-style `become`, and replies
through I-cells. Reasons:
1. **No linearity needed.** A mailbox address may be copied freely, which
   is the actor norm. Session types need each endpoint used once, which
   FX-26 cannot check yet (the draft's approximations 1–3).
2. **Many-to-one is the common case.** Servers, supervisors and
   registries have many clients. Binary sessions are one-to-one, and
   multiparty sessions fix the participants in advance.
3. **Request/response is already typed.** A request that carries
   `(icell Reply R)` covers `gen_server:call`, Akka's ask and E's
   promises. It needs no selective receive, because the reply never enters
   the mailbox. That removes the case that forced Erlang's ref
   optimisation.
4. **Failure is simpler.** A dead peer breaks one cell. In a session, it
   must be threaded through affine or exceptional session types, which
   is research (Fowler et al. 2019).
5. **Distribution is simpler.** One type fingerprint per address,
   checked at connect, as Cloud Haskell's `Typeable` does. No protocol
   state has to be kept in step across a partition.

Session types remain right for the deterministic layer: private pipelines
of child processes, whose masking to `pure` is their payoff (P9–P11).
Mailbox types (Pat) are the eventual typed answer to selective receive.
Until then, selective receive is a library with a documented O(n) cost.

**Failure.**
- A crash is an abort to the process's top prompt. The scheduler's
  handler turns it into signals to links and monitors. Following Akka,
  signals are delivered to a separate handler, so `M` stays the user's
  type and need not include `down`.
- There is no "may fail" effect for local failure. Every call can trap
  (fuel, memory, a second `icell-put!`), so the atom would be everywhere
  and say nothing: Erlang's premise.
- Failure *is* visible where it can be acted on:
  - a `call` returns `(sumof (ok T) (down reason) (timeout))`;
  - a broken I-cell aborts on `await` to a tag whose region is in the
    type.
- Links, monitors and supervisors are a library over those primitives,
  as in OTP. The language provides the top prompt, the break of a
  cell, and the signal.
- To check: I found no documentation that a runtime error (car of an
  empty list, a second put) reaches an FX-26 prompt. If it does not,
  catching one is a runtime change (F1).

**Distribution.**
- A node is identified by a name plus an incarnation number, so a
  restarted node's addresses are not confused with the old ones. Erlang's
  pids carry a "creation" field for the same reason.
- A remote address is `(addr M R)` whose representation holds the node.
  The type does not change; the effect and the result do.
- `send` to a remote address has `(send R)` like any other. Latency and
  partial failure appear where Waldo wants them:
  - `call` has the sum result above and needs an explicit timeout;
  - sending never fails, which is end-to-end;
  - monitors report `noconnection`.
- A registry maps a name to `(addr M R)` together with `M`'s fingerprint,
  so a lookup at the wrong type fails at connect, not at the first
  message.
- Trust: cookies are not security. For now nodes are the same user's
  processes on one machine, talking over a pipe or socket on localhost.
  Admitting code from another node is exactly the licence question (C11).

**Scheduling.**
- Green threads over composable continuations: a switch is capture, abort
  and resume, about 0.56 µs at depth 20 (`docs/performance.md`).
- Handler-style actors avoid most captures, since a finished handler
  leaves an empty stack and the next turn is a plain call. That is why
  handlers come first. Blocking `receive` and `call` capture.
- Preemption is the fuel poll. When the budget runs out *under a
  scheduler*, the poll's slow path captures to the scheduler's prompt
  instead of raising the step-limit error: Erlang's reductions.
  - This needs R2 (fuel on continuation resume) and R3 (no poll on
    forward branches).
  - It needs the per-thread region stacks (Q1), because the checker does
    not see preemption.
  - Lucassen gave up fairness for `par`. Actors need Clinger's fairness,
    which a FIFO run queue plus preemption provides.

## 5. Tasks (refining P1–P12)

Staged: local actors as a library, then failure, then runtime and types,
then heaps, then nodes. P4, P5, P7, P8 (`init`, interference, `par`,
`par-map`) are kept unchanged as the deterministic layer. P9–P11 (session
types) are kept but moved after M1. P12 is replaced by H1–H3.

**Stage A: local actors, a library in FX-26, no language change.**

1. **A1 (S). Scheduler** (was P1).
   - Changes: `tests/programs/run/threads.fx`, with `spawn`/`yield`/`run`
     over prompts and a FIFO run queue in a `ref`.
   - First step: two threads interleave deterministically.
   - Tests:
     - a `tests/run.rs` case on every machine, under the timeout;
     - a rejection test: a `yield` inside `letrena` is refused, which
       pins finding 1.
   - Deps: none.
2. **A2 (S). Handler-style actors.**
   - Changes: `spawn-actor` takes an initial handler of type `beh`
     (`(define-type beh (subr F (M) beh))`), and `send` enqueues and marks
     the actor runnable. A turn is a plain call, with no capture.
   - Note: the scheduler tag's effect bound `D` must name the mailboxes'
     region, so in the library every mailbox of one scheduler shares one
     region. Per-actor regions need M1.
   - First step: a counter and a ping-pong.
   - Tests: output on every machine, and 10,000 messages with no growth
     of the stack.
   - Deps: A1.
3. **A3 (S). Replies through I-vars** (was P2, extended).
   - Changes: a library ivar in a `ref` of a sum. `call` sends a request
     that carries a fresh ivar and parks on it.
   - First step: a gen_server-style counter with `call` and `cast`.
   - Tests: the deliberate cycle "A calls B while B calls A" gives a
     deadlock error, not a hang.
   - Deps: A2.
4. **A4 (S). Costs** (was P3).
   - Changes: `bench/actors.fx`, measuring a switch, a handler turn and a
     `call` round trip at stack depths 1, 20 and 200.
   - First step: µs per operation, recorded in `docs/performance.md`.
   - Deps: A3.
5. **A5 (S). Erlang-style selective `receive`** as a library.
   - Changes: a mailbox as a list of sums, and `receive` taking a
     predicate, which captures when nothing matches.
   - First step: it gives the same answers as A2.
   - Tests: the cost of scanning against mailbox length, measured to
     confirm O(n).
   - Deps: A4.

**Stage F: failure and supervision.**

6. **F1 (S). Do traps reach prompts?**
   - Changes: none, or a runtime hook that makes an error an abort to a
     designated tag.
   - First step: a test that a second `icell-put!` in a thread is caught
     by the scheduler, on every machine.
   - Deps: A1.
7. **F2 (S–M). Links and monitors.**
   - Changes: each turn runs under the process's top prompt; a crash
     sends `down` signals to monitors, and exits along links.
   - First step: a monitor sees a crash.
   - Tests: link propagation, and `trap-exit`.
   - Deps: F1, A2.
8. **F3 (M). Supervisor.**
   - Changes: the `one-for-one`, `one-for-all` and `rest-for-one`
     strategies, and restart intensity.
   - First step: a worker that crashes on every third message is
     restarted with its initial state.
   - Tests: when intensity is exceeded, the supervisor escalates.
   - Deps: F2.
9. **F4 (S). Broken I-vars.**
   - Changes: an ivar gets a third state, `broken`. A `call` whose server
     dies breaks its reply ivar, and `await` aborts.
   - First step: `call` to a crashed server returns `down`.
   - Deps: F2, A3.

**Stage Q: runtime.**

10. **Q1 (M). Per-thread region stacks.**
    - Changes: region handles become per thread, and `REGION_SLOTS`'
      table is saved and restored at a switch, or indexed per thread.
    - First step: a Rust test in `fixpt-heap` that interleaves two region
      stacks and ends them out of order, with no chunk freed early.
    - Tests: the test under `--features gc-stress`.
    - Deps: none.
11. **Q2 (M). Preemption at fuel polls.**
    - Changes: under a scheduler prompt, the fuel slow path yields
      instead of erroring.
    - First step: two actors that each loop forever both make progress.
    - Tests: fairness, as a count of turns within a factor of each
      other; every machine.
    - Deps: R2, R3, Q1, A1.
12. **Q3 (M). Primitive I-cells that suspend** (was P6).
    - Changes: A3's library ivar is replaced by `icell`, plus F4's
      broken state.
    - Deps: A3, F4, P4.

**Stage M: types.**

13. **M1 (M). `(addr M R)`, `(send R)` and `(receive R)`** in both
    checkers, with `spawn` and a process-extent region.
    - Rules:
      - the body's own region and its receive right are masked;
      - control is delimited inside;
      - Sheldon's rule applies: no hidden mutable region.
    - First step: A2's library retyped, with a message of the wrong type
      rejected.
    - Tests: mutation tests, as `control.rs` has.
    - Deps: A2, Q1.
14. **M2 (S). `send` in the interference table**: send against send is X,
    except for one-sender regions. Deps: P5, M1.
15. **M3 (M). `nondet`**, an atom with no region that masking keeps, set
    by a receive with several senders. The licence reports it, following
    the design of R6.
    - First step: a function that forwards two actors' replies in arrival
      order is not `pure`.
    - Deps: M1, R6.
16. **P9–P11 (M, L, M). Session types**, as in the draft, for
    parent-to-child channels. Deps: M1.

**Stage H: several heaps.**

17. **H1 (S). A transmissible-type check**: region-free apart from
    addresses, and no mutable or control types.
    - First step: unit tests over the standard types.
    - Deps: M1.
18. **H2 (M). A process owns a reap.**
    - Changes: spawn's region becomes a reap, collected from that thread's
      stack alone, and messages are copied into the receiver's reap.
    - First step: a message's words are counted as copied.
    - Tests: a gc-stress run of the A-stage programs; the heap does not
      grow when one actor churns.
    - Deps: Q1, H1.
19. **H3 (S). Measure copy against share** for messages of 1 to 10,000
    words, in `docs/performance.md`, to set the threshold for sharing
    large bloblets. Deps: H2.

**Stage N: nodes (localhost only, never an external network).**

20. **N1 (M). Message images.**
    - Changes: serialize a message's graph as a small base-relative
      image, with symbols by name and a type fingerprint; load it into a
      live heap with relocation.
    - First step: a round trip within one process, equal by structure.
    - Tests: fuzzed truncations are refused (with the C3 checks on any
      words).
    - Deps: H1.
21. **N2 (M). Two `fixpt` processes over a pipe.**
    - Changes: a parent spawns a child `fixpt` with stdin/stdout as the
      link. Node names carry an incarnation, and a remote `addr` has the
      same type.
    - First step: a ping-pong between the processes.
    - Tests: `tests/nodes.rs` under the timeout wrapper, and a
      Unix-domain socket variant.
    - Deps: N1, A2.
22. **N3 (S). Node failure.**
    - Changes: killing the child makes monitors fire with `noconnection`,
      and outstanding `call`s return `down`.
    - Tests: a remote timeout returns `timeout`.
    - Deps: N2, F4.
23. **N4 (S). A typed registry**: a name bound to an address together
    with its type fingerprint.
    - First step: a lookup at the wrong type fails at lookup.
    - Deps: N2.
24. **N5 (L). Sending closures.**
    - Changes: a closure is shipped as a verified fragment, with a closed
      latent effect.
    - First step: a pure `(subr pure (int) int)` sent to a node and run
      there.
    - Tests: a tampered word is refused.
    - Deps: C9–C11, N2.
25. **N6 (M). Upgrading a behaviour.**
    - Changes: an actor receives a new handler at the same type and
      `become`s it: Erlang's two versions, with FX-26's rule that a new
      `define` is a new binding.
    - First step: a counter upgraded while running keeps its count.
    - Deps: N5 for the remote case; local only after M1.

**The first to do:** A1–A4, F1 and Q1. The first five are small and need
no language change. Q1 is a runtime fix that everything later depends on.
