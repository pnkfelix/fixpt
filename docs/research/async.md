# Asynchronous operations for FX-26

Research note, 2026-09-29. Nothing here is implemented. It asks what
Python, Node.js and other dynamic languages offer for asynchronous
operations, and what the equivalent is for FX-26.

**Sources.** The first draft was written from memory. On 2026-09-29, with
the user's leave to read online (read only, nothing installed or run),
every claim about another system was checked against the official
documentation, PEPs, papers or source. Each is cited in "Sources" with
its URL and the version of the documentation read. What the check
changed is listed in "Corrections after checking" at the end. Claims
about FX-26 are from the
repo: `docs/fx26.md`, `docs/research/*.md`, `crates/fixpt-fx26/src/check.rs`,
`crates/fixpt-heap/src/heap/regions.rs`. Larceny's tasking is read from
`~/Dev/LangPlay/larceny/lib/Standard/tasking.sch` and its neighbours.

**Where it sits.** `docs/research/actors-and-distribution.md` (tasks
A1–N6) and section 3 of `docs/research/type-and-effect-directions.md`
(P1–P12) already plan green threads, I-vars and actors. This note is the
layer under them: a scheduler with timers and I/O, structured
concurrency, and cancellation. It refines A1 (scheduler), P2/Q3 (I-vars
that suspend) and Q2 (preemption), and it does not change the actors
plan above A2.

**Examples** (added 2026-09-29). Each main idea has a toy example beside
it, with the snippet from the language the idea comes from. Two kinds are
kept apart:
- **FX-26 today.** Files under `docs/research/examples/async/`, each
  checked with `fixpt check` (both checkers agree) and run with
  `fixpt eval`; the comment after the last form gives the value it
  printed. Excerpts in the text are copied from them. §8 lists them all.
- **Proposed.** Blocks headed `;;; PROPOSED`, using §6.1's operations
  (`with-loop`, `spawn`, `sleep`, …), which do not exist. Not checked.

The Python, JavaScript, OCaml, Rust and Go snippets were written for this
note from the documentation cited in "Sources"; none was run.

## Findings first

1. **FX-26 already has the hard parts.** asyncio and Node build
   suspension out of generators and promises because their languages have
   no first-class control. FX-26 has composable continuations, which give
   *stackful* suspension, and I-cells, which are promises. Its continuation
   marks already travel with a captured continuation, so they give task-local
   context (`contextvars`, `AsyncLocalStorage`). What is missing is a
   scheduler, a reactor for timers and I/O, and the typing of scopes.
2. **Suspension is already typed.** A task that suspends captures up to
   its loop's prompt: `(comefrom c)` on the loop's region `c`, and
   `(goto c)` when cancellation aborts it. No new effect is needed for a
   first design. "Function colour" becomes an effect in the latent
   effect, not a second compilation of the code: effect-polymorphic
   `map` works for both, and masking at the loop's scope is `asyncio.run`.
3. **Structured concurrency is the region discipline.** A nursery is a
   region: its tasks' handles mention it, so none leaves it, and it
   returns only when they have all ended. A loop inside a `letrena` may
   use the arena from every task, and this is accepted by the checker as
   it stands.
4. **A task cannot suspend inside its own `letrena` or `letreap` today,
   and must not.** `close_region` (`check.rs`) refuses a body whose
   masked effect keeps a `comefrom`, and at run time an abort to the
   loop's prompt would end the arena. This is finding 1 of the actors
   note seen from the other side. Lifting it needs per-task place stacks
   (Q1) and a one-shot suspension effect distinct from `comefrom` (§3.6).
5. **Two things to check before building.**
   - Whether a continuation can be captured across a nested run (native
     code calling cellular code calling native code has a Rust frame
     between the runs). This is Lua's "attempt to yield across a C-call
     boundary".
   - K26's `(Region)` rule as printed (`soundness.md` §2.4) says "no
     `comefrom r` ∈ φ"; the checker masks *before* it looks, so a
     `comefrom` on the region being closed is removed and allowed.
     §2.6 says K26's `priv` allows it. The loop's scope (§3.1) relies on
     the checker's reading, so the two should be reconciled first.

## 1. Survey

### 1.1 Python: asyncio, and the generators under it

**Substrate.** Generators became coroutines in steps:
- PEP 342 (created 2005, Python 2.5), "Coroutines via Enhanced
  Generators": `yield` is an expression; `gen.send(v)`, `gen.throw(…)`,
  `gen.close()`.
- PEP 380 (2009, Python 3.3), "Syntax for Delegating to a Subgenerator":
  `yield from sub`, so a chain of generator frames acts as one coroutine.
- PEP 3156 (2012, Python 3.3), "Asynchronous IO Support Rebooted: the
  'asyncio' Module": a pluggable event loop, transports and protocols,
  and a scheduler based on `yield from`.
- PEP 492 (2015, Python 3.5): `async def`, `await`, native coroutine
  objects, `async with`, `async for`, `__await__`. "Coroutines are based
  on generators internally, thus they share the implementation."
- PEP 525 (2016, Python 3.6): asynchronous generators, with `asend()`,
  `athrow()`, `aclose()`; PEP 530: asynchronous comprehensions.
- PEP 567 (2017, Python 3.7): `contextvars`; "Tasks in asyncio need to
  maintain their own context that they inherit from the point they were
  created at". PEP 654 (2021, Python 3.11): `ExceptionGroup`,
  `BaseExceptionGroup` and `except*`, which `TaskGroup` needs.

A coroutine is **stackless**: each `async def` frame is a heap object, and
`await` suspends the whole chain of frames by returning up through each
`__await__`. A Task drives a coroutine by calling `coro.send(None)`. When
the chain yields a Future, the Task adds a done-callback to it that
schedules the next `send`.

The whole of asyncio in one toy, the one §2 builds in FX-26: two tasks
take turns, each giving the loop back with `sleep(0)`.

```python
import asyncio
log = []

async def pinger(who, n):
    for i in range(n, 0, -1):
        log.append(who + i)
        await asyncio.sleep(0)            # yield to the loop

async def main():
    async with asyncio.TaskGroup() as tg:
        tg.create_task(pinger(100, 3))
        tg.create_task(pinger(200, 3))

asyncio.run(main())                       # log: [103, 203, 102, 202, 101, 201]
```

**The loop.** `asyncio.run(main())` makes a loop, runs `main` to the end,
and cancels whatever is left. Callbacks go in with `loop.call_soon`,
`call_later` and `call_at`. I/O readiness comes from `selectors`
(kqueue on macOS, epoll on Linux); Windows uses the proactor loop over
IOCP. `loop.add_reader`/`add_writer` expose readiness; `run_in_executor`
runs a function on a thread pool.

| API                                                              | Semantics                                                                                                                                                                                                                                                                       |
| ---------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `asyncio.create_task(coro, name=, context=)`                     | Schedule a coroutine as a Task (`context=` since 3.11). "The event loop only keeps weak references to tasks", so a Task nobody holds can disappear mid-run: the documented pitfall of unstructured spawn.                                                                       |
| `asyncio.Future`, `loop.create_future()`                         | A one-shot result cell: `set_result`, `set_exception`, `add_done_callback`, `cancel`.                                                                                                                                                                                           |
| `asyncio.gather(*aws, return_exceptions=False)`                  | Await all, in order. The first exception propagates, and the others "won't be cancelled and will continue to run"; cancelling the `gather` cancels them all.                                                                                                                    |
| `asyncio.wait(aws, timeout=, return_when=)`                      | Returns `(done, pending)`; `FIRST_COMPLETED`, `FIRST_EXCEPTION`, `ALL_COMPLETED`. Cancels nothing, not on timeout and not when `wait` itself is cancelled.                                                                                                                      |
| `asyncio.TaskGroup()` (3.11)                                     | `async with asyncio.TaskGroup() as tg: tg.create_task(...)`. Exit waits for all; the first failure other than `CancelledError` cancels the rest; the failures are raised together as an `ExceptionGroup` or `BaseExceptionGroup`.                                               |
| `task.cancel(msg=)`                                              | Throws `CancelledError` into the coroutine at its next `await`: *edge-triggered*, once. `msg` since 3.9; `CancelledError` a `BaseException` since 3.8; `Task.cancelling()`/`uncancel()` since 3.11, and since 3.13 `uncancel()` to zero rescinds pending cancellation requests. |
| `asyncio.timeout(delay)`, `timeout_at` (3.11), `wait_for(aw, t)` | Cancel what is inside after a deadline, turning its `CancelledError` into the builtin `TimeoutError` (`wait_for` too, since 3.11). `asyncio.shield(aw)` protects an inner awaitable from an outer cancel.                                                                       |
| `asyncio.to_thread(f, *args)` (3.9)                              | Run a blocking function in a separate thread; "the current `contextvars.Context` is propagated" to it.                                                                                                                                                                          |
| `asyncio.open_connection`, `start_server`                        | Streams: `StreamReader.read`/`readline`/`readexactly`; `StreamWriter.write` then `await writer.drain()` for backpressure; `close()`, `await wait_closed()`.                                                                                                                     |
| `asyncio.Lock`, `Event`, `Condition`, `Semaphore`, `Queue`       | Synchronization without threads; `Queue(maxsize)` gives backpressure.                                                                                                                                                                                                           |
| `contextvars.ContextVar`, `copy_context()`                       | Dynamic binding. Each Task runs in a *copy* of the context current when it was created, so writes in a child do not leak to the parent.                                                                                                                                         |
| `asyncio.sleep(0)`                                               | The idiom for "yield to the loop".                                                                                                                                                                                                                                              |
| `asyncio.eager_task_factory` (3.12)                              | Eager tasks: the coroutine starts running synchronously in `create_task`, and is scheduled on the loop only if it blocks.                                                                                                                                                       |

**trio and anyio.** Nathaniel J. Smith's trio (2017) made structured
concurrency the only way to spawn:
- `async with trio.open_nursery() as nursery: nursery.start_soon(f, x)`.
  The block does not exit until every child has ended. A child's
  exception cancels its siblings and the body, and propagates. Since trio
  0.25.0 (2024-03-17) `strict_exception_groups` defaults to `True`: "nurseries
  will always wrap even a single raised exception in an exception group".
  `await nursery.start(f)` waits until the child calls
  `task_status.started(v)`.
- **Cancel scopes**: `with trio.CancelScope() as cs:`, `cs.cancel()`,
  `trio.move_on_after(t)`, `move_on_at`, `fail_after` and `fail_at` (raise
  `TooSlowError`), and `cs.shield = True`. Cancellation is
  **level-triggered**: "once a block has been cancelled, *all* cancellable
  operations in that block will keep raising `Cancelled`". A checkpoint is
  both a point where trio checks for cancellation and one where the
  scheduler may switch; trio's own async functions are checkpoints.
- `trio.open_memory_channel(max_buffer_size)` gives a send and a receive
  channel, with backpressure and `aclose` (channels are not closed by
  the garbage collector).
- `trio.testing.MockClock` (with `autojump_threshold`) makes timeouts
  deterministic in tests.

anyio puts the same API (`anyio.create_task_group()`, `tg.start_soon`,
`anyio.CancelScope`, `move_on_after`, `fail_after`) over either an asyncio
or a trio backend. asyncio's `TaskGroup` (3.11) and `timeout` (3.11)
have the same shape as trio's nursery and `move_on_after`.

### 1.2 Node.js: libuv, callbacks, promises

**The loop** (Node's guide "The Node.js Event Loop, Timers, and
`process.nextTick()`"). libuv runs phases in order:

| Phase             | Runs                                                                              |
| ----------------- | --------------------------------------------------------------------------------- |
| timers            | expired `setTimeout`/`setInterval` callbacks                                      |
| pending callbacks | some system errors deferred from the last iteration                               |
| idle, prepare     | internal                                                                          |
| poll              | waits for I/O (epoll, kqueue, IOCP), runs I/O callbacks; blocks when nothing else |
| check             | `setImmediate` callbacks                                                          |
| close callbacks   | `'close'` events                                                                  |

`process.nextTick` "is not technically part of the event loop": the
next-tick queue is processed "after the current operation is completed,
regardless of the current phase". "Every time the 'next tick queue' is
drained, the microtask queue is drained immediately after" (promise
reactions, `queueMicrotask`), so in CommonJS ticks run before promise
reactions; in an ES module, whose body already runs as a microtask, the
order is the other way round. Since Node 11.0.0 (nodejs/node PR #22842,
"timers: run nextTicks after each immediate and timer") both queues drain
after *each* timer and immediate callback, as browsers do, not after the
whole batch. So a promise chain runs to completion before the next
callback, and a recursive `nextTick` starves the loop. libuv's thread
pool ("default size is 4", `UV_THREADPOOL_SIZE`, at most 1024) runs "all
file system operations, as well as getaddrinfo and getnameinfo
requests", and whatever is queued with `uv_queue_work`; completions come
back as callbacks.

| API                                                             | Semantics                                                                                                                                                                                                                                                                           |
| --------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| error-first callbacks `(err, result) => …`                      | The original style. `util.promisify` converts.                                                                                                                                                                                                                                      |
| `Promise`, `.then`, `.catch`, `.finally`                        | Promises/A+; reactions are microtasks. `--unhandled-rejections=throw` is the default since Node 15.0.0: an unhandled rejection is raised as an uncaught exception.                                                                                                                  |
| `Promise.all`, `allSettled`, `race`, `any`                      | Combinators; `any` rejects with `AggregateError`. None cancels the losers: a promise is not cancellable.                                                                                                                                                                            |
| `async function`, `await` (ES2017)                              | Sugar over promises: stackless, each `await` a microtask. `for await` and async generators (ES2018).                                                                                                                                                                                |
| `setTimeout`, `setInterval`, `setImmediate`, `process.nextTick` | Timers phase, check phase, and the tick queue ahead of promises.                                                                                                                                                                                                                    |
| streams: `Readable`, `Writable`, `Duplex`, `Transform`          | Backpressure: `write()` returns `false`, wait for `'drain'`; `stream.pipeline()`; `stream/promises`; a `Readable` is an async iterable.                                                                                                                                             |
| `worker_threads`: `Worker`, `parentPort`, `MessageChannel`      | Separate isolates, each with its own loop; `postMessage` copies by structured clone, with a transfer list; `SharedArrayBuffer` and `Atomics` share memory.                                                                                                                          |
| `AbortController`, `AbortSignal`                                | `controller.abort([reason])` (v15.0.0; `reason` v17.2.0); `signal.aborted`, `signal.reason`, `throwIfAborted()` (v17.3.0); `AbortSignal.abort()`, `AbortSignal.timeout(delay)` (v17.3.0), `AbortSignal.any(signals)` (v20.3.0). APIs take `{ signal }`: cancellation by convention. |
| `AsyncLocalStorage` (`node:async_hooks`)                        | Stable since v16.4.0. `als.run(store, callback)`: "the store is accessible to any asynchronous operations created within the callback"; `als.getStore()`. The TC39 proposal `AsyncContext` (stage 2: `AsyncContext.Variable`, `AsyncContext.Snapshot`) would standardize it.        |

JavaScript generators (`function*`, `yield`, `next(v)`, `throw(e)`,
`return(v)`) came first; libraries such as `co` drove them with promises
to get async/await before ES2017. In miniature, a generator, and the same
suspension written as `await` on a promise, whose rest runs as a
microtask:

```js
function* countUp(i, n) { while (i <= n) yield i++; }
let s = 0; for (const v of countUp(1, 4)) s += v;      // s === 10

const fut = new Promise(resolve => setTimeout(() => resolve(42), 0));
async function consumer() { log.push(1); log.push(await fut); }
```

§2's `generator.fx` and §2's `promise.fx` are the FX-26 versions of these
two.

### 1.3 Others

| System                               | Unit                                                                                                              | Suspension                                                                                                                                                       | Composition and cancellation                                                                                                                                                                                                                                                           | I/O                                                                                                                                                                                         |
| ------------------------------------ | ----------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Racket 9.3                           | `thread`: "one thread can preempt another without its cooperation"; since 8.18.0.2, `#:pool` for parallel threads | stackful userspace threads, events "based on Concurrent ML" (Racket CS paper)                                                                                    | events: `sync`, `sync/timeout`, `choice-evt`, `wrap-evt`, `handle-evt`, `guard-evt`, `nack-guard-evt`, `poll-guard-evt`, `replace-evt`, `alarm-evt`; `kill-thread`, `break-thread`, `thread-dead-evt`                                                                                  | ports are events; a custodian manages "threads, file-stream ports, TCP ports, TCP listeners, UDP sockets, byte converters, and places"                                                      |
| CML (Reppy)                          | `spawn`ed threads                                                                                                 | stackful, on SML/NJ's first-class continuations                                                                                                                  | first-class events: `sendEvt : 'a chan * 'a -> unit event`, `recvEvt`, `choose`, `wrap`, `wrapHandler`, `guard`, `withNack : (unit event -> 'a event) -> 'a event`, `sync`, `select`, `timeOutEvt`, `atTimeEvt`                                                                        | through events                                                                                                                                                                              |
| Guile Fibers 1.3.1 (Wingo)           | `spawn-fiber` under `run-fibers`                                                                                  | "a fiber is a delimited continuation"; it runs within a prompt and suspends to it (`suspend-current-task`, an `abort-to-prompt`)                                 | CML operations: `put-operation`, `get-operation`, `choice-operation`, `wrap-operation`, `sleep-operation`, `timer-operation`, `perform-operation`, `make-base-operation`; conditions                                                                                                   | epoll (or libevent); suspendable ports (`current-read-waiter`); one scheduler per core by default, with work stealing                                                                       |
| Gambit / Termite                     | Gambit's own threads (not OS threads), `thread-quantum-set!`; Termite processes                                   | stackful; Termite can serialize a process's continuation                                                                                                         | `thread-send`, `thread-receive`, `thread-mailbox-next`, `thread-mailbox-rewind`; Termite's Erlang-style `!`, `?`, `recv`, links                                                                                                                                                        | Gambit's scheduler polls                                                                                                                                                                    |
| Erlang/BEAM (OTP 29)                 | process, own heap and mailbox                                                                                     | preempted after a reduction budget (`erlang:bump_reductions/1`, `erlang:yield/0`)                                                                                | `receive … after`, `spawn`, `link`, `monitor`, `exit`, `process_flag(trap_exit, true)`; covered in the actors note                                                                                                                                                                     | ports, NIFs, dirty schedulers                                                                                                                                                               |
| Lua 5.4                              | `coroutine.create`                                                                                                | asymmetric, stackful: `resume`, `yield`, `wrap`, `status`, `running`, `close`                                                                                    | none built in; `coroutine.isyieldable`                                                                                                                                                                                                                                                 | libraries; "Lua raises an error whenever it tries to yield across an API call, except for three functions: `lua_yieldk`, `lua_callk`, and `lua_pcallk`", which take a continuation function |
| OCaml Lwt 6.1.0                      | promise `'a Lwt.t`                                                                                                | monadic: `Lwt.bind`, `let*`                                                                                                                                      | `Lwt.join`; `Lwt.pick` "tries to cancel all other promises that are still pending"; `Lwt.choose` cancels nothing; `Lwt.cancel`; `Lwt.wait` gives promise and resolver                                                                                                                  | `Lwt_unix`; `Lwt_preemptive.detach` to threads                                                                                                                                              |
| Jane Street Async                    | `'a Deferred.t`, filled through an `Ivar.t`                                                                       | monadic, `upon`, `>>=`                                                                                                                                           | no cancellation of a deferred: an `interrupt` deferred is passed by convention, and `choose` runs only the chosen branch; errors through monitors, "arranged in a tree"                                                                                                                | cooperative on one thread; `In_thread.run` for blocking work                                                                                                                                |
| OCaml 5.3, Eio 1.6                   | fiber: "runtime-managed, dynamically growing segments of stack"                                                   | effect handlers; continuations resumed "exactly once" (else `Continuation_already_resumed`)                                                                      | `Eio.Switch.run`, `Fiber.fork ~sw`, `Fiber.both`, `Fiber.all`, `Fiber.first`, `Fiber.any`, `Eio.Cancel`, `Eio.Promise`, `Eio.Stream`; a switch also "releases any attached resources (e.g. closing all attached file handles)"                                                         | `eio_linux` (io_uring), `eio_posix`, `eio_windows`; capabilities from `env` (`Eio.Stdenv.net env`)                                                                                          |
| Kotlin                               | coroutine, `Job`                                                                                                  | stackless: `suspend fun await(): T` compiles to `fun await(continuation: Continuation<T>): Any?`, one state machine per suspending lambda, `COROUTINE_SUSPENDED` | `coroutineScope`, `supervisorScope`, `launch`, `async`/`await`, `withTimeout` (`TimeoutCancellationException`), `withTimeoutOrNull`, `NonCancellable`; cancellation cooperative, checked by kotlinx.coroutines' suspending functions, `ensureActive()`, `yield()`                      | `withContext(Dispatchers.IO)`                                                                                                                                                               |
| Go                                   | goroutine                                                                                                         | stackful; contiguous stacks, moved when they grow (since 1.3); asynchronously preemptible (since 1.14, by signals)                                               | channels, `select`, `sync.WaitGroup`, `context.Context` (`WithCancel`, `WithTimeout`, `Done()`), `errgroup.Group` (`WithContext` cancels on the first error; `SetLimit`)                                                                                                               | netpoller in the scheduler, invisible to code                                                                                                                                               |
| Rust 1.98, tokio 1.53                | `Future`, polled; "futures alone are inert"                                                                       | stackless state machines; `Pin`                                                                                                                                  | `fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>`; a pending future stores a clone of the `Waker`, and `Waker::wake` has it polled again; cancellation is `drop`; tokio `spawn`, `JoinSet`, `select!` ("cancelling the remaining branches"), `time::timeout` | tokio over mio (epoll, kqueue)                                                                                                                                                              |
| Koka                                 | effect handlers with typed effect rows                                                                            | asynchrony as a library of effect handlers                                                                                                                       | Leijen, "Structured Asynchrony with Algebraic Effects" (TyDe 2017): "block-scoped interleaving, cancellation, and timeouts", and "ambient state" local to a strand                                                                                                                     | libuv                                                                                                                                                                                       |
| Larceny (`lib/Standard/tasking.sch`) | `spawn` under `with-tasking`                                                                                      | full `call/cc`; timer interrupt preempts every 5000 ticks                                                                                                        | `yield`, `block`, `unblock`, `kill`, `without-interrupts`                                                                                                                                                                                                                              | `tasking-with-io.sch` polls with `poll(2)` when idle                                                                                                                                        |

Points worth taking from them:
- **Rust**: stackless because there is no runtime and no GC. A future is a
  value of known size, `await` allocates nothing, and borrowing across an
  `await` needs `Pin`. RFC 230, "Remove runtime" (2014), moved `libgreen`
  out of the standard library, citing forced co-evolution of the two
  models, overhead, and poor interoperation. Dropping a future cancels it
  at any `await`, which gives "cancellation safety" bugs. withoutboats'
  "The Scoped Task trilemma" (2023): of concurrency, parallelizability
  and borrowing, a scoped task API can have two, because "every object in
  Rust can be leaked without running its destructor".
- **Go** moved from segmented to contiguous stacks in 1.3: the stack "is
  transferred to a larger single block of memory", which "eliminates the
  old 'hot spot' problem when a calculation repeatedly steps across a
  segment boundary". Rust announced that it was abandoning segmented
  stacks in 2013 (Brian Anderson, rust-dev). The same problem is usually
  given as the reason and called the "hot split", but that post was not
  reachable to check. Moving a stack needs every pointer into it to be
  found.
- **OCaml 5**: "the program stack in OCaml is a linked list of such
  fibers"; "capturing a continuation does not involve copying stack
  frames"; one-shot continuations "are also much cheaper to implement
  compared to multi-shot continuations since they do not require stack
  frames to be copied". Effects are untyped (an unhandled one raises
  `Effect.Unhandled`, and the interface carries an "unstable" alert).
- **Eio's `Switch`** is trio's nursery *and* Racket's custodian at once:
  it waits for its fibers and closes the resources attached to it.
- **Racket's custodians** show resource ownership by scope: shutting a
  custodian closes everything it manages. A new Racket thread takes the
  current values of *preserved* thread cells (parameters among them) as
  its initial values.
- **CML's events** unify `Promise.race`, `asyncio.wait(FIRST_COMPLETED)`,
  Go's `select` and `tokio::select!`, with `withNack` as the cancellation
  of the arms not chosen.
- **Guile Fibers** is FX-26's closest relative: fibers are delimited
  continuations suspended to a scheduler's prompt, and yet they run on
  all cores with work stealing, which shows that prompt-based fibers do
  not rule out parallelism.
- **Larceny** notes that `call/cc` across tasks is legal only within the
  task that took it, which it could not check. In FX-26 the types check it
  (§3.1).

### 1.4 What the survey says

- **Two families.** Languages without first-class control (Python,
  JavaScript, Kotlin, Rust) transform code: generators, CPS or state
  machines. That forces function colour, and higher-order code has to be
  written twice (Nystrom, "What Color is Your Function?"). Languages with
  first-class control (Racket, Guile, CML, Go's runtime, OCaml 5) suspend
  a whole stack, and have no colour.
- **Unstructured spawn is a mistake the others are all correcting.**
  asyncio added `TaskGroup` and `timeout`; Kotlin made scopes the default;
  Go added `errgroup` and `context`; Java's `StructuredTaskScope` is in
  its sixth preview in JDK 26 (JEP 525), with a seventh proposed (JEP 533).
  Smith, "Notes on structured concurrency, or: Go statement considered
  harmful", is the argument.
- **Cancellation must be delivered at a suspension point and unwind.**
  Dropping (Rust) or ignoring (JavaScript promises) loses cleanup.
  Level-triggered (trio) is harder to swallow by accident than
  edge-triggered (asyncio).
- **Run to completion between suspension points** (JavaScript, asyncio,
  Lwt) makes a stretch of code with no `await` atomic. Programs rely on
  it, and preemption takes it away.

## 2. The design space for FX-26

FX-26's control, as it is (`docs/fx26.md`, "Control, typed"): `(prompt
tag body handler)`; a tag `(prompt-tag A H D R)` fixes the answer `A`, the
abort payload `H`, and the bound `D` on the effect of what it delimits.
`call-with-composable-continuation` has `(comefrom R)` and gives a
`(composable T A D R)`, which is multi-shot. `abort-current-continuation`
has `(goto R)`. On native frames a capture copies the frames up to the
prompt into a heap vector (`native-conventions.md`, step 5), about 1 ns a
word plus 0.15 µs. A whole round of prompt, capture, abort and resume
takes 0.56 µs at depth 20 (`docs/performance.md`, "What a capture
costs").

| Model                           | In FX-26                                                                                                 | Cost                                                                                                                      | Verdict                                                                                                                      |
| ------------------------------- | -------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------- |
| callbacks                       | closures in a queue; possible now                                                                        | cheapest per event; no capture                                                                                            | the loop's internals and the reactor's wakeups only; not a user API                                                          |
| promises / futures              | `(icell T R)` already: write once, `(await R)`                                                           | an allocation per promise                                                                                                 | yes, as the result of a task and for dataflow; answers Lucassen's objection to futures (§3.4)                                |
| async/await, stackless          | a second compilation of each async function to a state machine or CPS, in 2 checkers and 4+ compilers    | no stack copy; a heap frame per suspended call; colour, and duplicated higher-order code                                  | no: FX-26 has continuations already, and this is the cost the others pay for lacking them                                    |
| stackful fibers over prompts    | a task is a composable continuation up to its own prompt                                                 | copy of the task's frames at each suspension (depth from the task's entry, not the program's); works on every machine now | **yes, first**                                                                                                               |
| fibers on stack segments        | each task its own native stack segment (and its own `ds`/`rs` on cellular machines); one-shot resumption | O(1) switch; a stack per task; the stack limit per segment; the collector walks every suspended stack                     | later, if S4's benchmark asks (below)                                                                                        |
| effect handlers (OCaml 5, Koka) | a prompt whose handler takes `(op, k)`: FX-26's prompts are handlers with one fixed answer type per tag  | as fibers                                                                                                                 | the scheduler *is* one handler; typed per-operation signatures (Koka) are not needed if every suspension resumes with `unit` |
| CML events                      | `(event T c)` built on the same wakers                                                                   | an allocation per `sync`                                                                                                  | yes, second: `choose`/`wrap`/`sync` give select and timeouts on one channel                                                  |
| actors                          | the actors note's A2–A5, on this scheduler                                                               | handler-style actors avoid captures                                                                                       | above this layer, unchanged                                                                                                  |

**Why fibers over prompts fit.** The PLDI '89 paper already observes
that "the only control frames that have to be dumped into the heap when a
continuation in region r is captured are the ones that are flagged with
the same `(comefrom r)` effect" (`GiffordHistory/papers/pldi89-jouvelot.pdf`,
§5). If the loop runs each task under a prompt of its own, a suspension
copies only the task's frames. A typical task is shallow (a handler, a
read loop, a few helpers), so a switch should cost well under a
microsecond on native code, and nothing new is needed on any machine.

**Example: two tasks ping-ponging** (FX-26 today;
`examples/async/ping-pong.fx`, checked and run). §1.1's asyncio program,
with the scheduler written out. A task is the rest of a computation up to
the scheduler's prompt, `(composable unit unit D @p)`. `yield!` captures
it and aborts to the prompt's handler with it, which queues it; `run!`
resumes queued tasks, each under a fresh prompt, until none is left.

```scheme
(define-type task (composable unit unit D @p))
(define sched (prompt-tag unit task D @p) (make-continuation-prompt-tag))
(define queue (ref (listof task @q) @q) (new nil))

(define* yield! (subr (maxeff (goto @p) (comefrom @p)) () unit)
  (lambda ()
    (call-with-composable-continuation
      (lambda (k) (abort-current-continuation sched k))
      sched)))

(define* run! (subr (maxeff D (goto @p) (comefrom @p)) () unit)
  (lambda ()
    (let ((q (get queue)))
      (if (null? q)
          #u
          (begin
            (set queue (cdr q))
            (prompt sched ((car q) #u) (lambda (k) (enqueue! k)))
            (run!))))))

(define* pinger (subr (maxeff D (goto @p) (comefrom @p)) (int int) unit)
  (lambda (who n)
    (if (= n 0)
        #u
        (begin (set log (cons (+ who n) (get log)))
               (yield!)
               (pinger who (- n 1))))))

(spawn! (lambda () (pinger 100 3)))
(spawn! (lambda () (pinger 200 3)))
(run!)
(the (listof int @q) (reverse (get log)))   ; (103 203 102 202 101 201)
```

`D` is the bound on what tasks do (the queue and log at `@q`, the globals
they read, `spin`); `enqueue!`, `spawn!` and `log` are in the file. The
same loop in OCaml 5 is a handler of a `Yield` effect, from the manual's
scheduler example:

```ocaml
type _ Effect.t += Yield : unit t
let yield () = perform Yield
(* in the scheduler's handler: *)
| effect Yield, k -> enqueue k (); dequeue ()
```

`perform Yield` is `yield!`; the handler's `k` is the continuation the
abort carries.

**Handlers without per-operation types.** An effect handler resumes each
operation at its own result type. FX-26's tag fixes one `H`, and a
continuation's `T` is fixed where it is captured, so a sum of operations
each carrying a continuation of a different `T` is awkward. The way out,
used by Guile Fibers' `suspend-current-task` and by Rust's `Waker`:
**every suspension resumes with `unit`**, and the value it waited for
travels through a cell. Then `H` is one type, the continuation is always
`(composable unit A D c)`, and all operations are built from one
primitive, `suspend` (§6.1).

**Example: a generator is a handler** (FX-26 today;
`examples/async/generator.fx`, checked and run). Where a handler *does*
want a value with the continuation, a product carries both, and the tag
fixes the one type. The consumer `sum-all` is the prompt's handler; it
resumes the producer under a new prompt of the same tag, which is what a
deep handler does.

```scheme
(define-type step (productof (v int) (k (composable unit int D @p))))
(define g (prompt-tag int step D @p) (make-continuation-prompt-tag))

(define* yield-int (subr (maxeff (goto @p) (comefrom @p)) (int) unit)
  (lambda (x)
    (call-with-composable-continuation
      (lambda (k) (abort-current-continuation g (product (v x) (k k))))
      g)))

(define* count-up (subr (maxeff (goto @p) (comefrom @p) spin) (int int) unit)
  (lambda (i n)
    (if (> i n) #u (begin (yield-int i) (count-up (+ i 1) n)))))

(define* sum-all (subr (maxeff (goto @p) (comefrom @p) spin) (step) int)
  (lambda (s)
    (+ (extract s v) (prompt g ((extract s k) #u) (lambda (s2) (sum-all s2))))))

(prompt g (begin (count-up 1 4) 0) sum-all)   ; 10
```

Python and OCaml 5 (the manual's first example, whose handler resumes
with a value, as `sum-all` does not):

```python
def count_up(i, n):
    while i <= n:
        yield i
        i += 1
sum(count_up(1, 4))                       # 10
```

```ocaml
type _ Effect.t += Xchg: int -> int t
let comp1 () = perform (Xchg 0) + perform (Xchg 1)
try comp1 () with
| effect (Xchg n), k -> continue k (n+1)
```

One thing the types show: the last line's effect keeps `(goto @p)` and
`(comefrom @p)`. The prompt inside `sum-all` cannot delimit, because its
body calls `k`, a variable whose type mentions `@p` ("Control, typed").
A handler that resumes a stored continuation always shows control on the
tag's region, until the region itself is masked (§3.1's example).

**Example: a promise and `await`, from one `suspend!`** (FX-26 today;
`examples/async/promise.fx`, checked and run). Here the abort carries a
thunk that files the task somewhere, as Guile's `suspend-current-task`
takes a procedure. `yield!` files it on the run queue, `await!` among the
promise's waiters; every suspension resumes with unit, and `await!` reads
the value from the promise when it wakes.

```scheme
(define-type promise (ref (sumof (pending (listof task @q)) (resolved int)) @q))
(define sched (prompt-tag unit (subr Q () unit) D @p) (make-continuation-prompt-tag))

(define* suspend! (subr (maxeff (goto @p) (comefrom @p)) ((subr Q (task) unit)) unit)
  (lambda (file)
    (call-with-composable-continuation
      (lambda (k) (abort-current-continuation sched (lambda () (file k))))
      sched)))

(define* yield! (subr (maxeff (goto @p) (comefrom @p)) () unit)
  (lambda () (suspend! enqueue!)))

(define* await! (subr (maxeff D (goto @p) (comefrom @p)) (promise) int)
  (lambda (pr)
    (tagcase (get pr)
      (resolved v v)
      (pending ws (begin (suspend! (lambda (k) (set pr (sum pending (cons k ws)))))
                         (await! pr))))))

(spawn! (lambda () (begin (note! 1) (note! (await! fut)))))
(spawn! (lambda () (begin (note! 2) (yield!) (note! 3) (resolve! fut 42))))
(run!)                                    ; log: (1 2 3 42)
```

`resolve!` sets the value and queues the waiters. The promise is a `ref`
of a sum, not an `icell`: FX-26 has no test for whether an I-cell is full,
and `icell-get` on an empty one is an error, not a suspension (§6.1, open
question 8). Python and Eio (Eio's README):

```python
async def consumer(): log.append(1); log.append(await fut)
async def producer():
    log.append(2); await asyncio.sleep(0); log.append(3)
    fut.set_result(42)                    # fut = loop.create_future()
```

```ocaml
let promise, resolver = Promise.create () in
Fiber.both
  (fun () -> let x = Promise.await promise in traceln "x = %d" x)
  (fun () -> Promise.resolve resolver 42)
```

**Segmented stacks, and whether to have them.** The copying scheme
suffices until tasks are deep or switch very often. The alternatives,
in order of cost to build:
1. *A stack cache* (Hieb, Dybvig and Bruggeman, PLDI 1990; Larceny's):
   the capture splits the stack and the frames stay where they are until
   reinstated. PLAN.md's queue item 7 defers this "for a workload that
   captures deeply and often". An async server is that workload.
2. *One-shot suspension* (Bruggeman, Waddell and Dybvig, PLDI 1996; OCaml
   5): since `suspend`'s continuation is resumed exactly once, the task can
   own a stack segment and a switch swaps the stack pointer. How a
   segment grows is a choice between two known answers:
   - *linked segments, Chez's way*: on overflow, allocate a new segment
     and copy a few of the caller's frames into it. Farvardin and Reppy
     (PLDI 2020) note that segment thrashing (the hot split) "was solved
     by Bruggeman et al. in the Chez Scheme compiler", and that the
     solution works only "for runtime systems that do not allow pointers
     into the stack", which FX-26 is: a heap object never points into
     the native stack.
   - *resizing, Go's way*: move the whole stack to a block twice the
     size. The native convention already stores frame links as offsets
     when it copies frames, so this is the same relocation.

   That paper compares six strategies on one compiler (Manticore) and
   concludes that for languages with fine-grained concurrency "there is
   no simple answer"; its Table 3 lists the trade-offs, and S4's
   benchmark should decide. Costs either way: a stack limit per segment
   (step 6's checks), the collector walking every suspended segment by
   its stack maps, and a segment per task.
3. *Cellular machines* keep `ds`/`rs` as vectors; a task owning its own
   pair makes a switch two pointer swaps in the Rust machine.

Multi-shot `composable` continuations stay as they are; only `suspend` is
one-shot, checked at run time (a second resume traps, as a second
`icell-put!` does).

## 3. Typing

### 3.1 Suspension is a control effect on the loop's region

A loop has a region `c`. Its run queue, timers and waiters live at `c`,
and so does its prompt tag, `(prompt-tag unit (op c) D c)`. A suspension
captures up to the task's prompt, `(comefrom c)`, and may not return if
the task is cancelled, `(goto c)`. It also writes the queues, `(write
c)`. Give the combination a name (proposed; `define-effect` takes no
parameters today):

```
;; PROPOSED
(define-effect (suspends c) (maxeff (comefrom c) (goto c) (read c) (write c) (alloc c)))
```

The loop's scope binds `c` with `letregion`, and the checker masks every
atom on `c` there (`close_region` masks before refusing a `comefrom`,
§"Findings" 5). So `with-loop` is `asyncio.run` or `block_on`: code
outside cannot tell that it suspended inside. A task cannot take a
continuation that leaves its loop, because every such continuation's type
mentions `c`. That is the check Larceny's notes wanted and could not make.

**Example: `asyncio.run` is masking** (FX-26 today;
`examples/async/run-masked.fx`, checked and run). The ping-pong again,
with the tag, the run queue and the log made inside one procedure, at a
region `@s` that nothing outside names:

```scheme
(define-effect L (maxeff spin (read @s) (write @s) (alloc @s) (alloc @l)))
(define-type ltask (composable unit unit L @s))

(define interleave (subr (maxeff spin (alloc @l) (read @l)) (int) (listof int @l))
  (lambda (n)
    (let* ((sched (the (prompt-tag unit ltask L @s) (make-continuation-prompt-tag)))
           (queue (the (ref (listof ltask @s) @s) (new nil)))
           (log (the (ref (listof int @l) @s) (new nil)))
           (yield! …) (enqueue! …))              ; as in ping-pong.fx
      (letrec ((pinger …) (run! …))
        (begin
          (prompt sched (pinger 100 n) (lambda (k) (enqueue! k)))
          (prompt sched (pinger 200 n) (lambda (k) (enqueue! k)))
          (run!)
          (the (listof int @l) (reverse (get log))))))))

(interleave 3)   ; (103 203 102 202 101 201)
```

The checker gives `interleave` the type it was declared, `(subr (maxeff
spin (alloc @l) (read @l)) (int) (listof int @l))`: every `goto`,
`comefrom`, read and write on `@s` is masked, so a caller cannot tell
that tasks were switched inside. In Python the same boundary is a call,
and nothing in `interleave`'s signature says what it does:

```python
def interleave(n):
    log = []
    async def pinger(who, i): ...        # as in §1.1
    async def main(): ...
    asyncio.run(main())
    return log
```

What is missing today is only the packaging: `with-loop` would bind `@s`
with `letregion` (as `arena-outside.fx` in §3.6 does) rather than rely on
the procedure's boundary.

### 3.2 Colour

A function suspends iff its latent effect mentions `(suspends c)` for
some loop. Against Nystrom's rules:

| Nystrom's rule                      | FX-26                                                                                                            |
| ----------------------------------- | ---------------------------------------------------------------------------------------------------------------- |
| every function has a colour         | every function has an effect; suspension is part of it                                                           |
| red and blue are called differently | no: one call, one compilation                                                                                    |
| red can only be called from red     | an effect propagates to the caller, and is refused only where a closed effect was declared, or in a place binder |
| red is more painful to call         | no                                                                                                               |
| some core library functions are red | yes: `sleep`, channel operations, I/O                                                                            |

Effect polymorphism removes the duplication: `map` over `(subr e (a) b)`
takes a suspending `f` and has its effect. What remains is the writing of
effects in signatures, which `define-effect` shortens, and the places
where a closed effect was written (a `(subr pure …)` callback slot) and so
a suspending procedure cannot go. That is the right refusal: code that
took a pure callback may rely on it not interleaving.

**Example: one `for-each` for both colours** (FX-26 today;
`examples/async/colour.fx`, checked and run). `for-each` is polymorphic
in its argument's effect. Given `generator.fx`'s `yield-int` it
suspends, and its call has `(goto @p)` and `(comefrom @p)`; given a
procedure that writes a ref, its call has `(write @r)` and no control
effect. One definition, one compilation:

```scheme
(define for-each
  (poly ((e effect)) (subr (maxeff e spin (read @l)) ((subr e (int) unit) (listof int @l)) unit))
  (plambda ((e effect))
    (lambda (f xs)
      (letrec ((go (subr (maxeff e spin (read @l)) ((listof int @l)) unit)
                 (lambda (ys) (if (null? ys) #u (begin (f (car ys)) (go (cdr ys)))))))
        (go xs)))))

(prompt g (begin (for-each yield-int xs) 0) sum-all)          ; 6, suspending
(for-each (lambda (x) (set total (+ x (get total)))) xs)      ; not suspending
(get total)                                                   ; 6
```

Python needs the helper twice, once per colour:

```python
def for_each(f, xs):
    for x in xs: f(x)

async def for_each_async(f, xs):
    for x in xs: await f(x)
```

**Cancellation points are visible.** In a design with no preemption, a
procedure whose effect lacks `(suspends c)` runs to completion between
two points in its callers. Nothing else in the loop runs meanwhile, and
it cannot be cancelled midway. JavaScript and asyncio programmers rely
on this without the types saying it; FX-26's types would say it.

### 3.3 The loop's effect bound

The tag's `D` bounds what every task may do (apart from control on `c`),
and it is fixed when the loop is made. So a loop is `(loop c D)`, and a
task is a thunk of type `(subr (maxeff D (suspends c)) () T)`. A thunk
with less effect is a subtype, since a latent effect is covariant, so no
bounded effect quantification is needed (the P8 question). The price is
that `D` is written once per loop, or inferred from the tasks: open
question 1.

### 3.4 Spawning charges the task's effect, which answers Lucassen

Lucassen rejected futures (thesis §9.1.2) because a future has its
value's type, so the effects of computing it cannot be tracked. Here a
task handle has a type of its own, `(task T n)`, and `spawn` charges its
thunk's latent effect `D` where it is spawned. That is sound because the
nursery does not return until the task has ended, so the task's effects
happen within the nursery's extent, as a call's would. Masking then works
as for a call: a task that writes a region private to the enclosing
function is masked with it.

### 3.5 Cancellation and failure

- **Cancellation** is delivered at a suspension point. `suspend`, woken
  by a cancel rather than a wake, aborts to the innermost cancel scope
  that was cancelled: `(goto c)`, already in `(suspends c)`.
  Level-triggered, as trio's: while the scope is cancelled, every further
  suspension inside it aborts too. Aborting to a prompt already ends the
  places entered inside it (`native-conventions.md`, step 5), so the
  unwinding frees arenas, which is the cleanup that matters most. Other
  resources (file descriptors) need an unwind hook: FX-26 has no
  `dynamic-wind`, and §5 proposes places as custodians instead.
- **Failure.** FX-26 has no exceptions. A domain error is a value, a sum
  in the task's result. A trap (a second `icell-put!`, fuel, memory) must
  reach the task's prompt: that is the actors note's F1, still unchecked.
  When it does, the nursery cancels the task's siblings, waits for them,
  and propagates the trap from `with-nursery`, as `TaskGroup` does.
  Several traps: report the first and count the rest, or a list (open
  question 4). No "may fail" atom, for the actors note's reason: every
  call can trap.

**Example: a level-triggered cancel scope** (FX-26 today;
`examples/async/cancel.fx`, checked and run, with `ping-pong.fx`'s
scheduler). A scope is a prompt of a second tag, `scope`, *inside* the
task, and a flag. `checkpoint!` suspends; on resuming it aborts to the
scope if the flag is set, and so would every later checkpoint in the
scope. The captured continuation contains the scope's prompt, so the
abort finds it after any number of suspensions. A second task sets the
flag; `ticker` would count for ever.

```scheme
(define-type outcome (sumof (done int) (cancelled unit)))
(define scope (prompt-tag outcome unit (maxeff D (goto @p) (comefrom @p)) @c)
  (make-continuation-prompt-tag))
(define stop? (ref bool @q) (new #f))

(define* checkpoint! (subr (maxeff D (goto @p) (comefrom @p)) () unit)
  (lambda ()
    (begin (yield!)
           (if (get stop?) (abort-current-continuation scope #u) #u))))

(define* ticker (subr (maxeff D (goto @p) (comefrom @p)) (int) int)
  (lambda (i) (begin (set log (cons i (get log))) (checkpoint!) (ticker (+ i 1)))))

(spawn! (lambda ()
          (tagcase (prompt scope (sum done (ticker 0)) (lambda (u) (sum cancelled u)))
            (done n (set log (cons n (get log))))
            (cancelled u (set log (cons -1 (get log)))))))
(spawn! (lambda () (begin (yield!) (yield!) (set stop? #t))))
(run!)                                    ; log: (0 1 2 -1)
```

The two tags bound each other: `scope`'s delimited computations suspend
to `sched`, so its bound has control on `@p`, and `sched`'s `D` has
control on `@c`. That is allowed, since a bound excludes only its own
tag's region. trio's version (the order of the two tasks is not
guaranteed there):

```python
scope = trio.CancelScope()

async def ticker():
    with scope:
        i = 0
        while True:
            log.append(i); i += 1
            await trio.sleep(0)           # a checkpoint
    log.append(-1)

async def canceller():
    await trio.sleep(0); await trio.sleep(0)
    scope.cancel()
```

The toy checks the flag only when the task is resumed. The real design
(§6.1) has `cancel!` also wake a task suspended in the scope, so it need
not wait for its timer or channel.

### 3.6 What a suspended task may hold

| Held across a suspension                             | Today                         | Why                                                                                                            |
| ---------------------------------------------------- | ----------------------------- | -------------------------------------------------------------------------------------------------------------- |
| heap data                                            | yes                           | the continuation is a heap object, traced                                                                      |
| data in a place opened *outside* the loop            | yes                           | the place outlives the loop, which outlives every task                                                         |
| data in a place opened by the task, across `suspend` | **refused** by `close_region` | the masked body keeps `(comefrom c)`, with `c` visible; and the abort to the task's prompt would end the place |
| a `letregion` (analysis only) around a `suspend`     | refused, as above             | `soundness.md` §2.6 says K26's `priv` allows a `comefrom` for a region with no memory; the checker could too   |
| a composable continuation of a tag inside the task   | yes, within the task          | its type mentions the tag's region                                                                             |
| a continuation or task handle, out of its loop       | refused                       | its type mentions `c`                                                                                          |

**Example: rows 2 and 3 of the table** (FX-26 today). Accepted
(`examples/async/arena-outside.fx`, checked and run; §6.2's `squares`
sketch, with no proposed operation): an arena encloses the loop, whose
region `s` is bound by `letregion`, and every task writes the arena.

```scheme
(define-type (stask (s region) (r region))
  (composable unit unit (maxeff spin (read s) (write s) (alloc s) (write r)) s))
(define-type (sched-tag (s region) (r region))
  (prompt-tag unit (stask s r) (maxeff spin (read s) (write s) (alloc s) (write r)) s))

(define squares (subr spin (int) int)
  (lambda (k)
    (letrena r
      (let ((out (the (arrayof int r) (rmake-array r k 0))))
        (begin
          (letregion s
            (let* ((sched (the (sched-tag s r) (make-continuation-prompt-tag)))
                   … queue, park!, yield! …)
              (letrec ((spawn-all … (prompt sched (begin (yield!) (array-set! out i (* i i))) park!) …)
                       (run! …))
                (begin (spawn-all 0) (run!)))))
          (sum-from 0 0))))))                 ; a local loop over `out`

(squares 5)   ; 30
```

`squares` checks at `(subr spin (int) int)`: the continuations mention
`s`, not `r`, and `letregion s` masks their control effects before
`letrena r` looks. Rust's scoped threads are the nearest thing, a scope
that tasks may borrow from:

```rust
let mut out = vec![0; 5];
std::thread::scope(|s| {
    for (i, x) in out.iter_mut().enumerate() {
        s.spawn(move || *x = i * i);
    }
});
```

Refused (`examples/async/suspend-in-arena.fx`, checked: the checker
rejects it): a task that opens its own arena and suspends inside it.

```scheme
(define* holder (subr (maxeff D (goto @p) (comefrom @p)) () int)
  (lambda ()
    (letrena r
      (let ((x (the (ref int r) (rnew r 1))))
        (begin (yield!) (get x))))))
;; ! a continuation captured in `letrena r` could outlive its region:
;;   its effect is (maxeff (comefrom @p) (goto @p) (read (globals sched yield!)))
```

To let a task suspend inside its own `letrena` needs two things:
1. **Per-task place stacks** (the actors note's Q1). Regions end newest
   first, and interleaved tasks break that: A enters `r1` and suspends; B
   enters `r2` and suspends; A leaves `r1`, which ends B's `r2`. Each task
   needs a stack of places of its own, whose base is the spawner's stack at
   the nursery: a cactus stack, as Cilk's.
2. **A suspension atom distinct from `comefrom`**: `(suspend c)`, meaning
   "captured to `c`'s prompt, **one-shot**, and the loop will resume it
   exactly once, with a wake or a cancel". A place binder refuses
   `comefrom` because such a continuation may be dropped or run twice. A
   `(suspend c)` continuation is neither, provided a loop never returns
   with a suspended task (structured concurrency guarantees that; a
   deadlock cancels what is left). The runtime detaches the task's places
   with its frames, rather than ending them at the abort.

### 3.7 Scheduler state is a region

The loop's queues, timers, waiter lists and channel buffers are
ordinary data at `c`, written by `(write c)`. Masking `c` at `with-loop`
is what lets a function that runs a loop be pure (or have only its I/O
effects). A reactor call is a primitive with an effect on a region
standing for the outside world; the REPL's licence already refuses
speculation on anything with such an effect.

### 3.8 FX history

Lucassen's `cobegin` (thesis ch. 6) requires branches not to interfere,
and promises no fairness, which permits green threads. Jouvelot and
Gifford continued with communication effects (PLDI '89 cites "Parallel
Functional Programming: The FX-87 Project", 1989, and "Communication
Effects for Message-Based Concurrency", MIT/LCS/TM-386, 1989; neither is
on disk). The PLDI '89 paper cites Wand, "Continuation-based
Multiprocessing" (LFP 1980), and Haynes, Friedman and Wand, "Obtaining
Coroutines with Continuations" (1986): building processes from
continuations is where FX's own control effects came from.

## 4. The runtime

### 4.1 The scheduler in FX-26, the reactor in Rust

The scheduler is policy: queues, nurseries, cancel scopes, timers,
channels. It is best written in FX-26 over prompts, as a library, so
it is checked like any other program, runs on every machine, and is
changed without touching Rust. It is the actors note's A1, grown.

The reactor is mechanism: a monotonic clock and readiness of file
descriptors. It is best in Rust, as a small module over kqueue (macOS)
and epoll (Linux) through `libc`, which `fixpt-native` and
`fixpt-memmgmt` already depend on. No new crate is needed. Its interface
to FX-26 is three primitives, reached through `prim` on every machine:

| Primitive (proposed)                   | Does                                                                              |
| -------------------------------------- | --------------------------------------------------------------------------------- |
| `%clock-now`                           | monotonic milliseconds                                                            |
| `%reactor-interest fd readable? token` | register one-shot interest; `token` is a fixnum the loop maps to a waker          |
| `%reactor-wait timeout-ms`             | block until some interest is ready or the timeout passes; return the ready tokens |

The loop calls `%reactor-wait` only when its run queue is empty, with the
earliest timer's deadline as the timeout. So no task's frames are on the
native stack while the process blocks. Timers are a binary heap at `c`.
Blocking work with no readiness (regular files on macOS) goes to a Rust
thread pool whose completions arrive through the reactor as a pipe or
`EVFILT_USER` event; this is `asyncio.to_thread` and libuv's pool. Only
Rust code runs on those threads until FX-26 has threads.

A **virtual clock** comes first: with no reactor, `sleep` advances a
clock when the run queue empties (trio's `MockClock` with autojump).
Tests with timeouts are then deterministic and fast, which suits the
two-minute suite budget.

### 4.2 How native code yields

A suspension is a capture and an abort, which native code already does
(step 5), so native code needs no new call-out. Two things to check:
- **Nested runs.** Native code may call cellular code that calls native
  code; the inner run uses the stack below the outer's, with a Rust frame
  between. A capture that would cross that frame cannot copy it. Lua's
  answer is `lua_callk`: a continuation function to resume in place of the
  C frame. Options: make adapters capture-transparent, trap on a capture
  that would cross (a clear error, as Lua's), or keep tasks' code in one
  convention. First measure whether it happens.
- **Fuel polls.** A poll's slow path raises the step-limit error today.
  Under a loop it could yield instead (§4.4).

### 4.3 The collector

- A suspended task is a heap vector of frames (links as offsets, return
  addresses as fixnums). The loop's queue holds it, so it is a root like
  anything else. Step 5's "a continuation's frames as a bloblet of its own
  kind" becomes worth doing, since the collector could then skip the raw
  words.
- Each suspension allocates a frame vector (122 words at depth 20,
  `performance.md`). The nursery of 2^20 words takes about 8,000 such
  switches between minor collections. A task that waits long is promoted
  with its frames, and resuming copies them back to the stack, which is
  not a heap write and needs no barrier. Writes of continuations into the
  loop's old queues are ordinary stores, marked by the card barrier.
- After Q1, a suspended task's reap must be collected with that task's
  frames as its roots, so the task's place stack travels with its frame
  vector, where the collector can find it.
- With one-shot stack segments (§2), the collector walks every suspended
  segment by the stack maps (`generational-gc.md` §1), exactly as it walks
  the live stack.

### 4.4 Fairness and fuel

Cooperative first: a task runs until it suspends. `spin`-free code is
bounded, so only code whose effect says `spin` can hog the loop. The loop
can see a hog without preempting: the machines count fuel, so a task that
used more than a budget between suspensions can be reported, as asyncio's
debug mode logs "callbacks taking longer than 100 milliseconds"
(`loop.slow_callback_duration`).

Preemption at the fuel poll (the actors note's Q2; Erlang's reductions;
Haynes and Friedman's engines, "a new programming language abstraction
for timed preemption", which Dybvig and Hieb showed "may be defined in
terms of continuations and timer interrupts"; Larceny's tasking, which
switches on a timer interrupt every 5000 ticks) needs Q1 first. It also takes away "atomic between
suspension points" (§3.2), so a preemptible task should be one whose
effects do not interfere with its siblings' (the `par` table of
`type-and-effect-directions.md` §3). Open question 2.

### 4.5 Task-local context: marks

A mark is in the frames, and the frames are what a suspension captures,
so `with-mark`/`first-mark` are already task-local and survive
suspension. That is `contextvars` and `AsyncLocalStorage` for free.
Inheritance at spawn is the one gap. A child starts from the loop's
frames, not its parent's, so it sees none of the parent's marks unless
`spawn` copies them. A Racket thread starts with the current values of
the *preserved* thread cells (parameters among them); an asyncio Task
runs in a copy of the context current at its creation (PEP 567); Node's
`AsyncLocalStorage` store follows every asynchronous operation created
within `run`. The proposal is that `spawn` takes a list of
keys to carry (typed per key), since copying all marks cannot be typed
generically. Open question 6.

**Example: task-local context** (FX-26 today; `examples/async/context.fx`,
checked and run, with `ping-pong.fx`'s scheduler). Each task sets a mark
for `who` inside its own prompt; after every `yield!` each still reads
its own value, though the two interleave.

```scheme
(define who (mark-key int @m) (make-continuation-mark-key))

(define* worker (subr (maxeff D (goto @p) (comefrom @p)) (int) unit)
  (lambda (i)
    (if (= i 0)
        #u
        (begin (set log (cons (+ (first-mark who 0) i) (get log)))
               (yield!)
               (worker (- i 1))))))

(spawn! (lambda () (with-mark who 100 (lambda () (worker 3)))))
(spawn! (lambda () (with-mark who 200 (lambda () (worker 3)))))
(run!)                                    ; log: (103 203 102 202 101 201)
```

The mark is set by the task itself, so inheritance is not tested here.
Python and Node:

```python
who = contextvars.ContextVar("who")

async def worker(n):
    for i in range(n, 0, -1):
        log.append(who.get() + i)
        await asyncio.sleep(0)

async def task(w):
    who.set(w)          # this Task's copy of the context
    await worker(3)
```

```js
const who = new AsyncLocalStorage();
who.run(100, () => worker(3));            // worker reads who.getStore()
who.run(200, () => worker(3));
```

## 5. Structured concurrency and regions

A nursery is a region `n` bound inside the loop, and `with-nursery` is a
region binder:
- a task handle `(task T n)` mentions `n`, so it cannot leave the nursery;
- `with-nursery` returns only after every task spawned in it has ended,
  so a task may use any region or place in scope at the nursery; its
  effects are charged where it is spawned (§3.4);
- the result may not mention `n`.

This is the scoped-task pattern that Rust cannot make sound, since a Rust
scope is a destructor that `mem::forget` can skip. Here the scope is the
dynamic extent of a form, which a program cannot skip. A continuation
that would resume inside the nursery after it ended cannot exist,
because its type mentions `c` and it never leaves the loop. The loop
itself does not return while a task is suspended: on deadlock (run queue
empty, no timers, no interests) it cancels what is left, and so unwinds
it.

**No unstructured spawn.** asyncio's `create_task`, and Go's `go`, would
be `spawn` into the loop's own outermost nursery. The first design passes
nurseries explicitly and offers no such global nursery. Open question 5.

**Places as custodians.** Racket's custodians manage threads, ports,
sockets and places, and shutting one closes them. Eio's `Switch.run`
does both jobs at once: it "waits until fn and all other attached fibers
have finished, and then releases any attached resources (e.g. closing all
attached file handles)". A place already has a lifetime ended by its
binder, on return, abort or cancellation alike. A file descriptor opened
*in a place* (`(open p path)`, proposed), closed when the place ends,
gives custodians with no new mechanism. It also gives cancellation its
cleanup without `dynamic-wind`. Eio suggests going one step further: let
`with-nursery` bind a place as well as a region, so that what its tasks
open in it is closed when the nursery ends (open question 13).

**The order of scopes that works today** is `letrena` ⊃ `with-loop` ⊃
`with-nursery` ⊃ tasks, with no place opened inside a task across a
suspension. The order that needs §3.6's two changes is a place opened
inside a task.

## 6. Recommendation

### 6.1 A minimal first design (proposed)

Types are sketches in FX-26 notation. `(suspends c)` is §3.1's
abbreviation. `(loop c D)`, `(nursery n c D)`, `(task T n)`, `(waker c)`,
`(scope s c)` and `(channel T c)` are abstract types, which
`define-generative` can make over records at `c`.

| Name                              | Type (sketch)                                                                                                | Semantics                                                                                            | Analogue                                        |
| --------------------------------- | ------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------------------------------------------------- | ----------------------------------------------- |
| `(with-loop (lp c D) body)`       | form; body `T ! (maxeff D (suspends c))`, result `T` not mentioning `c`, effect `D∖c`                        | a region `c`, a loop, `body` as the first task; returns when it has ended                            | `asyncio.run`, `trio.run`, `Eio_main.run`       |
| `(with-nursery lp (n) body)`      | form; result not mentioning `n`                                                                              | a nursery; waits for every child; a child's trap cancels the rest and propagates                     | `TaskGroup`, `open_nursery`, `Switch.run`       |
| `spawn`                           | `(subr (maxeff D (write c)) ((nursery n c D) (subr (maxeff D (suspends c)) () T)) (task T n))`               | enqueue a task; its effect charged here                                                              | `start_soon`, `tg.create_task`, `Fiber.fork`    |
| `join`                            | `(subr (suspends c) ((task T n)) (sumof (done T) (cancelled unit)))`                                         | wait for a task's end                                                                                | `await task`                                    |
| `suspend`                         | `(subr (suspends c) ((loop c D) (subr (write c) ((waker c)) unit)) unit)`                                    | capture to the task's prompt; hand a one-shot waker to the registration procedure; resume when woken | Guile `suspend-current-task`, Rust `Waker`      |
| `wake!`                           | `(subr (write c) ((waker c)) unit)`                                                                          | enqueue the task; later wakes of the same waker do nothing, so a timer and a channel may race        | `Waker::wake`                                   |
| `yield`                           | `(subr (suspends c) ((loop c D)) unit)`                                                                      | go to the back of the run queue                                                                      | `asyncio.sleep(0)`                              |
| `sleep`                           | `(subr (suspends c) ((loop c D) int) unit)`                                                                  | milliseconds, on the loop's clock (virtual first)                                                    | `asyncio.sleep`, `trio.sleep`                   |
| `(with-cancel-scope lp (s) body)` | form; result `(sumof (done T) (cancelled unit))`                                                             | `(cancel! s)` makes every suspension inside abort to here, until the body ends                       | `trio.CancelScope`                              |
| `move-on-after`                   | `(subr (suspends c) ((loop c D) int (subr (maxeff D (suspends c)) () T)) (sumof (done T) (cancelled unit)))` | a cancel scope with a deadline                                                                       | `trio.move_on_after`, `asyncio.timeout`         |
| `make-channel`                    | `(subr (maxeff (alloc c) (write c)) ((loop c D) int) (channel T c))`                                         | a bounded channel; capacity 0 is a rendezvous                                                        | `open_memory_channel`, `Queue(maxsize)`, `chan` |
| `channel-send`, `channel-receive` | `(suspends c)`; receive gives `(sumof (value T) (closed unit))`                                              | suspend while full or empty: backpressure                                                            | `send`, `receive`                               |
| `channel-close!`                  | `(subr (write c) ((channel T c)) unit)`                                                                      | wakes receivers with `closed`                                                                        | `aclose`                                        |

Stage 3 adds `wait-readable`, `wait-writable`, `read-some` and
`write-some` on descriptors, all `(suspends c)` plus an effect on the
outside world. Stage 6 adds CML's `(event T c)` with `choose`, `wrap`,
`with-nack` and `sync`. A receive with a timeout, as it would read:

```scheme
;;; PROPOSED — sketch only; `receive-evt` and `timeout-evt` are made up here.
(sync (choose (wrap (receive-evt ch) (lambda (v) (sum value v)))
              (wrap (timeout-evt lp 50) (lambda (u) (sum timed-out u)))))
```

```go
select {
case v := <-ch:
    return v, true
case <-time.After(50 * time.Millisecond):
    return 0, false
}
```

Both arms hold the task's one waker. The first to fire wakes it, and a
later wake by the other does nothing, as `wake!` says in the table above.

A task's result is kept in an `(icell T c)`: `join` is an `icell-get`
that suspends first while the cell is empty. The general "`icell-get`
suspends when a scheduler is present" (P6/Q3) is left until it can be
typed: an `icell-get` whose effect is only `(await r)` must not suspend
inside a place binder.

### 6.2 Examples (proposed syntax; not checked, not implemented)

Two tasks with timers, joined; the loop masked, so `race-two` is pure
apart from `spin`:

```
;;; PROPOSED — sketch only.
(define race-two (subr spin () int)
  (lambda ()
    (with-loop (lp c spin)
      (with-nursery lp (n)
        (let ((a (spawn n (lambda () (begin (sleep lp 20) 1))))
              (b (spawn n (lambda () (begin (sleep lp 10) 2)))))
          (+ (tagcase (join a) (done x x) (cancelled u 0))
             (tagcase (join b) (done x x) (cancelled u 0))))))))
(race-two)   ; 3, after 20 ms of (virtual) time
```

The same in asyncio:

```python
async def race_two():
    async def after(ms, v):
        await asyncio.sleep(ms / 1000)
        return v
    async with asyncio.TaskGroup() as tg:
        a = tg.create_task(after(20, 1))
        b = tg.create_task(after(10, 2))
    return a.result() + b.result()        # 3
```

The difference that matters: `race-two`'s type says it is pure apart from
`spin`, and `a` and `b` cannot outlive the nursery because their types
mention `n`. Python's `a` and `b` can be kept after the `async with`.

A producer and a consumer over a bounded channel, under a deadline.
Region-polymorphic helpers take the loop, as `caller-place.fx`'s `build`
takes its caller's place:

```
;;; PROPOSED — sketch only.
(define-rec
  (produce (poly ((c region)) (subr (maxeff (suspends c) spin) ((loop c spin) (channel int c) int) unit))
    (plambda ((c region))
      (lambda (lp ch i)
        (if (= i 0)
            (channel-close! ch)
            (begin (channel-send ch i) ((proj produce c) lp ch (- i 1)))))))
  (consume (poly ((c region)) (subr (maxeff (suspends c) spin) ((loop c spin) (channel int c) int) int))
    (plambda ((c region))
      (lambda (lp ch acc)
        (tagcase (channel-receive ch)
          (value v ((proj consume c) lp ch (+ acc v)))
          (closed u acc))))))

(define sum-before (subr spin (int int) (sumof (done int) (cancelled unit)))
  (lambda (k ms)
    (with-loop (lp c spin)
      (move-on-after lp ms
        (lambda ()
          (with-nursery lp (n)
            (let ((ch (the (channel int c) (make-channel lp 4))))
              (begin
                (spawn n (lambda () ((proj produce c) lp ch k)))
                ((proj consume c) lp ch 0)))))))))
```

The same in trio, whose memory channel and `move_on_after` §6.1 copies:

```python
async def sum_before(k, ms):
    total = 0
    with trio.move_on_after(ms / 1000) as cs:
        send, recv = trio.open_memory_channel(4)
        async def produce():
            async with send:
                for i in range(k, 0, -1):
                    await send.send(i)
        async with trio.open_nursery() as n:
            n.start_soon(produce)
            async with recv:
                async for v in recv:
                    total += v
    return None if cs.cancelled_caught else total
```

Structured concurrency meeting a region. The arena encloses the loop,
every task writes it, and the whole is accepted by today's rules (a
version with the loop written out, and no proposed operation, is
checked and run: `examples/async/arena-outside.fx`, §3.6):

```
;;; PROPOSED — sketch only.
(define squares (subr spin (int) int)
  (lambda (k)
    (letrena r
      (let ((out (the (arrayof int r) (rmake-array r k 0))))
        (begin
          (with-loop (lp c (maxeff (write r) spin))
            (with-nursery lp (n)
              (for-each-index k                      ; a helper, assumed
                (lambda ((i int))
                  (begin (spawn n (lambda () (begin (yield lp) (array-set! out i (* i i)))))
                         unit)))))
          (sum-array out))))))                        ; a helper, assumed
```

And the variant that is refused until §3.6's changes: a task that opens
its own arena and suspends inside it (checked as refused, with
`yield!` for `sleep`: `examples/async/suspend-in-arena.fx`, §3.6).

```
;;; PROPOSED — refused by the checker today, rightly.
(spawn n (lambda ()
  (letrena s
    (let ((xs (rcons s 1 nil)))
      (begin (sleep lp 5) (car xs))))))   ; `(comefrom c)` escapes `letrena s`
```

### 6.3 Stages

| Stage | Size | What                                                                                                                                                                                                                                                               | Depends on |
| ----- | ---- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ | ---------- |
| S0    | S    | The loop as an FX-26 library program (A1 grown): `suspend`, `wake!`, `yield`, `spawn`, `join`, `sleep` on a virtual clock; `with-loop` and `with-nursery` written out long-hand. Tests on every machine under the timeout; a rejection test for §6.2's last sketch | none       |
| S1    | S    | Cancel scopes, `move-on-after`, bounded channels, deadlock as cancellation of what is left; traps reaching task prompts                                                                                                                                            | S0, F1     |
| S2    | M    | `with-loop`, `with-nursery`, `with-cancel-scope` as derived forms in both checkers and both compilers; `define-effect` with parameters, for `(suspends c)`                                                                                                         | S1         |
| S3    | M    | The Rust reactor (`%clock-now`, `%reactor-interest`, `%reactor-wait`) over kqueue/epoll via `libc`; non-blocking stdin and pipes; a thread pool for files. Tests with pipes only, under the timeout, no network                                                    | S1         |
| S4    | S    | `bench/async.fx`: switch, spawn, 10,000 sleeping tasks, a channel ping-pong, at task depths 1, 20 and 200; recorded in `performance.md`. Decides S6                                                                                                                | S0         |
| S5    | M–L  | Per-task place stacks (Q1) and the one-shot `(suspend c)` atom: a task may suspend inside its own `letrena`/`letreap`                                                                                                                                              | S2, Q1     |
| S6    | L    | If S4 asks: one-shot suspension on native stack segments (or a stack cache), per-task `ds`/`rs` on cellular machines                                                                                                                                               | S4         |
| S7    | M    | CML events (`choose`, `wrap`, `with-nack`, `sync`) over wakers; then the actors note's A2–A5 on this loop                                                                                                                                                          | S1         |
| S8    | M    | Preemption at fuel polls (Q2) for tasks whose effects do not interfere                                                                                                                                                                                             | S5, P5     |

S0 and S4 need no language change and are the first to do.

### 6.4 What threads would change

- **One loop per OS thread** (Node's `worker_threads`, Racket places, OCaml
  domains each running Eio): each thread has its own heap, or one heap
  under a stop-the-world collector. Racket (since 8.18.0.2) also lets a
  `thread` join a parallel thread pool (`#:pool`). Messages between loops must be
  transmissible types (actors note H1). Nothing in §6.1 changes.
- **Tasks migrating between threads** (Go, tokio's multi-threaded runtime,
  Guile Fibers, whose schedulers steal work from each other): a suspended
  continuation is a heap object, so it can resume on another thread if
  the heap is shared. Guile shows this works for fibers built on prompts.
  Then:
  - "atomic between suspension points" no longer holds, so two tasks of
    one nursery may run in parallel only if their effects do not interfere
    (the `par` table), which the checker can decide at `spawn`. Tasks that
    interfere stay on one thread. This is the FX-91 report's stated goal,
    scheduling for parallelism from effects;
  - places shared by a nursery's tasks need per-thread chunks, and
    `REGION_SLOTS`' table per thread;
  - the card barrier and the nursery become per thread or concurrent;
  - symbols, globals, and code patched in place need an inventory (P12).
- The effect `(suspends c)` is unchanged; `c` becomes a region shared
  between threads, so its queues need synchronization in the runtime, not
  in the types.

## 7. Open questions for the user

1. **The loop's effect bound `D`**: written once per `with-loop`, or
   inferred from the tasks spawned in it? And may `define-effect` take
   parameters, for `(suspends c)`?
2. **Preemption**: cooperative only (atomic between suspension points,
   visible in types), or preemption at fuel polls for tasks that say
   `spin`, after Q1?
3. **Cancellation**: level-triggered as in trio (recommended), or
   edge-triggered as in asyncio?
4. **Failure**: traps propagate out of `with-nursery` after the siblings
   are cancelled. Report one trap, or all of them? Both asyncio's
   `TaskGroup` and trio (since 0.25.0, even for a single exception) raise
   a group; Go's `errgroup` returns the first error. Should a nursery also
   carry a typed error `E` that tasks can abort with?
5. **Unstructured spawn**: none at all (recommended), or a loop-wide
   nursery as trio's system nursery and asyncio's `create_task`?
6. **Marks at spawn**: which marks does a child inherit? Nothing, an
   explicit list of keys (recommended), or all?
7. **Nested loops**: a `with-loop` inside a task blocks its outer loop
   until it finishes. Allow it (Python raises instead), forbid it by an
   effect, or let the inner loop share the outer's reactor?
8. **I-cells**: should `icell-get` itself suspend under a loop (P6/Q3),
   which needs `(await r)` treated as a suspension inside place binders?
   Or should promises stay loop-owned `(icell T c)`?
9. **I/O scope**: which descriptors first: stdin, pipes, regular files
   through a thread pool? Sockets on localhost only, as the actors note
   has it for nodes?
10. **Capture across nested runs** (§4.2): trap on it, or make adapters
    transparent to capture?
11. **K26's `(Region)` against the checker** (Findings, 5): which is the
    intended rule for a `comefrom` on the region being closed?
12. *(Answered 2026-09-29: yes, read-only; the sources below were
    checked.)*
13. **Nursery as custodian**: should `with-nursery` also bind a place
    that owns what its tasks open (Eio's switch), or should resources be
    tied only to places the program opens itself?

## 8. The examples, and what writing them showed

Every file below was checked with `fixpt check FILE` (both checkers
agree) and run with `fixpt eval FILE`, on the release binary of
2026-09-29, under a 60-second limit. Paths are under
`docs/research/examples/async/`.

| File                  | Shows                                                | Where | Result                      |
| --------------------- | ---------------------------------------------------- | ----- | --------------------------- |
| `ping-pong.fx`        | round-robin scheduler; `yield!`, `spawn!`, `run!`    | §2    | `(103 203 102 202 101 201)` |
| `generator.fx`        | a generator; the consumer is the prompt's handler    | §2    | `10`                        |
| `promise.fx`          | one `suspend!`; a promise with waiters; `await!`     | §2    | `(1 2 3 42)`                |
| `run-masked.fx`       | the loop inside a procedure: control effects masked  | §3.1  | `(103 203 102 202 101 201)` |
| `colour.fx`           | one effect-polymorphic `for-each`, suspending or not | §3.2  | `6`, `6`                    |
| `cancel.fx`           | a level-triggered cancel scope as a second tag       | §3.5  | `(0 1 2 -1)`                |
| `arena-outside.fx`    | `letrena` ⊃ loop ⊃ tasks writing the arena: accepted | §3.6  | `30`                        |
| `suspend-in-arena.fx` | a task suspending inside its own `letrena`: refused  | §3.6  | refused, as expected        |
| `context.fx`          | marks as task-local context across suspensions       | §4.5  | `(103 203 102 202 101 201)` |

The `;;; PROPOSED` blocks in §6.1 and §6.2 are not checked, since the
operations they use do not exist.

What writing them showed, beyond the findings at the top:
- **Findings 1 and 3 hold as checked code.** A scheduler over a prompt,
  a promise, a generator, a cancel scope and task-local marks all run on
  today's FX-26, with no new primitive. `arena-outside.fx` is the
  "order of scopes that works today" of §5, accepted by the checker.
- **Control effects stay visible until the loop's region is masked.**
  A prompt whose body resumes a stored continuation cannot delimit it,
  since the continuation is a variable whose type mentions the tag's
  region. So `run!`, `spawn!` and a generator's consumer all show
  `(goto @p)` and `(comefrom @p)`, and at the top level, with `@p`
  named, so does every program that runs them. They go only where `@p`
  is private (`run-masked.fx`) or bound by `letregion`
  (`arena-outside.fx`). `with-loop` should be a region binder, as §3.1
  says, rather than a prompt.
- **Each tag's bound names the other's region.** In `cancel.fx`, the
  scope tag's bound has control on the loop's region, and the loop's `D`
  has control on the scope's. Two `define-effect`s written in terms of
  each other were needed, and every cancel scope of §6.1 would need its
  bound to include `(suspends c)`.
- **`define-effect` takes no parameters,** so a loop whose region is
  bound locally (`arena-outside.fx`) writes its effect out in full each
  time; a parametric `define-type` for the task type saved most of it.
  This is open question 1 again.
- **Precise globals lengthen `D`.** With `define*`, the tag's bound must
  list every global the tasks read (`(read (globals sched queue log
  yield! pinger))`). A procedure whose latent effect names its own
  global must say `spin`, so `promise.fx`'s `Q` could not list
  `enqueue!`. `(read @globals)` would be shorter, but precision is the
  project's rule; a library scheduler would be region-polymorphic and
  read no globals.
- **No test for a full I-cell,** and reading an empty one is an error
  ("an i-cell read before it was written"), so `promise.fx` uses a `ref`
  of a sum. Open question 8.
- **Small frictions.** A queue needs `the` on the result of `reverse`
  and `cons` to fix their regions; a `lambda` passed to
  `call-with-composable-continuation` from a `let*`-bound procedure
  needs its type written (`the (subr …)`); there is no `append`, so the
  FIFO queue reverses twice.

## Corrections after checking (2026-09-29)

The first draft was written from memory. Checking it against the sources
below changed these points:
- **Go** moved to contiguous stacks in **1.3**, not 1.4, and its release
  notes call the problem the "hot spot", not the "hot split".
- **withoutboats' "The Scoped Task trilemma"** is from 2023, not 2022.
  Its three properties are concurrency, parallelizability and borrowing.
- **Guile Fibers** runs one scheduler per core by default, with work
  stealing, so it is not single-threaded. Its suspension primitive is
  `suspend-current-task`, confirmed in `fibers/scheduler.scm`.
- **Racket**: the claim that Racket CS threads are built on Chez engines
  is withdrawn. The Racket CS paper describes userspace threads with events
  "based on Concurrent ML" and does not say how they are built. The 9.3
  docs add parallel threads (`#:pool`, since 8.18.0.2). A new thread
  inherits *preserved* thread cells, not the whole parameterization.
- **Jane Street Async** is not simply "no cancellation": by convention an
  `interrupt` deferred is passed, as `AbortSignal` is in Node.
- **Node**: ticks run before promise reactions only in CommonJS; in an ES
  module the order is reversed. The Node 11 change is PR #22842. The
  libuv pool runs file system operations and `getaddrinfo`/`getnameinfo`.
  The draft's "crypto and zlib" was not confirmed by libuv's docs (Node
  queues such work itself), and was dropped.
- **trio** nurseries always raise an exception group (since 0.25.0), even
  for one exception. The draft's "asyncio's `TaskGroup` was modelled on
  trio" is not stated in the Python docs, and was softened to "has the
  same shape".
- **Segmented stacks**: Farvardin and Reppy (PLDI 2020) report that
  Bruggeman et al. solved segment thrashing for runtimes with no pointers
  into the stack, as FX-26 has none. So Chez-style linked segments are a
  real option for S6 beside Go-style resizing, and §2 now says so.

Effect on the recommendation:
- **§5**: Eio's switch, which both waits for fibers and closes attached
  resources, strengthens "places as custodians". It adds open question 13
  (a nursery that is also a place).
- **§6.4**: Guile Fibers shows that fibers built on prompts can migrate
  between cores.
- **Open question 4** now records that asyncio and trio both raise
  groups.
- **Stages**: none change.

## Sources

Read online on 2026-09-29, read-only; versions as the pages showed them.

**Python** (documentation for 3.14.7).
- "Coroutines and Tasks", <https://docs.python.org/3/library/asyncio-task.html>:
  `create_task`, `gather`, `wait`, `TaskGroup`, `cancel`, `timeout`,
  `wait_for`, `shield`, `to_thread`, `eager_task_factory`.
- "Developing with asyncio", <https://docs.python.org/3/library/asyncio-dev.html>:
  debug mode, slow callbacks.
- PEPs 342, 380, 492, 525, 567, 654 and 3156, at
  <https://peps.python.org/pep-0342/>, <https://peps.python.org/pep-0380/>,
  <https://peps.python.org/pep-0492/>, <https://peps.python.org/pep-0525/>,
  <https://peps.python.org/pep-0567/>, <https://peps.python.org/pep-0654/>
  and <https://peps.python.org/pep-3156/>. PEP 530 was not re-read.
- trio 0.34.0 (2026-08-10):
  <https://trio.readthedocs.io/en/stable/reference-core.html>, and the
  release history, <https://trio.readthedocs.io/en/stable/history.html>
  (0.25.0, `strict_exception_groups`).
- Nathaniel J. Smith, "Notes on structured concurrency, or: Go statement
  considered harmful" (2018-04-25),
  <https://vorpus.org/blog/notes-on-structured-concurrency-or-go-statement-considered-harmful/>,
  and "Timeouts and cancellation for humans" (2018-01-11),
  <https://vorpus.org/blog/timeouts-and-cancellation-for-humans/>.
- anyio, <https://anyio.readthedocs.io/>: not re-read. `create_task_group`,
  `start_soon`, `CancelScope`, `move_on_after` and `fail_after` are from
  memory.

**Node.js** (API docs v26.10.0).
- "The Node.js Event Loop",
  <https://nodejs.org/en/learn/asynchronous-work/event-loop-timers-and-nexttick>.
- `process.md`, "When to use `queueMicrotask()` vs. `process.nextTick()`",
  <https://raw.githubusercontent.com/nodejs/node/main/doc/api/process.md>.
- `--unhandled-rejections`, <https://nodejs.org/api/cli.html>.
- `AbortController`, `AbortSignal`, `queueMicrotask`,
  <https://nodejs.org/api/globals.html>.
- `AsyncLocalStorage`, <https://nodejs.org/api/async_context.html>.
- PR #22842, "timers: run nextTicks after each immediate and timer",
  <https://github.com/nodejs/node/pull/22842>: seen through search
  results, not opened.
- libuv v1.x thread pool, <https://docs.libuv.org/en/v1.x/threadpool.html>.
- Promises/A+, <https://promisesaplus.com/> (note 3.1).
- TC39 `AsyncContext` (stage 2),
  <https://github.com/tc39/proposal-async-context>.
- Bob Nystrom, "What Color is Your Function?" (2015-02-01),
  <https://journal.stuffwithstuff.com/2015/02/01/what-color-is-your-function/>.
- Streams and `worker_threads` were not re-read.

**Racket** (Reference, 9.3).
- <https://docs.racket-lang.org/reference/threads.html>
- <https://docs.racket-lang.org/reference/sync.html>
- <https://docs.racket-lang.org/reference/custodians.html>
- <https://docs.racket-lang.org/reference/eval-model.html>
- Flatt et al., "Rebuilding Racket on Chez Scheme (Experience Report)",
  PACMPL 3 (ICFP 2019), article 78,
  <https://www-old.cs.utah.edu/plt/publications/icfp19-fddkmstz.pdf>.
- Flatt and Findler, "Kill-Safe Synchronization Abstractions", PLDI
  2004, <https://doi.org/10.1145/996841.996849>.
- Flatt, Findler, Krishnamurthi and Felleisen, "Programming Languages as
  Operating Systems (or Revenge of the Son of the Lisp Machine)", ICFP
  1999: title and venue confirmed by search only.

**CML, Guile, Gambit.**
- CML's signature, from the SML/NJ CML pages
  <http://cml.cs.uchicago.edu/pages/cml.html>, as quoted in search
  results. The page itself failed a certificate check.
- Reppy, "CML: A Higher-order Concurrent Language", PLDI 1991,
  <http://www.cs.tufts.edu/comp/250RTS/archive/john-reppy/cml-pldi.pdf>
  (not re-read).
- Guile Fibers manual 1.3.1 (2023-05-30),
  <https://github.com/wingo/fibers/wiki/Manual>.
- `fibers/scheduler.scm` at the `master` branch,
  <https://raw.githubusercontent.com/wingo/fibers/master/fibers/scheduler.scm>.
- Andy Wingo, "a new concurrent ml" (2017-06-29),
  <https://wingolog.org/archives/2017/06/29/a-new-concurrent-ml>.
- Gambit manual 4.8.3, <https://gambitscheme.org/4.8.3/manual/>.
  The latest manual's URL returned 404.
- Germain, Feeley and Monnier, "Concurrency Oriented Programming in
  Termite Scheme", Scheme and Functional Programming Workshop 2006,
  <http://scheme2006.cs.uchicago.edu/09-germain.pdf>.

**Erlang.** `erlang` module, OTP 29.1.1 (erts 17.1),
<https://www.erlang.org/doc/apps/erts/erlang.html>.

**Lua.**
- Lua 5.4 Reference Manual, §2.6 and §4.5,
  <https://www.lua.org/manual/5.4/manual.html>.
- de Moura and Ierusalimschy, "Revisiting Coroutines", TOPLAS 31(2),
  2009, <https://doi.org/10.1145/1462166.1462167>.

**OCaml.**
- OCaml 5.3 manual, "Language extensions: effect handlers",
  <https://ocaml.org/manual/5.3/effects.html>, and the `Effect` module,
  <https://ocaml.org/manual/5.3/api/Effect.html>.
- Sivaramakrishnan, Dolan, White, Kelly, Jaffer and Madhavapeddy,
  "Retrofitting Effect Handlers onto OCaml", PLDI 2021,
  <https://doi.org/10.1145/3453483.3454039>.
- Eio v1.6, <https://github.com/ocaml-multicore/eio> (README at `main`).
- Lwt 6.1.0, <https://github.com/ocsigen/lwt/releases>. The `pick`/`choose`
  semantics are from the Lwt 5.3.0 API page,
  <https://ocsigen.org/lwt/5.3.0/api/Lwt>, as quoted in search results.
- Real World OCaml, "Concurrent Programming with Async",
  <https://dev.realworldocaml.org/concurrent-programming.html>.

**Kotlin.**
- "Cancellation and timeouts",
  <https://kotlinlang.org/docs/cancellation-and-timeouts.html>.
- "Composing suspending functions",
  <https://kotlinlang.org/docs/composing-suspending-functions.html>.
- KEEP "Kotlin Coroutines",
  <https://github.com/Kotlin/KEEP/blob/master/proposals/coroutines.md>.
- Roman Elizarov, "Structured concurrency" (2018-09-12, with
  kotlinx.coroutines 0.26.0),
  <https://elizarov.medium.com/structured-concurrency-722d765aa952>.

**Go.**
- Release notes: Go 1.3, <https://go.dev/doc/go1.3>, and Go 1.14,
  <https://go.dev/doc/go1.14>.
- `errgroup` v0.23.0, <https://pkg.go.dev/golang.org/x/sync/errgroup>.

**Rust.**
- `std::future::Future`, Rust 1.98.1,
  <https://doc.rust-lang.org/std/future/trait.Future.html>.
- RFC 230, "Remove runtime" (2014-09-16),
  <https://rust-lang.github.io/rfcs/0230-remove-runtime.html>.
- withoutboats, "The Scoped Task trilemma" (2023-04-08),
  <https://without.boats/blog/the-scoped-task-trilemma/>.
- tokio 1.53.1, <https://docs.rs/tokio/latest/tokio/>.
- Brian Anderson, "Abandoning segmented stacks in Rust", rust-dev,
  2013-11-04,
  <https://mail.mozilla.org/pipermail/rust-dev/2013-November/006314.html>:
  the host no longer resolves, so it was seen only through search results.

**Java.** JEP 525, "Structured Concurrency (Sixth Preview)",
<https://openjdk.org/jeps/525>; JEP 533, <https://openjdk.org/jeps/533>.
Both were seen through search results.

**Koka.** Daan Leijen, "Structured Asynchrony with Algebraic Effects",
TyDe 2017, <https://doi.org/10.1145/3122975.3122977>. Only the abstract
was read, through search results.

**Continuations and stacks.**
- Wand, "Continuation-based Multiprocessing", LFP 1980, and Haynes,
  Friedman and Wand, "Obtaining Coroutines with Continuations", Computer
  Languages 11(3/4), 1986: as cited by PLDI '89.
- Haynes and Friedman, "Engines Build Process Abstractions", LFP 1984,
  pp. 18–24.
- Dybvig and Hieb, "Engines from Continuations", Computer Languages
  14(2), 1989, pp. 109–123, <https://doi.org/10.1016/0096-0551(89)90018-0>.
- Hieb, Dybvig and Bruggeman, "Representing Control in the Presence of
  First-Class Continuations", PLDI 1990, pp. 66–77,
  <https://doi.org/10.1145/93548.93554>.
- Bruggeman, Waddell and Dybvig, "Representing Control in the Presence
  of One-Shot Continuations", PLDI 1996, pp. 99–107,
  <https://doi.org/10.1145/249069.231395>.
- Farvardin and Reppy, "From Folklore to Fact: Comparing Implementations
  of Stacks and Continuations", PLDI 2020,
  <https://www.cs.tufts.edu/comp/150FP/archive/john-reppy/pldi20-stacks-n-conts.pdf>
  (§1 and §6 read).

**For the examples' snippets** (read 2026-09-29).
- OCaml 5.3 manual, "Language extensions: effect handlers",
  <https://ocaml.org/manual/5.3/effects.html>: the `Xchg` example and the
  `Fork`/`Yield` scheduler's handler, quoted in §2.
- Eio README at `main`, <https://github.com/ocaml-multicore/eio>: the
  `Promise.create`/`Fiber.both` example, quoted in §2.
- Rust `std::thread::scope`, Rust 1.98.1,
  <https://doc.rust-lang.org/std/thread/fn.scope.html>: §3.6's snippet
  is written after its example.
- The Go specification, go1.27 (2026-05-26), <https://go.dev/ref/spec>:
  the page was fetched, but its "Select statements" section was not in
  what was read, so §6.1's `select` is from memory.
- The Python (asyncio, trio, `contextvars`) and JavaScript (generators,
  promises, `AsyncLocalStorage`) snippets use only the APIs cited above
  under Python and Node.js; they were written for this note and not run.

**On disk.** Jouvelot and Gifford, "Reasoning about Continuations with
Control Effects", PLDI '89,
`~/Dev/LangPlay/GiffordHistory/papers/pldi89-jouvelot.pdf` (§5 on
dumping only the frames flagged by `comefrom`; related work citing
JG89a/b, W80, HFW86). Lucassen's thesis,
`~/Dev/LangPlay/GiffordHistory/papers/lucassen-1987-types-and-effects-thesis.pdf`
(ch. 6; §9.1.2 on futures, as summarized in
`type-and-effect-directions.md` §3). Larceny, `lib/Standard/tasking.sch`,
`lib/Standard/tasking-with-io.sch`, `lib/Experimental/tasking-notes.txt`
and `lib/Experimental/poll.sch` under `~/Dev/LangPlay/larceny`. In this
repo: `docs/fx26.md`; `docs/research/actors-and-distribution.md`,
`type-and-effect-directions.md`, `native-conventions.md` (step 5),
`generational-gc.md`, `places-and-regions.md`, `soundness.md` (§2.4,
§2.6, Lemma 4.9); `docs/performance.md` ("What a capture costs");
`crates/fixpt-fx26/src/check.rs` (`close_region`, `mask`);
`crates/fixpt-heap/src/heap/regions.rs`.
