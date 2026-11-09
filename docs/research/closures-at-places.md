# Closures at places: user code in a session of its own

Design note, 2026-10-28, from a conversation with the user. Nothing is
built and nothing is decided. It proposes an answer to `TODO.md` §105
(a program's own code at run time) and Heist's R4
(`heist/docs/fx26-for-yank.md`) for the case where the editor and the
code its user writes run in two address spaces. Citations are from
memory, as are the claims about Apple's platforms; both should be
checked.

## Why two address spaces

The user wants an IDE on the headset itself: Heist on a Vision Pro.
- visionOS gives a third-party app no memory it can both write and
  execute: no JIT. Apple's own processes have it; WebKit's web content
  process is one, so JavaScript and WebAssembly run in a `WKWebView` are
  compiled.
- So Heist, compiled ahead of time (Kayak's Rust, built for
  `aarch64-apple-visionos`, tier 3), runs at native speed, but code its
  user writes on the device can only be interpreted there
  (Fixpt's cellular machine written in Rust, or the evaluator), or
  compiled to WebAssembly and run by WebKit, in another OS process.
- Fixpt's other machines write code at run time
  (`fixpt-native/src/codespace.rs`, `fixpt-memmgmt/src/exec.rs`):
  the hand-encoded cellular machine, register code, the stencils,
  `(io native)`. None runs there.

The second way puts user code in a heap the editor cannot point into.
Yank's extension, as R4 says, is closures crossing that line both ways:
user code calls the editor's procedures, and the editor keeps commands,
hooks and keymap entries that user code made and calls them later.

## What FX-26 has now

- A `(subr E (A …) R)` says nothing of where the closure is. It mentions
  regions only through `E`, and a pure one mentions none.
- A procedure is transmissible when its parameters, result and latent
  effect are (`docs/research/processes.md`, the transmissible-type rule).
  Messages share procedures by pointer, as they share I-cells and
  addresses. That needs one address space, or code that is the same
  in both.
- A process has a place of its own, `r` in `(spawn (box M r) …)`, a reap
  with the process's extent (`docs/fx26.md`, "The process's place").
- The distribution note planned sending a closure as code, verified on
  arrival (`actors-and-distribution.md`, N5).

N5 does not serve here: code sent from WebKit to the editor could only
be interpreted by the editor, and code sent the other way would be
compiled again by WebKit, losing the editor's identity for it. A
closure should stay where it was made, and its type should say where.

## The proposal: values at a place

**A located value**, `(at P T)`: a `T` that lives at place `P` and may
be held anywhere. The type is ML5's `A at w` (Murphy, Crary and Harper,
"Type-safe distributed programming with ML5", 2007; its calculus Lambda5,
with Pfenning, 2004). Its main use is a closure, `(at P (subr E (A …)
R))`, but a buffer the editor gives user code is one too: `(at P
buffer)`, usable only through procedures at `P`.

A `subr`'s own type is unchanged. "Attach a place to each closure" would
put a place in every `subr` type and make every higher-order procedure
polymorphic in it; `at` puts one only where a value crosses, which is
rare, and leaves today's types as they are.

`(at P T)` is transmissible for any `T`: what crosses is a handle, not
the value.

| form                     | what it is                                                                                     |
| ------------------------ | ---------------------------------------------------------------------------------------------- |
| `(locate p v)`           | `v`, of type `T`, as an `(at p T)`; `p` the place the code runs at                             |
| `(here x)`               | an `(at p T)`'s `T`, where the code runs at `p`; elsewhere refused                              |
| `(call-at f x …)`        | `f`, an `(at P (subr E (A …) R))`, called at `P`, from anywhere                                 |

**Where code runs.** The checker knows the place it is checking for: a
session's code runs at the session's place, the editor's at its own
(below). That is the one new thing it tracks; `here` and `locate` need
it, and at the place itself `(here (locate p v))` is `v`.

**`call-at`.** Waldo, Wyant, Wollrath and Kendall ("A Note on Distributed
Computing", Sun Labs SMLI TR-94-29, 1994): a remote call is not a local
one, and hiding the difference is the mistake. So:
- `A …` and `R` must be transmissible (a located value is);
- its effect is a send to `P`, an await, `nondet`, and the `io` atoms of
  `E`; `E` itself must be closed (no effect variable, as the
  transmissible rule asks) and may mention only regions of `P`, which
  the caller cannot see;
- its result says what can go wrong:

  ```
  (sumof (value R) (fault diagnostic) (gone unit))
  ```

  `fault` the closure failed at `P` (R4's third requirement: a failure
  as a value, with its kind, message and span); `gone` the place has
  ended, or the handle was let go.
- At `P` itself, `call-at` is a call of `(here f)`, its result still the
  sum, so that code means the same wherever it runs.

`call-at` is a send of the arguments and an I-cell for the reply, then
an await, so on one machine it is a library over `spawn`, `send` and
`icell-get`, but for the typing of the handle's slot (below).

## Sessions

A **session** is an `eval` with state (§105 option (a), as an explicit
value):

```
(session H S)        ; H a moduleof: what the host lets user code see;
                     ; S the session's place
(eval-at T s text)   ; `text` read, checked against T, run in s
  → (sumof (value T) (refused diagnostic) (fault diagnostic) (gone unit))
```

- `S` is a place with the session's extent, as a process's is. Its globals
  are a REPL's, with redefinition's rules (`docs/fx26.md`,
  "Redefinition"; re-runs wait, as at the REPL).
- `T` crosses as canonical text, as a syscall's type does
  (`docs/fx26.md`, "Syscalls"), so the session needs no shared type
  representation with the host. It must be transmissible: a command
  user code makes comes back as an `(at S (subr …))`.
- A value, not an ambient `(io session)`: an editor has several (the init
  file, `*scratch*`, a test run, untrusted code), each seeing its own
  `H`. The runtime may give a program a default one, as it gives `args`.

**The host's procedures, seen from the session.** `H`'s items are at the
editor's place, `E`. Calls from the session to them could be `call-at`s,
but that makes every `insert` in user code a sum to take apart. The two
sides are not equal: a session lives inside its host, and when the host
ends the session ends with it. So inside the session `H`'s procedures
have their own types, plus an effect atom for the crossing, `(host E)`,
and a host that has gone is a failure of the session, not a value its
code must handle. Only the host's calls into the session carry `gone`.

## Handles

- An `(at P T)` is, at run time, the place's identity, an incarnation
  (as the distribution note's node names have, so a session started
  again does not take the old one's handles), and a slot.
- The place keeps a table from slots to values, which keeps them alive.
  On the WebKit side the table is a JavaScript array holding the
  closures, or the shared `WebAssembly.Table` that compiled code calls
  through.
- **A closure or a global.** `(locate p f)` holds the value `f` has now:
  redefining `f` later does not change it, as `fx26.md` says of code
  holding an old procedure. An Emacs keymap holds a command's name, so
  that `C-x C-e` on a new definition takes effect at once. So a second
  form, `(locate-global p f)`, holds the global, and a call reads it
  then; at a redefinition at another type the handle is `fault`ed
  (broken), as a use of a broken definition is.
- On one machine (the interpreter case) a handle may be the value itself
  and `call-at` a direct call, its result put in the sum. Which a runtime
  does is its choice; the meaning is the same.

## Collection across two heaps

A handle held by the editor keeps a value alive in the session. Letting it
go needs the editor's collector to say a handle has died, and a message
to the place. Birrell et al.'s network objects did this by reference
listing ("Network Objects", SOSP 1993).
- Fixpt has weak pairs, but no guardians or cleanups
  (`docs/research/weak-references.md`, "What is left"); this needs one,
  as a polled queue of dead handles.
- A cycle through both heaps (a session's closure holding a handle to an
  editor buffer that holds the closure's handle) is never collected.
  For commands and hooks that is acceptable: they die with the session.
  The note should not promise more.
- A session that ends frees its table at once; every handle into it is
  `gone` from then on.

## What it costs: state crosses by copy

Cahoots' commands are code sent to a buffer and run on its state in its
turn (`heist/docs/cahoots-on-fx26.md`). A command at `S` cannot run on a
buffer at `E`. Either:
- the editor sends the state (a rope, products and sums, so
  transmissible) and gets the new state back, copied each way. Ropes are
  large; H3 measured copying against sharing for small messages
  (`processes.md`), not for this. Sending only what changed needs
  ropes whose chunks have identities both sides keep, which is a design
  of its own; or
- the command acts through `(at E buffer)` and `H`'s procedures, a call
  across per edit: right for `insert` and `goto-char`, slow for a
  command that walks the buffer.

This is the price of compiled user code on that platform. The
alternative is one address space: all of Heist compiled to WebAssembly
in the web content process, with its own JIT, and only the display
protocol crossing to the native renderer. That needs none of this note,
at the cost of the editor itself running as WebAssembly. Which way is
the user's to decide; both keep the session value, and `at` then has a
use only between machines (the distribution note's nodes).

## Turns and re-entry

A host that waits in `call-at` while the session calls back into `H`
waits forever unless it serves those calls meanwhile. In cahoots a turn
is a transaction run in an engine of 20 ms, and a wait inside one is
already out of place. So a call into user code is not made inside a
turn: the command's activity sends the request, ends its turn, and the
reply is the message that begins the next. Calls from the session into
`H` are then messages to the actors that own what they touch, each
handled in a turn of its own, as any other. `C-g` is the activity given
up, and a message to the session to stop it (R4's time slices, by `race`
in the session).

## Steps

1. **A prototype with no checker change.** A library: a session as a
   process with its own place, running the evaluator in FX-26; commands
   of one fixed type, `(subr E () unit)`, registered and called through
   slots. Done when R4's test passes: `(define (f x) (host-insert! x))`,
   then `(f "hi")`, the host keeping `f` and calling it later, a refusal
   and a fault both values.
2. **`at`, `locate`, `here`, `call-at` in both checkers**, the place code
   runs at tracked, handles typed by their slot's type. On one machine.
3. **`eval-at` with `T` as canonical text**, and `(host E)`.
4. **Dead handles let go**: a guardian, and the release message.
5. **The WebKit backend**: the session in a `WKWebView`, user code as
   small WebAssembly modules, the message transport over WebKit's script
   message bridge.

## Open questions

- Whether `(host E)` is one atom or `H`'s own effects with a marker; the
  REPL's speculation must never run it, as it never runs `io`.
- Whether `here` should be allowed under a `poly` over places, as
  Lambda5's `get` is, or only at a place the checker knows.
- What `fault` carries across: a diagnostic's span is in the session's
  text, which the host has (it sent it).
- Whether `(at P T)` for data (a buffer) needs `T` to be anything but a
  type the host names abstractly; probably not.
- How it meets the distribution note: a node's place is a place, so `at`
  may be its remote reference too, and N5 (code that moves) its
  complement.
