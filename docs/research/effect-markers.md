# Effect markers: properties of effects, apart from their atoms

Status: proposed 2026-11-09, in answer to kayak's request
`docs/requests/fixpt-responsive-effects.md` (kayak 40a951197, C388, on
Fixpt 13114974). Nothing built yet.

## The request, in short

kayak wants to say "this procedure stays responsive": a key handler or an
event loop's step that never waits itself. It asks for three things:

1. An atom `wait`, beside `spin` and `nondet`, that every operation that
   may block has, as well as its own atoms (`receive`, `icell-get`,
   `pselect`, `read-line`, `read-byte`, `read-bytes`, `sleep-until`,
   `process-exit`, and blocking writes). Wait-free would then mean no
   `wait` and no `spin`. `clock` would no longer share `(io clock)` with
   `sleep-until`.
2. A supertype `rep` of all evidence, which a syscall's type may name,
   so that a runtime could offer `kayak:effect-within/1`. That would tell
   a loop generic in `e` whether its handlers may wait.
3. Bounded effect variables, `(poly ((e effect (within E))) …)`, with each
   instantiation checked against the bound.

The diagnosis is right, and the third item is wanted. This note proposes a
different shape for the first two.

## An atom is two statements

An atom in a latent effect says two things at once:
- **to the caller, an upper bound**: what calling it may do, and what the
  caller must allow for;
- **to the body, a permission**: what the body is checked against, so what
  it may do.

For a capability (an atom that unlocks operations: `(io stdout)`,
`(alloc r)`, `(send R)`, `(receive r)`), the two are one fact seen from
two sides. The body is checked against the effect, and subsumption lets
callers rely on it. Permitted ⊇ performed.

A **summary** atom like the requested `wait` breaks this. It unlocks
nothing: `receive` would still need `(receive r)`. Whether code waits is
already fixed by its other atoms. So `wait` would be a property of the
effect written as if it were a capability:
- `(receive r)` without `wait` would be an effect nothing can perform;
- granting `wait` gives a body nothing it can use;
- every waiting operation would have to keep two atoms in step, by hand
  or by an implication rule.

`receive` already does this with `nondet`: it says `(maxeff (receive r)
nondet)`, and the `nondet` is implied by the `(receive r)`.

## Markers, as Rust's auto traits

Rust separates the two statements for types. A struct's fields are what
it holds. `Send` is a property, *derived* from the fields: a type is
`Send` if all its fields are, and a few primitive types opt out. No one
writes `Send` into a struct next to its fields. FX-26 already has one of
these, for types: the `sendable` kind.

The proposal does the same for effects. A **marker** is a property of an
effect, derived from its atoms by a table the language fixes:

| marker          | holds of an effect with none of                                      |
| --------------- | -------------------------------------------------------------------- |
| `nonblocking`   | the waiting atoms (below), and `wait` (the residue of masking, below) |
| `terminating`   | `spin`                                                               |
| `deterministic` | `nondet`                                                             |

kayak's wait-free is `nonblocking` and `terminating` together. Markers
are closed under `maxeff`: the join of two effects with a marker has it.
So a marker holds of an effect exactly when it holds of each of its atoms.

Unlike Rust's auto traits:
- **The table is closed.** No program can opt a capability in or out. So
  none of Rust's coherence and negative-reasoning problems arise.
  Syscalls build their effects from the existing atoms (`(io sys)`
  included), so they are covered by the same table.
- **Nothing leaks.** Rust's `impl Trait` leaks auto traits, and an async
  future's `Send` is computed from what it captures, so a change to an
  implementation can silently change its callers' types. FX-26's effects
  are declared in signatures, so a marker can change only when a
  signature does.

## Masking: why `wait` survives, as a residue

A marker computed from the atoms of a *masked* effect is unsound for
waiting. `mask_keeps` (`check.rs`) drops `(await r)` and `(receive r)`
when nothing outside the expression sees `r`. So a procedure that makes a
private I-cell, spawns a process to fill it, and awaits it has neither
atom in its effect after masking, yet it blocks until the other process
acts:

```
(letregion r
  (let ((c (the (icell int r) (make-icell))))
    (begin (spawn-filler c) (icell-get c))))   ; (await r) masked away
```

`spin`, `nondet` and `io` are safe because they have no region and are
never masked. Waiting on a region needs the same treatment. So:

- **Masking leaves a residue.** Where masking drops a waiting atom, it
  adds the region-less atom `wait`. `wait` means "waits on something
  nothing outside can see". It is never written beside a visible waiting
  atom, and nothing implies it. It is a real capability, the one a body
  has once its waiting has gone private, and it is what `nonblocking`
  rules out besides the visible atoms.
- **`spawn` is not masking.** A spawned process's waits are its own: the
  spawner does not wait for them, so the place `spawn` drops leaves no
  residue. The same goes for a `race` loser stopped at a wait.
- **The cells' verifier** must agree with the checker on where the
  residue goes, since it masks the same expressions (`facts.masked`).

This is how `nondet` already behaves ("Masking never removes it"). One
consequence, left for later: `nondet` too could become a derived marker
whose atom appears only as a masking residue. `receive` would then say
`(receive r)` alone. That would change existing types, and kayak does not
need it.

## The waiting atoms: capabilities need splitting first

For the table to work, each capability must either always wait or never
wait. Three do not:

| capability     | waits                                 | does not wait                                   |
| -------------- | ------------------------------------- | ----------------------------------------------- |
| `(io clock)`   | `sleep-until`                         | `clock`                                         |
| `(io stdin)`   | `read-line`, `read-byte`, `read-bytes` | `stdin-ready?`                                  |
| `(io process)` | `process-exit`, `process-write`       | `process-output`, `process-status`, `process-news` |

The proposal splits each: `(io sleep)` for sleeping, a separate atom for
the non-waiting stdin query, and `(io process-wait)` for the process
operations that wait. Spelling is open. The waiting atoms are then
`(receive r)`, `(await r)`, `(io sleep)`, `(io stdin)`,
`(io process-wait)`, `wait`, and whatever the next question adds.

**Which writes and files wait** is a question about table entries, not
about which operations carry a token. Under "sound by construction" the
table must be honest:
- `write-out` and `write-err` can block on a full pipe that no one reads,
  and kayak's async mode makes that a real wait. So they wait, unless the
  runtime makes them never block (buffering, with a separate flush that
  waits). The cost of the honest entry: a `nonblocking` handler cannot
  log. If kayak needs that, the buffered write is the way to provide it.
- Files: `read-file` on a FIFO blocks until a writer appears, and a
  network mount can stall. kayak's "bounded by the machine" holds only if
  the file operations refuse what is not a regular file (or a directory,
  for `list-dir`). Recommended: refuse those, and leave `fs-read` and
  `fs-write` off the waiting list.
- `pselect` is waiting by its arms' atoms (it waits for them), with
  `nondet` as now.

## Bounded effect variables (kayak's item 3)

Two kinds of bound on an effect variable:

```
(poly ((e effect (within (maxeff (send @w) (alloc @r))))) …)   ; upper bound
(poly ((e effect nonblocking terminating)) …)                  ; markers
(poly ((e effect (within E) nonblocking)) …)                   ; both
```

- **At instantiation**, both checkers check the effect given: within `E`
  by effect subtyping, and each marker by the table. Refused otherwise,
  saying which atom fails which marker.
- **In the body**, `e ≤ E` holds, and `e` has its markers. An effect
  built from `e` and atoms with the marker has the marker (closure under
  `maxeff`). So `(maxeff e (alloc @r))` is `nonblocking` if `e` is.
- **Upper bounds are needed less often than they seem.** Latent effects
  are covariant. So a loop that takes handlers of type
  `(subr (maxeff (send @w) (alloc @r)) …)` already accepts every smaller
  handler, with no `poly` (`async.md` §3.3). A bound is needed when the
  loop is generic in `e` *and* must report `e` in its own effect, as
  Lucassen's `par-map` does (P8 in `type-and-effect-directions.md`).
- **Marker bounds cover what upper bounds cannot.** "Anything that does
  not wait" is not an upper bound, because regions are open-ended:
  there is no `E` with every effect but the waiting ones below it. So the
  generic responsive loop wants `(e effect nonblocking)`, not `within`.
- **Evidence:** `(effectbound e)` would carry the markers as it carries
  the bound, and `given` would check them.

## Instead of `rep`: a test that narrows (kayak's item 2)

`rep` as asked is safe: a supertype that forgets, with nothing that
converts back, cannot forge evidence. But it does not do what kayak wants
it for:
- The question "may this handler wait?" is a marker, not an upper bound,
  so `effect-within` cannot ask it.
- The answer would be a `bool`, which does not narrow `e`. The loop would
  still have to treat a handler as if it might wait.

Proposed instead: a language form that tests evidence and narrows the
variable in the branch that passes:

```
(effect-case er
  ((nonblocking terminating) (run-inline h))   ; here e is nonblocking, terminating
  ((within (maxeff (send @w))) …)               ; here e ≤ (maxeff (send @w))
  (else (hand-to-a-process h)))
```

`er` is `(effectrep e)`. Evidence is generative and invariant, so it
names `e` exactly, and the test runs on the effect it describes at run
time. Markers are closed under `maxeff`, so evidence built from other
evidence is decided the same way. In a passing branch, `e` gets the
bound or markers, exactly as a bounded `poly` binder would. It is a
checked downcast on effects, and it reuses item 3's machinery. It needs
no syscall, no `stage`, and no change to what a syscall's type may name.

Whether to provide `rep` anyway, so that a runtime can read type text for
its own purposes, is a separate question about a capability. We would
like to know whether kayak needs it beyond this use.

## What kayak's tests need

`tests/kfx/responsive.kfx`'s handler, `(maxeff (send @srv) (alloc @r))`,
is `nonblocking` today by the table: no change is needed.
`tests/kfx-refused/responsive-handler-waits.kfx` is refused today for its
`(await @r)`, and still would be. With markers, a handler could also be
declared `nonblocking` and generic, with the refusal naming the marker.

## Order of work

Each step goes into both front ends, and the cells' verifier where it
masks.
1. Split `(io clock)`, `(io stdin)` and `(io process)`. Make the file
   operations refuse non-regular files. Fix the annotations this breaks.
2. The `wait` residue in masking (checker and verifier), with a test of
   the private I-cell example above.
3. Markers and both kinds of bound on effect variables, with their
   evidence (`effectbound`, `given`).
4. `effect-case`.
5. Later, separately: `nondet` as a derived marker.

## Open

- Spelling: `(io sleep)`, the stdin query's atom, `(io process-wait)`,
  the marker names.
- Standard-stream writes: honest-and-waiting, or a buffered non-waiting
  write.
- Whether `comefrom` (kayak lists it among waits) belongs in the table.
  A control effect's prompt is the program's own, so it is not a wait on
  another party. Our reading is that it does not.
