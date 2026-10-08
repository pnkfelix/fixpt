# Weak references: which mechanisms, and what fixpt adopts

2026-10-08. Written after the user asked which weak-reference mechanism to
adopt ("ephemerons?? Guardians? Custodians? Is there anything in the async
io design space to inspire us here?"), once quoted data were interned in a
table on the heap (`TODO.md` §51, `crates/fixpt-heap/src/heap/intern.rs`)
that held its entries strongly. The survey below was gathered by a research
pass; the papers it downloaded are in `docs/research/papers/weak-references/`
(not committed; `SOURCES.md` there).

## Findings first

1. **Four mechanisms, three questions.** A weak reference (or weak pair)
   answers "keep this only if something else does"; an ephemeron answers
   "keep the value only while the key lives", even when the value refers
   to the key; a guardian (or will, or cleanup) answers "tell me when this
   died, so I can clean up"; a custodian answers "shut down everything this
   activity owns". The first two are about what the collector may free; the
   third about what happens after; the fourth is not about the collector
   at all.
2. **Interning needs only weak pairs.** An entry is found by a key made
   from the object itself, so no value can hold its own key alive, which is
   what ephemerons are for. And interning is invisible: two interned equal
   data are one object while both live, and once one is dead nothing can
   compare it with anything. So weak interning needs no effect.
   **Adopted** (2026-10-08): weak pairs in the collector, and the intern
   table's entries made of them.
3. **Weak-key tables need ephemerons** (a property table, a memo table for
   a pure function such as the derived equality of `polytypic.md`). Not
   yet: `TODO.md` §59.
4. **External resources want scopes, not the collector.** Every system
   surveyed that tried finalization pushes it to a last resort; the async
   designs (trio's nurseries and cancel scopes, Racket's custodians,
   io_uring's owned buffers) tie a resource's life to a scope the program
   names. FX-26's regions already reclaim everything at scope exit
   (`letrena`, `letreap`), and `async.md` §5 ties tasks to scopes: a region
   that owns resources, with their cleanups, is a custodian the type and
   effect system checks.
5. **What carries an effect is observing.** Making a weak reference is
   pure (or needs sequencing); reading one, testing a broken car, polling a
   guardian depend on when the collector ran. Haskell puts `deRefWeak` in
   `IO` for exactly that reason. In FX-26 such an operation would carry an
   effect; the transparent uses (interning, a weak cache of a pure
   function) are standard operations that never hand the reference out.

## 1. The mechanisms

**Weak pairs (Chez).** `weak-cons`, `weak-pair?`, `bwp-object?`: the car
is not traced, and when the collector proves its object unreachable it
"replaces each weak pointer to the object with … `#!bwp`"; the cdr is
strong, so weak lists work (Chez Scheme User's Guide 10, §13.2,
<https://cisco.github.io/ChezScheme/csug10.0/smgmt.html>). In the 1993
paper below a broken car became `#f`.

**Ephemerons** (Hayes, "Ephemerons: A New Finalization Mechanism",
OOPSLA '97, pp. 176-183; the idea is George Bosworth's, as Hayes says). A
key/value object whose slots are "neither weak nor strong", for the
"unreachable property" problem: with weak pairs, a value that refers to its
key keeps the entry alive. Tracing is a fixpoint: an ephemeron met is
queued, not traced; the queue is rescanned, an ephemeron whose key has been
reached traced through its value, until only unreached keys remain;
O(n·d) for d the longest chain, or O(n) with a queue per unreached key.
Hayes's ephemerons were a *finalization* mechanism: an unreached one is
signalled, and then traced. Chez (`ephemeron-cons`, 9.5, with ephemeron
hashtables), Racket (`make-ephemeron`), JavaScript (`WeakMap`) and GHC
(`mkWeak`, whose value is kept while its key is) clear instead.

**Guardians** (Dybvig, Bruggeman, Eby, "Guardians in a Generation-Based
Garbage Collector", PLDI '93, pp. 207-216). `(make-guardian)` gives G;
`(G x)` registers x; `(G)` returns one registered object found
inaccessible, or `#f`. The object is *preserved* and handed back, with no
special status: resurrection is the interface, not a hazard. What
guardians avoid is the finalizer's other problems: code run inside the
collector, critical sections, limits on what it may allocate or raise, and
the order of cleanup of shared or cyclic structures, which the program
chooses. A guarded object stays in weak cars until the program drops it
after the guardian returns it (Chez today, and Racket's wills alike).

**Cleanups (Go, Java).** Go 1.24's `runtime.AddCleanup` gives the cleanup
an argument, never the object, so there is no resurrection, the object is
reclaimed at once (a finalizer needs "at a minimum two full garbage
collection cycles"), and objects in a cycle all get their cleanups;
`SetFinalizer` is not deprecated, but "new Go code should consider using
AddCleanup instead" (<https://go.dev/blog/cleanups-and-weak>,
<https://pkg.go.dev/runtime#AddCleanup>). Java 9's `Cleaner` is the same
idea ("the cleaning action must not refer to the object being
registered"); `finalize` is deprecated for removal (JEP 421, Java 18).

**Custodians** (Flatt, Findler, Krishnamurthi, Felleisen, "Programming
Languages as Operating Systems", ICFP '99). Every thread, port and
connection is made under `current-custodian`; `custodian-shutdown-all`
closes or kills them all; custodians form a strict hierarchy, so "a
program cannot evade a shut-down command". Racket today also accounts
memory by custodian (`custodian-limit-memory`).

**Go's `unique` and `weak`.** The closest precedent for what fixpt did
first: `unique` (Go 1.23) interns comparable values, built on internal weak
pointers; `weak.Pointer` came after (Go 1.24) (<https://go.dev/blog/unique>,
<https://pkg.go.dev/weak>). Go clears weak pointers before finalizers run,
the opposite of Chez and Racket.

**JavaScript.** `WeakRef` and `FinalizationRegistry` (ES2021): "if an
application or library depends on GC cleaning up a WeakRef or calling a
finalizer … in a timely, predictable manner, it's likely to be
disappointed" (<https://github.com/tc39/proposal-weakrefs>). The spec
keeps a target `deref` returned alive until the end of the synchronous job,
and may empty, atomically, the WeakRefs, registry cells and `WeakMap`
entries of a set of objects that is not live (§9.9).

## 2. The async design space

- **Trio**: a nursery does not exit until all its tasks have; a failure
  cancels the rest; cancel scopes nest, with deadlines and shields. The
  custodian made lexical: cleanup at scope exit, not on demand.
- **io_uring under cancellation**: a borrowed buffer is unsound when the
  future is dropped mid-operation, since the kernel keeps writing, and Rust
  cannot block in `drop` ("any object can be leaked")
  (<https://without.boats/blog/io-uring/>). So the runtime owns the buffer:
  tokio-uring takes buffers by value, and a dropped in-flight operation's
  buffer moves to the driver until the completion arrives. The runtime is
  a custodian of orphaned buffers.
- **Async drop** remains open in Rust
  (<https://without.boats/blog/asynchronous-clean-up/>).
- **Erlang**: links (both ways; an exit signal, or a message with
  `trap_exit`) and monitors (one way, `{'DOWN', …}`): a guardian for
  processes, explicit and structured, not driven by the collector.

The lesson, for FX-26: a resource's end belongs to a scope the program can
see, which the region system already checks; the collector's part is the
weak structures that are invisible (interning, caches), and at most a
guardian for what escapes every scope.

## 3. What fixpt adopted: weak pairs

A weak pair is a bloblet of kind `weak-pair` (`layout::KINDS`, code 44):
field 2 the car, held weakly; field 1 the cdr, held as a pair's
(`Heap::make_weak_pair`, `weak_car`, `weak_cdr`, `set_weak_cdr`). A
bloblet, not a tagged pair, so that the collector can tell it by its
header, and an image keeps it.

The collectors (`heap.rs`, `heap/young.rs`):
- `scan_one` traces a weak pair's fields but its car (the first field it
  meets, `main + 1`), and notes the pair (`Copier::weak_pairs`). So does
  the minor collection's scan of dirty cards, for an old weak pair: a car
  stored into an old weak pair marks its card, as any store does (Chez's
  collector treats a dirty weak-pair card the same way: "skip car field
  and handle cdr field").
- Once everything live is copied, each noted car is moved on with its
  object, or, if the object was not copied, cleared to `WEAK_DEAD`; one
  that did not move (in the old space during a minor collection, in an
  arena, in the code area) is left (`update_weak_pairs`, the same rule the
  Rust-side weak references follow, `weak_moved`).
- Chez must recompute a card's state after this pass, since a weak car may
  still point into a younger generation; fixpt's nursery promotes
  everything live at once, so after a minor collection no old object points
  into the nursery and every card is clean.

The intern table's chain entries are weak pairs of the object and the next
entry. What only the table holds (a quote in code since redefined, say) is
collected; the table, hashed by address, is relinked by the first intern
after a collection, which drops the dead entries and counts the live
(`interned_relink`, `interned_count`). Tests: `crates/fixpt-heap/tests/weak.rs`.

## 4. What is left

- **Ephemerons and weak-key tables** (`TODO.md` §59): an eqtable whose
  keys are held as ephemerons, for property and memo tables; the tracing
  fixpoint in both collectors (Hayes's, or Chez's pending lists kept per
  segment).
- **Guardians or cleanups**, only for what no scope owns, as a polled
  queue (guardian) or an argument-only cleanup (Go, Java); the poll an
  effect.
- **Custodians** as regions that own resources: with the async work.
- **Observation as an effect**: a weak reference handed to programs, if
  ever, read under an effect, as Haskell's `deRefWeak` is in `IO`;
  Donnelly, Hallett and Kfoury give a semantics of weak references and a
  criterion for programs that behave deterministically ("Formal semantics
  of weak references", ISMM 2006; Hallett and Kfoury, BU tech report 2005).

## Sources

- B. Hayes, "Ephemerons: A New Finalization Mechanism", OOPSLA 1997, pp.
  176-183.
- R. K. Dybvig, C. Bruggeman, D. Eby, "Guardians in a Generation-Based
  Garbage Collector", PLDI 1993, pp. 207-216,
  <https://legacy.cs.indiana.edu/~dyb/papers/guardians-abstract.html>.
- Chez Scheme User's Guide 10, §13.2,
  <https://cisco.github.io/ChezScheme/csug10.0/smgmt.html>; release notes,
  <https://github.com/cisco/ChezScheme/blob/main/release_notes/release_notes.stex>;
  collector, <https://github.com/cisco/ChezScheme/blob/main/c/gc.c>.
- M. Flatt, R. B. Findler, S. Krishnamurthi, M. Felleisen, "Programming
  Languages as Operating Systems (or Revenge of the Son of the Lisp
  Machine)", ICFP 1999,
  <https://cs.brown.edu/~sk/Publications/Papers/Published/ffkf-mred/>.
- Racket Reference: custodians, wills and executors, weak boxes,
  ephemerons, <https://docs.racket-lang.org/reference/>.
- M. Knyszek, "New unique package", 2024, <https://go.dev/blog/unique>;
  "From unique to cleanups and weak", 2025,
  <https://go.dev/blog/cleanups-and-weak>; <https://pkg.go.dev/weak>.
- TC39, WeakRefs proposal, <https://github.com/tc39/proposal-weakrefs>;
  ECMA-262 §9.9.
- Java SE 21, `java.lang.ref`, `Cleaner`; JEP 421,
  <https://openjdk.org/jeps/421>.
- Trio reference, <https://trio.readthedocs.io/en/stable/reference-core.html>;
  boats, "Notes on io-uring", 2020, and "Asynchronous clean-up", 2024,
  <https://without.boats/>; tokio-uring, <https://docs.rs/tokio-uring/>.
- Erlang reference manual, processes,
  <https://www.erlang.org/doc/system/ref_man_processes.html>.
- S. Peyton Jones, S. Marlow, C. Elliott, "Stretching the storage manager:
  weak pointers and stable names in Haskell", IFL 1999;
  `System.Mem.Weak`, <https://hackage.haskell.org/package/base/docs/System-Mem-Weak.html>.
- K. Donnelly, J. J. Hallett, A. Kfoury, "Formal semantics of weak
  references", ISMM 2006, doi:10.1145/1133956.1133974.
