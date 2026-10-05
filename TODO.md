# Things deliberately left undone

Milestones live in [`PLAN.md`](PLAN.md); intentional differences from the 1987
and 1991 references live in [`docs/divergences.md`](docs/divergences.md). This
file is for the third category: things noticed *while building something else*,
judged not worth doing then, and worth doing later. Each says what it is, why it
was deferred, and where to start — because the reason is the part that goes
stale first.

Only what is still to do is here. When something is done it moves to
[`DONE.md`](DONE.md), under the same section number, so "§19" means the same
thing in both files and numbers are never reused. A section partly done is in
both files: what is left here, the finished part there. A section done
completely is only there, which is why some numbers are missing below.

---

## 1. The eager reader: what it does not read yet

The eager reader does not yet handle:
- **FX profiles.** The FX REPLs still re-read each form with the Rust
  reader.
- **Datum labels**, `#n=` and `#n#`.
- **A position for a bad bytevector element.**

What is built: `DONE.md` §1.

## 2. Integrate known primitives: Scheme, a program's own procedures, shape

**Scheme.** It cannot prove a standard binding is never reassigned: it needs
an "integrate primitives" switch or a guard that de-optimises on
redefinition.

**A program's own procedures.** The 42.5% of instructions that were call
plumbing did not all go, because only *standard* bindings are integrable. A
program's own procedures — `loop`, `fib`, `go` in the benchmark — are
`letrec`-bound, so a recursive call still costs a global load and a generic
call.

Those are immutable too. A `letrec` binding with no explicit region lives in
`@=` exactly as a standard one does, so `(set! loop …)` is the same type error,
and a self-call could compile to a direct jump rather than a dispatch. That is
the obvious next win and it is the same mechanism: one more claim through the
same channel. `fib 24` gains least from the metadata (1.17×) precisely
because it is dominated by exactly this call.

**Shape, not just annotations.** The 2026-09-21 diagnosis found three things
lost at erasure: annotations, resolution and **shape**. The first two now
travel as `%fx-note` claims. Shape does not. FX-87's eraser still lowers
`(select r a)` to `(cadr (assv 'a r))`, an assoc-list walk
(`crates/fixpt-fx87/src/erase.rs`), although the checker knows the field's
offset. The reference's own default, `*order-independent-records* = #f`, has
`desc-of-select` stash that offset and emit `(vector-ref r N)`. `tagcase`
likewise becomes a linear `case`, though the checker knows the full set of
tags. The fix is in the eraser, not the channel: lower records to vectors at
checked offsets.

What is built: `DONE.md` §2.

## 3. Patch closures instead of boxing `letrec`

Assignment conversion boxes every binding of a `letrec*` whose initialisers
capture one of them, costing an indirection on every recursive call — see
`docs/divergences.md`. Where every initialiser is syntactically a `lambda`
(overwhelmingly the common case) the closures could instead be built with their
capture slots empty and patched once all of them exist. Nothing in the encoding
stands in the way.

## 5. The larger Larceny GC workloads

`tests/gc_workloads.rs` ports GCBench, `grow` and three parts of `permsort`.
Larceny's `test/GC` also has `nboyer`/`sboyer`, `earley`, `lattice`,
`nucleic2`, `nbody`, `dynamic` and `twobit` — substantial programs that would
exercise the whole engine rather than just the collector, and which are the
natural content for M8's benchmark story. Some may need `syntax-rules` (M9).

`gcold.sch` targets old-to-young pointers and write barriers. It was left off
this list while the heap was a single-generation Cheney semispace; since
2026-09-29 there is a nursery and a card-marking write barrier (PLAN, "The
collector"), so it now has something to test.

## 6. A standard input port

There is none: input ports hold a whole file as a heap string plus a cursor,
which is what lets a port survive collection and a heap image without a dangling
descriptor. Adding stdin would reintroduce the problem that arrangement avoids,
and one more besides — the REPL's own reader and a program calling `read-char`
would be competing for the same stream, with the editor having buffered ahead.
Worth solving deliberately rather than discovering.

## 7. Line editor gaps

`crates/fixpt-cli/src/lineedit.rs`, in rough order of how much they would be
missed:

* **No `^R`** reverse history search.
* **No bracketed paste**, so pasting a large form is processed a keystroke at a
  time and echoes messily.
* **Unix only.** Raw mode is `stty`.

What is built: `DONE.md` §7.

## 8. Syntax highlighting in the REPL: what is left

In rough order of value for effort:

* **The unclosed delimiter.** `form_status` already runs, and `ReadError`
  carries a `Span`. Underlining the offender is nearly free now that colour
  exists.
* **Binding sites.** Underline where the identifier at the cursor is bound, when
  the binder is on screen — a scope walk over the current form's datum tree
  recognising `lambda`, `let`, `let*`, `letrec`, `define`, `do` and named `let`.
  Bounded work, since the "view" is one form. It cannot reach binders from
  earlier REPL forms, which are not on screen; for those, "bound global" versus
  "unknown" is the honest signal.
* **Colour by kind**, for FX-91 and FX-87 (and FX-26): their checkers know
  what is a type, an effect and a region, and nothing else in either language
  makes that distinction visible.

**Cost.** Re-parsing per keystroke is O(n), so O(n²) over a line. Fine at REPL
sizes — but highlighting is what makes per-keystroke parsing routine rather
than occasional, which is the condition under which §1's
continuation-checkpoint reader stops being a luxury.

What is built: `DONE.md` §8.

---

## 9. Delimited control: what is still not right

SRFI 226's control features: what is still approximate, and why each was
left.

- *Winding on `call/cc` and composable application is Dybvig's, not exact.*
  An abort leaves extents one at a time, cutting to each extent's own frame, so
  every `after` runs in exactly its `dynamic-wind`'s context. Applying a
  continuation instead runs the `after`/`before` thunks from the call site
  (`%continuation-apply` in the prelude), as the old code did. Making it exact
  means reinstating a continuation in stages, running each `before` with only
  the extents outside it live; the step mechanism `%abort` uses would work, run
  in the other direction.
- *`call/cc` captures the whole machine.* SRFI 226 delimits a non-composable
  continuation by the default prompt. Here it crosses prompts, as before. Since
  every input runs under a default prompt, this only shows in programs that
  install their own.
- *A composable segment's bottom marks are appended, not merged.* If the frame
  a segment is composed onto already has a mark for the same key, both are
  visible. SRFI 226 would make them one frame's marks.
- *Not implemented:* `call-with-immediate-continuation-mark`, `parameterize`
  and parameter objects (there are none yet at all), `call-in-continuation`,
  `continuation-prompt-tag` handler conventions beyond the default.
- *Fatal escapes do not unwind.* A step-limit overrun, or a hole reached where
  there is no top-level prompt, leaves the engine without running `after`
  thunks. Nothing leaks, because the mark stack is reset with the machine, but
  the thunks do not run.
- *One held hole.* `,resume` continues the most recent; reaching a new hole
  replaces it. A stack of holes needs a way to name one that does not collide
  with `,resume`'s argument.
- *FX holes are not held.* The FX dialects answer a hole by checking and by
  evaluating the siblings the effect system allows; they do not run *to* it, so
  there is no continuation to hold. Doing so needs `%hole` to have an FX type.
- *`%prompt-result`.* A prompt is installed in argument position of an identity
  primitive, which guarantees it a frame of its own in both engines. A real
  frame kind would say so directly.

**References.**
- J. Clements, M. Felleisen. *A Tail-Recursive Machine with Stack
  Inspection.* TOPLAS 26(6), 2004. The CM machine; marks without losing tail
  calls.
- M. Flatt, G. Yu, R. B. Findler, M. Felleisen. *Adding Delimited and
  Composable Control to a Production Programming Environment.* ICFP 2007.
  Prompts, composable continuations, `dynamic-wind`, dynamic binding and
  exceptions together, and how they interact.
- M. Flatt, R. K. Dybvig. *Compiler and Runtime Support for Continuation
  Marks.* PLDI 2020. The attachments-stack implementation in Chez, the
  design to copy.
- SRFI 226, *Control Features*. The specification.

What is built: `DONE.md` §9.

---

## 10. Syntax parameters: `identifier-syntax` with a `set!` rule

Not needed yet:
`identifier-syntax`'s two-clause form with a `set!` rule (R6RS), which would
let `(set! it v)` mean something.

What is built: `DONE.md` §10.

---

## 11. Speculative analysis as you type, and moving the tooling into FX

**The idea.** The eager reader reports *read* errors as they are typed. The
same should hold for expansion errors and, in FX, type and effect errors, by
analysing each form speculatively while it is still being written. Anything run
speculatively must have no effects anyone could notice, and the language that
can *check* that is FX. So the REPL's own machinery — the eager reader, and
eventually the expander — should move from Scheme into FX, where the effect
system says what may be run on every keystroke.

**What "safe to speculate" should mean.** It is not "pure". The eager reader
returns its checkpoint continuation to its caller, so its `comefrom` effect
cannot be masked. What makes it safe is that its effects are confined to
regions the caller owns: allocation, and control on its own prompt. The
criterion to aim for is no `read` or `write` on a region the REPL shares with
the user's program.

**Left, in order.**
1. Speculative `syntax-rules` expansion for Scheme, against a throwaway copy
   of the expander state. Stop at procedural macros, which run arbitrary
   Scheme.
2. The expander and the speculative checker in FX-26.
3. Carrying more of FX-26's facts (region and control claims) through the
   lowering; and the shape loss in FX-87's eraser (§2).

What is built: `DONE.md` §11.

---

## 12. What the benchmark ports found hard to write (2026-09-29)

Nine agents ported 87 benchmarks (`scheme-bench/`, `mllang-bench/fx/`);
each header says what its port worked around. The same things came up
in batch after batch. In `PLAN.md` they are queue item Q11; the bigger
ones (identity, integers, floats, unions) are items of their own.

- **`define-rec` and the globals its members read.** A local `letrec` now
  infers them; `define-rec` still needs every global read, transitively,
  datatype constructors included, named in each member's effect (a
  `define-rec*`, or the same inference).
- **One answer type per prompt tag.** OCaml exceptions caught at several
  types need a wrapping sum, allocated at every `handle`; and a prompt
  rarely masks `goto` when a free variable's type mentions the tag's
  region, so helpers that abort must be bound inside the prompt body.
  (Proposed: a note on tags whose prompts choose their answer type.)
  Waiting on the user.
- **`quote` takes only symbols.** Constant lists of numbers, strings or
  booleans become `list` calls or `cons` chains, or an in-file reader.
  Quoted literals typed `(listof T acyclic)` would do (and §17). Waiting on
  the user.
- **Names.** `sum` is reserved; defining `get`, `null?` or `pair?`
  silently shadows the standard one for the rest of the program. Waiting on
  the user.

What is built: `DONE.md` §12.

## 13. Checker limitations the ports met

Each has a small reproduction in the port that met it:
- A `cons` in one branch of an `if` gets a fresh region instead of the one
  the other branch or the expected type fixes; a lambda passed to a
  polymorphic procedure is not checked against the solved result type. (The
  `let` case of the same is decided: left as it is.)
- Facts through the disjunctive side of `or` and `and` (the then of an `or`,
  the else of an `and`): `(if (or (= n 0) (null? xs)) …)` learns nothing in
  its then. Waits on logical types and occurrence typing, PLAN Q7.

What is built: `DONE.md` §13.

## 14. Standard operations the ports wrote themselves: the rest

- `map`, `for-each` and `fold`, which take procedures and so cannot be
  runtime primitives: they wait on a standard prelude written in FX-26
  (§22).
- `string-ci<?`.
- A `make-array` with no fill element.
- An n-ary `string-append` (PLAN Q13, O8).
- A mutable string, or an array of chars to a string without a list.

Some become generic operations by dictionary (`PLAN.md` Q8).

What is built: `DONE.md` §14.

## 15. Tools the ports wished for

- **Inner lambdas named by their binding.** A global defined as a lambda
  names its word now (`DONE.md` §15); an inner lambda is still named only
  by a byte offset (`lambda@59`), in profiles too. Name it by the `let` or
  `letrec` binding it has and the global it is in, `k-check/go@59`, in
  both compilers alike, since their words must agree, and in register
  code's. And the native REPL compiles a definition as a thunk, `(lambda
  () init)`, so its own lambda is an inner one there: name it for the
  definition too.
- **Start-up that grows with the program.** Before the front end was cached,
  native start-up was 2.9–3.5 s before the first iteration for `boyer`,
  `ratio-regions`, `tyan`, and 6.3 s for `parsing` with its 28 KB string.
  The front end's part is gone (0.19 s, `DONE.md` §21); what grows with the
  program is its own checking and compiling: separate compilation (`PLAN.md`
  Q9) and faster checking would both help. Re-measure first.

What is built: `DONE.md` §15.

## 16. FX source indentation (the user's, 2026-09-29)

The lint (`fixpt_tidy`) should check that `.fx` code is indented as Lisp and Scheme are: a form's
arguments under its first argument or its body indented two past its head
(`define`, `lambda`, `let`, `tagcase`, `cond` and the like), and an `if`'s
branches under its test. The user found an `if` whose else branch, itself an
`if`, sat at its parent's column (`k-synth-app-plain`, now a `cond`). An
indenter in `sexp-edit` would compute what the lint compares against.
`fx26-mode` (`editors/emacs/`) now indents as the repository does, and
re-indenting the front end with it changes 3% of the lines: those are what
the lint would report first, and the two indenters should agree.

What is built: `DONE.md` §16.

## 17. `(list CONST …)` as a constant (the user's, 2026-09-29)

The register compilers' `r_const` (and the FX-26 mirror) should recognise
`(list c …)` whose elements are all constants as a constant itself: a
frozen list made once, at compile time, as sums and products of constants
are. The type allows it: `list` gives `(listof T acyclic)`, which cannot
be written, and FX-26 has no `eq?`, so no run can tell a shared list from
a fresh one. Today each call makes its pairs at run time (inline, natively).
The rewrite of code and benchmarks to use `list` will turn up constant
lists, which is where this pays.

## 19. `eq?`: what is left (PLAN Q5)

- maybe an equality kind, as SML's `''a`, to refuse `eq?` on procedures;
- tables keyed by bloblets;
- `uniqueof` for interning, and the two-level tables, both below;
- maybe never (the user's, 2026-09-30), an `eqv?` as R7RS has it (numbers
  and characters by value, otherwise `eq?`), for tables keyed by any value
  (PLAN.md "Next", item 11).

**Later: `uniqueof`, for interning** (the user's, 2026-09-30). Interning
(hash-consing) needs exact identity, so that `eq?` is structural equality,
and contents read purely, so that interned values act as values. Today
each is had only without the other: immutable data reads purely, but
`eq?` of it is only "`#t` if equal"; a bloblet never written has exact
identity, but each read costs `(read r)`, which spreads to everything that
looks at the structure (a checker's types, say), and it is not `data`.
Symbols have both, as a special case. FX-87 and FX-91 had the general one
(`GiffordHistory/mit-psrg-fx/fx87/dist/standard.scm`, lines 225–244;
`crates/fixpt-fx91/src/fx-module.fx`):
- `(uniqueof t)`, a standard generative type;
  `unique : (subr (alloc @uniqueof) (t) (uniqueof t))`, `value` pure, and
  `eq?` exact on it.
- The allocation is at a global region, as FX-87's `@uniqueof`, not a
  region parameter: a `letregion` or `letfreeze` could mask an allocation
  at `r`, leaving a pure expression a compiler may fold or merge, which
  exact identity forbids. (Our reading; the sources give no reason.)
  FX-91's `init` effect does the same work.
- An interning table: `intern`, given a hash and an equality on `t` (a
  dictionary), gives the existing node or makes one with `unique`; its
  effect `(alloc @uniqueof)` and the table's region's.
- Weak references, or an interning table keeps every node it made alive.
  The heap has them since 2026-10-05 (`Heap::weak_add`, for collecting the
  REPL's code); FX-26 does not yet.

**Later: an `eqtable` in two tablets, as Larceny's** (the user's,
2026-09-30; the single stamp is fine for now). With one stamp, the first
operation after any collection relinks every entry, though a minor
collection moves none of the old keys: a large, long-lived table used in
a loop that allocates pays O(entries) every nursery's worth (8 MB). Our
heap suits the split: a minor collection promotes everything live, so old
keys move only at a major one, and every young key has left the nursery
after one minor collection; the heap counts the two apart (`gc_count`,
`minor_count`).
- An old tablet stamped with the major count, a young one with the total.
- A key goes into the young tablet if it is in the nursery (the heap
  would need a cheap test for that), otherwise the old.
- On a stale stamp: after a minor collection, rehash only the young
  tablet, its entries into the old; after a major one, both.
- Check whether a collection ever moves what a `letrena` region holds,
  before its keys count as old.
- First, a benchmark: a million old keys looked up in a loop that
  allocates, to show the cost now and that the split removes it.

What is built: `DONE.md` §19.

## 20. Shape conflicts during inference are errors, and checking goes on (the user's, 2026-09-29)

A polymorphic call's result, then its arguments, are checked by outermost
shape before any binder is found unsolved. What is left: conflicts below
the outermost shape, the hint for `list`, and checking on after an error.

The problem is general, not `list`'s or `cons`'s (the user's point). `unify`
walks a pattern against an actual type only to solve unknowns, and says
nothing when their shapes differ. Every use of it in inference ignores such
a conflict. In `infer.rs` those are:
- the expected type against the result;
- each argument against its parameter, in both passes;
- a polymorphic argument instantiated at its parameter;
- `instantiate_against` (a polymorphic variable at an expected type).

`k-unify`'s uses in the FX-26 checker are the same. Any polymorphic call can
show it: `(car xs)` where a `string` is wanted and `xs` holds ints;
`(map f xs)` where an `int` is wanted; a projection at the wrong type. Below
the outermost shape, the error then comes from whatever fails next, an
unknown not solved or a later subtype check, not from the conflict itself.

To do:
1. **Make `unify` report a shape conflict** at any depth: a type constructor
   against a different one, as opposed to an unknown merely left unsolved.
   Each of its uses should then report it at once, as the mismatch it is,
   naming what was being matched: "argument 2 is a pair, `(pairof int ? r)`,
   where an `int` is expected". No choice of the unknowns could make a pair an
   `int`. Unsolved unknowns stay a hint, as now. (Alternatively, defer "not
   yet known" errors until the result has been checked against the context;
   reporting at once is simpler and names the right place.) Then add hints
   where a common mistake has an obvious repair, such as the standard `list`
   given a `cons` or `list` argument: "did you mean `(cons 1 (cons 2
   nil))`, or `(list 1 2)`?"
2. **Keep checking after an error**, to report the errors that follow from the
   same mistake, which often point at the true one. Both checkers now stop at
   the first error, because failures are returned. Going on needs:
   - errors collected, not returned;
   - a failed expression given a stand-in type that unifies with anything
     and is itself reported no further, so that one mistake does not cascade
     into noise;
   - both checkers agreeing on the list of errors, not only on the first.

What is built: `DONE.md` §20.

## 21. Verified after: certificates (the user's, 2026-09-30)

The user asked whether type and effect information carried in the code would
let the check be done once, the code cached, and later passes merely verify
it.

1. **Verifiable register code, for separate compilation (PLAN Q9)**:
   annotations a verifier checks in one linear pass, as the JVM's stack
   maps, WebAssembly's validation, Typed Assembly Language and
   proof-carrying code do. In order of difficulty:
   - types of registers and slots at entry and at branch targets;
   - each word's latent effect, the instructions' effects summed within it;
   - regions (entered and left, `letfreeze`, `acyclic`), which register
     code now forgets: typed as capabilities (Walker, Crary and
     Morrisett), a design, not an extension;
   - termination, below.
   The verifier joins the checkers in what must be right; the soundness
   notes would then need "verified code is safe", not only "checked source
   is".
2. **Termination as a checkable proof**, so that the size-change search is
   not trusted:
   - each edge of a call's graph with its local reason (a `cdr` of a
     parameter at `acyclic`; `n - 1` under a test bounding `n` below), which
     a verifier checks against the code and its types (regions first);
   - the closure's success as a ranking function, lexicographic in
     practice (Lee, "Ranking functions for size-change termination",
     TOPLAS 2009: every group that passes has one, possibly large), checked
     by one pass over the call edges; `up`'s ranking is `bound − i`;
   - where no small ranking is found, the graphs themselves, the verifier
     redoing the closure under the same limit (`MOST_GRAPHS`).
   First, cheaply: have `terminate.rs` try to extract a lexicographic
   ranking from each group that passes, over the test programs, the front
   end and the benchmark ports, and report those it cannot.

What is built: `DONE.md` §21.

## 22. A prelude, and a standard library in FX-26, after modules (the user's, 2026-09-30)

The user wants as much as can be moved out of Rust into FX-26: `map`,
`for-each` and `fold` first (they take procedures, so they cannot be
runtime primitives, which cannot call back into FX-26), then what is a
primitive today only for want of a library (`append`, `reverse`,
`array->list`, `list->array`, `max`, `min`, `zero?`, the comparisons), one
at a time, each kept only if native code stays in the ballpark.

**Waits on modules** (the user's): a prelude's names must not mix with the
REPL's globals. A module would give it separate names, exports that
cannot be reassigned (so that using `map` is a constant, adding no `(read
(globals map))` to a caller's effect, as a global would), and one check
and compilation, cached as the front end's register code is (Q9: `(unit
…)` files with `.fxi` interfaces). The prelude is then the first module
every program imports. Open with the user: first-class modules, as
FX-91's, or second-class units; how the REPL opens one. (Since
2026-10-01 first-class modules exist, PLAN Q12's M1–M7, `load-module`
among them; units and their cached compilation, Q9, do not.)

What was measured and found (2026-09-30), for when it is built:
- **Native speed.** `append`, a list's length and `max` written in FX-26
  against the Rust primitives, 20,000 rounds over 1000-element lists:
  0.380 s against 0.355 s, about 7% slower, the same allocation (44.7 M
  words) and collections. In the ballpark.
- **Termination without `spin`.** A walk of a list at a writable region
  needs `spin` (it may have been made cyclic), where a primitive checks for
  a cycle and fails instead. A library walk avoids it in two phases, one
  `letrec` group: first a fuel of, say, 1024 steps counted down; only if
  the list is longer, the rest's length by a cycle-checking pass
  (`list-length`), then that many steps. Each loop counts down a natural
  and the first hands over to the second once, so size-change accepts it:
  the type is `(subr (read @l) (ints) int)`, as a primitive's. Lists under
  the threshold pay a counter; longer ones one more pass over the rest; a
  cycle always passes the threshold and fails as the primitives do. If the
  procedure mapped lengthens the list, the second phase stops at the
  length it found. (Resetting the fuel within one procedure does not
  check: that call makes nothing smaller.) Prototype:
  `docs/research/examples/fuel-walk.fx`.
- **Step limits.** A primitive is one step; a library procedure is every
  step it takes, so a program near FX-26's default limit (20M) may need
  more fuel than before. Only interpreted paths count.
- **Stack depth.** A naive recursive `append` recurses as deep as the list
  is long; library procedures that build lists should use an accumulator
  and reverse, so that a long list cannot overflow the native stack.

## 23. What trailers cost fields-only bloblets: measure, someday (the user's, 2026-09-30)

Not now; a measurement to take at some point. Nearly every bloblet is
made with a trailer, fields-only data too (sums, products, records: a
zero-length suffix): a 2-field sum is 4 words where it could be 3.
Statically typed code reaching a known field never needs the header; the
trailer serves the collector and dynamic checks (`docs/object-model.md`,
"The fast path: the trailer"). The one bloblet without one, the
`eqtable` record (`fixpt-runtime` `eqtable.rs`), lacks it by oversight.

The measurement, or something like it: on the scheme-bench and
mllang-bench ports, how many allocations are fields-only, and what share
of words allocated their trailers are. Only if that share is large is
either change worth weighing:
- drop the trailer where the layout is static, and let the collector and
  dynamic accessors take the backward scan;
- or point at the header for fields-only bloblets, reviving tag `010`
  (`layout.rs`: "retired: pointed at an object's header"), chosen per
  object at allocation and kept for its life, so that each object has one
  pointer form and `eq?` stays a comparison of bits. Field offsets then
  do not depend on *F*. The cost is two object tags wherever one is
  tested. Find first why the uniform suffix pointer won when that tag was
  retired.

## 24. A peephole pass over register code, if the frame traffic is worth it (the user's, 2026-10-01)

In each register compiler (the Rust one, `cellular/regcode.rs`, and the
FX-26 one, `regcode*.fx`, word for word), over the items made before they
are assembled, where branches still go to labels and nothing needs moving:
- `store k s … load j s` becomes `movereg k j`, and `stack s` becomes
  `reg k`, where REGk is untouched between (no call, no call-out, no
  write of it);
- a `load j s` of the slot REGj was just stored to goes;
- a store to a slot never read after it goes;
- `save` and `pop` go once no slot is used.

This is most of what keeping parameters in registers until the first call
would buy in procedures that keep a frame, without changing how either
compiler generates code. A peephole cannot reorder, so shuffles whose
values are fetched after their registers are overwritten keep the frame;
those are what tail calls in leaves (2026-10-01, `docs/performance.md`)
already handle in the generators.

First, the data: what share of the instructions native code runs are a
frame's loads, stores, saves and pops. Tail calls in leaves removed this
kind of work and measured nothing, so build the pass only if the share is
large. Register code runs only on the native machines, which have no
counters; the ways in:
- `FIXPT_PROFILE` on the Rust cellular machine counts cells by word. The
  stack code's slot cells are a proxy for register code's frame traffic,
  not the same thing.
- A counting build of `direct.rs`, an increment per frame `ldr`/`str`
  and per instruction run, behind a feature; or a small register code
  interpreter in Rust, written only to count (exact, and slow).

## 25. Emacs: an LSP server, a REPL that lasts (the user's, 2026-10-05; PLAN Q14)

The user edits in Emacs, stock 30.2 with no configuration of its own:
`eglot`, `flymake`, `eldoc`, `xref`, `completion-at-point` and
`project.el` built in, `project.el` already knowing this repository. So
the most for the least Elisp is an LSP server that `eglot` drives, beside
a small major mode and a comint REPL. After `fx26-mode`:

2. **`fixpt lsp`.** JSON read and written by hand (`fixpt` has no external
   crates); diagnostics from both checkers with start and end, in
   characters (Emacs counts characters; our messages use `…`); hover with
   the type and effect at point, which needs the checker to keep types by
   span (it keeps only effects by span, `Checker::effect_summaries`);
   definitions' spans for `xref`; names in scope for completion. The
   speculative checker (`fixpt-cli/src/speculate.rs`) already checks
   half-typed forms and believes only errors about finished subforms: what
   diagnostics on each keystroke want.
3. **The rest of what a REPL running all day needs.** Output, results,
   errors and notes kept apart (tagged, or `--format sexp`, which Elisp's
   `read` takes as is); `C-c C-c` (SIGINT) stopping a running form, by the
   resumable fuel trap of §26.

Deferred because: the user is to use step 1 first, to learn what they
actually reach for before the server is built.

What is built: `DONE.md` §25.

## 26. Debugging compiled code: names for `lldb`, then decide (the user's, 2026-10-05; PLAN Q15)

`docs/research/debugging.md`. `lldb` already unwinds through native
frames (verified); every compiled frame is a bare address. In order:
names through the GDB JIT interface (in-memory Mach-O objects with
symbols, the registry `fixpt-native/src/faults.rs` keeps under
`FIXPT_FAULTS` made always on); source spans carried through both
compilers (for `lldb`'s lines and for our own debugger alike, and for
run-time errors' locations); then the user decides between `lldb` lines
and formatters, and a debugger of our own in the REPL, whose first piece
would be a fuel trap that calls out and resumes rather than abandoning
the run (also `^C` for §25, and a sampling point for a profiler).

Deferred because: the user is not yet sure which debugger they want; the
first two steps serve both.

## 27. The collector's next spaces: static, large objects, and regions that reclaim everything (the user's, 2026-10-05; PLAN Q16)

What the heap has today (`crates/fixpt-heap/src/heap.rs`): a nursery,
minor collections promoting into one old semispace through a card-marking
write barrier; major collections a Cheney copy of everything live; the
regions' arenas and reaps; and the non-moving code area. What it lacks:

- **A static area.** What lives forever (a loaded image: the standard
  library, the FX-26 front end the REPL loads) is in the old space, copied
  by every major collection. The user's idea: a static area, never
  collected, with a remembered set of its own for what it points into the
  collected generations. Larceny has a static area
  (`~/Dev/LangPlay/accomplice`, `src/Rts/Sys/static-heap.c`): to read
  before designing ours.
- **A large-object space.** Every object is bump-allocated and copied,
  however big. Past a size, an object would get blocks of its own (whole
  pages), never moved: swept when the heap owns it.
- **Regions that reclaim everything they allocated.** The user's
  semantics for `letrena` and `letreap`: leaving the scope reclaims at
  once every object still allocated in it. Today
  (`heap/regions.rs`, its module comment) an object bigger than a chunk
  (64 KiB), or one allocated once the region's area is full, goes to the
  heap instead, to be reclaimed only when a collection finds it dead. With
  a large-object space, a large object allocated in a region is owned by
  the region and freed with its chunks when the scope ends (a reap's
  address range kept back, as its chunks are, until a collection finds no
  reference into it; its pages given back at once). The area being full
  (2^31 words reserved) is then an out-of-memory error, not a fallback.

Deferred because: a design to agree with the user first; each changes the
collector's core.

## 28. Introspecting the heap from inside: SRO with referrers, typed (the user's, 2026-10-05; PLAN Q15)

The retention leak of 2026-10-05 (PLAN Q13, O2) was found by asking the
heap, from Rust, who refers to what: `Heap::sro_referrers(kind, N, …)`,
the user's generalisation of SRO, gives every reachable object up to N of
its referrers (an object and field, or a root), or "more than N"; one
trace, no target. Walking back from every object of a kind (all live
cellular words, say) and tallying what the walks pass through finds what
holds things, without knowing beforehand what should be dead.

1. **From the Scheme REPL.** `%sro-referrers kind limit` (and `%path-to
   obj`), as `%sro` is an engine operation (`fixpt-runtime/src/prim.rs`:
   only the engine knows its stacks), and a test that finds the
   `c-made-now` leak again from Scheme, against the old compiler.
2. **From FX-26, typed.** What is expressible now: each object as an
   opaque mirror, `heap-object`, a standard type as `identity` and
   `eqtable` are (identity, its kind, its field count; holding a weak
   reference, so asking does not keep the answer alive); a referrer as a
   `sumof` (root, global, symbol, a field of a mirror, many); the table in
   a region the caller names, an arena say. What is not: the effect.
   Introspection reads every region, private ones too, which masking says
   no one outside can observe; and its answer depends on reachability,
   which collection timing and the optimizer (inlining, CSE, constants made
   once) change. So a new effect atom, `(introspect)`:
   - never masked: a function that introspects is never pure, whatever it
     allocates privately;
   - in effect summaries with `comefrom` and global writes, so that no
     transformation moves, merges or drops across it;
   - outside the formal core's soundness claim, as `datum`'s acyclicity
     is by contract (A3), or given a semantics there that says what it may
     observe.
3. **What delimits it.** Who may introspect what, so that a library's
   private regions or abstract types are not laid open to any caller.
   Racket's answers, *from memory, to check* (a research agent may read
   the Racket reference): **inspectors** (`make-inspector`,
   `current-inspector`) make a struct transparent only to an inspector
   superior to the one it was made under, and reflection opaque to others;
   code inspectors the same for compiled code. **Custodians** group and
   shut down resources (threads, ports) and account and limit memory per
   group. **Guardians** (Chez Scheme's; Racket's wills and executors) say
   when an object has become unreachable, which our weak references
   already do in part. For FX-26 the question is how an inspector-like
   capability shows in types: perhaps `(introspect r)` on a region (an
   inspector as a region one must be given), so that what a scope
   allocates privately stays out of reach unless it hands the capability
   out.

Deferred because: the debugger (§26) is the first client; item 1 is small
and could come first.

## 32. Remove `,redefine b|r` (the user's, 2026-10-05)

`,redefine b|r` says ahead what the next redefinition that would break
definitions does, and `ask_redefine` asks it at a terminal
(`fixpt-cli/src/fx26.rs`; `Fx26Session::next_redefine`, `Redefine`). At
the REPL re-runs now wait (`DONE.md` §29), so no redefinition breaks
anything there, and neither is ever reached. Remove the command, the
question and their help line; keep `Redefine` only if a session that
re-runs at once still wants to refuse (the `tests/redefine.rs` cases
`keeping_a_value_and_refusing` use it), else remove it too, and the
paragraph of `docs/fx26.md`, "Redefinition", that describes it.

Deferred because: the user's choice; nothing is wrong meanwhile.

## 33. Shape and how a type is defined: two axes, two kinds (the user's, 2026-10-05)

`docs/research/shapes.md`, "Two axes, not one". The shape of the run-time
values (flat ≤ tree, no sharing, perhaps `linear` ≤ acyclic ≤ graphic,
today's `data`, perhaps `serial` ≤ a top with functions and generative types, which cannot be sent over the
wire) is one property; how the type itself is defined (PolyP's
fixed points of one-parameter functors ≤ regular ≤ `type`, purely static,
with casts of no run-time effect between definitions of the same
structure) is another. `data` mixes them today. To do: name both, say how
each is written in type expressions and how they compose, and where each
is checked.

Deferred because: the user's, to think through before designing; it bears
on Q8's generic operations and on shapes' syntax, both open.

## 34. Private regions shared by two files: is the licence still sound? (the user's, 2026-10-05)

Since `DONE.md` §30, a region declared private again stands for the one
the program already has, so that a file loaded again is the same program.
But two different files loaded into one REPL that both declare `@q`
private now share it. `private-regions` is what the licence (`licence.rs`;
`docs/fx26.md`, "A licence is masking relative to an observer") rests on:
what a program does to its own regions is masked from everything outside
it, by construction, since nothing else can name them. That is what lets
the REPL run the eager reader's entry points speculatively, as each
character is typed. With `@q` shared, the second file's code can read what
the first's wrote, which the first's licence called unobservable.

To check:
- whether anything relies on it beyond the speculation driver (masking of
  private regions' effects in types; effect summaries; the compilers);
- whether a counterexample exists: a licensed expression of file A whose
  run, speculative, is observed by file B through a shared `@q`;
- if so, the fix: key a private region by the file that declares it (its
  path, or its `load-module` identity), so that the same file loaded again
  gets its regions back and another file gets its own; or refuse a second
  file's declaration of a name already private.

Deferred because: the user's question, to answer before the REPL relies
on reloads of more than one file.

**Where it is going (2026-10-05, with the user).** The fix is to move the
front end's files, and programs like `okasaki.fx`, into modules, a file at
a time, with only the program that assembles them declaring private
regions. Two ways for a module to reach the regions its state is in were
weighed, both working today:
- **Regions as parameters**: the file a `plambda` over its regions whose
  body is a thunk building the module, `(plambda ((t region)) (lambda ()
  (module …)))`, instantiated by the program with its own (checked: both
  checkers, both paths). Any number of instances; loadable with
  `load-module`, which sees only the standard environment; an interface
  that stands alone, as separate compilation (Q9) wants. The cost: `@t`
  becomes `t` in the file's text.
- **Regions as program-wide names**: one top-level `(private-regions @t
  …)` ahead of the files, each an inline `(define m (module …))` that names
  `@t` directly. No change to the files' text beyond the wrapper; one
  instance; not loadable by `load-module` (`@t` is unbound there).

**Chosen first: program-wide names** (the user's). **A wart to keep in
mind**: modules depend on ambient region names, so they cannot be
loaded, instantiated twice or compiled apart; and KFX26
(`docs/research/kfx26.md`, "Decisions to make first", 1) renders a
phase's state as one `&mut State`, which a region parameter is and an
ambient region is not (a `static`, in Rust). KFX26's plan may well decide
for parameters; revisit then, a file at a time.

The other blockers to moving files into modules, found surveying the
front end (`fixpt front-end-files`): `define-datatype` in `module` forms
(25 in 8 files); `define-effect` in modules, and effect abbreviations
exported (31 in 9); `define*` in modules (33 in 13); top-level `(set hook
impl)` forward references between files (16 in 7). A first pilot,
`table.fx`, needs none of them.

## 35. Provenance in the names of our code (the user's, 2026-10-05)

`FIXPT_SYMBOLS` names (`docs/performance.md`, "Profiling with `sample`")
say what kind of code a frame is (`word`, `register word`, `native`, the
machines' routines and stubs), not which compiler made it (the Rust one or
the one written in FX-26), which assembler placed it (`assemble_word` or
`native.fx`), nor how (inlining, specialization, versions). A profile
comparing the oracles with the FX-26 pieces wants that. The map's name is
free text, so the cheap form is a tag, `k-check [register code; FX-26
compiler; Rust assembler]`; the word records none of it, so it needs a
field on the word, or a tag given to `install` by whoever assembled it.

Deferred because: names first; add provenance when a profile needs to
tell the two apart.

## 36. A Scheme session recompiles its whole program at every evaluation (found 2026-10-05)

`Session::eval_forms_raw` keeps one program arena for the session; each
evaluation expands the new forms into it, then runs `fixpt_core::analyze`
over all of it and `Prepared::update`, which compiles all of it again
(`build_thunk` → `compile` → `assign::convert`, which clones it). So the
k-th evaluation costs in proportion to everything evaluated before it, and
a session of N evaluations is quadratic. Loading the lowered front end
form by form was 3 s of every session's start until it was done in one
evaluation (`docs/performance.md`, "Loading the lowered front end in one
evaluation"); the Scheme REPL, and anything that evaluates form by form,
still pays it. Compile only the new top-level forms, against what earlier
ones defined (their closures already hold their own code, as `update`'s
comment says), and analyze only them.

Deferred because: the front end's loading, the cost the suite paid, is
fixed; this is the general case.

## 37. A module's definitions see each other, as FX-91's (the user's, 2026-10-05)

In FX-26 a module's items are read in order, each seeing those before
it, and a definition does not see its own name: recursion needs
`(define-rec (f T e) …)`, even for one procedure. FX-26's own top level
differs (a typed `define` of a lambda sees itself), and so does FX-91,
whose report (§2.3.11, `module`) makes a module's values "successively
evaluated and … mutually recursive": every definition's type is in scope
in every definition. Found moving `table.fx` into a module (§34).

**The design (agreed with the user).**
- Every definition in a module whose value is a lambda (under `the`,
  `plambda`, conventions) and whose type is written is visible everywhere
  in the module, itself included: together they are one recursive group,
  made first. `define-rec` stays accepted, and is no longer needed.
- Every other definition is visible only after it, and its initializer
  may read only definitions before it; it may name the group's lambdas
  anywhere.
- **The initialization hazard.** FX-91's dynamic semantics is stuck when
  an initializer reaches a definition not yet evaluated, and our FX-91
  port fails at run time ("f is used before it is defined") although the
  module's type says pure: `(module (define a (f)) (define f (lambda ()
  b)) (define b 1))`. FX-26 refuses it statically, by reachability: for
  each non-lambda definition, the lambdas its initializer may reach (those
  it names, those they name, and those named by the initializers of
  earlier definitions it reads, since a value may carry a closure) must
  read no non-lambda definition at or after it. Lambdas' positions never
  matter; a module without a genuine initialization cycle is accepted
  once its non-lambda definitions are in dependency order, and the error
  names the definition to move earlier. Conservative where a value only
  stores a closure (`(define handlers (list f g))` with `f` reading
  `handlers`): rejected, though it would run; pass the table as an
  argument, or fill it through a ref after.
- Forward references need written types (as `define-rec`'s); FX-91 also
  infers mutually recursive untyped definitions, which FX-26 does not.
- A first rule, refusing any lambda's read of a non-lambda definition
  after the first that runs module code, was dropped: it refuses the
  common, safe pattern of state built by the module's own procedures and
  read by others, and no reordering fixes it.

Everywhere: both checkers (the rule in both, its message the same), the
lowering, both compilers and the evaluator (the group made first, then
the rest in order). Tests: the stuck FX-91 module refused, saying which
definition; the `build`/`std`/`lookup` pattern accepted; self- and mutual
recursion without `define-rec`; the `handlers` case refused.

Deferred because: just designed; then the pilot (§34) goes on without
its `define-rec`s.
