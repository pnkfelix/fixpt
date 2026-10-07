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

- **The native REPL's definitions named.** Inner lambdas are named within
  their definitions now (`DONE.md` §15), but the native REPL compiles a
  definition as a thunk, `(lambda () init)`, so its words are
  `lambda@N` and `lambda/lambda@N` there. Name them for the definition by
  telling the compiler, not by rewriting the text: bound by a `let`, the
  definition compiled differently, and no longer inlined
  (`direct.rs`, `inlined_calls_see_a_redefinition`).
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

**The pilot, done (2026-10-05): `table.fx` is a module.** Its six type
abbreviations stay at the top level, where it and other files name them;
its procedures are `(define tables (module …))`; the seven names other
files (and `tests/table.rs`) use are re-exported, `(define table-ref
(with tables table-ref))`, and its helpers stay inside. No other file
changed. Both checkers, both compilers, the bootstrap fixpoints and the
register-code cache all hold; the native REPL's 20 reloads of
`okasaki.fx` print the same. The self-compile, three runs each, the
module against the file as it was: check 1.214–1.221 s against
1.213–1.236 s, compile 0.360–0.364 s against 0.369–0.376 s, so no cost
measurable. What it found:
- a module's `define` did not see its own name: fixed, a module's values
  now see each other as a `letrec*`'s (`DONE.md` §37);
- a parameterised type re-exported, `(define-type (table (k type) …)
  ((select tables table) k v r))`, failed when used, "`r` is not a type",
  in both checkers: a region parameter bound while a family expands was
  not read as a region where the head was a `select`. Fixed (2026-10-05),
  and `(define-type table (select tables table))` now names the family
  itself, applied as the `select` is (`parse_type_node`, `k-select-alias`;
  tests `modules/family-alias.fx`, `modules/family-region-param.fx`). The
  types can move into the module.

**The pilot, again (2026-10-05).** `table.fx`'s six types are now inside
`tables`, its three one-member `define-rec`s plain `define`s (§37), and
the one type other files name re-exported, `(define-type table (select
tables table))`. The self-compile as register code, back to back, three
runs before and six after (`tests/bootstrap.rs`, `comparison`): check
1.21–1.22 s against 1.23–1.24 s, about 1.5% slower; compile 0.15 s both.
Probably each use of `(table …)` elsewhere now going through a `select`
resolved at its use; not looked into.

**First of the files that need nothing new (2026-10-05): `check-facts.fx`**,
four procedures in `(define test-facts (module …))`, the two
`check-synth.fx` calls re-exported (neither inlined: both name
themselves). Back to back, new, old, new, three runs each: check
1.20–1.23 s, 1.22–1.23 s, 1.23 s; compile 0.15 s throughout. No cost
measurable; but its procedures are called once a test, not in the
checker's inner loops, so a hotter file is the real test of re-exports
(§38's remainder). Items are indented two spaces under `(define m
(module`, so a file's lines stay within 100 columns. The other files that
need nothing new: `check-args`, `check-generative`, `check-mask`,
`check-errors`, `check-calls`, `check-close`, `check-synth`, `layout`,
`standard`, `compile-exps`, `compile-programs`, `regcode-core`,
`native-layout`.

**The rest of them (2026-10-05)**, one commit each, each timed new, old,
new against the commit before (`tests/bootstrap.rs`, `comparison`):
`check-synth`, `check-args`, `check-generative`, `check-mask`,
`check-errors`, `check-calls`, `check-close`, `compile-exps`,
`compile-programs`, `regcode-core`. Items unindented between `(define
<file>-module (module` and `))`, so no line grows. Compile stayed 0.15 s
throughout: the re-exports cost nothing measurable at run time. Check did
not: 1.24 s before `compile-exps`, 1.65 s after `regcode-core` (+5%,
+12%, +6% for those three; the checker files' modules cost nothing
measurable). Checking a large module grows faster than its size: to look
into before more files move. Found, profiling (`docs/performance.md`,
"Printing a type was quadratic"): not the module code, but printing a
type, quadratic in the type names in scope at each node, a module's type
being large; fixed, check 0.99 s. Found on the way, each fixed or set
aside:
- each lambda's recursive group was checked to end once per member
  (fixed, `c71bbc2`: check 2.65 s → 1.31 s with `compile-exps`);
- a module counts a type and a value of one name as defined twice, where
  the top level keeps them apart (`c-mval`; renamed): to decide;
- a second top-level `define-type` of a name already a type is taken
  silently, its uses failing later and far away (`k-whys`): to refuse or
  say;
- a type re-exported from a module cannot be named by an earlier file,
  though types are otherwise declared ahead (`c-inline`; moved to its
  first user);
- `define*` in a module (done, `41796d6`), then the files it alone
  blocked: `check-data`, `check-letrec`, `check-print`, `check-subtype`,
  `check-infer`, `check-program`, `compile-lift` (check 0.97 s to 1.06 s
  over the nine; compile 0.15–0.16 s). A file's `define-type`s now stay at
  top level, before its module, as they are declared ahead and named
  before their definitions; earlier files' modules keep theirs inside.
  `check-syntax.fx` and `regcode-exps.fx` would pass 1000 lines with the
  wrapper and their re-exports: each to be split first. Loading the
  lowered front end now counts against no step limit (`7c7d276`): found
  when `check-program.fx`'s module passed a test's 100,000;
- with a module's types declared ahead (`43483dd`), the files' types are
  back inside their modules, re-exported by `select` where later files
  name them; a type an earlier file names (`k-seen-pol`) moved to it.
  `check-print.fx`'s second half is `check-holds.fx`. Cost found and
  fixed: resolving a `select` rebuilt the whole type (`docs/
  performance.md`); check 0.91 s;
- `layout.fx`, `standard.fx` and `native-layout.fx` are generated from
  Rust tables (`tests/layout.rs`): their generators would write modules;
  set aside, and mostly constants, which want checking that a re-exported
  constant stays one to the compilers.

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

## 38. Re-exported module members that name other members (found 2026-10-05)

A re-export of a member that names no other member is inlined now
(`DONE.md` §38). Left, deliberately (the user's: the re-exports are a
crutch while the front end moves into modules; fast enough, not every
cycle):
- **A member that names another member** is still called, not inlined:
  its body, inlined outside the module, would name a member that is only
  a slot of the module's code. To inline it, the compiler would compile
  such a name as the member's field of the module in its global (two
  loads), behind a guard on that global; or make a top-level module's
  members hidden globals.
- **Native code** does not inline re-exports: the loop of `DONE.md` §38
  natively, 400 M calls, 0.57 s against 0.51 s direct, unchanged.

Measure a hot file moved into a module before doing either.

## 39. A checker's arena grows for the whole session (the user's, 2026-10-06)

Every type node, binder and generative type a checker makes is an entry
in a vector (`Arena`'s `tys`, `Checker::generatives`; the FX-26 checker's
`k-tys` and its tables), named by its index, and none is ever removed: in
a long REPL session, the types of definitions since redefined, and every
form's intermediate types, stay. An index names nothing a collector can
see, so the heap's collector cannot help, nor can a weak table keyed by
them.

Two parts, in both checkers (they must agree on what they print):
- **A nursery per REPL form**: check each form in a scratch arena, copy
  what the new globals reach into the session's, drop the rest. Most of a
  form's types (inference variables, intermediate and error-path types)
  die with it. Old generations, a generative type redefined, stay.
- **The FX-26 checker's types as heap objects**, pointing at each other,
  links included, instead of indices into `k-tys`: the heap's collector
  then reclaims what nothing reaches, and the tables that must not keep a
  type alive (memo and fact tables) become weak tables. The Rust checker
  keeps its arena (`Rc` would leak recursive types, which are cycles); for
  it, an occasional copying pass from the session's roots, renumbering.

Done first: the ids are checked (`DONE.md` §39).

## 40. A call graph from the code, not from names (the user's, 2026-10-06)

The front end's cycles were found by a regular expression over names
(definitions, and the names their bodies mention): enough to size the
cycles, not to trust. A tool that extracts the real call graph of an FX-26
program, from the checked trees (a call's callee known statically, or by
a control-flow analysis such as k-CFA where it is a value), would serve
the cycle work (`TODO.md` §34), dead-code checks and the profiler's
callers.

## 41. One set of decisions, two back ends (the user's, 2026-10-06)

The stack and register compilers call each other: the register compiler
makes each word's twin as the stack compiler makes the word, and calls it
back for words it needs (specialized copies). A middle phase would make
the decisions they share once, so that each is a back end over a decided
program and the front end's last hook cycle between them goes:
`docs/research/compiler-middle-phase.md`, for review before any code.
Steps 1–4 done in both compilers (2026-10-06): copies memoized, the
procedure table, every call decided in the plan (inlined bodies and
copies included), and twins as a phase, the hooks `c-register-code` and
`c-standard-register-code` gone. Step 5 (2026-10-06): the register
compiler's own three hooks (`r-module-code`, `r-reshape-code`,
`r-leaf-call`) removed by folding their knot into `regcode-core.fx`'s
recursive group, 1127 lines, over the 1000-line limit by the user's
decision (`crates/fixpt-tidy/fx-size-debt.txt`).

To revisit (the user's: "we can think about coming back here and
addressing this in a cleaner way later"): bring `regcode-core.fx` back
under the limit without hooks. The options weighed: pass the recursion
explicitly (the module and leaf-call code take `r-exp`, `r-exp-as-is`,
`r-lambda`, `r-make-frozen`, `r-into` as parameters, and move before the
core); the same as a functor module (M5) over the core's procedures; or
split the core group at a seam (calls, inlining and specialization,
~300 lines) with the recursion passed across it.

## 42. Constant globals folded where they are used (the user's, 2026-10-06)

Neither compiler folds a global defined as a constant: every use of
`tag-pair` or `n-base` (`layout.fx`, `native-layout.fx`), and of any
program's `(define k int 5)`, is a `global` load, in stack code and in
register code alike, because a global may be redefined. Checked: a
top-level `(define tag-a int 5)` and a module member re-exported as
`(define tag-b (with m tag-b))` compile to the same `global` load, so
making the generated files modules changes nothing here, but neither is
folded.

What would let them fold, types first (no new syntax): a global the
checker sees defined once as a literal (or a constant expression of
literals and such globals) and never assigned, whose definition no later
form redefines. The front end is checked whole, so for it that is known
at compile time; a REPL session is not, and a redefinition there must
still be seen, as inlined calls see one now: behind a guard on the
global, or by recompiling what folded it.

To decide with the user: whether redefining such a constant should stay
allowed (and pay a guard, or a recompile), or be refused for globals
defined by a module (`layout-module` and its kin), where nothing outside
the module can assign them. Measure first: how many `global` loads of
constants the self-compile and the native compiler run, and what folding
them saves.

Measured (2026-10-07; `FIXPT_PROFILE_PHASE` with `FIXPT_PROFILE_GLOBALS`,
which counts each `global` read by name on the Rust machine): of the
self-compile's global reads, constants are few. Check: 34.5 M reads, 31 K
of constants (0.1%, seven of them: `k-int`, `k-bool`, …). Compile: 6.8 M
reads, 420 K of constants (6.2%, 73: `routine-slot`, `register-regs`,
`rop-field`, …). Natively each is a load or two: folding them all would
save about a millisecond of the self-compile. Statically, 932 uses of 229
constant globals, 601 in `native.fx` (arm64's register numbers), 94 an
operand of arithmetic or a comparison; none reached through a `with` in
a procedure body (a path, the user's: to generalize to when it occurs).
`native.fx`, which the self-compile does not run, is not measured yet.
What the reads are instead: procedures, at calls. Check reads `k-resolve`
9.6 M times, `k-get` 5.2 M, `k-has-id?` 3.3 M: a call of a global through
its cell, a check that it holds a closure, and the call. That is PLAN's
"the rest of known calls", worth more than this. (No: natively a global's
procedure is already bound to its code when its machine code is made,
`global_value`'s `Field::Code`, so those calls are direct; the counts
were the stack code's on the Rust machine. Lesson recorded: predict a
compiler's gain from the native code, not from an interpreter's counts.)

Measured natively (2026-10-07), the best case for folding: a loop of 10^9
iterations whose only work is adding a constant, `(+ acc k)` against
`(+ acc 3)`, under `--calling-convention native`: 0.564, 0.559 s against
0.556, 0.558 s, under 1%. The global costs four instructions an
iteration (a load of the cell, of its value, a tag test, a move), none
on the loop's dependence chain, so the processor overlaps them with the
loop's own. Folding would save code, not time: not built. Worth looking
at again only if a constant's folding would decide a test or remove a
branch in hot code (immediates alone do not pay), or for code size.

Built after all (2026-10-07, the user's: "the reason to constant fold is
because of the *other* optimizations it unlocks downstream"): a fast
version folds the constant globals its body names (`r_consts_named`;
`r-consts-named`), each behind a `value-guard` at its start, the
assumption the inlining guards make for closures, here of the same word
(an immediate, or an object by identity, so it scales to constants that
are objects); everything downstream then sees a constant (`RLoc::Const`,
`rl-const`): tests decided, branches gone, immediates, constant arguments
to inlined calls. Both compilers; every machine runs `value-guard`, and
the native compiler drops it where the cell holds the value when the
code is made. Left: the REPL folds nothing yet (each form is compiled
apart, and the session would have to tell the compiler the constants, as
it tells it inlining candidates); globals reached by a path; constants
that are objects (only immediates are noted as constants so far). And
the fast versions themselves are rare in the front end (2 procedures
fold a constant), being kept only for leaves and loops whose effect
allows: what folding unlocks there depends on that policy.

One guard since (2026-10-07, the user's: one guard "that checks if the
global was written", not one per kind of value; and no tracking of who
depends on a write, which could leak, "keep the opening check"): a
`global-guard g n` tests that `g` has been written `n` times, a count
every machine's write adds to (`docs/performance.md`, "One guard"). So
the guard is the same for a procedure, a constant of any kind (a list or
array literal costs no more than an immediate) and a module. Constants
reached by a path are folded now: a `with`'s member of a global module
that is a literal, behind the module's guard; and a `with` in a leaf
keeps its values in registers. Left: the REPL folds nothing yet (each
form is compiled apart, and the session would have to tell the compiler
the constants); constants that are objects (only literals are noted).

## 43. A survey of list searches in the front end (the user's, 2026-10-07)

"Seems like we keep hitting this": a list searched once per item of
something that grows with the program, so the work is quadratic. Found
one at a time so far: `c-field-index` (a table since), printing a type
(quadratic in the type names in scope, `docs/performance.md`, "Printing
a type was quadratic"), a `with` binding its whole module (only what its
body names since), and the FX-26 compiler's count of writes (`c-writes`,
a list appended at each of the front end's 4479 definitions and searched
at each: `fx words` 252 → 262–272 ms, a table by name since). Survey the
rest instead of waiting for the next. A first pass by pattern (a helper
recurring on `(cdr …)` and comparing `(car (car …))`, or named `-in`,
`-of`, `-named`, `-without`, `-find`) finds about 60 in the front end:
13 in `compile-programs.fx`, 8 in `compile.fx`, 6 each in `regcode.fx`
and `regcode-exps.fx`, 5 in `evaluator.fx`, 4 each in `compile-plan.fx`,
`check-types.fx` and `check-terminate.fx`, and fewer elsewhere. For each:
how long its list gets on the self-compile (the front end) and how often
it is searched, counted on the native path (`docs/performance.md`; not
on an interpreter's counts); then a table where both grow with the
program, and nothing where the list stays short (a module's members, a
lambda's parameters).

The survey, first pass (2026-10-07): the compile phase of the front end
compiling itself, as register code on the Rust machine, cells by word
(`FIXPT_PROFILE_PHASE=compile`, `tests/bootstrap.rs`'s
`probe_phases_as_register_code`): 781.6 M cells. The searches at the top:

| word                                   | cells  | share | its list                         |
| -------------------------------------- | -----: | ----: | -------------------------------- |
| `c-find`                               | 71.7 M | 9.2%  | a procedure's locals, per name   |
| `standard-primitive`                   | 69.6 M | 8.9%  | a `cond` of 293 `string=?`       |
| `c-with-in`, `c-with-places-in`        | 61.0 M | 7.8%  | every `with` (1431), per `with`  |
| `exp-start`, `exp-end`                 | 67.1 M | 8.6%  | (a dispatch, not a search)       |
| `r-where`                              | 26.8 M | 3.4%  | register code's locals, per name |
| `c-member?`                            | 24.2 M | 3.1%  | free names, bound names          |
| `p-inline-named` (and `r-inline-named`)| 22.3 M | 2.9%  | every inlining note, per call    |

Done, where the list grows with the program or is large for nothing: the
`with`s indexed by where each starts (`c-with-index`); `standard-primitive`
generated as a `cond` on the name's length, then the names of that length;
the inlining notes kept by name too (`c-inlines-by-name`, beside the list
genv pruning walks). The compile phase: 781.6 M → 632.6 M cells (−19%);
the front end compiled by FX-26 (`fx words`), back to back against HEAD,
four runs: 273.8 / 280.9 / 313.4 / 284.4 → 251.9 / 249.5 / 278.5 / 255.0
ms (about −10%). Left: `c-find` and `r-where`, scans of a procedure's
locals, which grow with a procedure, not the program (a long `let*`
pays); `c-member?`'s callers (17), sets of names kept as lists; and
`c-genv-limits`, which walks every inlining note at each global made.

## 44. One simplifier: propagation, folding and reduction together (the user's, 2026-10-07)

"We probably need to combine these things together. Eg arith eval yields
more constants which can then be propagated, and so on." Constant
propagation, arithmetic folding and reduction (`x*1`, `x+0`, constants
combined across operations), and branch reduction (a known test; a test
repeated on a path; `tagcase` on a known variant) each make work for the
others, and inlining makes more for all of them; run as separate passes,
each misses what the next would have shown it. The classic results:
Wegman and Zadeck, "Constant Propagation with Conditional Branches"
(TOPLAS 13(2), 1991), sparse conditional constant propagation, which
finds more constants than propagation and dead-branch removal apart;
Click and Cooper, "Combining Analyses, Combining Optimizations" (TOPLAS
17(2), 1995), the general case; Twobit's pass 2 (Clinger), an iterated
simplifier of inlining, folding, copy propagation and dead code removal.

The shape: one simplifier per lambda body, in the middle phase (where
the plan, inlining and specialization are decided for both back ends),
before register code. An environment maps each name to a constant, a
copy of another name, or unknown; each step does what applies (fold an
operation, decide a test, drop an unused binding, inline a small known
call, reduce an identity), and it repeats until nothing changes, within a
bound, its growth kept as the inline limits keep it. Inside an arm the
test is known (`x` is 0 in `(if (= x 0) …)`'s then-arm). It works under
a fast version's assumptions, so the globals and module members folded
behind guards (§42) join in; in a plain version it stops at a call's
guard. Only what is pure is moved or dropped (the effect summaries), and
integers are folded only where neither compiler can overflow. Both
compilers, agreeing.

First, a baseline (`fixpt regcode-survey`): what the register code made
today still leaves to fold, decide or reduce, in the benchmarks and the
front end, so the simplifier can be judged against it.

The baseline (2026-10-07, `fixpt regcode-survey`, static counts over
register code, the Rust compiler's, which FX-26's matches; what is known
is forgotten where branches meet, so an under-count of what a simplifier
that merges paths finds). The benchmarks: nothing left, in every
category. The front end (2904 words, 439 786 cells), counts with those
in loops in parentheses:

| finding                                  | as made  | literals propagated |
| ---------------------------------------- | -------- | ------------------- |
| operation on constants                   | 2 (0)    | 59 (0)              |
| branch on a constant                     | 0        | 30 (0)              |
| identity (`+ 0`, `* 1`)                  | 0        | 0                   |
| test repeated on a path                  | 1 (0)    | 1 (0)               |
| pure operation repeated                  | 86 (52)  | 90 (52)             |
| global load of a literal                 | 996 (80) | —                   |
| global module's literal member read      | 263 (10) | —                   |

"Literals propagated" (`--propagate`): the globals and module members
holding literals taken as known everywhere, not only in fast versions,
and `+ - * < = eq` on constants worked out, so what they make is known
in turn. So in the code as written, the cascade is small: 59 operations
and 30 branches more, none in a loop. What is left in loops is `car`
taken twice (63 of the 86; list searches testing `(car (car xs))` and
returning `(cdr (car xs))`), which common subexpressions do not merge,
a pair's field not being known not to change; and 80 loads of literal
globals. A planted case (`(if (< x k) (if (< x k) (+ x 0) 2) (* k 2))`)
shows what is missing today: `(+ x 0)` kept, the second test kept, and
`(* 3 2)` not folded even in the fast version that knows `k` (`*` is a
primitive the folding does not know). What the survey cannot see is what
inlining would expose once these are done; it counts what is there.

`car` taken twice, timed (2026-10-07, the user's question: merge it where
the pair cannot change?): an association list of 200 searched 20 000
times, `(= (car (car xs)) k) (cdr (car xs))` against `(car xs)` bound
once, three rounds in both orders, best of 9: natively 3.6 / 3.6, 3.6 /
3.6, 3.5 / 3.5 ms; register code 3.7–5.1 ms either way, by order. No
difference: the second `car` reads a word loaded a few instructions
before, from L1, beside the comparison. Merging it would not need the
pair immutable (nothing between the two reads writes anything, which the
effect summaries say), but it is not worth building for time.

List literals propagated (the user's idea, 2026-10-07): where a list is
known, `car`, `cdr` and `null?` fold, and a recursion over it can be
unrolled. Where it occurs: the front end, nowhere (3 `(list <literal>
…)`); the benchmark ports, 82 in 17 files, nearly all built with computed
elements (`dynamic.fx`'s `(list 'quote syntax-arg)`), the exception
`parsing.fx`: eight global sets of token kinds, `(define k-list syms
(list 'lparen 'quote …))`, each tested by `(one-of? t k-list)`, a
recursion over the list. Unrolled by hand into `(or (symbol=? t 'lparen)
…)` at its 10 sites, at 100 iterations, best of 5: register code 92.2 →
81.7 ms, and 91.9 → 81.6 ms in the other order; compiled words 834 → 787
ms. About 11% of the benchmark.

What it takes: the list must be immutable by its type. `syms` is
`(listof symbol @heap)`, which a `set-car!` anywhere may write; a list
built in order may be `acyclic` with no `letfreeze` (`docs/fx26.md`,
"Finite data"), so the port would say `(listof symbol acyclic)`. Then:
a list of constants in `acyclic` or `const` is constant data, made once
while compiling as sums and products are; `car`, `cdr`, `null?` of it
fold (reading frozen heap data is pure); and a call of a small recursive
procedure with a constant list argument is unrolled, inlining it once
for each element, bounded by the list's length and a size limit: the
simplifier above, its first customer.

Built (2026-10-07): constant lists, folded and unrolled, both compilers.
- Both checkers note each top-level definition typed a list in a frozen
  region (`frozen_defines`, the fact -501); its value, if built of
  literals, is made once as constant data (`const_list`; `c-const-list`),
  seen through calls of small procedures noted for inlining, so a helper
  that builds a list (`parsing.fx`'s `syms5`) is no obstacle (the user's
  question: "why aren't we inlining sym5?"). `nil` is a constant list.
- `car` and `cdr` of a constant pair fold (`r_const`; `r-fold`).
- A small procedure that calls itself (`unrolls`; `c-unrolls`, by name) is
  unrolled where called with a constant list, a constant here or a global
  holding one: its body inlined with the list known, its call of itself on
  the rest unrolled in turn, at most 16 deep, until the test that ends the
  list is decided. Behind guards on the procedure's global (at the
  outermost call only; its body writes no global) and each global a list
  was read from; where one fails, the call, the list read from its global
  again. Not planned: each level knows a different list.
- The FX-26 compiler keeps its constant lists apart from the other
  constants, by name, and its unroll notes by name (the user's: segregate
  what a call asks of, rather than a flag to skip asking).

`parsing.fx`'s token sets typed `acyclic` (the user's approval): register
code 91.7 / 92.0 → 84.0 / 83.6 ms at 100 iterations, against HEAD back to
back; the hand-unrolled version, 82.5–82.9. The front end compiled by
FX-26 (`fx words`): 265.4 / 261.5 → 273.5 / 265.3 ms, the front end itself
1.2% longer. Tests: `programs/run/unrolled-lists.fx` (`register_code.rs`,
`direct.rs`, with `k` redefined).

The planted case's gaps closed (2026-10-07, the user's "smaller, self
contained thing" first), both compilers: `*` folds on constants whose
product is under 2^30; `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x` are `x`
(`r_identity_arg`); and a comparison of places and literal constants that
an `if` around decided is known in its arms (`RLoc::Test` in Rust's
environment, `rl-test` in FX-26's: scoped as bindings are, so not seen in
an inlined body or a lambda). The planted case's fast version: 72 → 53
cells, the second test and `+ 0` gone, `(* k 2)` the constant 6
(`register_code.rs`, `identities_decided_tests_and_products_fold`). The
FX-26 compiler's cost: the front end's `fx words` 264.3 / 264.2 → 272.6 /
272.5 ms, 3%; a first version that keyed decided tests by a symbol made
from a string cost 10% (the key built at every comparison `r-known` sees),
the second compares structurally, and only for comparisons. To look at
again with §43.

## 45. Cdr-coding frozen lists (the user's, 2026-10-07)

The user's idea: we control the value representation, the allocator and
the collector, so a list's spine could be laid out compactly: a cell whose
successor is the next cell in memory, rather than a pointer to another
pair. The classic design (Hansen 1969; Clark and Green 1977, who found most
`cdr`s point to the very next cell; Bobrow and Clark 1979; the MIT Lisp
Machine and the Symbolics 3600's 2-bit cdr codes; Li and Hudak 1986;
Shao, Reppy and Appel, "Unrolling lists", LFP 1994, for typed languages
with immutable lists). Papers, as they are found, under
`docs/research/papers/cdr-coding/` with `SOURCES.md` (uncommitted).

Why FX-26 may do better than the Lisp machines did: their cost was
`rplacd` of a cell in the middle of a run, which needed forwarding
("invisible") pointers that every access had to follow. FX-26's types say
which lists nothing writes, `acyclic` and `const` (the constant lists of
§44 among them), so compacting only those needs no forwarding at all; and
`eq?` on frozen data already promises only that `#t` means equal
(`docs/fx26.md`), so a run may be copied or shared.

What it would take, and what to measure first:
- A representation: a spare bit in a cell's car word, or a run as an
  object kind of its own; `cdr` of a compacted cell the address of the next
  cell, so a pair's identity stays its car's address.
- The collector: a run copied as one object; pointers into its middle
  (what `cdr` returns) mapped back to the run, or each cell able to find
  its run's start.
- Who makes runs: `list` of known length; the copying collector, copying a
  frozen spine as one run (Clark and Green's data says copying already
  almost lays lists out so); constant lists made while compiling.
- Measure first: after a collection, how many frozen pairs' cdrs already
  point to the adjacent cell, and how much of the benchmarks' and the
  front end's time goes to walking frozen spines; then whether halving a
  spine's words pays natively (`car`/`cdr` stay one load; the gain would
  be cache and allocation).

What the papers say (a research agent's reading, 2026-10-07;
`docs/research/papers/cdr-coding/SOURCES.md`; Hansen, Clark and Green, and
Li and Hudak are paywalled or unavailable, read at the abstract only):
- Adjacency: Bobrow and Clark's Table II, five Interlisp programs: 53.7–
  75.8% of cdrs within one cell before linearizing, about 99% to the next
  cell after a cdr-first linearizing pass.
- `rplacd` is the difficulty: about half of all cells see one, counting
  the list primitives' own; the answer was the invisible cell (its car
  forwards to the real cell), with `eq` made to see through it, and on
  the CADR the car moved and a forwarding pointer left.
- Collectors: a copying or compacting one builds the runs; Moon (LFP
  1984) copies about depth-first, so children land near their parent.
- Benefit claimed: about half the space, at little cost on microcoded
  machines. Against it on modern machines: Shao, Reppy and Appel (1994)
  find run-time cdr-coding unattractive, its tag test on every `car`
  lengthening control dependences, and unroll immutable lists at compile
  time instead (two items a cell: a quarter fewer words and loads for
  lists past two, half the cdr links and nil tests). Read before quoting
  their measurements. Nothing after the 1990s re-measures run-time
  cdr-coding that the agent found.
So for FX-26: the frozen subset removes the `rplacd` problem; Shao et
al.'s point (a test on every `car`) is what to measure natively, and their
compile-time unrolling, chosen by type, is the alternative to weigh.

## 46. A `case` on atoms (the user's question, 2026-10-07)

FX-26 dispatches on a sum's variants with `tagcase`, and on anything else
with `cond`: there is no `case` on symbols, integers, characters or
strings. Where a program means `case`, it writes a chain of comparisons
or a search of a list: `parsing.fx`'s `(one-of? t k-list)`, whose Scheme
original is `case` (§44 unrolls it back), and the generated
`standard-primitive`, a `cond` of 293 `string=?` (§43 now splits it by
length first). A `case` whose data are literals by definition would say
what is meant, need no constant-list unrolling, and let the compilers
choose the dispatch: a jump table or range test on small integers and
characters, a compare chain or a hash on interned symbols (`eq`), a test
of the length first on strings. Typing is plain: the key's type, the data
of it, every arm's result the `case`'s. Both checkers, both compilers, the
lowering (Scheme's own `case`) and the evaluator.

**First step, done (2026-10-07):** `case` as a derived form in both
parsers, as `cond` is: `(let ((%case-key key)) …)` and a chain of `if`s,
each datum compared by its kind's equality (`=`, `char=?`, `string=?`,
`symbol=?`, `bool=?`), several data to a clause as an `or`. The data are
of one kind and distinct, floats and `#u` refused, `else` required; the
parsers agree on the trees and on each refusal
(`tests/parser.rs`, `case_parse_errors_agree`), and
`programs/run/case.fx` answers the same lowered, on the Rust machine and
natively. Every checker, compiler and machine sees only what it already
handled. **Left:** the dispatch, as a recognition of comparison chains on
one variable in the compilers, which helps a hand-written `cond` as much;
then the front end's own `cond`s on a symbol rewritten as `case`.

**Hygiene (the user, 2026-10-07).** An expansion's own variable is named
for what its form does not mention (`fresh_name`, `fresh-name`: `%case-key`,
else `%case-key1`, …), in `case`, `confirm-length`, `acyclic` and
`confirm-nat`, the same in both parsers; nothing refers to a name it does
not write, so it captures nothing (`programs/sizes/fresh-temporaries.fx`;
not under `run/`, which the FX-26 evaluator runs too: it has no
`length-is?`, `acyclic?` or `nat?` yet, and `evaluator.fx` is at 992
lines, so they wait on a split).
**Done (2026-10-07): the names an expansion calls.** They could be
shadowed or redefined (`(let ((= (lambda ((a int) (b int)) #t))) (case 2
((1) 'one) (else 'other)))` answered `one`). Now every expansion calls
`(with #%fx name)`, the standard binding whatever binds `name` there
(`docs/fx26.md`, "`#%fx`"): both readers read `#%fx` (no other `#%`), both
checkers type it and refuse it bound, every rule keyed on a standard name
asks `standard_ref`/`k-std-op`, which accepts it, and where nothing shadows
`name` both checkers note it plain (fact -502) and both compilers read it
as the plain `name` from that fact alone (`Compiler::exp_at`,
`c-plain-fx`; the tree is not rewritten), so `case.fx` compiles to the
same code to the cell. Shadowed, the lowering, both
compilers' stack and register code, and the FX-26 evaluator give the
standard operation (`programs/run/standard-refs.fx`, every machine). The
audit of name-keyed rules found F15 and F16 (`soundness-findings.md`).
**Left:** a polymorphic value through `#%fx` is not instantiated where a
type is expected (§48 would settle `nil`'s).

**Prior art (the user's pointer):** Clinger, "Rapid Case Dispatch in
Scheme", Scheme Workshop 2006 (`docs/research/papers/case-dispatch/`,
gitignored; `SOURCES.md` there). Larceny's Twobit recovers the clauses
from `if` chains of `eq?`/`eqv?`/`memq`/`memv` on one variable, so it
helps code with no `case` in it (p. 64); below 12 constants it keeps the
sequential search (p. 64; `src/Compiler/pass2if.sch:15-21`). Otherwise it
dispatches three times: on the type (characters, symbols, other
constants, then fixnums), to a clause index, then by binary search on
that index (p. 63, fig. 1). Fixnums and characters (as their codes) get
a range check, then a table if `hi - lo < 5 × intervals`, else a binary
search on intervals (p. 65; `pass2if.sch:454`). Symbols get a closed hash
table probed in straight-line code to the largest distance the compiler
found (`pass2if.sch:572`). The hash is computed at intern time and stored
in the symbol (p. 65; `Lib/Common/oblist.sch:36`); it is a function of the
name alone, `string-hash` (`Lib/Common/string.sch:269`), which Twobit
duplicates by hand (`pass2if.sch:764-794`). At 1000 symbols the result was
.13 s against 3.94 s sequentially, per million dispatches (Table 1, p. 68).
Ours already has that hash: each symbol's slot 1 is FNV-1a of its name,
made by `intern` (`crates/fixpt-heap/src/heap.rs:1196`), so a compiler can
compute it from the datum. One function shared by the heap and the
compilers keeps the two the same, with no copy to keep in sync. FX-26 is
typed, so the dispatch on the type is not needed: the key's type is the
data's kind.

## 47. Second-class `cwcc` and `certify-*`: revisit (the user's, 2026-10-07)

F15 and F16 (`docs/research/soundness-findings.md`) were closed by making
`cwcc`, `certify-length`, `certify-acyclic` and `certify-nat` second class:
named only as a call's operator, past `proj` and `the`, so that every call
meets the rule that finds it by name. That is a restriction, not a typing:
the rules still rest on a name, not on anything a type says. Come back to
it, and ask whether the types themselves can carry what the rules check,
so the operations can be first class again:
- `cwcc`: F3 and F9's question is whether the receiver's continuation can
  outlive the call. An effect or a region on the continuation's type (it
  escapes only into storage the type names) would let a `cwcc` passed as a
  value be checked where it is called through any name.
- `certify-*`: a certificate is a fact about one variable at one place.
  A type that only a test can produce (a refinement, `(nat s)` as the
  result of `nat?`'s true branch, or a token type a test hands to its
  branch) would make the certify operations ordinary functions of that
  token.
- Meanwhile, every new rule that finds a standard operation by name must
  either only add facts (an alias then loses precision, never gains) or
  join the second-class list; the audit in F15's note is the template.

## 48. `nil` of a type of its own (the user's, 2026-10-07)

`nil` is `(poly ((r region) (t type)) (listof t r))`, and a polymorphic
value is instantiated only where a type is expected of it; elsewhere a
program `proj`s it, or wraps it in `the`, at every use that the checker
cannot solve (an argument given before the one that fixes `t`, a `let`
of it, a branch of an `if` checked first). Instead: a singleton type, say
`null`, not polymorphic, of `nil` alone, a subtype of every `(listof T R)`
(and of `(pairof T1 T2 R)`'s "or none" while that is the absent pair, Q7
making `pairof` non-nil). Subtyping then does what instantiation does now,
everywhere a list is expected, and a `let` of `nil` or an `if` with `nil`
in one branch joins to the other branch's list type.
- Joins: `(if c nil xs)` is `xs`'s type; `(if c nil nil)` is `null`.
- Inference: a parameter whose argument is `nil` alone stays `null`, not a
  list; the checkers may widen at the binder's use.
- Both checkers; the lowering and the compilers need nothing (the value is
  the same); `(with #%fx nil)` stops needing instantiation (§46).
- Ties to Q7 (unions of atoms): `null` is the one-value atom type that
  unions like `(union symbol null)` would be built from.
