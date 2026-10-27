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

**Measured (2026-10-22, x86_64, release): where checking goes.** The
Rust checker on the whole front end takes 1.85 s; loading it lowered
takes 1.85 s more to check, 0.13 s to lower, 1.6 s to load the Scheme.
By phase, each phase's own time (timed at its entry, 2.0 s with the
timers):

| phase | share |
| --- | --- |
| synth and check, the rest | 37% |
| subtyping | 12% |
| parse (syntax to AST, types included) | 11% |
| cyclic types (`cyclic`) | 9% |
| regions (`regions_in`) | 8% |
| knots (`no_knot`) | 7% |
| module selects (`resolve_selects`) | 7% |
| substitution (`subst_memo`) | 6% |
| termination (size-change) | 1.3% |
| effect inference (`->*`, `define*`) | 1.3% |
| unification (instantiating at calls) | 1.0% |
| recording uses, for redefinition | 0.5% |

Inference proper (effects found, instantiation, the termination search)
is under 4%: the front end writes its types. A verifier of an
elaborated source form would redo most of the rest, so would save
little; what would save the 1.85 s, and the 1.6 s of loading, is a
verified *compiled* form (item 1), whose types are resolved and whose
selects, subtyping and regions are already settled. Apart from that,
the checker spends much in hashing (`RandomState`, SipHash: 8% hashing
`DVar`s, 5% cloning `SubState`'s assumptions in `sub`); a faster hash
and an assumption set not cloned per branch would be a cheap gain.

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
- **Sorting**, wanted by an editor (2026-10-18): `list-sort` and
  `vector-sort`, stable, taking the order as a procedure; none exists.
  The Larceny prototype (`~/Dev/Emacs/yank`) sorts in 48 places
  (completions, buffer lists, the analysis's results).

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

Second pass, the check phase (2026-10-11, after `DONE.md` §69's bucket
fix): `FIXPT_PROFILE_PHASE=check`, the same probe (nine minutes), 5.23 G
cells. The top, by word itself:

| word                      |   cells | share | what it is                     |
| ------------------------- | ------: | ----: | ------------------------------ |
| `k-has-name?`             | 433.6 M |  8.3% | a name in a list of names      |
| `k-resolve`               | 335.3 M |  6.4% | a type's link followed         |
| `k-on-path?`              | 250.9 M |  4.8% | the cycle walk's path, a list  |
| `bucket-find` (tables)    | 228.1 M |  4.4% | a table's bucket searched      |
| `k-cyclic-from?`          | 205.7 M |  3.9% | the `acyclic` check's walk     |
| `k-length`                | 182.0 M |  3.5% | a list's length, counted again |
| `rehash-bucket`, `-array` | 251.0 M |  4.8% | tables growing                 |
| `k-strail-in?`            |  85.3 M |  1.6% | a subtyping trail, a list      |

These are the Rust machine's cells, not native time: a memo of
`k-with-used`, `k-has-name?`'s largest caller by reading, changed the
native `fx check` by nothing measurable. To do: time natively (with
`FIXPT_SYMBOLS` and `fixpt-symbolize`) the callers of `k-has-name?`,
`k-on-path?` and `k-length` before changing any; tables that grow from
empty might start at the size they reach. Natively the top FX-26 word of the
whole front-end compile was the assembler's `arm-times-pow2`: fixed
(`docs/performance.md`, "`fx arm64` halved"). And the Rust checker's
`lookup` (with `is_standard` and a dozen like it) scanned every binding in
scope for a name: an index now (`Bindings`), `check` on the front end
568 → 520 ms. Its `mask` walks each masked expression's free names
(`free_into`, about a fifth of the Rust `check` now): a node's free names
could be kept as it is checked, if `with`'s facts allow.

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

**Dispatch (2026-10-07).** A `case` of many data is two searches by
halving, made when it is expanded (both parsers, the same trees): the
clause's index from the data sorted by the integer, or by the key's hash
computed once (`string-hash`, `symbol-name-hash`, their values known at
parse time from the same functions, `fixpt_heap::heap::string_hash_of`,
`symbol_hash_of`), leaves of three or fewer testing the key itself (so a
collision is only slower); then the body from the index. With a clause per
datum and an `else` of one atom, each leaf gives its body and the `else`,
with no second search. From how many data, measured natively (register
code, 2M dispatches, against the same `cond`): integers 8 (32 with an
index), symbols 32 (64), strings 16; characters never (`char->integer` a
call-out against `char=?` one instruction). At 64 symbols 53 -> 22 ms, at
32 strings 96 -> 39 ms, at 32 integers 21 -> 13 ms. The FX-26 evaluator
learned `string-hash` and `symbol-name-hash`. Test
`programs/run/case-tree.fx`, both forms of each kind, every machine.

**Front end rewritten (2026-10-07).** Every `cond` in the front end that
compares one variable with literals is a `case` (the generated
`standard.fx` and `native-layout.fx` from their generators): 63 whole, 11
whose other tests go in the `else`, moved after the literals only where
each such test is a predicate on a literal set found disjoint from the
literals after it (`region-form?`, `bloblet-form?`, `k-module-type-head?`,
`std-eq-name?`, `region-prim?`, `+`/`-`), and `char-in?` on a literal
string as its characters. A `case` on a variable compares it as it is,
with no `let` (both parsers), so it compiles as the `cond` did: of the
front end's 1294 words, all compile the same but `parse-form`,
`k-parse-type-form`, `k-synth-app`, `apply-prim` (reordered) and
`read-hash` (no `char-in?` scan). No nested `if`s compared one variable
twice. The source is 8 KB smaller, its lines 4 fewer; the front end's
times the same. Clauses keep the first on the `case`'s line, as fx26-mode
indents it, where that fits in 100 columns.

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
**Left:** `(with #%fx nil)` is not of the type `nil` where nothing says
which list, as `nil` is (`DONE.md` §48). (Where a type is expected, a
polymorphic value through `#%fx` is instantiated as the plain name is,
since 2026-10-08, for `quote`'s sake.)

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

## 49. `sexp-edit indent`: re-indent as fx26-mode does (the user's, 2026-10-07)

Rewriting the front end's `cond`s as `case` (§46) needed a one-off script
to keep clauses aligned: `cond` becoming `case key` moves every later
clause, and a shortened test moves what is aligned after it. An `indent`
command in `sexp-edit` (by definition name, or a line range) would do it
generally: Emacs's `lisp-indent-specform` rules with fx26-mode's table
(`fx26-indent-specs`: a count of distinguished arguments, `defun`, the
`define-rec` and `tagcase` members as definitions; otherwise the
arguments lined up), so that what the tool writes is what TAB in Emacs
would leave. One table for both, generated from one place, keeps them
from drifting; a test that re-indents every front-end file and finds
nothing to change keeps the files to it. It never rewraps a line: a line
past 100 columns after re-indenting is reported, for extraction.

## 50. Sets for FX-26 code, imperative and persistent (the user's, 2026-10-07)

The front end keeps sets as lists and searches them (`k-has-id?` over a
walk's `seen`, `k-kseen-has?`, `k-sc-has?`, `k-named-has?`): §43's survey
and the 2026-10-07 profile found them quadratic and hot, and their fixes
each built a set on `table.fx` by hand (`k-seen`, the knot search's table
by type, the size-change calls by members). A library, beside `table.fx`,
with the hash or order passed as tables' are (dictionary passing):
- **Imperative**: `(set K R)`, `set-add!`, `set-has?`, `set-add-new!`
  (has it, and if not adds it: every walk's "seen"), `set-count`, a fold.
  Small sets cost as much as a table: start as a short list and become a
  table past a size, since most walks meet a handful of types.
- **Persistent**: Clojure's hash array mapped trie for unordered sets, and
  an ordered one (a balanced tree, or the sorted lists the checker now
  merges, `k-merge`) where order matters: effects and regions kept sorted
  (`k-atom-cmp`) so that equal sets compare equal. Shared structure, `acyclic`
  so it can be frozen into a place.
- Then: the hand-made ones above replaced, and §43's remaining searches
  (`c-find`, `r-where`, `c-member?`) looked at again.
- Later (the user's, not yet): reader syntax for table and set literals,
  made once as constant data, as §51's quoted lists would be.

## 51. Quoted list literals, with their shape (the user's, 2026-10-07)

FX-26 reads `'x` as a symbol and nothing more: `'((a b) c d)` is not an
expression. Read it as constant data, made once (as §44's constant lists
are), and typed by its shape: `(listof … acyclic)` for now, whatever the
nesting (a `datum`, or nested `listof`s where the elements agree). Later,
infer the precise category of the lattice (`docs/research/shapes.md`):
- **tree** (acyclic, no sharing), **flat** (no pointers into the heap),
  **atomic** (no parts: integers, characters, symbols, bignums), and
  **flatomic**, the user's name for both flat and atomic (fixnums,
  characters, booleans). Bignums and symbols are atomic but not flat: they
  point into the heap. This refines the `atomic` kind planned with Q7's
  unions (§46): `flatomic ⊂ atomic`, `flatomic ⊂ flat`.
- Both parsers, both checkers; the compilers make the datum once, as a
  frozen constant, and fold `car`/`cdr` through it as §44 does.
- **Progress (2026-10-08).** `datum` is no longer opaque: a union, `(union
  int f64 char bool string symbol nil (pairof datum datum acyclic) vector
  bytevector)` (`check::DATUM`), in both checkers' standard environment,
  with `vector` and `bytevector` new opaque shapes and `f64?`, `vector?`,
  `bytevector?` new tests; `car`/`cdr` of a union's pair member count as
  parts for termination. So a quoted list's type can be `datum` with no
  new type. A cyclic counterpart (datum labels) would be the same union at
  `const`. The `datum-` constructors, predicates and accessors are
  retired (2026-10-08): `car`/`cdr` of a union with a pair member are
  checked as of a pair that may be `nil`; the identity casts
  (`datum-int-value` and kin, unchecked at run time) became tests or
  `typecase`s. Natively: `deriv` 2.69 → 0.92 s, `dderiv` 3.38 → 1.65,
  `earley` 3.77 → 3.34, `peval` 7.18 → 6.77, answers the same; `parsing`
  8.1 → 8.3 (same allocation and collections: to look into).
- **Progress (2026-10-08).** `quote` of any datum and `quasiquote`, with
  `unquote` and `unquote-splicing` and R7RS depth, in both parsers
  (`docs/fx26.md`, "Datums"). Quoted data are interned, a weak
  hash-consing table in the heap (the user's; its entries weak pairs since
  2026-10-08, `docs/research/weak-references.md`): made once at compile time
  where all literals, one object for equal quotes and inlined copies, a
  quasiquote's constant parts too, `eq?` alike on every machine and the
  FX-26 evaluator (a table of its own, `ev-intern`). Register code folds
  `car` and `cdr` of a quote made at compile time, as of a constant list.
  Left: a splice before a dotted tail; a quoted
  bytevector; and the lattice's categories, above.

## 52. Deep recursion in native code: what is left (the user's, 2026-10-07)

Larceny's stack cache, stages 1 and 2, is done (`DONE.md` §52;
`docs/research/deep-recursion.md`): native code recurses as deep as its
heap allows (up to `FIXPT_NATIVE_STACK_MAX`, 2^28 words by default), its
stack in the nursery, flushed in place at every collection and overflow.
Left:

- **Deep recursion and the return stack predictor** (2026-10-11,
  `docs/performance.md`, "Native returns by `br`, tried and undone"):
  past a few dozen frames every native `ret` is mispredicted (`closures`
  21.4 ms, against 9.2 returning by `br x30`); but `br` costs shallow
  calls (`fib`, `peek` about 10 %). To try: `br` only where a recursion
  is deep, e.g. a second entry for calls made deeper than the predictor
  holds (a depth counter in the frame), or returning by `br` from frames
  that a stack-cache flush or a counter marks deep.
- **A capture copies its frames** (sampled 2026-10-11): `captures` is
  slower natively than as register code in the cellular convention (9.4
  against 7.5 ms). A third of its native time is `Heap::vector_with`,
  `chunks_of` copying the 20 frames each capture takes into a heap
  vector (about 1.3 ns a word, so the copying itself is not slow; that
  it happens each round is). Ideas, for later: copy lazily (the frames
  stay on the stack until a resumption or a collection needs them), or a
  capture that its handler resumes at once (as here) not copying at all.

- **What the stack costs the collector, measured (2026-10-07).** Unlike
  Larceny, which flushes the stack at every collection, minor or major
  (`src/Rts/Sys/nursery.c:211-216`), so its collector never walks one,
  fixpt's collections take the native frames as roots, each by its stack
  map; and an overflow's chunks go to the nursery, to be copied again when
  promoted (the user's two questions). `(dive D 200000)`: a recursion `D`
  deep that allocates nothing, then 200 000 lists of 100 made and dropped
  at its bottom, about 38 minor collections (`direct.rs`, a scratch test,
  not kept; default cache, 2^25 words):

  | depth `D` | total ms | minor ms each | M words flushed, then copied by minors |
  | --------: | -------: | ------------: | -------------------------------------: |
  |        10 |       41 |          0.03 |                                      0 |
  |   100 000 |      100 |          0.13 |                                      0 |
  | 1 000 000 |      732 |          1.39 |                                      0 |
  | 3 000 000 |    2 118 |          4.31 |                                      0 |
  | 4 500 000 |      458 |          2.01 |                             33.6, 33.6 |
  | 8 000 000 |    2 935 |          7.59 |                             33.6, 33.6 |

  - The collector's scan of the frames: about 1.4 ns a frame a minor
    collection (Cheng, Harper and Lee's problem).
  - Gathering them, before it: about 17 ns a frame a collection, most of
    the total (at 1M deep, ~650 of 732 ms). `native_frames` builds a
    `Vec` of runs per frame (`traced`) and a slice per run, every
    collection: `malloc` and `free` lead the profile, `collect_minor`
    well behind. A quick win whatever the design: hand the collector the
    runs without a `Vec` per frame.
  - Flushing beats scanning even copied twice: 4.5M deep (one overflow,
    33.6M words flushed, then all of it copied by one minor collection)
    took 458 ms; 3M deep, all in the cache, 2 118.
  - So the copying cache paid both costs Larceny's design avoids: frames
    in the cache scanned at every collection, frames past it copied
    twice. Larceny pays instead an underflow per frame returned to after
    each collection. Adopted (the user's, 2026-10-07): stage 1, the stack
    flushed at every collection, and stage 2, in place in the nursery, are
    done (`DONE.md` §52: 1M deep 732 → 88 → 65 ms); stage 3 is below.
- **Stage 3, underflow in line: not worth it yet (measured 2026-10-07).**
  Larceny's `memory.s` gained 15-50% on deep recursion by doing its
  underflow in assembly, but it switched context for every frame; fixpt's
  call-out restores up to 256 words each time. `,native down 150000000`
  (3.75 s), by samples: the minor collections promoting the chunks about
  33%, `memmove` (mostly theirs) 20%, the native code 17%, `restore`'s
  copying 11%, `flush_in_place` 8%, the frames' list collected into a
  `Vec` (`frames_from(…).collect()`, per overflow) 7%, the call-out
  machinery 1%. The copying is the cost, not the call-out; the `Vec` is
  the cheap win. Measure the window (Hieb, Dybvig and Bruggeman:
  "determined only by experimentation") against one frame, as Clinger,
  Hartheimer and Ost recommend, if underflows ever show.
- **A nested run's room**: a native call from cellular code a native run
  called (`call_native`) runs below the outer run's frames; its overflow
  flushes only its own, so an outer run that filled the stack leaves it
  little. Flush the outer run's too, or give the nested run a fresh area.
- **Control frames past the limit**: a prompt's or a mark's frame checks
  only against the limit less 32 KB (the next procedure's frame flushes
  it): about 680 control frames with no procedure frame between would
  overflow the stack.
- **Return addresses as addresses, for images** (the user's question,
  2026-10-07): a chunk keeps a frame's return address, and a native
  continuation where it resumes (`Pos.pc`), as fixnums of addresses. The
  code area does not move, so they stay right while the process runs; a
  heap image that carries native code would need them as offsets.
  - Today nothing is unsafe: an image refuses any heap with native code
    in it (`Heap::image_parts` asserts the code area empty), a native
    continuation's included, by a panic. Making that an error saying why
    is a small change, wanted sooner or not (the user's to say).
  - Larceny converts at every flush and every restore
    (`src/Rts/Sys/stack.c:159`, `retaddr - (codeaddr + 4)`; and
    `stk_restore_frame`, `stack.c:236-249`, `(codeaddr + 4) + retoffs`,
    from the procedure in the frame's `REG0` slot; a slot of 0 keeps the
    address raw, for code that never moves). Its code vectors are
    bytevectors in a moving heap, so it must: a raw address would go stale
    at the next collection.
  - fixpt's code does not move, so only an image needs offsets. The plan
    (the user's choice): convert when the image is made, walking every
    chunk and native continuation, and back when it is loaded; nothing on
    the flush and restore paths. Each procedure frame keeps its code
    bloblet in a slot, the base for its offset. To decide then: the frames
    with none (a 16-byte stub's, whose return is into its caller's code; a
    prompt's landing, into its owner's; the run's outermost, into the
    machine's trampoline, which is not the heap's), as Larceny's `REG0 = 0`
    frames are.
  - Part of the same change as images carrying the code area at all
    (`docs/object-model.md`, "A collected code area").
- **"Never collects"**: the overflow allocates (never collecting; the next
  call-out that may collects); an inference of procedures that never
  collect (discussed with `never_collects`) must count a frame-making entry
  as allocating.


## 54. Propositions in procedure types (the user's, 2026-10-07)

What a test's result says of its arguments is not an effect (what a call
does) but part of its type: Typed Racket's latent propositions (a
function type `τ → σ ; ψ+ | ψ− ; o`, propositions where the result is true
and where false, about an object such as parameter 1; Tobin-Hochstadt
and Felleisen, ICFP 2010), TypeScript's `x is T`, Python's `TypeIs`; in
refinement terms a refined `bool` that depends on an argument.

FX-26 has several, each hard-coded in both checkers: `null?` (and Q7's
shape predicates, `pair?`, `int?`, …) narrowing a variable; `<`, `=` and
`null?` of a `nlist` giving size facts; `length-is?` and `acyclic?`
certifying. One mechanism would take their place, the built-ins then
ordinary standard types, and let a user's `item-null?` narrow too
(`docs/research/logical-types.md`, question 5).
- A form in `subr`'s result, `(bool (then P …) (else Q …))`, `P` and `Q`
  conjunctions of facts about parameters: a shape (`(shape 0 pair)`, cheap,
  since union members' shapes are disjoint), a size relation (the linear
  facts the checkers solve already), a certification.
- A call on variables gives the facts for its branches; `not`, `and`, `or`
  combine them as now (conjunctions only).
- Checking a `lambda` against such a type: its body's own propositions
  must imply the declared ones (what makes a user's predicate sound).
- Subtyping: proving more fits asking less, covariantly, as a result does.
- After Q7's stage 2, whose built-in predicates are the first instance.
- Types on paths (the user's, 2026-10-07): what a proposition is about is
  an object, as Typed Racket's are, a path from a variable — `(car x)`,
  `(cdr (cdr x))`, `(extract p 1)` — not only a variable, so `(if (int?
  (car x)) (+ (car x) 1) …)` narrows. Sound only where nothing between
  the test and the use can change what the path reaches: through frozen
  pairs, products, sums and immutable bindings, never a mutable pair, a
  `ref` or an array (whose writes would have to forget what is known, as
  `set!` would). A proposition in a procedure's type names its object by
  parameter and path (`(shape (car 0) int)`).
  Done (2026-10-08), by the effects rather than immutability alone (the
  user's): a test's fact of a path from a variable (`car`, `cdr`,
  `extract`) lasts, in the order of evaluation, until an effect writes a
  region the path reads through, or one that may be it, or transfers
  control; not in closures' bodies; through frozen data and products for
  the branch. Sound under the concurrency rule written into
  `docs/fx26.md`: only tasks whose effects do not interfere run
  interleaved, and every suspension is a control effect. Not yet:
  propositions in a procedure's type about its parameters' paths, `(shape
  (car 0) int)`, which wait on checking a `lambda` against such a type.

The user's word (2026-10-07): once stage 2 works, reframe its narrowing as
explicit latent propositions in the predicates' standard types, a coherent
type-signature model for the analysis; checking a `lambda` against such a
type can wait.

Begun (2026-10-07), the shapes: a procedure's result may be `(bool (then P
…) (else Q …))` (the user's dislike of `tests`; `proves` is the lemmas'),
each proposition `(shape i S)` or `(not (shape i S))`; the shape
predicates' standard types say what they prove, and both checkers narrow
from the callee's type, not a table of names; a call's own type is
`bool`. Then (2026-10-08) the size facts and certifications too: `(<
a b)`, `(<= a b)`, `(= a b)`, `(not (= a b))` of terms (an argument as a
natural, `(length i)`, `(lit k)`), and `(acyclic i)`, `(nat i)`, `(length
i j)`; `<`, `=`, `null?`, `acyclic?`, `nat?`, `length-is?` say theirs in
their types, and both checkers read every test's facts from its callee's
type, none from its name (`sizes/latent-alias.fx`: aliases at their types
do as they do). Left: checking a `lambda` against such a type (until then
refused, its body a `bool`). Paths done too (2026-10-08, below).
Checking a `lambda` against such a type waits on a concrete motivation, a
program that needs its own predicate to narrow (the user's, 2026-10-08).
Since 2026-10-23 the form is an `ensures` (§116); the rule against a
`lambda` claiming it covers an `ensures`'s `(implies r …)` conjuncts too.

## 58. `sum` cannot be a keyword (the user's, 2026-10-08)

`(sum tag expression)`, the injection into an anonymous sum, takes the
name `sum` from every program: writing the `datum` union's test program, a
`(define* sum …)` was read as a malformed injection (`(sum tag
expression)`), in both parsers (`parse.rs`, `parser-exps.fx`). A program's
own definition should win, as a local binding does for an ordinary name.
Likely through modules (§34, §37): the core forms as a module's names,
imported by default and shadowed or qualified (`(with #%fx sum)`, as
standard references already are, §46). The same holds for the other
forms written as names a program would want (`product`, `extract`,
`new`, `get`, `set`, …): a survey of which are keywords, which are
standard bindings, and which could move from the first to the second.

## 59. Weak tables: ephemerons, and an eqtable that holds keys weakly (the user's, 2026-10-08)

Weak pairs are in both collectors (`docs/research/weak-references.md` §3),
and the intern table is made of them. A table keyed by identity whose keys
are held weakly needs more: its value may refer to its key (a property
table, a memo table of a pure function, such as the derived equality and
hash of `polytypic.md`), and with weak pairs that value keeps its own key,
and so its entry, alive. That is what ephemerons are for (Hayes, OOPSLA
1997):
- An `ephemeron` kind beside `weak-pair`: key and value traced only once
  the key is reached otherwise, by a fixpoint in both collectors (a queue
  of ephemerons met, rescanned until only unreached keys remain; Chez's
  collector keeps them pending per segment instead), then both cleared.
- A weak-key `eqtable` (`fixpt_runtime::eqtable`) of ephemeron entries,
  pruned at its rehash after a collection as the intern table is.
- Its type and effect: invisible as long as a program cannot tell an entry
  went (a cache of a pure function); a lookup that can tell is an
  observation of the collector, and carries an effect.
- Then, if wanted: guardians (or argument-only cleanups, as Go's
  `AddCleanup`) for what no region owns, the poll an effect; and regions
  that own resources (custodians) with the async work (`async.md` §5).
- **An editor needs it** (2026-10-18): a buffer's marks move with its
  changes, so the buffer must reach them; one held only by the buffer
  should die, or every mark a command makes and drops lives as long as
  its buffer (the prototype keeps a list of them, and leaks so).

## 60. Type-family applications kept, unfolded on demand (the user's, 2026-10-08)

A family (`(define-type (stack (t type)) …)`, a `define-datatype` with
parameters) is expanded by substitution where it is used ("Type
abbreviations with parameters", `docs/fx26.md`), so a message shows
`(stack int)` written out, and a datatype of one shows its expansion at
every use; closed types keep their names (`closed_named`, 2026-10-08), an
instance of a family cannot. The user's suggestion: do not beta-reduce the
application and force the substitution; keep `(stack int)` as an
application with its arguments (an environment for the body's
parameters), and unfold it only where an operation needs its structure.
Then substitution maps over the arguments and shares the rest, and the
printer shows the application as written, families that are not regular
(a recursive use at other arguments) included, since nothing needs to
unfold them whole.
- Precedent: OCaml keeps an abbreviation as `Tconstr` and expands it
  lazily (`Ctype.expand_head`), with a cache of expansions; FX-26 itself
  keeps generative types as `Ty::Named` and description functions as
  `Ty::App`.
- Each structural operation (subtyping, unification, shape, narrowing,
  `closed_data`) unfolds one level on demand, under the trails it has; an
  application against the same family's application compares arguments
  first (by variance), and unfolds only if that does not decide.
- Both checkers; the printing then needs no matching of a type against the
  families. Ties to the non-regular work (`docs/research/nonregular-*.md`).

## 63. Fixed-width values as sizes (2026-10-08)

`i64` and `u64` are below `int`, with literals (`DONE.md` §63). Left:
fixed-width values could also count as sizes (`nat` terms), since each is
an integer the checker knows the range of.

## 65. Named parameters in `subr` types (the user's, 2026-10-08)

`(subr pure ((x val)) (bool (then (shape x int))))`: a `subr` type may name
its parameters, and a latent proposition refers to them by name, as a GADT
guard refers to a type variable (`docs/research/gadts.md`, "GADTs and latent
propositions"). Numbered references stay for unnamed parameters. Both
checkers, both printers (a named type prints its names), and the standard
predicates' types rewritten to use names. Names are not part of the type's
identity: `(subr pure ((x int)) int)` and `(subr pure (int) int)` are the
same type.

## 68. The front end as modules: what is left (the user's, 2026-10-08)

The conversion is done (`DONE.md` §68). Left from it:

- Profiled (2026-10-09), against 452274e^ (before phase 2), back to
  back: the front end's text grew 34% (29,878 lines to 40,019; 3,946
  more definitions, nearly all imports). Three costs had grown far
  faster, each a walk along something phase 2 made long, and each fixed:
  the Rust checker's masking walked the regions of every free variable's
  type, signatures included, at each node (now kept by type, `69d9fc2`:
  1300 ms to 540, from 677 before phase 2); the FX checker looked for
  each type among the closed named ones in a list (now a table,
  `c9485fa`: 5.36 G cells to 4.51 G, from 4.43 G); and the FX compiler
  looked for each expression among every module reshaped (now indexed by
  start, `7989f6f`: 5.37 G cells to 1.04 G, from 0.80 G; 646 ms to 301,
  from 252). Left: every phase but one now grows no faster than its
  input (`fx check` +23%, `fx words` +19%, `fx arm64` +21%, `fx read`
  +27%); `fx parse` (11.3 ms before phase 2, 23.6 after): its search for
  each load's file among all 850 is gone (`2980a06`), and each loaded
  file is read at its base rather than its syntax moved there afterwards
  (`77d7ec5`): 13.9 ms, 27.6 M cells (26.0 M before phase 2). In the FX
  compiler, `c-find` (90 M cells to 181 M) and `c-member?` (38 M to 116
  M) walk lists of names that the imports lengthen; in the FX checker,
  `k-has-name?` (160 M to 317 M). §69 and §70 shorten the imports; these
  may be worth tables then. `probe_profile_check` names each word by its
  loaded file's number now (`lambda/k-…@1009:…`), so its count of the
  checker's own cells says 0: to fix.
- Effects written naming globals that are now a module's imports,
  `(read (globals exp-end exp-start))` and the like (`regcode.fx`,
  `compile-programs.fx`): checked, as they say more than is done, but
  naming what is no longer a global.
- The size debts phase 2 raised by imports alone: `check-rules.fx` 1358
  lines (from 998 before it was made by the conductor), `regcode-core.fx`
  1419 (from 1125); each split moved into `check-rules.fx` raised it two
  lines more. After §69 and §70 shrink the import blocks, set each entry
  to its new size, or split the file if it is still over 1000
  (`crates/fixpt-tidy/fx-size-debt.txt`).
- A constructor imported from a types file, `(with X-types ctor)`, is not
  known code to either checker, so a call of it may `spin` where its own
  module's call would not (found in the pilot, 2026-10-08). Phase 2 put
  such imports in nearly every file, so more of the front end's effects
  say `spin` than need to, which hides from the compilers what the types
  prove. Wanted: an import of a known procedure or constructor from a
  module as written is known, in both checkers, agreeing; then count the
  front end's `spin`s before and after.

## 69. Combining modules: what is left (the user's, 2026-10-09: high priority)

`(extend e0 e1)`, `(include m)` and `(hide item …)` are done (`DONE.md`
§69), all made one way: a module of hidden items its values are taken
from by path (a reshape, as a module given where fewer values are wanted
is). Left:

- A hidden abstract type in an exported one: refused for now (the
  user's, 2026-10-09); abstract in the module's type, the existential
  reading, could come later. Likewise an `extend` whose `e1` replaces an
  abstract type of `e0`'s own that a value kept still mentions (`DONE.md`
  §69, `modules/extend-abstract-replaced.fx`).
- Done (2026-10-11): an `include`'s types in scope inside the module;
  they were already, by `with` shadowing (§69's `with` work), but an
  item was not checked against the type it declares (its `(with
  %include e)` synthesized), so `cons` there made its pair at a fresh
  region; now a `with` checked against a type checks its body (`DONE.md`
  §69).
- Done (2026-10-11): the pass these were wanted for (`DONE.md` §69):
  5,684 import lines in the front end's files down to 637, by `(hide
  (include m) …)` of the modules each file is given and the types files
  it loads. What stays: a module whose value the file's signature gives
  on (an include would give it twice), a types module whose type family
  the file uses (an included family is not yet applied in a declared
  type: to do), and re-exported types' lines.
- The cost, measured on a quiet machine (2026-10-11, the commits before
  and after the pass built side by side, alternated four times). Running
  the compiler (peval's `fx` phases): about 3 % slower, `fx check` and
  `fx words`; an item's lambda's body is `(with %include …)`, so each
  call loads the included names it uses from the bucket, where an import
  bound them once. Done (2026-10-16, `DONE.md` §69): the names bound once,
  at the module, as the import lines did. Checking the front end itself,
  much more: `check` 575 → 762 ms,
  `fx check` 1295 → 2127, 223.6 → 273.9 M words. Mostly the bucket made
  quadratically, each name looked for in a list of those so far, in both
  checkers; fixed (`DONE.md` §69): `check` 555, `fx check` 1475, 228.7 M
  words; and since the front end's integer arithmetic went in line
  (`docs/performance.md`), 1233, below before. Was left: `fx check`
  still about 14 % over; not `k-with-used`'s scan
  of the bucket for each item (a memo of it changed nothing). Profiled
  with `FIXPT_SYMBOLS` and `fixpt-symbolize`, before the pass and after
  the fixes: no one place; the difference spread over collections (+56
  samples of 7,302), copying, the assembler over more code (+25) and
  `k-has-name?` (+8).
- Done (2026-10-11): an included type family applied in a declared
  type (`DONE.md` §69). Left: the front end's files that kept
  table-types's import lines for it could now include it.

If `extend` is ever n-ary, `(extend m1 m2 m3)` should be a left fold (the
later wins), not "all at once", which would blur it and `include` together:
`extend` is ordered, binary and nested, the later and deeper winning;
`include`s are unordered, side by side, as a module's own definitions are.

## 70. Short names for the modules a file binds, after §68 phase 2 (the user's, 2026-10-09)

Once every file is made by the conductor, a pass that alpha-renames the
modules each file binds locally to succinct abbreviations: the types
files its `let*` loads (`check-types-types`) and the modules its
`lambda` is given (`check-subtype`, typed `check-subtype-sig`), wherever
they are named in the file (`(select check-types-types k-map)`,
`(with check-subtype k-subtype)`). Today each is its file's full name,
which makes the import blocks long and wide. Mechanical, a commit for the
pass; the conductor's own names are untouched (they are its bindings, not
the file's). To decide with it: one abbreviation per module for every
file (so `ct` means the same everywhere), and how it sits with §69,
which may remove many of these names outright, so perhaps after §69.
The tools that know which name comes from which file and module are in
`scripts/conductor/` (`deps.py`, `registry2.py`; see its README).

## 74. A list one element short, said of its length (the user's, 2026-10-10)

`(the (nlist int 4) (cons 1 (cons 2 (cons 3 nil))))` is told, at the
`nil`, `a (nlist int 1) is expected here, and this is a (listof int
acyclic)`: the size wanted is pushed through each `cons`, and `nil`, read
as a list, is shown as one. Wanted (the user's): an error about `nil`'s
reading as `(nlist T 0)`, the list being one element short; better still,
said at the `the` of the list's length, 3 where 4 are wanted. The user's
thought: `nil` as `(listof T acyclic) & (nlist T 0)`; the singleton type
`nil` (`check.rs:2874`) is already below both, so what is wanted is the
message choosing the `nlist` reading. One too long is told likewise, at a
`cons` against `(nlist int 0)`. For later.

## 75. `string->int` and `string->number` (the user's, 2026-10-10)

There is `int->string` and `f64->string`, and no way back: a program
reading a number from text parses its digits by hand (`k-digits`, in
`check-print-parts.fx`, which reads the variable numbers out of a
message's marks, did, 2026-10-10). Wanted: `string->int` (an `int`, a
bignum past 60 bits, as `int` is) and `string->number` as Scheme's, with
Scheme's answer to text that is no number (`#f`: here a union, `(union
int false)`, or a `sumof`). What `number` is depends on §76; until then
`string->int`, and `string->f64` beside it, are what can be typed. A
candidate for §22's library written in FX-26, no Rust at all (the
user's): digits to an `int` is a loop over `string-ref` and `*`/`+`.
- **An editor needs `string->int`** (2026-10-18): `goto-line`'s line, a
  prefix argument typed in the minibuffer, a number in a user's setting.

## 76. Scheme's numeric tower, perhaps by module functors (the user's, 2026-10-10)

FX-26's numbers are `int` (a bignum past 61 bits), the fixed widths
(`u32`, `i64` …, each with its own operations, `u32+`), and `f64`; there
is no `number`, and no rationals or complex numbers. Look into adapting
Scheme's tower (R7RS §6.2: integer ⊂ rational ⊂ real ⊂ complex, exact and
inexact), and how it fits a language whose operations are named per type:
a `number` type that is a union and operations that dispatch on it; or a
signature of arithmetic (`(moduleof (abs n type) (val + …) …)`) with one
module per kind of number, and functors over it building the next (the
rationals from any integers, the complex from any reals), generic code
taking the module, as dictionaries are passed today rather than code
copied per type. Rationals and the tower are candidates for §22's library
written in FX-26, no Rust at all (the user's). Open: what `(+ 1 1/2)`
means without a union; literals `1/2` in the reader; native speed of the
`int` path once a tower is there (it must not pay for the rest).

## 77. Suffix refs: what is left (the user's, 2026-10-10)

The runtime is done (`DONE.md` §77): tag `010`, made, projected, read and
written through the runtime's `%suffix-ref…` primitives, followed by
every collection, the verifier, images and graph copies. Left:

**The language side, after the runtime** (the user's, 2026-10-10). Suffix
refs are what FX-26's flat data will be reached by:
- **`flat` is a kind of its own**, not a subkind of `type`. Its members
  today are the six scalars `flatlayout` has (`f64`, `f32`, `i32`, `u32`,
  `i64`, `u64`); to come, `productof`, `sumof` and `arrayof` as flat
  constructors, of kind `flat → flat`, at least conceptually.
- **A flat instance is not a value.** A composite need not fit a word, so
  no `t : type` can be instantiated with one, and it is not atomic: it is
  reached at most indirectly, through `(ref F R)`, `F : flat`, which is
  first class and is a suffix ref. Projection (a field of a flat product,
  an element of a flat array) is a suffix ref at a further offset.
- **Only word-sized scalars come out as values**: reading `(ref f64 R)`
  gives an `f64`, as FX-26 has it today; that is the only place a flat
  thing becomes a value one can manipulate (the user's reading (a): a
  stored flat element is not a value; `f64` results stay first class).
- Open: how `get`/`set` know a scalar's width (the owner's layout, as a
  flat array keeps it in field 2, or the type, statically); layout of
  flat sums (a tag word, alignment); `new` of a flat ref (a one-element
  flat array, a ref at offset 0).

**Done so far** (`DONE.md` §77): the kind `flat` (the scalars), the type
`(blobref B F)`, and its operations (`blobref-at`, `blobref+`,
`blobref-owner`, `blobref-offset`, `blobref-get`, `blobref-set!`), flat
products and arrays (`extract`, `blobref-index`), flat sums
(`blobref-variant!`, `tagcase` on a blobref); in native code, a numeric
key's tag, a blobref's step by a constant, `blobref-index`,
`blobref-set!`, `blobref-variant!` (`prim3imm`) and an `f64` read raw,
in line, and a flat `tagcase` in a leaf; an index key's tag and variant
too, and `blobref-at` at a literal offset (2026-10-11). Next: each step
of a blobref takes its owner apart again (`suffix_owner`, about 20
instructions, two loads that depend on each other: the trailer, then the
header for the suffix's length), which a loop could do once. Proposed
(2026-10-11, for the user: it changes when an error comes), from what the
types already say: let `(blobref O F)` promise that all of `F` lies in
the suffix, checked where a ref is made, by the layout's size, which the
checker knows there (`blobref-at`, `blobref+`; `extract`, `blobref-index`
and a variant keep it by construction). Then no step or read needs the
length: a read is the owner's word, the offset and a load (about five
instructions), a step by a constant one `add`, and `blobref-index`
compares with its constant `n` only. The change: `(blobref-at b 10)` of
an `i32` in a 12-byte suffix would fail where it is made, not where it
is read; a wider index into
the owner's fields than a byte (`(key symbol u16)` was proposed); and
flat arrays of a length not literal, decided below. The rule
(the user's): no operation copies more than a word unless its name says
so.

**Flat arrays of a length not literal** (decided with the user,
2026-10-12): built (`DONE.md` §77), an array that runs to the end of the
suffix, its length named where its blobref is bound, `blobref-length`,
and an index shown in bounds recorded; a new blobref's flat checked whole
in the suffix where it is made, so that its type's length holds;
`blobref-length` in line natively. Measured (2026-10-12, a loop summing a
million `i64`s, ns an element): 9.4 with `blobref-length` a call-out, 3.2
in line; a read with no owner found 2.8; and a proved index with no check
at all 2.7. So leaving out checks the proof makes needless gains 15% at
most here, and the index's part nothing measurable: not done, as memory
safety would then rest on the checker. What remains of the loop's cost
is the length found again each time round (its owner, a division), and
an `f64` total's box (about 7 ns, `fixpt bench`'s concern). Heap
arrays' bounds are shown as flat ones' are (`narrayof`, `DONE.md` §77),
34 of the ports' 732 indexes; more would need indexes counted as `nat`s,
facts of a count down (`(>= i 0)` before `(- i 1)`), or arrays of arrays'
lengths, each waiting on a need. A non-last array of a length a `(nat n)`
in scope gives (offsets after it computed from `n`), waiting on a need.

**Flat sums: their key** (the user's, 2026-10-10; the goal: a "flat
world" with Rust's model of values, for apples-to-apples benchmarks).
FX-26's labels are names (a positive integer only a spelling, interned
as a name; a sum value holds a symbol), and a sum has no key type. A flat
sum says its key, which decides the encoding:
- **None given, the default: the tag is an index into the owner's
  fields**, which hold the labels as symbols (`u8` wide; wider not yet):
  so a flat sum's tags mean what a value sum's do, and sum types
  interoperate (the user's choice, for that). A read loads the byte, then
  the field; a `tagcase` with no arm for what it finds fails at run time.
  Done so: no static table; `(blobref-variant! r 'b)` finds the first
  field holding `b`, a write failing where none does; the program puts
  the labels in fields itself (`(make-bloblet n 'a 'b)`).
  Sound whatever the bytes say: flat scalars have no invalid bits, so a
  wrong tag only reads bytes as another variant (the payload area sized
  for the largest). Nothing keeps the labels unique or stable (the
  user's, 2026-10-10: "we'll see how it goes"): a label in two fields
  reads back the same through either index, the lowest one written; a
  label field overwritten turns every value tagged with it into the new
  label's variant. Declared tables (singleton symbol types, which FX-26
  lacks: its unions are of shapes, and every symbol has one) would make
  both static: distinct labels a condition of the type, and a field of
  type `'a` holding only `'a`.
- **A key, `(sumof u8 …)`, `u16`, `u32`: numeric labels, stored as they
  are** (0 allowed, everywhere now), compared against constants: Rust's
  model; and sum types sharing codes agree on them with no indirection.
  `u8`/`u16` only as key widths, no value types. Done; written as a bare
  first item, not `(key u8)`, which a variant named `key` could be.
- Reading through a flat sum (done): a `tagcase` on a blobref to one binds
  each arm to a blobref to its payload (no copy); `else` binds the blobref
  as it is, and may later be refined to the tags left, the run-time check
  keeping it sound under aliasing. The payload at the widest variant's
  alignment, the size padded to it.

**Field indices in flat data** (the user's, 2026-10-10: to be leveraged).
A suffix ref has one owning bloblet, recoverable from it, so a flat
component can be a small index (a byte) naming one of the owner's fields:
pointers held in tagged fields, named from flat data, with the suffix
still holding none (the collector traces fields only, a store goes
through the field and its barrier, and the flat data stays
position-independent when the owner moves). Open:
- the connection need not be in `F` (the user's, 2026-10-10): the index
  is a plain byte, and code makes the connection explicitly, through a
  primitive from a blobref to its owning bloblet (the runtime's
  `%suffix-ref-owner`). Open is that primitive's result type: (a) the
  blobref's type carries the owner's, `(blobref O F R)`, so field accesses
  are checked statically; (b) a bloblet of no known fields, checked at run
  time or cast; (c) none: code that needs the fields keeps the typed
  bloblet it made the refs from;
- an index's width: a byte (255 fields), or by the layout;
- who establishes and keeps "field k holds a T", and aliasing (two bytes
  naming one field);
- a frozen suffix with fields not frozen: layout fixed, pointers mutable,
  which the flags already allow.

**Bloblet types by width: an interface for a family** (the user's,
2026-10-10). If a blobref's type carries its owner's bloblet type, it must
respect subtyping: one type covering a family of bloblets with more fields
and a longer suffix. Today `(bloblet (fields T …) R)` declares each
field's type, the suffix has none (bytes), and subtyping demands the same
number of fields (`check.rs`, mutable fields invariant, frozen covariant).
Width subtyping looks sound by the layout: a program's field `i` is the
object model's `i + 2`, counted *from the suffix* outward, so a bloblet
with more fields (further out, as `bloblet_extend` adds them) keeps every
field's offset, and a longer suffix every byte's. Checked 2026-10-10:
compiled code reaches a field by that offset alone (`cellular.rs`'s
`self.field(code, i + 2)`, `lower.rs`'s `%bloblet-ref b (i+2)`), and the
rest (freezing, bytes, length) through runtime primitives that read the
header; nothing uses a static field count. So:
- `(bloblet (fields T₀ … Tₙ Tₙ₊₁ …) R) ≤ (bloblet (fields T₀ … Tₙ) R)`,
  each shared field as today (invariant, or covariant if frozen). Every
  bloblet type then reads "at least these fields": the interface needs no
  form of its own, unless something comes to need an exact count (an
  inline header read by a static F), which could be marked then.
- With a suffix layout in the type, `(bloblet (fields …) F R)`, likewise
  by prefix: `F₁ ≤ F₂` where `F₂`'s layout is a prefix of `F₁`'s.
- Kept: freezing is still a change of type, never a subtype.
- **Exact or a lower bound, both** (the user's, 2026-10-10: fine to tell
  apart a type that declares its exact field list from one that declares
  only a lower bound). Proposed: `(bloblet (fields T …) R)` stays exact,
  today's meaning and what `make-bloblet` gives; `(bloblet (at-least
  (fields T …)) R)` is a lower bound, and `(at-least (frozen T …))` with
  it. Exact ≤ exact when the counts are equal; exact or at-least of m
  fields ≤ at-least of n when m ≥ n; at-least ≤ exact never. Shared
  fields compared as today. What exact buys: field access is by offset
  from the suffix either way, but an exact count puts the header at
  8(F+1) bytes before the suffix, so compiled code could read the length,
  frozen flags and kind in line, without the trailer or a backward scan.
  The suffix's layout likewise: `F` exact, or `(at-least F)`, a prefix.
- **Is the exact form needed?** (the user's question, 2026-10-10.) Not for
  speed: nothing uses a static field count today. But exactness does a
  soundness job now: every bloblet type lists every field, so it mentions
  every region its fields reach, and `letrena`/`letreap`'s escape check
  (`close_region`: the regions a value's type mentions) and masking rely
  on that. A lower bound forgets its hidden fields' regions: a bloblet in
  `@heap` with a hidden `(ref int r)` field, viewed as `(at-least (fields
  int))`, would escape `(letrena r …)` and dangle. (Products have no width
  subtyping either, likely for this.) So a lower bound must say what it
  hides: proposed, it names the regions its hidden fields may reach,
  `(at-least (fields T …) (regions r …))`, and widening is allowed only
  where every forgotten field's regions are among them (a coarser rule,
  "hidden fields reach only regions outliving the bloblet's", needs
  outlives facts FX-26 does not generally have). To check too: whether
  the `data`/`acyclic` shape analyses (`check.rs`) need every field seen.
- **Done** (`DONE.md` §77): width subtyping, by the rule below. Left: a
  message saying which field could not be forgotten and why; the
  suffix's layout in the type, by prefix, once `F` is there.
- **Plan (the user's, 2026-10-10): today's syntax *is* the lower bound**;
  an exact form waits for a need. Checked against `check.rs`'s walks of
  a bloblet's fields: the region-only ones (`regions_walk`, the escape
  check and masking; `storage_regions`; `data_places`; `writes_in`) stay
  sound if forgotten fields reach no other region; but `data_walk` (a
  frozen bloblet is data only if every field is) and `knot_in` (recursion
  tied through the store, for termination) need more, and a lower-bound
  type cannot say whether anything is hidden, so they would have to
  assume the worst of every bloblet, changing existing verdicts. So
  widening checks what it forgets, against one fixed rule that keeps a
  type's hidden fields invisible to every analysis: a field may be
  forgotten only if (1) it reaches no region but the bloblet's own
  (whether `@heap` may be left out: see `storage_regions`), (2) it is data
  where the bloblet is frozen, and (3) it holds no procedure, directly or
  through storage. Every analysis then keeps reading the listed fields
  alone, existing programs keep their verdicts, and the common widenings
  (fields of numbers, flat data, same-region structure) pass. An exact
  form, or a way past the rule (a hidden-region list), when needed.

**`(blobref F R)` or `(ref F R)`?** (the user's, 2026-10-10: open to a
type of its own, since a suffix ref is "a pretty special snowflake".)
Leaning to a type of its own: its parameter is of another kind (`flat`,
not `type`); it has projections a box has not (a field, an element) and
reads only at scalars; writing through it marks no card and stores no
pointer; and `ref`'s rules (variance, `new`, `get`'s type) would each
need a case by kind; and if the owner's type rides along (`(blobref O F
R)`, above), `ref` cannot carry it. To decide with the user.

**Native code.** Compiled code reaches suffix refs only through the
runtime today. Once the language types them: read and write in line, the
owner by `ubfx` (bits 3..37), the offset by `lsr #37`, at heap base +
owner<<3 + offset.

**Not planned:** refs into fields or pairs (a locative would need another
encoding), the direct-address variant with owner hints, segment tables, a
boxed fallback for owners of 128 MiB or more.

## 79. Intersections of procedure types, `overload` (the user's, 2026-10-11)

Designed, not built: `docs/research/logical-types.md` (decision 4 and
§8, "Proposed syntax") proposes `(overload (subr …) …)`, intersections of
`subr` types only, with Davies and Pfenning's restrictions (introduced
only by checking a `lambda` against each arm, no distributivity),
ordered selection at a call, one convention; `PLAN.md` Q7 has it as
"later", its open questions the user's (`logical-types.md` §9).

A use that came up (kayak's `length` report, 2026-10-11): `length` of a
`(listof T acyclic)` now checks by subtyping (`b5ae910`), but of a list at
a region it is refused, `list-length` being the operation for that. One
`length` for both would be
`(overload (poly ((t type) (n size)) (subr pure ((nlist t n)) (nat n)))
(poly ((r region) (t type)) (subr (read r) ((listof t r)) nat)))`: each
call the more precise member it fits, its own effect. Arms that are
polymorphic are a question the note leaves open (its examples are
monomorphic). To settle with the open questions: how a call's choice is
shown in messages, principal types, inference's interaction with the
choice; both checkers must choose alike. The compilers need nothing for
`length`, whose arms are one list walk at run time; arms with different
code would.

## 80. Real literals as `f32` where one is expected (kayak's request, 2026-10-11)

Since `fb86975` an integer literal checks as any fixed-width integer type
it is in the range of. kayak also asked for a real literal checked
against `f32` to be one (the user's, 2026-10-11: left as a TODO for now).
Unlike the integers, this changes the value's representation: a real
literal is a boxed `f64`, an `f32` an immediate (subtag 9), so the
checker must tell every compiler (the lowering, the cellular and register
compilers in Rust and in FX-26, the evaluator) to make an `f32` constant
there, through a fact on the literal. To settle: a literal that does not
round-trip through `f32` exactly (`0.1`): accepted, rounded, as Rust and C
do, or refused.

## 81. Register code to machine code, in FX-26: `fx-regs-fxjit-nativecc` (found 2026-10-11)

Naming the machines by who generates code, what code, and what runs it
(§78) showed a gap: there is no `fx-regs-fxjit-nativecc`. `native.fx` ports only
the cellular words' assembler (`fixpt-native/src/cellular.rs`'s
`assemble_word`, about 935 lines of FX-26), which `--cellular-machine
fx-compiled` uses. The compiler from register code to arm64, `direct.rs`
and `direct/reps.rs` (about 4,900 lines of Rust), has no FX-26 twin, so the
fastest machine, `fx-regs-rsjit-cellcc` (the default since §78), depends on Rust
for its last step: "FX all the way down" (`PLAN.md`) holds for the
cellular machines only. A port would follow `native.fx`'s pattern: the
Rust compiler as its oracle, the same instructions for every procedure
(as `tests/native.rs` checks `native.fx`), over the encoder `arm64.fx`.
Size: about five times `native.fx`, and `direct.rs` is still moving
(blobrefs, flat sums, raw `f64`s in §77's follow-ups), so a port is best
started once it settles.

## 83. GADTs: constructors that refine their type's parameters (the user's, 2026-10-11)

Planned in `docs/research/gadts.md` (stages N1–N6) and listed in
`PLAN.md`'s queue (item 7, "GADTs (N4, to design with the user)"), but
until now with no section here. What is done: N1, nominal families; N2,
declared variance, invariant by default; N3, lemmas (`proves` types,
erased identity coercions); N6, the `data` kind and `acyclic`. On the
propositions' side: §54's latent propositions and §65's parameters by
name. Left, N4, GADTs proper, in both checkers and both front ends:

- **A variant states its result type.** `(tag field … => (expr int))`,
  with a leading list of binders, `((b type) …)`, for the constructor's
  own type variables; one not in the result is existential. A variant
  without `=>` means `(expr a)`, as `define-datatype` does today.
- **Refinement in `tagcase` arms.** With the scrutinee's type `(expr a)`,
  `a` rigid (a `poly` binder from a declared signature), an arm checks its
  body under the equation its constructor states (`a = int`). Equations,
  not inequalities, which is why indices are invariant (gadts.md, E8).
  The bidirectional checker already has the signature in hand.
- **Impossible arms and escape.** An arm whose equation cannot hold
  (`vnil`'s `0 = n + 1`) is not needed for exhaustiveness. An
  existential's type may not leave its arm, as a `letregion`'s region may
  not leave its body.
- **One grammar of propositions** (gadts.md, "GADTs and latent
  propositions"): a type equation `(= a int)` is one more atom beside
  §54's; `given` means "holds under" everywhere (lemmas already use it);
  `=> (expr int)` is sugar for `given (= a int)` on a variant of result
  `(expr a)`, which is how the checkers would elaborate it. Two rules in
  the checkers, not one: values narrow by a meet and die at a write;
  type variables refine by equations and need invariance.

**To decide with the user first** (PLAN.md's "Unknown"): the spelling
(`=>`, binders, `given`); how GADTs meet subtyping (an index covariant
only under Scherer and Rémy's upward closure, which few FX-26 types meet
given width sums and region and effect subsumption; or invariant
always); and which program motivates it first. Candidates: E1's typed
evaluator (`docs/research/examples/gadts/`), whose `eval` could then be
typed precisely, and perhaps the FX-26 evaluator's `val` (`eval-values.fx`);
E5's sized `head`, a size guard, which would want N5.

**After it:** N5, size indices as their own sort with their own decision
procedure, for `confirm` (CF1, CF3), where a variant's type would say its
size.

**Where to start:** the toy examples' `; proposed` forms in gadts.md as
the first test programs (refused today, accepted after, both checkers
agreeing), then the variant's result type in both parsers.

## 84. I/O: what is left (kayak's request, 2026-10-12)

All five stages are built (`DONE.md` §84): `u8`, `i8` and bytevectors;
the `io` effects under one ordering rule, `write-out`, `write-err`,
`exit`, `main` and the exit status; files; the clock and the arguments;
the standard input. Left:
- **kayak to confirm** what was proposed back to them and built so: the
  allocating primitives taking a region; `io-error`'s kind a sum; bytes
  not UTF-8 a failure of their own kind; bytevectors written in place
  (no builder); and the lines cut off in their message, which were
  filled in as R7RS has them (`bytevector-copy`'s start and end,
  `bytevector-copy!`'s `to at from start end`).
- **Bytevectors**: one in a place (`rmake-bytevector`); a quoted
  bytevector, still refused (a reader's is the opaque `bytevector`, not a
  `bytevectorof`). (Reads, writes and the length are in line natively
  since 2026-10-12.)
- **Later members of the family**, as kayak listed them: subprocesses,
  sockets, signals (terminal modes and bytes from the standard input are
  built, `DONE.md` §95); each a new kind of `(io k)` under
  the same ordering rule.
- **What an editor needs of them** (2026-10-18): subprocesses with pipes
  whose output is read through `pselect` beside the keyboard (`M-x shell`,
  `compile`, `grep`); and signals: `SIGWINCH` (the terminal resized,
  redisplay at the new size) and `SIGTSTP`/`SIGCONT` (`C-z`, then the
  terminal's modes set again).
- **Files: what is missing** (2026-10-18): whether a file exists; its kind
  (a directory?), size and modification time (a file changed on disk
  since it was visited); rename (saving by writing a new file and
  renaming it over the old); delete; the current directory. There are
  `read-file`, `write-file` and `list-dir`.
- **The environment** (2026-10-18): `getenv`, for `HOME` (the init file),
  `TERM`, `SHELL`, `EDITOR`; a new `(io k)` kind, or `(io args)`'s.

## 86. Failure as proof debt (the user's, 2026-10-12)

From `docs/research/failure-and-blame.md`: "may fail" read as a debt the
code carries, a precondition it has not discharged; inferred, not
written; blamed on the site that took it. In order, each stage deciding
how far the next goes:
1. Measured (`DONE.md` §86; the note's section 7, "Results"): "may
   fail" would leave 62% of the front end's definitions and 53% of the
   ports' failure-free; most spread is by calls, from few sources: `car`
   and `cdr` of a `listof` (the front end), indices (the ports).
2. Decided (the user, 2026-10-12): `error` keeps no effect; it is the
   panic, `pure`, never dropped. A failure a layer exports is a `raise`
   of §89's condition library, typed there.
3. **Debt inference in both checkers**: each expression's and
   procedure's debts, each with its site, and whether it is owed within
   or passed to callers. Replaces §85's conservative rule for `(pure)`.
4. **Blame in failure messages**: a failed run names the site that took
   the debt (a consumer, or a trusted assertion), not only the primitive
   that tripped. Debts are static, so the site can be compiled in.
5. Not for now (the user, 2026-10-12): inferred debt is enough. Later,
   perhaps, `total`, a promise a signature may make, verified.

Beside it:
- **The trusted boundaries, audited**: the standard operations' types,
  data from the host (A3), and `error` are the only places blame can
  land beyond consumers. Write the list where
  `docs/research/soundness-findings.md` keeps its assumptions, and check
  each I/O primitive's type against what the runtime guarantees.
- **Debts discharged statically**: N5's array bounds
  (`docs/research/gadts.md`) and facts that a divisor is nonzero each
  remove a class of debt; stage 1's measurement says what each is worth.

## 87. What a callee does, summarized for its callers (the user's, 2026-10-12)

Several facts are computed about a callee and wanted by its callers:
whether it may fail (§86), its effect summary (0 to 3), whether it never
collects (`never_collects`, so far for primitives only), whether it needs
a frame, and which registers it clobbers. Each wants the same three
things:
1. **A summary bottom-up for known callees**, over the call graph, a
   recursive group's settled by a fixpoint (as the checker's effect
   summaries are).
2. **Types to carry it to unknown callees**, a closure passed in or a
   higher-order procedure's argument. `subr` types already carry a
   calling convention (`cv-cellular`, `cv-native`, `cv-fx`) and
   convention variables (`cv-var`), so `map` is polymorphic in its
   argument's convention, and instantiating it brings the callee's facts
   along. A summary is effect-like: summaries join under `maxeff`, one
   fits where a larger is expected, and a procedure that saves and
   restores a register before returning masks it, as `letregion` masks
   a region. Inferred, never written, as §86's debts are.
3. **A guard where a fact can change underneath**: a global redefined by
   `define*` (F14 already guards the procedure a global is bound to; a
   summary taken from its old code needs the same guard, or its callers
   recompiled); a closure from outside whose real convention is wider
   than expected, given an adapter that saves the rest, as
   `%fx26-convert` makes adapters between conventions now.

**First instance: registers kept live across calls** (an "extra-flexible
calling convention"). Native code keeps no Value in a register across a
safepoint (`docs/research/native-conventions.md`): every call may
collect, and the collector updates only the frame's slots the stack map
names, so a pointer left in a register would be stale after a moving
collection. A Value may stay in a register across a call only when the
callee (with all it calls) never collects (no allocation that calls in,
no call-out that collects) and captures no continuation (effect summary
below 3: a copied stack holds no registers), and does not clobber that
register. Checked 2026-10-12: running out of fuel, or of stack, traps and
ends the run (`direct.rs`, `common_trap`), so a fuel check does not count
against a callee. A raw `i64`, `u64` or `f64` is not traced, so for one
only the clobber set matters.

**Measure first**: in the native code of the MLton ports, how many calls
are to callees that never collect, and how many values are spilled to the
frame around them. A code-generation trade-off, so timed on the MLton
ports both ways, not only `fixpt bench`'s eight. Other summaries this
would serve later: a frame's size, for the stack-limit check; bounded
work, for fuel checks; an allocation bound.

## 89. Conditions: raise and handle, design B (the user's, 2026-10-12)

`docs/research/conditions.md`. Decided with the user: Common Lisp's and
R6RS's model, a handler found in a continuation mark and called where
the condition is raised, before anything unwinds, returning a value to go
on with or escaping to a prompt (a restart); escape-only exceptions are
the handler that always escapes.
- **Standard procedures**, not syntax, for now (the region, key and tag
  written or inferred; syntax later if the bookkeeping proves heavy).
- The escape-only kind of prompt tag is built (`DONE.md` §89); the top
  effect, named `yolo`, kept for later.
- **Condition types: start small**, one type per key, and find what more
  is needed by using it.
- **`error` stays the panic** (§86): `pure`, never dropped, ending the
  run; caught only at a task's boundary, once there are tasks, never in
  place.
- First large user: the front end's `k-sfail`, a hand-made abort to a
  prompt today.
The first library is built (`DONE.md` §89). Left: inference into a
rank-2 argument (its parameters' types and the library procedure's
instantiation are written today; or syntax for `handle` and
`with-handler`, if that proves the better way); condition types grown as
programs need them; the front end's `k-sfail` moved onto it; a panic
caught at a task's boundary, once there are tasks.
- **An editor needs `condition-case`** (2026-10-18): a command that fails
  ends with its message in the echo area and the editor going on; §106
  is the rest of that.

## 91. Each native stack frame a bloblet (the user's, 2026-10-12)

Built (`DONE.md` §91): every native frame laid out as its bloblet, the
chain of flushed frames linked frame bloblets, and `f64`s kept raw in
frame slots, as the suffix. Left:
- **Copies leave out the alignment word** of a stub's or control frame's
  (and capture's cost, 8.75 → 10.5 ms on `captures`, the frames' header
  words): a frame copied into the heap need not keep the word that aligns
  it on the stack, its region rebuilt from its header.
- **Raw `i64` and `u64` slots**, as `f64`'s are (`raw_slots` takes only
  `f64`'s webs).
- **Deep recursion that collects as it goes costs more**: `merge` 0.66 →
  0.73 s (natively 438 → 519 ms, 95 collections each), a frame now an
  object the collector copies one by one (`copy_object`) where a chunk
  was one copy, and each restore scanning back to a frame's header (no
  trailer on the stack: a trailer word in every procedure frame pushed
  `merge`'s 50 000 frames past the stack cache, 500 collections, 1.97 s).
  Measured (2026-10-12, `merge` × 3000, best of 6: 2.91 s before §91,
  3.34 after): the collector's per-object costs (two forwarding words, a
  header read, the crossing map), about 4 ns a frame, where a chunk paid
  them once; and restore, frame by frame where a chunk was one copy.
  Tried and dropped (the user's suggestion, and the user's caution that
  Cheney's loop is hard to beat): copying ahead along a run of objects
  each linked to the next in memory (frames flushed in place), in one
  walk or by one `memmove`: 10% of minor collections' time, nothing end
  to end. Kept: restore looks for a frame's header where the frame before
  it ended (`native_frame_parts_after`), half of `merge`'s found so, 1%.
  A restore of adjacent frames by one copy needs them adjacent, which
  only the dropped run copy kept them. A trailer where a frame has a word
  to align it would not help `merge` (its frames have none).
- **Raw `f64`s at more calls** (known calls done, `DONE.md` §91; the
  user's, 2026-10-13: no masks). A call passes `f64`s raw only to a
  procedure known where it is compiled; and a procedure takes a parameter
  raw only where its code shows it an `f64`, so `nbody`'s `put`, whose
  `v` goes only to `flatarray-set!`, takes it as a value (120 M words).
  The `subr` type says `f64`, but polymorphism can hide it from a caller,
  which is why a mask was needed for unknown callees. The user's
  question (2026-10-13): unboxed floats as a kind of their own that no
  type variable ranges over, as `flat` is, so that every call agrees from
  the types; a design to write up and decide (GHC's `Double#`, OCaml's
  layouts). Written up (2026-10-16): `docs/research/raw-scalars.md`, a
  kind `raw` of types `(raw F)`, conversions inserted by the checker;
  its open questions are the user's, and it suggests measuring first
  (`nbody`'s `put`, an analysis fix; an integrator over a procedure).
- **Last, `f64`s in floating-point registers in the abstract register
  machine**: only once the `fmov`s between `x` and `d` registers show in a
  disassembly, and once register code keeps values in registers across
  more of a procedure (today nothing across a call, and parameters and
  `let`s in slots): a register allocator's project.
- **Later, frames' uniqueness restored by a collection** (the user's,
  2026-10-12). A frame (or chunk) gets a "shared" header flag, set when a
  continuation capture takes a reference to it; underflow or a resume
  that finds it clear moves the frames back and reuses them in place, not
  copying (a dynamic one-shot continuation). A collection clears it again
  where it finds exactly one reference: in a copying collection, the
  first reference reached copies the frame and leaves, in the old copy
  beside the forwarding pointer, a back pointer to the slot that reached
  it; a second reference follows that back pointer to mark the slot
  shared, and leaves a "shared" sentinel for any after. The old copy is
  garbage, so this takes no space in the live object; to-space slots and
  roots stay put during the collection, so the back pointer stays good. A
  minor collection sees every reference to a nursery object (roots, the
  nursery, the remembered set's cards), so it is exact for young frames;
  old ones wait on a major collection. Suffix refs count as references to
  their owner, roots and register code's registers too; weak references
  do not. Worth it once a workload captures often (PLAN queue item 7,
  `docs/performance.md`: capture is a small cost today). A uniqueness bit
  in every pointer is a separate, later question: no tag is free, and the
  mutator would mark a pointer shared at every copy that stays live.


## 92. Concurrency: processes and `par` (kayak's request, 2026-10-13)

Built, all three of kayak's stages (`DONE.md` §92; the design,
`docs/research/processes.md`; the forms, `docs/fx26.md`, "Processes and
`par`"). Left:
- **The cost of a switch** (the actors note's A4): measured, 585 ns for a
  message's two switches, after 890 (`DONE.md` §92). What is left is the
  call-out from native code and the frames copied to capture and
  reinstate: one-shot stack segments, a task's own stack switched to.
- **A time slice of one poll makes no progress** (found 2026-10-14):
  `FIXPT_SLICE=1` never ends even a native-only program of 30 iterations,
  on the old binaries too, and on the Rust cellular machine: the slice a
  task is given after a preemption (`take_grace`) is spent before its
  next poll, it seems. Testing uses 3 and more; nothing else sets so small
  a slice.
- Out of scope, as kayak asked: transfer of mutable data (by consuming a
  place's handle, after H3), session types, distribution, and links
  (monitors are built, `DONE.md` §94).

## 93. Cellular code calling native code, where the native convention declines (2026-10-13)

Found while making `append` and `string-append` `vsubr`s: on the REPL's
machine, a form the native convention declined runs as cellular code on
the arm64 cellular machine, and a typed call there of a global holding a
native closure entered it as a cellular one, a crash (`(stay-cellular (g
1))`, `g` native). Fixed (`DONE.md` §93): typed calls check for a cellular
closure as untyped ones do, and call anything else out to the Rust machine,
which calls native code; the check's cost to assembling words mostly
recovered (`DONE.md` §93). Left:
- **A prelude in FX-26** (raised by the user with `append` and
  `string-append`, 2026-10-13): standard procedures written as FX-26
  definitions every program sees, a module file built in and loaded
  implicitly, as `fx26:processes.fx` is for its forms. What it would cost:
  a variadic definition's call makes the list of its arguments, where a
  built-in primitive takes them as they are; and every machine would load
  and compile it.
- **Calls between the machines nest on Rust's stack**: recursion that
  alternates between native and cellular code is bounded by the thread's
  Rust stack, a few million deep on the CLI's, then a stack overflow
  (`DONE.md` §93; it crashed before), where native recursion goes on
  through the heap. Unbounded would need the calls not to nest:
  each machine resuming the other from a loop, not calling it.

## 97. Code bloblets a program makes and runs (kayak's request, 2026-10-14)

Design: `docs/research/declared-conventions.md` (its steps are the plan).

Built (2026-10-14), the note's steps 2 and 3: `seal-code`,
`native-procedure`, `native-code?` and `(io native)`, on all nine
machines (`programs/made-code/leaves.fx`, `fixpt-cli/tests/made_code.rs`).
And step 4: `define-convention`, fixpt's declaration generated from its
constants, both checkers comparing a program's with it
(`programs/made-code/declared.fx`). And step 5: code that is not a leaf, with `poll` and `cons` routines
(`programs/made-code/frames.fx`). And step 6: the declaration as data a
generator reads (`fx26:convention.fx`, `programs/made-code/generated.fx`).
And on x86_64 (kayak's request, 2026-10-18; CLAUDES_CHOICES.md "Code a
program makes, on x86_64"): its own declaration, `native-x86_64.conv`,
which `native-convention` gives there and both checkers compare with, and
each program above twinned in `programs/made-code-x86_64/`, made by
`fx26:x86_64.fx`.
Left:
- **Native code cannot call back the bytecode VM's procedures**: a
  primitive cannot run the VM again, so on `rs-scheme-vm` a made procedure
  given a procedure of the program fails, saying so.
- **A scheduler defined as cellular code does not preempt on the
  native-convention machine** (found 2026-10-14): declining the hidden
  global of `fx26:processes.fx` natively (it ran as cellular code) left
  `preempt.rs`'s spinning process unpreempted, and a `processes.rs` test
  hung. Only `load-input`'s hidden globals are declined now, so the
  scheduler is native again; the cellular path is still to fix.
- **Closures with captured values, when kayak asks** (2026-10-15).
  `native-procedure` makes a native closure of no captured values, and
  neither a program nor its made code can make one with them: the
  `bloblet` routine (`DONE.md` §97) makes only plain bloblets. Not a
  routine, as calling a primitive is not one: let `native-procedure` take
  them, `(native-procedure c v …)`, an FX-26 operation extended, no clause
  added to the contract (`closures` already lays them out). Made code
  making closures as it runs reaches that operation through a field and
  calls it by `foreign`, as `programs/made-code/linked.fx` calls `*`; it
  reads the captured values by the `closures` clause. Until then a
  generator can convert closures itself (the environment an extra
  argument, a pair of code and environment in a bloblet), which works
  now; only closures that the program calls as its own procedures need
  this.
- **An adapter from the native convention to the cellular one runs on
  only some machines** (found 2026-10-14, a made procedure typed
  `cellular`, which `native-procedure` now refuses): the cellular closure
  `%fx26-convert` makes (`cellular_adapter`) fails on the arm64 cellular
  machines ("no routine is numbered 27") and the bytecode VM ("attempt to
  call a non-procedure"); the Rust cellular machine and the evaluator run
  it.

Kayak is writing FX-26's native code generators in KFX, which may use only
what FX-26 has, and FX-26 has no way to place machine code it made and run
it. Asked for, as our own code is (`docs/object-model.md`, "A collected
code area"): code beside its fields, in the code area mapped twice.
- **Layer 1, the smallest useful.** Make a code bloblet in the code area,
  given its fields (traced values) and its suffix's size; write the suffix
  with the existing suffix writes; seal it (the suffix frozen, the header's
  bit 13, which `set_bloblet_byte` already refuses past; the instruction
  cache flushed; runnable); make a procedure of a sealed one at a type the
  program states, with an effect of its own, `(io native)`, or a
  capability; and ask whether this machine runs native code at all.
- **Layer 2, the contract** native code needs beyond leaf arithmetic,
  part of FX-26's definition so that the same code runs on fixpt and on
  kayak's runtime: the value layout (`layout.rs`), argument, result,
  closure and pinned registers, call-outs (allocation, collection,
  primitives, failure), how frames are described to the collector, fuel.
  The native convention (`docs/research/native-conventions.md`) the
  candidate.

Kayak's questions, and the answers proposed (not yet decided with the
user):
- **Both layers, or the first now?** Not leaf code only (the user's,
  2026-10-14): code a program makes may do all that ours does, so the
  contract comes with layer 1, *declared*: a convention is a description
  that means something, not a version number. Proposed:
  - `(define-convention NAME clause …)`, each clause a role bound to where
    it is: the target (`arm64`); the registers (arguments `x1`–`x8`, result
    `x0`, closure `x10`, link `x30`, frame `x29`, pinned: state `x24`, fuel
    `x28`, the stack's limit `x27`, the code area's distance `x26`; the
    rest lost across a call); the value layout (tags, header fields,
    closures' and frames' shapes); frames (header at `x29 − 8`, link,
    return, stack map at `x29 + 16` with its 48 live bits, values from
    `x29 + 24`, raw words after); the state's fields code may use, by
    offset; call-outs, each named with its arguments and whether it may
    collect (allocation, primitives, foreign calls, capture, reinstate,
    abort, poll, overflow, traps); fuel (where it is decremented and
    checked, what a spent slice calls); the write barrier (the card table,
    a card's size).
  - What a convention is, is its normal form: two declarations that
    normalise alike are the same convention. A program's declaration is
    accepted when it is one the implementation supports, and is then that
    convention (so `≤ fx`, and every machine calls it); otherwise refused,
    naming the first clause that differs. For the first deliverable the
    supported set is one declaration, fixpt's `native` as it is.
  - The declarations are generated from the implementation's own tables
    (`layout.rs`'s tags and fields, `DState`'s offsets, `direct.rs`'s
    registers and `Callout`s), as `standard.fx` is from `lower.rs`'s, and
    a test checks them against the code; so a change to the convention
    changes the declaration, and a program written to the old one is
    refused with the difference, not run. Kayak's runtime publishes its
    own set; where the two meet, the same code runs on both.
  - The declaration is also data a generator reads (registers, offsets,
    call-out numbers), so kayak's generators are written against it, not
    against numbers copied out of fixpt.
- **First-class, or called through a primitive?** First-class, a `subr`
  of the native convention at the stated type, latent effect included:
  every machine already calls native closures (cellular ones through the
  Rust machine, §93), so nothing new is needed to call one; and only the
  making carries `(io native)`, where the stated type is trusted. An
  effect over a capability: it is how FX-26 makes every other outside
  power visible, and both checkers see it; a capability can come later as
  a handle on top, if a program must hand the power on.
- **Meeting the collector?** As ours do: in the code area, never moving,
  mark-swept, fields updated in place, the procedure holding its code
  bloblet in a field so that it lives while the procedure does. A heap
  image carries no code area yet, so making an image of a program holding
  one is refused until images carry it.
- **A test in fixpt?** Yes: an FX-26 program that assembles a leaf adding
  two fixnums and one returning its own field across a collection that
  moves the field's value (as `fixpt-native/tests/code_exec.rs` does from
  Rust), run on every machine; the no-native-code branch run by a switch
  that turns native code off.

## 105. A program's own code at run time: the editor as the session (the user's editor, 2026-10-18)

The user is writing an Emacs-like editor in FX-26, extended in FX-26;
its prototype, in Larceny Scheme, is `~/Dev/Emacs/yank`. Its extension
is `eval` in Larceny's interaction environment: the init file, `M-:`,
`C-x C-e`, and `define-command` at run time, all seeing the editor's own
definitions. A running FX-26 program has nothing like it: no procedure
that reads, checks, compiles and runs new code against the program's
globals and types. Two ways, to decide with the user:
- **(a) The editor is the session** (recommended): as Emacs is an image,
  the program asks the session that runs it to take a form, which is
  checked, compiled and run as a REPL form is, with redefinition's
  rules (`docs/fx26.md`, "Redefinition"), and gets back its value or its
  failure. Wanted: that request (an `(io session)` effect, perhaps), and
  a say in which of the editor's globals user code sees.
- **(b) The front end as a library in the program**: it is FX-26
  modules already (`reader.fx`, `conductor.fx`) and §97 runs made code;
  the hard part is the code checked against the program's own globals
  and types, which rebuilds (a) by hand.
Either way, the type user code is checked against: a command's effect
fixed (an editor effect beside `(io terminal)`), so hooks and keymaps
are lists and tables of procedures of one type.

## 106. A failing command, and `C-g` (the user's editor, 2026-10-18)

An editor goes on when a command fails, and stops a command on `C-g`.
- **Failure**: `error` is a panic (§86), ending the run unless a
  monitored task group catches it (`docs/fx26.md`, "Monitors"). Each
  command run as such a task may be enough; to try, with a stack
  overflow and the step limit failures caught the same way (both end a
  run today). §89's conditions for what handles a failure in place.
- **`C-g`**: a key arriving cancels the running command. `race` cancels
  the branch that loses, so a race of the command and a wait for `C-g`
  may say it; but the wait must not take the keys typed ahead, so it
  needs a look at the input that leaves it there. To try.

## 107. Unwind protection for programs (the user's editor, 2026-10-18)

`dynamic-wind` is used inside the compiler (a region's exit, `lower.rs`)
but no program can name it. An editor needs it: `save-excursion` and
`save-window-excursion` put back point and the windows on any exit, and
the terminal's modes must be put back on every way out of the editor,
a panic included. The prototype uses it 19 times. Its interplay with
one-shot and composable continuations is the design question (what the
after thunk means when a continuation re-enters).

## 108. Per-buffer settings, typed (the user's editor, 2026-10-18)

An Emacs-like editor keeps settings by name, with a default and a value
per buffer (`tab-width`, `fill-column`, a mode's own), and hooks as such
settings holding lists of procedures; each has its own type. FX-26 has
no type of every value. Proposed: a setting is a typed key, as a
continuation mark's key is, `(define-setting tab-width int 8)` making a
key of `int`, and a buffer's settings a table from keys to values whose
lookups are typed by the key. Dynamic binding of settings (Emacs's `let`
of a special variable; the prototype's `parameterize`, 15 places) is a
mark with that key. To decide with the user against a type of every
value taken apart by `typecase`.

## 109. Text that changes: a buffer's characters, and building strings (the user's editor, 2026-10-18)

FX-26's strings do not change (no `make-string`, `string-set!`,
`string-copy!`), and there is no way to build one by pieces but a list.
An editor's buffer is a gap buffer of characters, and its redisplay
builds each frame's output in one buffer written once. Wanted:
- A flat array of characters that changes (an `array` of `char` boxes
  each one: a bloblet's suffix, or `u32` code points), with slices to a
  string and a string copied in.
- A string builder (the prototype's `open-output-string`, 19 places):
  appends of characters and strings, then the string, or its UTF-8
  bytes for `write-out`.

## 110. Tables keyed by structure (the user's editor, 2026-10-18)

There is `eqtable`, keyed by identity, and `string-hash`. An editor keys
by strings (buffer names, file names, completion candidates) and by
structured values (the prototype's analysis: addresses of several
parts); the prototype makes 54 hashtables, equal- and string-keyed.
Wanted: a table keyed by equality, its hash and equality derived from
the key's type (`docs/research/polytypic.md`), or given.

## 111. Optional parameters and `case-lambda` (the user's editor, 2026-10-18)

FX-26 has `vsubr` (any number of arguments of one type) and `apply` for
it, but no optional parameters and no `case-lambda`. An Emacs-like API
leans on them: commands taking a prefix argument or not, `insert` and
`goto-char` with optional parts, helpers with defaults; the Larceny
prototype uses `case-lambda` in 15 places. Its type is an intersection
of `subr` types, §79's `overload`, but with each arm's own body, which
§79 says the compilers would need; optional parameters could be the
special case whose arms differ only in the defaults filled in. Not
blocking: code can do without (separate names, every argument written),
so after §105–110.

## 112. x86_64: what is left of the native back end (the user's, 2026-10-11)

The user's: "a native backend for x86_64 Linux, to eventually be in FX26
itself". Done (CLAUDES_CHOICES.md, the two x86_64 entries): the
hand-encoded cellular machine (`cellular::x64`), the words Rust compiles
into it, and the same compiled by FX-26 (`native-x64.fx` over
`x86_64.fx`), each byte for byte against its oracle; the bootstrap
reaches its fixpoint on all three. Left, in the order they would pay:

1. ~~**Register code**~~ (done: `cellular::x64::regcode`, CLAUDES_CHOICES.md
   "Register code on x86_64"; REG1–REG3 in registers, the rest in the
   state; `fast` on x86_64 is now `fx-regs-rsjit-cellcc`). Left of it:
   `ret` measured against `pop`/`jmp` for deep recursions, as arm64's
   `br` was.
2. ~~**The native convention**~~ (done: `direct/x64.rs`, CLAUDES_CHOICES.md
   "The native convention on x86_64"; the same frames, so the Rust side is
   shared). Left of it: whether `fast` should name it on x86_64, as on
   arm64: it is the fastest there on all of `fixpt bench`'s programs but
   `captures` (22 against register code's 18 ms, continuations), so `fast`
   stays register code for now; and the native convention's `ret` against
   arm64's `br` (CLAUDES_CHOICES.md, "Native profiling" 6), unmeasured.
   Re-ported onto main's frames when rebased (2026-10-17, CLAUDES_CHOICES.md
   "The x86_64 back end rebased onto main"). ~~Left of that: code a
   program makes (§97) is arm64's, so on x86_64 `native-code?` is false~~
   (done, kayak's request, 2026-10-18: `native-x86_64.conv`, the
   programs of `programs/made-code-x86_64/`, CLAUDES_CHOICES.md "Code a
   program makes, on x86_64").
3. ~~**Stencils**~~ (done: CLAUDES_CHOICES.md "Stencils on x86_64"; the
   routines in `preserve_none`, all eight arguments in registers;
   branches checked in LLVM's assembly; 1.06–1.55 of the hand-encoded
   machine, as on arm64).
4. ~~**In FX-26**~~, as for arm64 (§81): register code and the native
   convention. Register code is done (`native-x64-regs.fx`, CLAUDES_CHOICES.md
   "Register code compiled by FX-26 on x86_64"; every register word of the
   front end, about 4,000 of them, the same bytes as Rust's;
   `fx-regs-fxjit-cellcc`). So is the native convention
   (`native-direct-x64.fx` and the files beside it, CLAUDES_CHOICES.md
   "The native convention compiled by FX-26 on x86_64";
   `fx-regs-fxjit-nativecc`; every test program's procedures the same as
   Rust's). Left of it: the driver (`compile`'s finding of procedures and
   binding of globals) is still Rust's, as `syn.rs`'s is for register
   code; and arm64's `direct.rs` has no FX-26 twin (§81), though
   `native-reps.fx` is of no machine's and would serve it.
5. **Smaller:** a 32-bit jump that could be 8 (relaxation) would shrink
   compiled words by about a fifth; `,disassemble-asm` for x86_64 shows
   bytes with the disassembler's text, which knows only the forms the
   encoder makes.

## 115. Typed cellular code: what is left (the user's, 2026-10-22)

`docs/research/typed-cellular-code.md`: certificates for the Rust
compiler's words, and a verifier, as Hoare logic. The goal of this stage
(the user's): every word of every program the checker accepts verifies,
by type assertions, before propositions beyond types are built on it.
Met (2026-10-23): all 1,109 test program words verify
(`tests/typed_cells.rs`, which now requires it), none with a VC failing
or open, 13 relative to named assumptions (the built-in scheduler's
procedures at their forms' types, `library_type`); 437 mutants of
verified words are all refused.

Done (2026-10-22): data made (products, sums, modules, bloblets: the
certificate names the type, the values are checked against it); calls
and uses of polymorphic values (the checker's instantiations given);
`letrec`'s placeholders (owed free values); generative types' and
modules' conversions (checked, not trusted); nested `poly`s and a
`plambda`'s value generalized where made purely; a dependent procedure's
selects; standard operations as values; idioms (`array-ref` and kin);
narrowing by predicates' latent propositions (shape, length, nat), by a
value tested, by a sum's tag both ways, a `tagcase`'s dead end; control
(prompts, marks, continuations); `car` of what may not be a pair, a debt.
Modules, by the checker's layout decisions kept as data (`module_raw`,
`reshape_chosen`, `packs`); regions' scopes, places, `rlambda`s and
bindings opened as the checker binds them; effects masked at a word's
boundary; size facts learned at branches and asked of the checker's own
procedures (`nat_arith`, `size_nonneg`, Fourier–Motzkin).

Done (2026-10-23):
- Two `poly`s compared with one's binders renamed to the other's
  (`Checker::renamed`, shared with checking a `plambda` against its
  signature): a flat array's length under a size binder.
- A lambda's free variables recorded after its body is checked, so a
  name a `with` in it binds is not taken from outside (`include`).
- Flat data by the checker's own rule, of types alone
  (`Checker::blobref_rule`, which `synth_blobref` now uses too): a new
  blobref's flat as the certificate says (`%flat`), its bytes checked to
  fit by the cells after it; the layout operand the compiler gives
  checked against the rule's; a flat product's field, and a flat sum's
  variant by the tag a `tagcase` tested (`State::variants`); a bloblet's
  bytes and fields. A literal, or literals' arithmetic, at a fixed-width
  integer type, in range.
- `prompt` bodies, which the compiler makes thunks, certified by the
  body's type and effect; escape-only tags.
- `list` as a value (a `vsubr`: `%fx26-vlambda` over a word signed with
  the `vsubr` unfolded, `Certs::settle`), `apply`'s copy of its list
  (`%copy`), and `certify-length`, from the `nlist` narrowing found.

Then the next stage: `requires` and `ensures` in procedure types, latent
propositions their special case (the note's §8; begun, §116); and TC6: the
certificate kept in the word, the FX-26 compiler making the same, and
fragments verified on loading, under the loader's policy for open VCs,
trusting one an effect (`(trust A)`; the note's §7).

## 116. `requires` and `ensures`: what is left (the user's, 2026-10-23)

`docs/research/typed-cellular-code.md` §8 and §10: specifications in
procedure types, carried by both checkers (the FX-26 one's `check-specs.fx`
reads them, `check-logic.fx` is `logic.rs`'s prover step for step), proved
of the cells by the verifier. `tests/programs/specs`, which both checkers
agree on (`every_test_program`). Left:
- ~~Latent propositions as an `ensures` of a `bool` result, sugar
  (`(bool (then …) (else …))`), so that the verifier's narrowing by a
  predicate is the call rule, and the checker's too.~~ Done (2026-10-23,
  the user: "making the existing `(bool (then …) (else …))` result type
  shorthand for an ensures"): `Ty::Proving` (`ty-proving`) is gone; the
  shorthand reads as a `bool` result and an `ensures` (`specs::latent`),
  prints back as written, and both checkers narrow by an `ensures`'s
  `(implies r …)` conjuncts however written. A `lambda` still may not
  claim them (§54): checking one against its claim is the verifier's,
  and the checkers' narrowing would trust it unproved. Left: the checkers
  trusting a claim the verifier has proved (a certificate's word), or
  checking a simple one themselves (a body that is a test of its own).
- Terms of more than integers: `(length xs)` of lists and arrays, a
  sum's tag; `old` for what refs and arrays held (§8, point 3).
- ~~Open VCs written for a prover outside (SMT-LIB 2; the note's open
  question 3)~~, done for `fixpt verify` (§119); the loader's policy for
  them (§7) is not.
- Total correctness: termination, by the size-change check or a ranking
  function in the certificate.


## 117. The verifier over every test directory: what is left (the user's, 2026-10-23)

`every_test_programs_words_verified` now verifies every directory's
programs but `specs` (which has its own test): 5,864 words, 5,860
verified; 1,704 mutants, all refused. `every_directory_surveyed`
(ignored; `DIRS=`, `FILES=`) reports each directory, and the time each
phase takes: the whole corpus checks in about 1.7 s, compiles in 0.1 s
and verifies in 0.3 s, no program above 0.04 s to verify. The four words
left (`KNOWN_GAPS`) each want more of the certificate:
- A prompt's own `goto` and `comefrom` on its tag's region, which the
  checker drops where nothing but the tag's variable reaches the tag
  (`reaches_only`), the verifier keeps (`native/raw-args.fx`'s `given`).
  The certificate could say the prompt delimits them, with what the
  verifier can check of it (the body's closure's free values' types).
- ~~Effects the checker masks at an expression inside a word, the
  verifier masks only at the word's boundary.~~ Done (the same day): the
  certificate marks each masked expression's cells (`Cert::masks`), and
  the verifier masks them by what it finds them given and give
  (`Masking`), as `Checker::mask_keeps` does.
- A global redefined at another type (`redefine/`): the certificate gives
  each global cell one type, the last, so a word that stored or read it at
  the type before fails. Each `global!` and `global` could carry the type
  the global had there.
- What the verifier does not compute of a word's effect, so that a
  certificate claiming less of it is not refused
  (`a_latent_effect_weakened_is_not_masked_away`: of 18,879 latent effects
  made one atom smaller, an atom the rest does not still say, 1,659 still
  verify): `spin` (55), termination not being verified (§116); what the
  scheduler's procedures, trusted at their forms' types, do to its private
  regions (`@sched`, most of them); and about 25 others, each an atom the
  checker's latent effect has that the verifier never sees the cells do
  (reading an `rlambda`'s or a reap's region, `native/whole-captures.fx`'s
  `@g` and its tag's control, a mark key's `comefrom`, `(read @globals)`
  of `modules/linked.fx`), to look at one by one. A global's read, which
  the verifier did not note at first (494 of them), it now does, and the
  test asserts it.

## 118. Specifications tested by running: what is left (the user's, 2026-10-23)

`docs/research/specs-and-counterexamples.md`'s S1, done but for these:
- Inputs of more types: `define-datatype`'s sums and products, strings,
  pairs; a value drawn of a type given by the program (a harness's
  parameter of a procedure type has none).
- Specifications checked as they run outside `fixpt test` (the loader's
  `guard` and `contract`, `typed-cellular-code.md` §7), and of a
  specified `lambda` that is not a top-level definition's.
- A counterexample made smaller (shrinking), and the path it took.
- The instrumented body checks its `ensures` after the body's value is
  had, so a tail call in it is no longer one: a deep recursion tested may
  run out of stack where the program would not.

## 119. Open VCs given to an SMT solver: what is left (the user's, 2026-10-23)

`docs/research/specs-and-counterexamples.md`'s S2, done for `fixpt verify`
and `,verify` (`fixpt_fx26::smt`, `verifying::sort`): each open VC is
asked of z3; proved, it is discharged; refuted, the solver's values of the
word's parameters are run, its specifications checked, and it is said
*false* (a specification broke, with the input) or *not inductive* (the
run keeps it, and the proof took a global's call to give what, run, it
does not, which is named). Not yet:
- The verifier's own runs (the tests, a loader) do not ask the solver:
  only the report does. A word verified by it is not marked so in its
  certificate.
- Terms are constants of their own, so the solver knows nothing of
  `(car x)`, `eq`, sizes' functions or datatypes (S4): a model may be
  one no run gives, said "open: the SMT solver refutes it …".
- Only a word that is a top-level procedure of drawable parameters is
  replayed; a VC of a `lambda` inside one, or of a list parameter the
  solver gave no value, is run at its first drawn value or not at all.
  A word named as a global is taken to be its `lambda`.
- ~~The places are cells, not source positions~~: done the same day
  (`Cert::sources`, each expression's cells and span). A place in a
  loaded module is said only to be one, and the REPL's are the
  expression alone (its program is the entries replayed).
- One solver process per VC; z3's 2-second limit fixed.

## 120. Logic functions in specifications: what is left (the user's, 2026-10-23)

`docs/research/specs-and-counterexamples.md`'s S4, begun: a specification
may call a `pure` global of a `bool`, `int` or `nat` result (both
checkers, `specs::spec_call`, `check-specs.fx`'s `k-spec-call`); the
verifier gives a call of one in the cells the same term (`Term::Call`),
and z3 an uninterpreted function. Not yet:
- ~~**Definitions.**~~ Done the same day, for z3 (`smt_theory`): a body
  of `if`, `null?`, `pair?`, guarded `car` and `cdr`, `cons`, arithmetic,
  comparisons and logic functions' calls is a `define-fun-rec` over
  `Int`, `Bool` and finite lists of integers (`L`); in a word that writes
  nothing, the VC's finite lists are `L`'s, what `cons` made its pair, and
  a model's lists are replayed. `logic-insert.fx`'s `insert` is proved.
  ~~Lists of other elements.~~ Done 2026-10-24: `(List T)`, a datatype of
  a parameter, for lists of `int`s, `bool`s and lists so
  (`logic-bools.fx`, `logic-nested.fx`). Still not: lists of `nat`s (the
  solver's `Int` is any integer; an assertion that every element is
  one is wanted), `define-datatype`'s sums and products, a body of `let`,
  `tagcase` or anything else (left undefined, a function only), and the
  verifier's own prover unfolding none.
- **A logic function calling another** is translated, but the checkers
  refuse it: reading a global is no `pure` effect (`(read (globals
  len))`), even a global never assigned. Wanted: a read of a global no
  `set!` reaches counted pure, or logic functions' effects so.
- **Totality** of a logic function is not asked of the checkers; the
  solver is given a definition only where every `car` and `cdr` is of a
  list a test showed a pair, so it is total where it is used.
- **Argument types** are not checked as the specification is read (the
  checker written in FX-26 has no subtyping there yet), only by a run.
- A logic function's own word is its `letrec`'s (`s@159`), not the
  global's name: the verifier links a call in the cells by the global's
  name, which a redefinition at another type would mislead (§117).


## 121. Kayak's stage 0, to run faster (the user's, 2026-10-24: high priority)

`docs/kayak-stage0-workload.md`: kayak's compiler compiling itself under
`fixpt run` (`fx-regs-rsjit-nativecc`) takes about 610 s, and kayak's
check waits for it; the target is 490 s or less. Only execution speed
counts (loading is about 1%).

**Profiled 2026-10-24** (`perf`, `--call-graph fp`, main at `4738986d`):
86% of the run is native code calling out (`common foreign call`,
`call_foreign`) to cellular closures, which `call_value` runs on Rust's
inner interpreter (`Machine::run_in`, `Machine::prim`), building a word
and a machine for each call (`make_cellular_word` 9%, malloc and free
8%). They are kayak's emitter's: `emitter` and `writing` are `(module
…)`s, and their members (`put-stmts`, a closure of 16 values, 332 calls
and 2.9 billion cells in 200 s; an inner lambda called 66 million times,
24 cells each) are not native, through `any?`, `put-sep` and `map`. The
13 cellular accessors are not seen. On `fx-regs-rsjit-cellcc` the same
run takes **37 s at kayak's pin, 39 s on main**, its output the same, so
kayak's check no longer waits for it once kayak passes that machine.

**Fixed the same day: 22 s on `fx-regs-rsjit-nativecc`** (from about
610 s; three at once, 23 s; every output the same). What was wrong:
- ~~**Why the emitter's members are not native.**~~ A definition's value
  is compiled natively whole, or not at all: `emitter`'s, a module, was
  declined for one accessor of a 9-field record with no register code
  (`ctx-effects`, the `tagcase` below), and `expressions`' for one
  closure of more than 32 values ("a closure too large", arm64's `ldur`
  limit, copied to x86_64, whose loads reach any distance). Both fixed.
  The reason was said nowhere: the note of the decline was overwritten by
  the pass that compiles the definition's procedures after, which lets a
  module be. Now kept when that pass compiles nothing.
- ~~**`call_value` on the Rust interpreter.**~~ A cellular closure made
  in a native program (`nclosure`) is compiled natively as it is made,
  where the compiler takes it, its code once per word (`direct::adapt`,
  `native_code_of`; weak references, which now die with code the code
  area frees): native code calls it with no call-out. 3 µs a call to 40
  ns, on a member of a module held cellular. Only on `rsjit` machines:
  the compiler written in FX-26 (`fxjit`) does not yet compile at `adapt`
  (its oracle compares the call-outs each compiler made). Not yet: a
  closure made while the native machine runs (cellular code native code
  called) is adapted still, its machine busy; and a call-out that is made
  still builds a word and copies every native frame (`call_foreign`).
- ~~**Strings called out for.**~~ Profiled again at 22 s: 13% of the run
  in `direct::callout` itself, and as much in the primitives it ran. Of
  200 million call-outs, 151 million were `string=?`, 27 million
  `string-ref`, 13 million `string-length` (kayak's checker and emitter
  compare names). Register code did all three in line; the native
  convention on x86_64 called out. Now in line in both its compilers
  (`pure_fast`, `string_eq`; `dq-pure-fast`, `dq-string-eq`). Not yet on
  arm64's native convention (`direct.rs`), which cannot be run here. The
  rest, about 9 million (`%fx26-string<?`, `string-append`,
  `char-whitespace?`, `char->integer`), each under 2%. Stage 0: 26.9 s
  to 17.4 s alone (three runs each, alternating, this machine busier than
  for the 22 s above), 17.5 s three at once; every output the same.
- **What is left, profiled at 17 s**: 43% of the run in three of kayak's
  own procedures, each a walk of the checker's whole list of facts for
  one (file, pos), for every name the emitter asks of (`first-fact`
  14%, `facts-at-place` 14%, `any?` over facts with a lambda 19%; and
  `find-bind` 4%). Kayak's to change (an index of its facts, by place),
  not ours; nothing of its compiler is declined now, and call-outs are
  1%. Ours in those loops: every value goes through a frame slot, stored
  and loaded again at once (`mov %rax,0x30(%rbp)` then `mov
  0x30(%rbp),%rdi`), and an `i64` field is unboxed with a call-out
  beside it. Values kept in registers across a procedure's straight-line
  code would help every program, at most by some tens of percent here;
  the samples fall mostly on the loads of the list's cells and the
  facts' fields.
- ~~**Frame slots kept in registers**~~ (the user's, 2026-10-24) in
  straight-line code, by both x86_64 native compilers: a slot read is a
  move, or nothing, while `RESULT` or REG1…REG3 still hold it (`held`,
  `do-held-step`). About 3% of stage 0's cycles (CLAUDES_CHOICES.md,
  "Frame slots held in registers"). What costs more, in kayak's loops
  (`first-fact`): an `i64=` of two fields, each unboxed with a call-out's
  code in line beside it, then a boolean made and tested (`cmov`, `cmp
  3`), about 15 instructions where a compare and a branch would do; and
  each operation's slow path in line, jumped over.
- **Memory traffic, measured** (the user's question, 2026-10-24): per
  stage 0 run, before and after the slots held, 40.1G and 38.25G loads,
  18.7G stores either way, and 11.05G and 10.7G loads served by store
  forwarding (Zen 2's `ls_stlf`). So a quarter of all loads still read a
  slot just stored: in `first-fact`, the `car` stored to a slot and read
  again two field chains later, each having used `rax`. Not REG4…REG8:
  the hot procedures read REG4 once, at entry. Why the loads removed
  bought little here: on this machine (a Threadripper 3990X, Zen 2) a
  store and then a load through the same `rbp` offset costs no more than
  a register move (memory renaming); through `rsp` one cycle more,
  through another register three. On a processor without it (Zen 3,
  most of Intel's) each would be a forward's few cycles, which this
  machine can't show. `ls_stlf` is not sampled precisely, and IBS wants
  `perf_event_paranoid` 0, so where they are is from the code, not a
  profile. Keeping slots in registers beyond `RESULT` and REG1…REG3
  wants scratch registers: all 16 are given out, 8 of them scratch.
- **Instruction selection, tried** (2026-10-24): a raw `i64` comparison
  only a branch reads, branched on the flags (`cmp`, `jne`) in place of
  `cmov`, `cmp 3`, `je`, with `RESULT` dead after rather than set first
  as the test for `op2`'s has it: 120.9G instructions to 117.5G, and no
  fewer cycles (pinned to a core, 69.9G before, 70.2G after). Kept, in
  both compilers, at the user's word (CLAUDES_CHOICES.md, "Raw
  comparisons branched on the flags"). Stage 0 waits on memory: 1.66G data reads per run miss L2
  (0.27G instruction fetches do), 78% of all misses in the walks of the
  facts (`any?`'s lambda 27%, `facts-at-place` 22%, `first-fact` 20%,
  `find-bind` 8%), each fact a pair, a record and a string's header.
  Kayak's index of its facts by place is the remedy; ours, if any, is
  where the collector puts a list's cells and what they hold.
- **`fast` on x86_64**: right again for this program. Whether one decline
  still sinks a module (or any definition) whole is the question left:
  a member the compiler declines could be adapted alone.
- **Names**: a module member's word is named `lambda/NAME@N`, not for its
  module; and `@N` in the native convention counts from the start of the
  definition's thunk, not of the file, so it finds nothing.

The leads before the profile, in order:
- ~~**A perf map**~~ Done 2026-10-24: `FIXPT_PERF_MAP` writes
  `/tmp/perf-PID.map` (`fixpt_native::symbols`; `docs/performance.md`,
  "Profiling with Linux's `perf`"), and a definition in the native
  convention names its procedure for its global, as kayak's are
  (`(define cv-where (subr …) (lambda …))`), not `lambda@11`. Next: the
  profile of the plain run, and every later step measured by one.
- ~~**`tagcase` loads only the fields its arm uses.**~~ Done 2026-10-24,
  in both register compilers (`ArmBind::Fields`, `r-members`): the 13
  words have register code, and are native.
- **A leaf out of registers made again with a frame**, its values in
  stack slots, not declined: `register_body_in` retries so only a leaf
  made of tail calls.
- **A reason for each decline.** Running out of registers in a leaf
  (`Gen::reg` returning none) records none, so the report says "?".
- **Measured**: the stage 0 run, three at once, by kayak's
  `scripts/fixpoint.sh`, its output still `boot/src/kfx/` byte for byte;
  first a shorter run (`tests/kfx/loaded-select.kfx` is the fixed cost
  only). Kayak's pin, `4caffc2`, is 39 commits behind main, none of them
  about speed.
- **Every procedure a frame, as a switch**, if a profile needs it: a
  leaf in the native convention has none, so perf's `--call-graph fp`
  misses its caller. Both native compilers (Rust's and `native-direct-
  x64.fx`), or their oracle off while it is on. Stacks are otherwise
  walked (`docs/performance.md`, "Profiling with Linux's `perf`").
- **A top-level expression's thunk** is still named for where its body
  starts (`lambda@11`), in the native convention: a run's last form,
  kayak's call of its compiler, would show so in a profile.

## 122. A list's cells near what they hold, where the collector copies them (2026-10-24)

Stage 0 waits on data cache misses (§121, "Instruction selection,
tried"): a walk of kayak's facts reads, for each, a pair, a fact record,
and a string's header, mostly on lines of their own. A collector that
copies a pair's `car` (and its fields) just after the pair, depth first
along `cdr`, would put a walk's reads on fewer lines, for any program
that walks a list. First measure: the lines a fact costs now (the
distance between a pair, its `car` and the `car`'s fields, from a dump
of the heap after a collection), and the misses per fact visited
(`l2_cache_req_stat.ls_rd_blk_c` over the walks' iterations).

## 123. ~~Kayak's facts indexed by place~~ (kayak's; done there, C143, 2026-10-24)

Done by kayak at `abecd81` (C143): a balanced tree of the facts by
position (`fidx`, `kfx/emit.kfx`). Stage 0 on it, Fixpt at `df3c90b7`:
29.5G cycles and 68.4G instructions (from about 57.5G and 117.5G), data
reads missing L2 0.36G times (from 1.66G); about 7.9 s. Left of the
same kind there: `find-bind` (`kfx/check-exprs.kfx`), the innermost
binding by a walk of every binding, 10.5% of stage 0's cycles; kayak's
to change, if anything.

What was here:

78% of stage 0's L2 misses are in `any?`'s lambda, `facts-at-place`,
`first-fact` and `find-bind` (§121): linear walks of every fact, at
every name the emitter asks about. An index by file and position (a
hash table, or the facts sorted) would remove the walks. Kayak's code
(`kfx/emit.kfx`), not ours: to propose to kayak, not to edit there
unasked.

## 124. Frame slots in more registers, native convention on x86_64 (2026-10-24)

The slot cache (CLAUDES_CHOICES.md, "Frame slots held in registers")
has only `RESULT` and REG1…REG3: all 16 registers are given out, 8 as
scratch (`X9`, `X11`–`X17`). A quarter of stage 0's loads read a slot
just stored (§121, "Memory traffic, measured"). Zen 2 renames those
through `rbp` at no latency, so this machine shows little; on one
without (Zen 3, most of Intel's) each is a store forward's few cycles.
Wants: the helpers that use every scratch register found and made to
use fewer, then free scratch registers holding slots across straight
line code. Measure on a processor without memory renaming, if one is
to hand.

## 125. Slow paths out of line, native convention on x86_64 (2026-10-24)

Each operation's slow path (an unboxing's call-out, about 20
instructions; `int_slows` already are out of line) sits in line, jumped
over by the fast path (`test`, `jne`, `sar`, `jmp`). Out of line, the
fast path falls through and the code is denser in the instruction
cache. Stage 0's instruction fetches miss L2 0.27G times a run against
1.66G data reads (§121), so expect little there; measure on a program
whose hot code is larger than the instruction cache.

## 126. Stage 0's fixed cost: Fixpt loading kayak's compiler (2026-10-24)

With kayak's facts indexed (§123), loading is most of stage 0, where it
was about 1% at 610 s: `tests/kfx/loaded-select.kfx` in place of
`kfx/kfx.unit OUT_DIR` (`docs/kayak-stage0-workload.md`) takes 20.7G of
the whole run's 29.5G cycles, 70%. Of the fixed cost (`perf`, cycles,
`df3c90b7`): register words 30%, the FX-26 checker written in FX-26
(`check-subst.fx`, `check-syntax.fx` and the rest) checking kfx.fx, not
native; the heap 18% (`bloblet_main`, `collect_minor`); the native
convention's compiler 13% (`reps::demands`, `webs`, `reps_of`,
`procedure_x64`); malloc and free 11%; hashing 5%; call-outs 5%; the
Rust front end 4%; native code 2%. Leads: the checker's words native;
the compiler's analyses cheaper, or done only for what runs often; what
mallocs.

Measuring: the first run of a new binary checks and compiles the front
end to register code and keeps it (`front_end_cache`, `as_register_code`
in `session.rs`): 88.3G instructions against 68.4G after, run to run
alike to 0.1%. Take the runs after it.

- ~~**The compiler's analyses found once**~~ (2026-10-24): `slot_facts`,
  by a register word's cells, across compiles; and code installed a
  word at a time (CLAUDES_CHOICES.md, "Slot facts kept across
  compiles"). Fixed cost 20.6G cycles to 18.1G, stage 0 29.5G to 27.1G.
  Then `webs` once where `split_slots` splits nothing (its webs give
  `raw_slots` too), and one `demands` for `raw_refs` and `live_in`, which
  `reps_of` takes rather than finds again: 17.0G, and 26.0G.
- **Next, by self time** (frame pointers, after the above): the front
  end's register words 37% (its generic tables, `table.fx`, some 7%:
  `bucket-of`, `table-entry`, `table-ref`, `bucket-find`, each a call
  and a closure's); the heap 16%; malloc and free 10%; the compiler 9%
  (each procedure's own `webs` twice, in `split_slots` and `raw_slots`,
  and `demands` some six times: since done once and three times);
  call-outs 6%; hashing 5%; the Rust
  checker 5%. The front end as native code, not register code, is the
  largest lead; its tables in line, a smaller one.
- ~~**The front end native**~~ (the user's, 2026-10-24): checked in the
  native convention where Rust compiles native code
  (CLAUDES_CHOICES.md, "The front end in the native convention"), and
  `reps_of`'s successors found once: loading 17.9G cycles to 16.8G,
  stage 0 27.0G to 26.1G (pinned, a busier machine than the figures
  above). Compiling the front end natively is now in every run, about
  2.9G cycles.
- ~~**Its native code kept in the cache**~~ (the user's, 2026-10-24): the
  front end as its first run left it, what `%run-front-end` gave and all
  it reaches, its native code as ordinary bloblets named in a list and
  made code again on reading (`Heap::copy_graph_with`), the native
  adapter's code shared, and the call-outs' table kept with it, given
  back to a machine that has numbered none of its own
  (CLAUDES_CHOICES.md, "The front end's native code kept"). Later runs
  neither check, compile nor run the front end. On the arm64 Mac: a
  6-line program 0.55 s to 0.15 s (2.5G cycles to 0.69G); stage 0 2.76 s
  to 2.42 s (59.8G instructions to 50.5G). Not yet measured on x86_64.
  **Next**: the native compiler faster (some 580K cycles a procedure),
  which serves kayak's compile too.
- **The runtime's share, measured** (2026-10-24, kayak `abecd81`,
  pinned): stage 0 22.0G cycles. Collections are not it: 228 minor
  (426 ms) and 3 major (90 ms) of a 9.3 s run (`FIXPT_GC_SUMMARY`, now
  for `fixpt run` too), 244M words allocated, 13% surviving a minor; a
  nursery of 2M to 8M words changes nothing (about 1%). The rest of the
  heap's 18% is objects read from Rust. Native code calls out about 18M
  times a run: `char-whitespace?` 3.0M, `%symbol-hash` 2.7M,
  `%fx26-string<?` 2.3M, `%fx26-char-in?` 1.3M, `string-append` 1.25M,
  `string` 1.0M, unbox 0.8M, `char->integer` 0.8M, a closure of any size
  0.6M. The dispatch (`direct::callout`) is 5.5% of the run, about 65
  cycles a call before the primitive; `collection_due`'s `f64`
  thresholds some 13% of that. Made quiet (`never_collects`), the
  non-allocating ones (`char-whitespace?`, `%fx26-char-in?`, `set-car!`,
  `set-cdr!`) cost the same: tried and not kept. Leads: those five in
  line, in both compilers (`pure_fast`, `dq-pure-fast`: `char->integer`,
  `char-whitespace?` for ASCII, `%symbol-hash` a field, `string<?` and
  `char-in?` loops as `string=?`'s), some 10M call-outs; the dispatch
  cheaper (integer thresholds, no vector for a primitive's arguments);
  who mallocs, still unseen (glibc unwinds by neither frame pointers nor
  DWARF here).
- ~~**Those leads taken**~~ (the user's, 2026-10-24): the five in line
  (CLAUDES_CHOICES.md, "Characters, symbols and strings read in line"),
  stage 0 22.2G cycles to 21.1G; the dispatch's vector and floats gone,
  some 0.5%; and who mallocs, by a sampling allocator
  (`FIXPT_ALLOC_PROFILE`, `docs/performance.md`), whose first two finds
  are fixed: stage 0 20.6G, loading 11.9G. **Next**, by its report on
  loading (10.3M allocations): `Datum::clone` 0.65M (88 MB), `reps::webs`
  0.55M, the Rust checker's `cyclic::walk` 0.44M and `Exp::clone` 0.4M,
  `procedure_x64` 0.36M, `ty_kids` 0.34M, the reader's `read_atom`
  0.3M; strings between Rust and the heap (`string_points_into`,
  `String::from_iter`) some 0.8M more.
- ~~**Loading's allocations**~~ (the user's, 2026-10-24): 10.3M to 5.8M
  (CLAUDES_CHOICES.md, "Fewer of Rust's allocations loading"): loading
  11.97G cycles to 11.26G, stage 0 20.65G to 19.4G. **Left**, by the
  profile (`FIXPT_ALLOC_DEPTH`, each function where first met): the
  reader's `read_atom` (unescaped atoms now slices; the rest) and its
  lists' growth; each form read twice by the Rust reader, once to find
  its loads (`syn::supply_loaded_in`) and again for its syntax (a text
  test to skip the first cannot know the forms that load implicitly,
  `spawn`, `send`, `self` among them: tried, and wrong); `Lowerer::go`'s
  strings; `Datum::clone` in `top_defining` and `record` (a form kept
  twice; an `Rc` would share it); `Ty::clone` in `regions_walk` and
  `knot_in`; `param_sels`' set. Who mallocs is not
  seen (glibc has no frame pointers): a DWARF call graph would say.
- ~~**Loading, by `perf` again**~~ (the user's "keep going", 2026-10-24):
  the reader lowered only for an eager reader, and an instruction's
  index by binary search in the native compilers, not a linear search
  for each (CLAUDES_CHOICES.md, "Loading: the reader lowered only when
  wanted"); and the checker's whole copies of forms (`top_defining`'s
  two now one `Rc`). Loading 11.25G cycles to 10.18G, stage 0 19.16G to
  18.21G. **Left**, by self time: the front end's native code some 39%;
  the heap's collections some 12% (5 majors, 136 ms, copying the live
  data again as it grows, a major copying 5.0M words to free 1.4M; 133
  minors, 229 ms, each scanning the code area and regions whole, 1.5M
  words, some 0.4 ms); the native compiler 7.5% (`demands` a fixpoint
  of every instruction, op names matched as strings, each pass);
  hashing some 4.5%, SipHash, over many maps.
- ~~**The heap's growth, every space counted**~~ (the user's, 2026-10-24):
  a major collection's budget twice the peak live, across the old space,
  the code area, the reaps and the cellular machines' code, which no
  longer forces majors of its own (CLAUDES_CHOICES.md, "The major
  collections' budget"): loading 10.30G cycles to 10.04G, stage 0 18.32G
  to 18.0G. **Left**: the minors, 135 loading (240 ms), each scanning
  the code area and regions whole (1.5M words): stores into them
  remembered, or code made since the last minor alone scanned.
- ~~**The code area scanned by its cards**~~ (the user's, 2026-10-25):
  the Rust barrier marks the code area's cards as the machines' already
  did, and a minor traces only the fields on its dirty cards, finding
  the objects there by a sorted list of their starts: loading's minors
  237 ms to 174 ms, its cycles 9.82G to 9.57G. **Left**: the regions,
  still scanned whole (none live when loading); machine code fills what
  it allocates there without marking cards.
- ~~**Self tail calls lost one form at a time**~~ (the user's "go for
  it", 2026-10-25, from a profile of stage 0's native code, 55% of it): a
  definition `fixpt run` or the REPL compiles on its own, in a thunk
  (`native_define`), had register code with no fast version, so its tail
  calls of itself went through the global, a frame torn down and made
  again each time round: `find-bind` alone was 16% of stage 0, some 40%
  of it that call. The lambda named for the definition is now its own
  (`compile-defining!`), whose global the driver writes once after, as a
  definition compiled whole is: a loop behind `global-guard`. Stage 0
  17.62G cycles to 16.70G (pinned, two runs each), loading unchanged
  (9.6G), output the
  same. **Left** in `find-bind`'s loop, its fast version: the list and
  name stored to frame slots and read again each time round (not a
  leaf: `string=?`'s slow path calls out); a frame map word stored before
  each `string=?`, which only the slow path reads; `string=?`'s loop a
  character at a time.
- **Measured now against kayak `d5840ee`** (C176, kayak's index of its
  checker's bindings, after the Fixpt team's proposal; the user's word,
  2026-10-25): stage 0 24.65G cycles at its parent to 19.4G, L2 misses
  0.62G to 0.12G; `find-bind` gone from the profile. Loading is 12.4G of
  it, 64%. And the kernel's share, which `cycles:u` had not shown: 1.4G
  in loading, page faults.
- ~~**The heap in huge pages**~~ (2026-10-25; `docs/performance.md`, "The
  heap in huge pages"): stage 0 21.2G cycles (user and kernel) to 20.0G.
  **Left**: the kept front end's image read and copied (`image::load`,
  16% of the faults left); the cellular code space's copying collection.

## 131. `type-at`: a primitive or a syscall (Heist's request, 2026-10-26)

`type-at` landed as a primitive (`DONE.md` §131). Its type fits a
syscall's (strings, an `int`, `io` effects), but only a runtime's own code
may declare one (§127). The editor is not a runtime, and `--syscalls` on
it would admit any syscall. A third way: a module built in, which may
declare, whose `define-optional-syscall type-at "fx26:type-at/1"` a
program imports. The editor would need no `--syscalls`, and a runtime
without a checker (kayak's, until it has one) answers `syscall-available?`
with `#f` instead of lacking a primitive. For the user to decide.

## 132. A `pselect` arm for a process (Heist's request, 2026-10-26)

`(io process)` landed (`DONE.md` §132), but a program cannot wait for a
process's output or exit: Heist's editor polls every 50 ms while one
runs. An arm, as for `(read-byte)`, needs a waker list per process in
`sched.rs`, the reader threads waking `wait_stdin`'s `poll` (a pipe it
polls too), and the arm in both parsers.

## 133. A module file's item using an included value compiles apart (found 2026-10-27)

Found while fixing Heist's problem D (`DONE.md` §135): in a module *file*
with `(include m)`, an item whose value uses one of `m`'s values, `(define
z (subr … ) mk)` or `(define z (lambda () (mk)))`, is compiled to different
words by the compiler written in FX-26 than by the Rust one (`tests/
rust_compiler.rs`: "99 fields and 98"), though it runs alike. The same
module as an expression, `(module (include m) …)`, compiles the same, and
so does a file item that only names an included type. Each item's value is
`(with %include …)` there (`with_includes`, `in-includes`), so likely the
FX-26 side keys its facts for that `with` differently in a file (its
identity, `(start end k)`, or the `%include` item's place after the item
that says the file). Repro: a file `(include (load-module "c.fx"))
(define z (subr (alloc @heap) () (ref int @heap)) mk)`, `c.fx` defining
`mk`; loaded by a program in `programs/modules`.
