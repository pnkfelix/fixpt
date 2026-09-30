# Things deliberately left undone

Milestones live in [`PLAN.md`](PLAN.md); intentional differences from the 1987
and 1991 references live in [`docs/divergences.md`](docs/divergences.md). This
file is for the third category: things noticed *while building something else*,
judged not worth doing then, and worth doing later. Each says what it is, why it
was deferred, and where to start — because the reason is the part that goes
stale first.

---

## 1. A self-correcting reader, built on `call/cc` — done (2026-09-24)

**Done.** `crates/fixpt-scheme/src/eager-reader.scm` is an R7RS reader written
in Scheme and fed one character at a time. When it needs a character it
captures a *composable* continuation up to its own prompt and hands it back,
so every state is a checkpoint and backspace returns to the previous one.
Its parse stack is read out of continuation marks. `fixpt_scheme::eager`
drives it from Rust, feeding only what changed since the last call. The
Scheme REPL uses it through the line editor's new `Oracle`:
- a mistake is marked at the character that makes it, with the message under
  the form;
- `,help` written before a form is finished is answered straight away, and
  the form is given back to carry on typing.

`tests/eager.rs` checks it against the Rust reader on corpora including the
whole prelude and the reader's own source. That found two bugs, both fixed:
the Rust reader called a cut-off dotted list an error, and the bytecode
engine did not tail-call a `call-with-values` consumer (§4).

**Not done.** FX profiles, so the FX REPLs still re-read with the Rust
reader. Datum labels. A position for a bad bytevector element. The original
plan follows.

**The idea.** Olin Shivers, *"Eager parsing and user interaction with
`call/cc`"* ([write-up][shivers]):

> "Reading s-expressions is a recursive task, meaning that when you detect
> invalid input in the middle of a partial s-expression, or want to delete a
> character, you might find yourself somewhere deep inside a stack of recursive
> calls and you'll need to backtrack to a previous checkpoint. That's an almost
> canonical use case for `call/cc`."

Terminal input is normally line-oriented: the driver buffers a line and the
reader sees it only on `Enter`, so bad input is not diagnosed until it is
submitted. Parse *eagerly* instead — feed the reader each character as it
arrives — and mistakes are caught at the keystroke that makes them. The
difficulty is going backwards: backspace has to undo a step of a recursive
descent. Capturing a continuation per character makes undo a matter of invoking
the one you saved.

**What we do instead, and why.** `fixpt_read::form_status` re-reads the whole
buffer from scratch on each `Enter`. That is microseconds for a REPL-sized form
and keeps no parser state between keystrokes, so it was the right first move —
it already bought the thing that mattered, which was [deleting the parenthesis
counter](#why-this-came-up) that disagreed with the real reader.

Re-reading stops being adequate when it stops being cheap or safe:

* **Per-keystroke**, not per-`Enter`. Re-reading on every character is O(n²)
  over a line. Fine at a hundred characters, not at a pasted ten-thousand-line
  definition.
* **Streaming input**, where the characters cannot be rewound to re-read.
* **A reader with side effects** — interning, `#n=` datum labels, reader
  macros — where re-reading is not idempotent. `fixpt`'s reader interns, which
  is why `form_status` uses a scratch `Interner`: a workaround that a
  checkpointing reader would not need.

**Why it fits here particularly.** Two properties this project already has, and
which most of the work has gone into:

* **Re-entrant `call/cc`**, in both engines, with a continuation that is an
  ordinary heap object — a copied value stack plus a bytevector of frames. The
  technique needs exactly this and nothing more.
* **The Core IR lives in the heap**, so a reader *written in Scheme* would be
  dumpable and resumable along with everything else. The reader is currently
  Rust, and is therefore the last significant piece of the REPL that a heap
  image does not carry. Moving it would make the language's own front end part
  of the image, which is the same argument that moved the IR there.

So this is not only a nicer editor; it is the natural next step in "everything
the engine touches is a heap object", and it would be the first place the
engine's `call/cc` is used for something other than testing that `call/cc`
works.

**Where to start.** Write the reader in Scheme against the prelude's `call/cc`,
as a character-at-a-time consumer: `(read-eagerly next-char on-error)` where a
checkpoint is `(call/cc (lambda (k) ...))` saved per character in a stack that
backspace pops. Keep the Rust reader — it is what the conformance corpora go
through, and it is what `form_status` answers with, so the two can be
differentially tested against each other on the same inputs, exactly as the two
engines are.

**Why it keeps coming up.** Three separate features have now wanted the
parser's state *mid-input*, which is the thing a checkpointing reader has and a
batch reader does not:

1. deciding where a form ends (§8's prerequisite, solved instead by re-reading);
2. per-keystroke highlighting, which makes re-reading routine rather than
   occasional;
3. **contextual help at a hole**, which is the sharpest of the three.

`,help` written inside a form asks what belongs there:

```text
fx87> (vector-ref (make-vector 3 0) ,help)
; the hole wants: int
```

That works because the parentheses balance, so the form can be read and
checked. But nobody types it that way. The natural gesture is

```text
fx87> (vector-ref (make-vector 3 0) ,help
```

— ask while still writing, before the form is finished — and that cannot be
read at all: `unterminated list, expected ')'`. The information needed is not
in the text, it is in the *parser's stack*: "argument 2 of `vector-ref`, whose
first argument was a `(vectorof int r)`". An eager reader holding a continuation
per checkpoint has exactly that at the cursor, for nothing. Re-reading a
complete form recovers it only when a complete form exists.

So the entry is no longer only about backspace. The interaction it enables —
asking what goes here, *here* being wherever the cursor is — is not available
any other way.

**Why this came up.** The REPL used to decide where a form ended by counting
parentheses in `fixpt-cli`, in a helper that was a second, ad-hoc s-expression
scanner sitting beside the real one. It did not know that the `)` in `#| ) |#`
closes nothing, nor that the `(` in `|a(b|` opens nothing, and it got both
wrong — submitting a truncated form in the first case and hanging forever in the
second. Commit `5ec8b6a` replaced it with `form_status`. The general lesson is
the one the eager-parsing framing makes obvious: **anything that has to decide
where a datum ends has to be the reader.**

[shivers]: https://programming-musings.org/2010/08/23/at_the_workshop/index.html

---

## 2. Integrate known primitives

**Done for FX, still open for Scheme.** An FX front end can prove a standard
binding is immutable — `(set! + -)` is a *type error* there, since standard
bindings live in `@=` — so it annotates the call and the compiler emits a direct
`prim`. Measured on FX-87, best of five:

|                | ast    | bytecode | + metadata |
| -------------- | ------ | -------- | ---------- |
| loop 1e6       | 0.112s | 0.075s   | 0.062s     |
| fib 24         | 0.014s | 0.011s   | 0.009s     |
| sum of squares | 0.058s | 0.040s   | 0.033s     |

**1.21× from the metadata alone, 1.77× over the AST engine.**

Scheme still cannot do this, and that part of the entry stands: it needs an
"integrate primitives" switch or a guard that de-optimises on redefinition.

### What the 1.21× does not cover

The 42.5% of instructions that were call plumbing did not all go, because only
*standard* bindings are integrable. A program's own procedures — `loop`, `fib`,
`go` in the benchmark — are `letrec`-bound, so a recursive call still costs a
global load and a generic call.

Those are immutable too. A `letrec` binding with no explicit region lives in
`@=` exactly as a standard one does, so `(set! loop …)` is the same type error,
and a self-call could compile to a direct jump rather than a dispatch. That is
the obvious next win and it is the same mechanism: one more claim through the
same channel. `fib 24` gains least from what is there now (1.17×) precisely
because it is dominated by exactly this call.

### Shape, not just annotations

The 2026-09-21 diagnosis found three things lost at erasure: annotations,
resolution and **shape**. The first two now travel as `%fx-note` claims. Shape
does not. FX-87's eraser still lowers `(select r a)` to `(cadr (assv 'a r))`,
an assoc-list walk (`crates/fixpt-fx87/src/erase.rs`), although the checker
knows the field's offset. The reference's own default,
`*order-independent-records* = #f`, has `desc-of-select` stash that offset
and emit `(vector-ref r N)`. `tagcase` likewise becomes a linear `case`,
though the checker knows the full set of tags. The fix is in the eraser, not
the channel: lower records to vectors at checked offsets.

## 3. Patch closures instead of boxing `letrec`

Assignment conversion boxes every binding of a `letrec*` whose initialisers
capture one of them, costing an indirection on every recursive call — see
`docs/divergences.md`. Where every initialiser is syntactically a `lambda`
(overwhelmingly the common case) the closures could instead be built with their
capture slots empty and patched once all of them exist. Nothing in the encoding
stands in the way.

## 4. `call-with-values` is not a tail call — fixed (2026-09-24)

It was, in the AST engine, which pops its `Consume` frame before calling the
consumer. The bytecode engine returned through the call site, so a loop
through `let-values` grew the stack and its continuation marks stacked
instead of replacing. `VmFrame::Consume` now records how `call-with-values`
was called, and in tail position the consumer call is a tail call.
`tests/control.rs` covers it.

## 5. The larger Larceny GC workloads

`tests/gc_workloads.rs` ports GCBench, `grow` and three parts of `permsort`.
Larceny's `test/GC` also has `nboyer`/`sboyer`, `earley`, `lattice`,
`nucleic2`, `nbody`, `dynamic` and `twobit` — substantial programs that would
exercise the whole engine rather than just the collector, and which are the
natural content for M8's benchmark story. Some may need `syntax-rules` (M9).

`gcold.sch` is deliberately not on this list: it targets old-to-young pointers
and write barriers, and this is a single-generation Cheney semispace collector,
so there is nothing there for it to test.

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

* ~~**Long lines redraw wrong.**~~ Done: the arithmetic is in screen rows now,
  with the width from `stty size`. Pulled out of `render` as a pure function so
  it could be tested — which immediately caught an off-by-one at exact
  multiples of the width, where `n` characters occupy `1 + (n-1)/w` rows rather
  than `1 + n/w`.
* **No `^R`** reverse history search.
* **No bracketed paste**, so pasting a large form is processed a keystroke at a
  time and echoes messily.
* **Unix only.** Raw mode is `stty`.

## 8. Syntax highlighting in the REPL

Live colouring as you type: tokens, paren matching, and — the part worth the
most — identifiers coloured by whether they are actually bound, so a typo shows
up before `Enter` rather than after.

**The enabling fact, verified rather than assumed.** `render` in
`crates/fixpt-cli/src/lineedit.rs` computes `target_row` and `target_col` from
the *logical* character buffer, entirely separately from the string it draws.
So SGR escapes inserted into the drawn text cannot disturb the cursor
arithmetic. Colour is close to free; the separation is already there.

**Landed:** unbound identifiers, paren matching, token colour, `NO_COLOR` and
`TERM=dumb`, and the wrapping prerequisite. All of it reads
`fixpt_read::tokens`, which lives in the reader so that a `)` inside `#| … |#`
or `|a(b|` is not mistaken for a delimiter.

**Still open:** binding-site highlighting (the scope walk), marking the
*unclosed* delimiter using the span `form_status` already returns, and — for
FX-91 and FX-87 — colouring by *kind*, since their checkers know what is a
type, an effect and a region.

**In rough order of value for effort:**

* **Unbound identifiers.** `bound_names()` already exists, for `Tab`
  completion. Dim or redden a name that is not bound, live. Catches typos at the
  keystroke, and costs almost nothing.
* **Paren matching** — highlight the partner of the delimiter at the cursor.
  **This must come from the reader.** The `)` in `#| ) |#` and the `(` in
  `|a(b|` are not delimiters, and a matcher that counted for itself would
  repeat the bug that §1 describes. It needs a token-level API out of
  `fixpt-read`: the lexing is all there, just not exposed.
* **Token colour** — strings, characters, numbers, comments, `|symbols|`. Same
  token API.
* **The unclosed delimiter.** `form_status` already runs, and `ReadError`
  carries a `Span`. Underlining the offender is nearly free once colour exists.
* **Binding sites.** Underline where the identifier at the cursor is bound, when
  the binder is on screen — a scope walk over the current form's datum tree
  recognising `lambda`, `let`, `let*`, `letrec`, `define`, `do` and named `let`.
  Bounded work, since the "view" is one form. It cannot reach binders from
  earlier REPL forms, which are not on screen; for those, "bound global" versus
  "unknown" is the honest signal.

**Prerequisite.** Fix the long-line redraw first (§7). The row arithmetic counts
newlines rather than screen rows, so a wrapped line already confuses the cursor,
and highlighting encourages looking at longer forms. `stty size` gives the
width, in keeping with how raw mode is already done.

**Also needed:** honour `NO_COLOR`, detect `TERM=dumb`, and stay monochrome when
not a terminal — the `Plain` reader must be untouched, since the test suite
drives both REPLs through pipes.

**Cost.** Re-parsing per keystroke is O(n), so O(n²) over a line. Fine at REPL
sizes, as §1 says — but highlighting is what makes per-keystroke parsing routine
rather than occasional, which is the condition under which §1's
continuation-checkpoint reader stops being a luxury. The two entries are
related: doing this one is the strongest argument for doing that one.

**Falls out for free:** the FX-91 REPL gets all of the above, since both drive
`LineReader`. Further out, FX-91 could colour by *kind* — the checker knows what
is a type, an effect and a region, and nothing else in either language makes
that distinction visible.

---

## 9. A hole that resumes instead of stopping — done; what remains

**Done (2026-09-24).** SRFI 226's core, on both engines: `with-continuation-mark`,
`current-continuation-marks`, `continuation-marks`, `continuation-mark-set->list`,
`continuation-mark-set-first`, tagged prompts (`call-with-continuation-prompt`,
`abort-current-continuation`, `make-continuation-prompt-tag`),
`call-with-composable-continuation`. Marks, prompts and `dynamic-wind`
extents live in a mark stack beside the frames (`crates/fixpt-runtime/src/cmarks.rs`),
Flatt & Dybvig's attachments. Exception handlers are marks. Every top-level
input runs under a top-level prompt, which uncaught conditions abort to — so
`after` thunks run and nothing leaks into the next input — and which a `,help`
hole captures up to: the hole is a composable continuation, held by the session,
resumable with `,resume EXPR` any number of times, and described by `,where`.
Tests: `crates/fixpt-scheme/tests/control.rs` (both engines, and under
`gc-stress`), `crates/fixpt-cli/tests/help.rs`.

The cost on code that uses none of it, measured against the previous commit
(fib 30 + tak 24 16 8 + a 10⁷ tail loop, release, best of five): bytecode
1.09 s → 1.10 s, AST 1.59 s → 1.65 s — a trim check on every return.

**What is still not right, and why each was left.**

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

**Related.** [§1](#1-a-self-correcting-reader-built-on-callcc) saves
continuations while *reading* a form; this saves one while *running* it.

---

## 10. Syntax parameters — done (2026-09-24)

SRFI 139's `define-syntax-parameter` and `syntax-parameterize`, with
`identifier-syntax` and R7RS `syntax-error`. See `docs/macros.md`. SRFI 139's
own `forever`/`abort` example and a capture-free `aif` are in
`crates/fixpt-scheme/tests/macros.rs`.

Not done, and not needed yet: `identifier-syntax`'s two-clause form with a
`set!` rule (R6RS), which would let `(set! it v)` mean something.

---

## 11. Speculative analysis as you type, and moving the tooling into FX

**The idea.** The eager reader reports *read* errors as they are typed. The
same should hold for expansion errors and, in FX, type and effect errors, by
analysing each form speculatively while it is still being written. Anything run
speculatively must have no effects anyone could notice, and the language that
can *check* that is FX. So the REPL's own machinery — the eager reader, and
eventually the expander — should move from Scheme into FX, where the effect
system says what may be run on every keystroke.

**The prerequisite: control effects.** The eager reader is built on first-class
continuations, and FX-87 as archived has none. Jouvelot & Gifford, *Reasoning
about Continuations with Control Effects* (PLDI '89), gives them. It is not in
the archive — the crawler never fetched it — but it is still served at
<https://groups.csail.mit.edu/cgs/pubs/pldi89-jouvelot.pdf>. The paper:

- adds two control effects on regions: `(goto r)`, for an expression that may
  not return to its continuation, and `(comefrom r)`, for one that may keep its
  continuation for later use;
- types `cwcc` as
  `(poly (r region) (poly (t type) (poly (e effect)
    (subr (maxeff (comefrom r) e) ((subr e ((subr (goto r) (t) void)) t)) t))))`;
- masks both when the expression neither imports variables nor returns values
  whose types mention `r`. The `goto` rule is stricter than FX-87's memory
  masking, and the paper has a contrived program showing why.
- notes that masked control effects make continuations stack-allocatable,
  and compares that to prompts and `shift`/`reset`, which "have to be
  introduced by the programmer".

It says the system was implemented as an extension of FX-87, but no
implementation survives in the archive (`grep` finds no `goto`/`comefrom`
effects in `mit-psrg-fx`). The paper is the specification, and its examples are
the conformance cases.

**What it does not cover, and has to be designed.** Our tooling uses delimited
control — tagged prompts, composable continuations, continuation marks — not
just `cwcc`. A hypothesis to test: a prompt tag plays the part of a region, and
`call-with-continuation-prompt` is where control effects on it are masked,
under the paper's conditions. Marks look like reads and writes on a dynamic
context. None of this is in the paper.

**What "safe to speculate" should mean.** It is not "pure". The eager reader
returns its checkpoint continuation to its caller, so its `comefrom` effect
cannot be masked. What makes it safe is that its effects are confined to
regions the caller owns: allocation, and control on its own prompt. The
criterion to aim for is no `read` or `write` on a region the REPL shares with
the user's program.

**Order.**
1. **Done (2026-09-24):** speculative checking in the FX REPLs
   (`crates/fixpt-cli/src/speculate.rs`, and each dialect's `Oracle`). As a
   form is typed, errors in subforms already finished are underlined, with
   the checker's message under the form. With no error, a hint says what the
   argument at the cursor must be. Original plan: speculative checking in the
   FX REPLs first. The checkers are pure Rust, so
   this needs none of the above: re-read, close off the unfinished form with
   holes, check, and report only errors that lie wholly inside subforms the user
   has already closed. The static `,help` answer ("the hole wants: int") can
   become a live hint at the cursor.
2. Speculative `syntax-rules` expansion for Scheme, against a throwaway copy
   of the expander state. Stop at procedural macros, which run arbitrary
   Scheme.
3. **Done (2026-09-25): the plan for FX-26, the tooling's own language**
   ([`docs/fx26.md`](docs/fx26.md)). The eager reader now exists in FX-26,
   and the Scheme REPL can read with it (`--reader fx26`) once its licence is
   checked. The FX-26 REPL runs licensed expressions as they are typed.
   Next, beyond that plan: the expander and the speculative checker in
   FX-26. Also still open: the shape loss in FX-87's eraser (§2), and
   carrying more of FX-26's facts (region and control claims) through the
   lowering.

---

## 12. What the benchmark ports found hard to write (2026-09-29)

Nine agents ported 87 benchmarks (`scheme-bench/`, `mllang-bench/fx/`);
each header says what its port worked around. The same things came up
in batch after batch. In `PLAN.md` they are queue item Q11; the bigger
ones (identity, integers, floats, unions) are items of their own.

- Done (2026-09-30), both checkers: a local `letrec`'s procedures need
  not name the globals they read (the user's choice: inferred, with no
  starred form); where the group does not check at its types, the globals
  each reads are found as `define*` finds them, round by round until calls
  of each other add none, and the group checked at those types. And an
  effect mismatch now prints, after both whole types, a line with what is
  beyond what is expected. `define-rec` is still as it was. As it was:
- **Globals listed transitively.** A local `letrec` procedure's effect
  must name every global it reads, and every global its callees read,
  datatype constructors included: a loop calling `ocons` must say
  `(read (globals ocons opair))`. Ports used long `define-effect` lists,
  or fell back to `(read @globals)`. `define*` infers this at the top
  level; do the same for local `letrec` and `define-rec` (a
  `define-rec*`). And name the missing atom in the error, instead of
  printing both whole effects (hundreds of names in `conform`).
- **One answer type per prompt tag.** OCaml exceptions caught at several
  types need a wrapping sum, allocated at every `handle`; and a prompt
  rarely masks `goto` when a free variable's type mentions the tag's
  region, so helpers that abort must be bound inside the prompt body.
  (Proposed: a note on tags whose prompts choose their answer type.)
- **`quote` takes only symbols.** Constant lists of numbers, strings or
  booleans become `cons` chains ending in `(the (listof T @heap) nil)`,
  or an in-file reader. Quoted literals typed `(listof T acyclic)` would
  do.
- **No `error`.** Unreachable error branches return made-up values;
  one port signals errors by an out-of-range `array-ref`.
- **Names.** `sum` is reserved; defining `get`, `null?` or `pair?`
  silently shadows the standard one for the rest of the program.

## 13. Checker limitations the ports met

Each has a small reproduction in the port that met it:
- Done (2026-09-30), both checkers: a `letrec` body is checked against
  the type expected of it, as a `let` body is. It was not: `(letrec (…) (if b nil (cons (g) nil)))` fails with
  "argument 2 must be a t2, which is not yet known here". Every port
  wraps such bodies in `(the T …)`.
- A `cons` in one branch of an `if`, or bound by a `let`, gets a fresh
  region instead of the one the other branch or the expected type
  fixes; a lambda passed to a polymorphic procedure is not checked
  against the solved result type. (2026-09-30: the `let` case is what
  bidirectional checking gives, since a binding has no expected type;
  the error says to give one with `the`. Left as it is.)
- Done (2026-09-30), both checkers: a `define-type` or `define-datatype`
  could not name a type defined after it, though `docs/fx26.md` says types
  are declared ahead, so two datatypes could not refer to each other. Each
  abbreviation defined once by name now has its slot in scope before any
  is read, and every cycle is checked to pass through a constructor once
  all are filled (`recursive/types-in-any-order.fx`,
  `recursive/type-cycle-of-names.fx`).
- Done (2026-09-30), both checkers: a `plambda` under a `let` was refused
  against its expected `poly`; a `let` now passes the `poly` to its body,
  and must itself be pure, as a `plambda` body must.
- Done (2026-09-30): `define*` without `spin` on a recursive procedure
  said "it does not check (a mistake of the checker's)"; it now says the
  real problem, the missing `spin`, since only the second check sees the
  recursion. The native path was also said to refuse, "may reach itself
  through a global", some top-level recursive procedures without `spin`
  that the lowered path accepts: not reproduced (a countdown on an `int`
  is refused alike on every path); a port's own case would be needed.
- `length` accepts only frozen `nlist`s, so every port over `@heap`
  lists writes its own. (2026-09-30: `list-length`, at any region.)
- Facts learned from a test were not learned through `or` (found
  2026-09-30): in the else of `(if (or (= n 0) (null? xs)) …)`, `n ≥ 1` was
  not known. Done the same day, both checkers, the conjunctive half (the
  user's): the else of an `or` knows what both its tests show when false,
  the then of an `and` what both show when true, and `not` swaps them. The
  disjunctive half (the then of an `or`, the else of an `and`) waits on
  logical types and occurrence typing, Q7. Tests `sizes/and-or-not-facts.fx`,
  `sizes/or-then-refused.fx`.

## 14. Standard operations the ports wrote themselves

*Mostly done (2026-09-30; `docs/fx26.md`, "Standard operations the ports
wanted"):* `remainder`, `zero?`, `max`, `min`, `bool=?`, `char<?` and its
three kin, `char-upcase`, `string<?` and its three kin, `error`, `append`,
`list-length` (any region), `array->list` and `list->array`, on every
machine and, but for the list and array ones, in the evaluator. `list`
and `eq?` came earlier. Left: `map`, `for-each` and `fold`, which take
procedures and so cannot be runtime primitives: they wait on a standard
prelude written in FX-26 (a question for the user); `string-ci<?`; a
`make-array` with no fill; n-ary `string-append`; mutable strings.

`remainder`, `zero?`, `list`, `append`, `map`, `for-each`, `fold`,
`max`, `min`, `char<?`, `char-upcase`, `string<?`, `string-ci<?`,
`vector->list`/`list->vector` (`array->list`/`list->array`), a
`make-array` without a fill element, `eq?` on booleans (`bool=?`), a
list length for `@heap` lists, n-ary `string-append`, and a mutable
string (or an array of chars to string without a list). Each is small;
together they are most of every port's helpers. Some become generic
operations by dictionary (`PLAN.md` Q8).

## 15. Tools the ports wished for

- Done (2026-09-30): the FX-26 reader reported an unbalanced parenthesis
  at 1:1 ("did not read the whole text"), wherever it was. A text it does
  not finish is now blamed where the Rust reader places it.
- Done (2026-09-30): `sexp-edit order` printed nothing for a forward use
  that `check` reports as unbound: it did not count a `define*` as a
  definition.
- A procedure that falls back to cellular code is named only by a byte
  offset (`lambda@59`), and only at run time; say it when compiling,
  with the procedure's name and why. (2026-09-30: a definition that the
  native compiler declines is said at once, as it is checked, with its
  name and why; left: naming an inner lambda by the `let` or `letrec`
  binding it has, `go@59`, in both compilers alike, since their words
  must agree, and in register code's.)
- Native start-up grows with program size (2.9–3.5 s before the first
  iteration for `boyer`, `ratio-regions`, `tyan`; 6.3 s for `parsing`
  with its 28 KB string): separate compilation's saved front-end image
  (`PLAN.md` Q9, S0) and faster checking would both help.

## 16. FX source sizes and indentation (the user's, 2026-09-29)

- **Size** (done as a lint, `fixpt_tidy::fx_size`): at most 1000 lines per
  `.fx` file and 100 characters per line, met by extracting meaningful
  subroutines and splitting files at their seams, never by re-wrapping.
  The debt, `crates/fixpt-tidy/fx-size-debt.txt`, only shrinks: `check.fx`
  (to split: lists and strings, types, effects, sizes, the checker proper,
  top-level forms), `compile.fx`, `regcode.fx` (its 1223-line `define-rec`
  broken up first), and some 130 lines in test programs and examples.
- **Indentation** (to do): the lint should check that `.fx` code is
  indented as Lisp and Scheme are: a form's arguments under its first
  argument or its body indented two past its head (`define`, `lambda`,
  `let`, `tagcase`, `cond` and the like), and an `if`'s branches under its
  test. The user found an `if` whose else branch, itself an `if`, sat at
  its parent's column (`k-synth-app-plain`, now a `cond`). An indenter in
  `sexp-edit` computes what the lint compares against.

## 17. `(list CONST …)` as a constant (the user's, 2026-09-29)

The register compilers' `r_const` (and the FX-26 mirror) should recognise
`(list c …)` whose elements are all constants as a constant itself: a
frozen list made once, at compile time, as sums and products of constants
are. The type allows it: `list` gives `(listof T acyclic)`, which cannot
be written, and FX-26 has no `eq?`, so no run can tell a shared list from
a fresh one. Today each call makes its pairs at run time (inline, natively).
The rewrite of code and benchmarks to use `list` will turn up constant
lists, which is where this pays.

## 18. The FX-26 evaluator's `set-cdr!` on a global's list (found 2026-09-29)

*Fixed (2026-09-29).* The evaluator keeps no state between forms: each form
is run after the text of those before it, and that text held definitions
only, so an expression's write was lost. Now an expression whose effect
writes is kept in that text too (the evaluator has no I/O, so a write
replayed does just what it did). Test `run/evaluator-writes.fx`.

In `fixpt eval --fx26-run evaluate`, after `(define xs (listof int @heap)
(cons 1 (cons 2 nil)))` and `(set-cdr! (cdr xs) xs)`, `(car (cdr (cdr xs)))`
fails with "a pair is expected": the write does not reach the list the
global holds. Every other path gives 1. Found writing F11's test
(`native/apply-cyclic.fx`).

## 19. `eq?`: identity (the user's, 2026-09-29; PLAN Q5)

*Done (2026-09-30; `docs/fx26.md`, "Identity"):* one `eq?`, `(poly ((t
type)) (subr pure (t t) bool))` (the user's choice, after a first version
with one test per kind of mutable object, each a write of its region):
exact on mutable objects and atoms; on immutable data and procedures `#t`
means equal and `#f` nothing (OCaml's `==`, R6RS's `eqv?` on procedures).
It reaches bloblets, and the evaluator has it. And `(eqtable k v kr r)`,
made with an `(identity k kr)` dictionary that only the standard
procedures make, its operations writing the keys' region, hashed by
address and restamped by the collection count. The ports'
workarounds are retired and `equal` and `dynamic` are ported (2026-09-30). Left: maybe an equality kind, as
SML's `''a`, to refuse `eq?` on procedures; tables keyed by bloblets;
`uniqueof` for interning, and the two-level tables, both below; and,
maybe never (the user's, 2026-09-30), an `eqv?` as R7RS has it (numbers
and characters by value, otherwise `eq?`), for tables keyed by any value
(PLAN.md "Next", item 11). The notes as they were:

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
- Weak references, which we do not have, or an interning table keeps every
  node it made alive.


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

FX-26 has no identity test. Wanted by:
- the benchmark ports (PLAN Q5 lists `browse`, `conform`, `maze`, `sboyer`,
  `peval`, `logic`, `boyer`, `hashtable0`);
- `eq?`-hashed tables;
- the FX-26 evaluator, which cannot find a cycle when `apply` copies a list
  without it (F11; `native/apply-cyclic.fx`).

Prior art, FX-91 (`crates/fixpt-fx91/src/fx-module.fx`, the `uniqueof`
module): identity is opt-in, through an abstract type.
- `(unique x)`: a fresh `(uniqueof t)` around `x`, of effect `init`.
- `(value u)`: its `t`, pure.
- `(eq? u1 u2)`: pure, on two `(uniqueof t)`.
FX-91's references (`refof`) have no `eq?`, and neither does FX-87.

The type is to be decided. Points either way:
- `eq?` must not reach immutable data (products, sums, frozen and `acyclic`
  lists). The compilers rely on no program being able to tell a shared value
  from a copy:
  - `r_const` makes constant data once;
  - `apply` shares an `acyclic` list (F11);
  - TODO §17 would share `(list CONST …)`.
- On mutable objects (refs, pairs and bloblets at a region, arrays, i-cells),
  identity is stable across moving collections, so `eq?` could be pure there.
  PLAN Q5 proposes one per kind of mutable object. FX-91's `uniqueof` is the
  narrower choice: identity only where a program asked for it.
- `eq?`-hashed tables need an address hash that survives collections.
  PLAN Q5 has Larceny's design (tablets stamped with GC counters).

## 20. Shape conflicts during inference are errors, and checking goes on (the user's, 2026-09-29)

*Part 1 done (2026-09-29), in both checkers.* After the first pass over a
polymorphic call's arguments, before any binder can be found unsolved:
- the callee's result is checked against the expected type by outermost
  shape;
- then the arguments found so far, against their parameters.

A conflict is the error, with each unsolved type binder shown as `?`:
`(list 1 (cons 2 nil))` is now "this is a (pairof int ? r), where a int is
expected" (test `a_shape_conflict_is_the_error`). `unify` itself still says
nothing: the check is by outermost shape, `wrong_shape`'s, at the two points
that matter. Still to do: deeper conflicts, the hint for `list`, and part 2.

`(list 1 (cons 2 nil))`, a real type error, is reported as "argument 2 must
be a t2, which is not yet known here". That is an error about `cons`'s own
type variables, which the user never wrote. Found by the `list` rewrite of
the benchmarks.

What happens, in both checkers (`instantiate` in `infer.rs`, `k-instantiate`
in `check-synth.fx`):
1. The expected type is unified with the callee's result first, as a hint:
   `(pairof t1 t2 r)` against `int`.
2. That fails, and the failure is ignored.
3. `nil` fixes nothing, so `t2` stays unknown, and the "not yet known" error
   fires before the result is ever compared with the context, which would
   have said the true thing.

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
`(map f xs)` where an `int` is wanted; a projection at the wrong type. The
error then comes from whatever fails next, an unknown not solved or a later
subtype check, not from the conflict itself.

To do:
1. **Make `unify` report a shape conflict**: a type constructor against a
   different one, as opposed to an unknown merely left unsolved. Each of its
   uses should then report it at once, as the mismatch it is, naming what was
   being matched: "argument 2 is a pair, `(pairof int ? r)`, where an `int`
   is expected". No choice of the unknowns could make a pair an `int`.
   Unsolved unknowns stay a hint, as now. (Alternatively, defer "not yet
   known" errors until the result has been checked against the context;
   reporting at once is simpler and names the right place.) Then add hints
   where a common mistake has an obvious repair, such as the standard `list`
   given a `cons` or `list` argument: "did you mean `(cons 1 (cons 2 nil))`,
   or `(list 1 2)`?"
2. **Keep checking after an error**, to report the errors that follow from the
   same mistake, which often point at the true one. Both checkers now stop at
   the first error, because failures are returned. Going on needs:
   - errors collected, not returned;
   - a failed expression given a stand-in type that unifies with anything
     and is itself reported no further, so that one mistake does not cascade
     into noise;
   - both checkers agreeing on the list of errors, not only on the first.

## 21. Checked once, verified after: a cache, then certificates (the user's, 2026-09-30)

Native start-up is 0.49 s (`docs/performance.md`, "Start-up"): 0.27 s of
it the one Rust check of the whole front end, 0.06 s its compilation to
register code, 0.04 s its run. The user asked whether type and effect
information carried in the code would let the check be done once, the
code cached, and later passes merely verify it.

To do:
1. Done (2026-09-30): **the front end's register code cached**, a heap
   image in the user's cache directory, keyed by a hash of its text and
   of the executable (`docs/performance.md`, "The front end cached").
   Our own code, built with the binary, needs no verifying: the check is
   there for the facts the register compiler reads (fields of `extract`,
   conversions, effect summaries, `apply` sharing), not for safety.
   Start-up 0.50 → 0.19 s.
2. **Verifiable register code, for separate compilation (PLAN Q9)**:
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
3. **Termination as a checkable proof**, so that the size-change search is
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
FX-91's, or second-class units; how the REPL opens one.

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

