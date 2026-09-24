# Things deliberately left undone

Milestones live in [`PLAN.md`](PLAN.md); intentional differences from the 1987
and 1991 references live in [`docs/divergences.md`](docs/divergences.md). This
file is for the third category: things noticed *while building something else*,
judged not worth doing then, and worth doing later. Each says what it is, why it
was deferred, and where to start — because the reason is the part that goes
stale first.

---

## 1. A self-correcting reader, built on `call/cc`

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

| | ast | bytecode | + metadata |
|---|---|---|---|
| loop 1e6 | 0.112s | 0.075s | 0.062s |
| fib 24 | 0.014s | 0.011s | 0.009s |
| sum of squares | 0.058s | 0.040s | 0.033s |

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

## 3. Patch closures instead of boxing `letrec`

Assignment conversion boxes every binding of a `letrec*` whose initialisers
capture one of them, costing an indirection on every recursive call — see
`docs/divergences.md`. Where every initialiser is syntactically a `lambda`
(overwhelmingly the common case) the closures could instead be built with their
capture slots empty and patched once all of them exist. Nothing in the encoding
stands in the way.

## 4. `call-with-values` is not a tail call

Neither engine calls the consumer in tail position, so a loop written as a
tail-recursive `call-with-values` grows the control stack. Both engines agree,
which is what makes the differential tests meaningful, but R7RS asks for the
tail call. Both are structured to allow it: the consumer call needs the
*enclosing* frame's continuation rather than the call site's.

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
