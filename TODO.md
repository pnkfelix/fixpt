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

The bytecode engine is only ~1.6× the AST engine, and the reason is visible in
the disassembly: `(+ a b)` compiles to a `GLOBAL` load of `+`, then a `CALL`
that dispatches through a `Primitive` heap object into the primitive table.
Both engines pay it, so arithmetic dominates and the compiled engine's real
advantages — flat closures, resolved slots, no environment chain — are diluted.

The fix is Larceny's: recognise calls to primitives that have not been
redefined and emit a direct opcode. The hazard is that Scheme permits
`(set! + -)`, so it needs either a "integrate primitives" switch, or a guard
that de-optimises on redefinition. `Node::PrimCall` already exists for exactly
this and is currently produced only by assignment conversion.

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

* **Long lines redraw wrong.** The row arithmetic counts newlines, not screen
  rows, so a line the terminal wraps confuses the cursor. Needs the terminal
  width — `stty size`, since there is no `libc` here.
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
