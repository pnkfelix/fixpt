# Done, from the list of things left undone

What [`TODO.md`](TODO.md) listed, once it was done. Each section keeps
its number from `TODO.md`, so a reference to "§19" means the same thing
in both files. A section that is partly done appears in both: the
finished part here, what is left there. A section done completely
appears only here (so far §4, §16's size lint, §18). Sections are in
number order, and each part says when it was done.

---

## 1. A self-correcting reader, built on `call/cc` (2026-09-24)

`crates/fixpt-scheme/src/eager-reader.scm` is an R7RS reader written
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

What is left is `TODO.md` §1. The plan as it was written follows.

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

**What we did before, and why.** `fixpt_read::form_status` re-reads the whole
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
  dumpable and resumable along with everything else. The reader was Rust, and
  therefore the last significant piece of the REPL that a heap image did not
  carry. Moving it makes the language's own front end part of the image,
  which is the same argument that moved the IR there.

So this was not only a nicer editor; it was the natural next step in
"everything the engine touches is a heap object", and the first place the
engine's `call/cc` is used for something other than testing that `call/cc`
works.

**Where to start (as planned).** Write the reader in Scheme against the
prelude's `call/cc`, as a character-at-a-time consumer: `(read-eagerly
next-char on-error)` where a checkpoint is `(call/cc (lambda (k) ...))` saved
per character in a stack that backspace pops. Keep the Rust reader — it is
what the conformance corpora go through, and it is what `form_status` answers
with, so the two can be differentially tested against each other on the same
inputs, exactly as the two engines are.

**Why it kept coming up.** Three separate features wanted the parser's state
*mid-input*, which is the thing a checkpointing reader has and a batch reader
does not:

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

## 2. Integrate known primitives: done for FX

An FX front end can prove a standard binding is immutable — `(set! + -)` is a
*type error* there, since standard bindings live in `@=` — so it annotates the
call and the compiler emits a direct `prim`. Measured on FX-87, best of five:

|                | ast    | bytecode | + metadata |
| -------------- | ------ | -------- | ---------- |
| loop 1e6       | 0.112s | 0.075s   | 0.062s     |
| fib 24         | 0.014s | 0.011s   | 0.009s     |
| sum of squares | 0.058s | 0.040s   | 0.033s     |

**1.21× from the metadata alone, 1.77× over the AST engine.** Scheme, a
`letrec`'s own procedures, and shape are `TODO.md` §2.

## 4. `call-with-values` is a tail call (2026-09-24)

It was, in the AST engine, which pops its `Consume` frame before calling the
consumer. The bytecode engine returned through the call site, so a loop
through `let-values` grew the stack and its continuation marks stacked
instead of replacing. `VmFrame::Consume` now records how `call-with-values`
was called, and in tail position the consumer call is a tail call.
`tests/control.rs` covers it.

## 7. Line editor: long lines

`crates/fixpt-cli/src/lineedit.rs`: long lines redrew wrong. The arithmetic
is in screen rows now, with the width from `stty size`. Pulled out of `render`
as a pure function so it could be tested — which immediately caught an
off-by-one at exact multiples of the width, where `n` characters occupy
`1 + (n-1)/w` rows rather than `1 + n/w`.

## 8. Syntax highlighting in the REPL: what landed

Unbound identifiers, paren matching, token colour, `NO_COLOR` and
`TERM=dumb`, and the wrapping prerequisite (§7). All of it reads
`fixpt_read::tokens`, which lives in the reader so that a `)` inside
`#| … |#` or `|a(b|` is not mistaken for a delimiter. The `Plain` reader is
untouched, since the test suite drives both REPLs through pipes, and the
FX-91 REPL has all of it too, since both drive `LineReader`.

**The enabling fact, verified rather than assumed.** `render` in
`crates/fixpt-cli/src/lineedit.rs` computes `target_row` and `target_col` from
the *logical* character buffer, entirely separately from the string it draws.
So SGR escapes inserted into the drawn text cannot disturb the cursor
arithmetic.

---

## 9. A hole that resumes instead of stopping (2026-09-24)

SRFI 226's core, on both engines: `with-continuation-mark`,
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

What is still approximate is `TODO.md` §9.

---

## 10. Syntax parameters (2026-09-24)

SRFI 139's `define-syntax-parameter` and `syntax-parameterize`, with
`identifier-syntax` and R7RS `syntax-error`. See `docs/macros.md`. SRFI 139's
own `forever`/`abort` example and a capture-free `aif` are in
`crates/fixpt-scheme/tests/macros.rs`.

---

## 11. Speculative analysis as you type: the first and third steps

1. **Speculative checking in the FX REPLs (2026-09-24)**
   (`crates/fixpt-cli/src/speculate.rs`, and each dialect's `Oracle`). As a
   form is typed, errors in subforms already finished are underlined, with
   the checker's message under the form. With no error, a hint says what the
   argument at the cursor must be. The checkers are pure Rust, so this needed
   none of the control effects below: re-read, close off the unfinished form
   with holes, check, and report only errors that lie wholly inside subforms
   the user has already closed. The static `,help` answer ("the hole wants:
   int") became a live hint at the cursor.
3. **FX-26, the tooling's own language (2026-09-25)**
   ([`docs/fx26.md`](docs/fx26.md)). The eager reader exists in FX-26, and
   the Scheme REPL can read with it (`--reader fx26`) once its licence is
   checked. The FX-26 REPL runs licensed expressions as they are typed.

**The prerequisite, control effects, is built** (`docs/fx26.md`, "Control,
typed"). The eager reader is built on first-class continuations, and FX-87 as
archived has none. Jouvelot & Gifford, *Reasoning about Continuations with
Control Effects* (PLDI '89), gives them. It is not in the archive — the
crawler never fetched it — but it is still served at
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

Delimited control, which the paper does not cover, was designed in step 3:
the hypothesis that a prompt tag plays the part of a region, and that a
prompt is where control effects on it are masked, held with two changes
(`docs/fx26.md`, "Ours to design: delimited control"); a mark key is a
location in the dynamic context, read and written as any other.

---

## 12. What the benchmark ports found hard to write: the parts done

- **Globals listed transitively** (2026-09-30, both checkers): a local
  `letrec`'s procedures need not name the globals they read (the user's
  choice: inferred, with no starred form); where the group does not check at
  its types, the globals each reads are found as `define*` finds them, round
  by round until calls of each other add none, and the group checked at
  those types. And an effect mismatch now prints, after both whole types, a
  line with what is beyond what is expected, instead of only the two whole
  effects (hundreds of names in `conform`). `define-rec` is `TODO.md` §12.
- **No `error`**: there is one now (§14).

## 13. Checker limitations the ports met: the parts done

- **A `letrec` body is checked against the type expected of it**, as a `let`
  body is (2026-09-30, both checkers). `(letrec (…) (if b nil (cons (g)
  nil)))` failed with "argument 2 must be a t2, which is not yet known
  here", and every port wrapped such bodies in `(the T …)`.
- **A `cons` bound by a `let`** gets a fresh region rather than the one an
  expected type would fix: that is what bidirectional checking gives, since a
  binding has no expected type; the error says to give one with `the`.
  Decided (2026-09-30): left as it is.
- **Types in any order** (2026-09-30, both checkers): a `define-type` or
  `define-datatype` could not name a type defined after it, though
  `docs/fx26.md` says types are declared ahead, so two datatypes could not
  refer to each other. Each abbreviation defined once by name now has its
  slot in scope before any is read, and every cycle is checked to pass
  through a constructor once all are filled (`recursive/types-in-any-order.fx`,
  `recursive/type-cycle-of-names.fx`).
- **A `plambda` under a `let`** (2026-09-30, both checkers) was refused
  against its expected `poly`; a `let` now passes the `poly` to its body,
  and must itself be pure, as a `plambda` body must.
- **`define*` without `spin`** on a recursive procedure (2026-09-30) said "it
  does not check (a mistake of the checker's)"; it now says the real
  problem, the missing `spin`, since only the second check sees the
  recursion. The native path was also said to refuse, "may reach itself
  through a global", some top-level recursive procedures without `spin`
  that the lowered path accepts: not reproduced (a countdown on an `int`
  is refused alike on every path); a port's own case would be needed.
- **`length` accepted only frozen `nlist`s**, so every port over `@heap`
  lists wrote its own (2026-09-30): `list-length`, at any region.
- **Facts through `or`, the conjunctive half** (2026-09-30, both checkers;
  the user's): in the else of `(if (or (= n 0) (null? xs)) …)`, `n ≥ 1` was
  not known. Now the else of an `or` knows what both its tests show when
  false, the then of an `and` what both show when true, and `not` swaps
  them. Tests `sizes/and-or-not-facts.fx`, `sizes/or-then-refused.fx`. The
  disjunctive half is `TODO.md` §13.

## 14. Standard operations the ports wrote themselves: most of them

2026-09-30 (`docs/fx26.md`, "Standard operations the ports wanted"):
`remainder`, `zero?`, `max`, `min`, `bool=?`, `char<?` and its three kin,
`char-upcase`, `string<?` and its three kin, `error`, `append`,
`list-length` (any region), `array->list` and `list->array`, on every
machine and, but for the list and array ones, in the evaluator. `list` and
`eq?` came earlier. What is left is `TODO.md` §14.

## 15. Tools the ports wished for: the parts done

- The FX-26 reader reported an unbalanced parenthesis at 1:1 ("did not read
  the whole text"), wherever it was (2026-09-30). A text it does not finish
  is now blamed where the Rust reader places it.
- `sexp-edit order` printed nothing for a forward use that `check` reports
  as unbound (2026-09-30): it did not count a `define*` as a definition.
- A procedure that falls back to cellular code was named only by a byte
  offset (`lambda@59`), and only at run time (2026-09-30): a definition that
  the native compiler declines is now said at once, as it is checked, with
  its name and why. Inner lambdas are `TODO.md` §15.
- Native start-up: the front end's own part is cached (§21, 0.50 → 0.19 s).
- A global defined as a lambda names its word for itself, in both compilers
  (`name_word_for`, `c-name-for!`; 2026-10-05), not `lambda@N`: what a
  disassembly, a fault and a profile show (`FIXPT_SYMBOLS` and
  `fixpt-symbolize`, `docs/performance.md`, "Profiling with `sample`").
- An inner lambda was named only by where its body starts, `lambda@N`
  (2026-10-06): it is named within the one it is in now, for the `letrec`
  or `let` name it is bound to, or `lambda`, and where its body starts,
  `k-mentions-token?/from@174485`, in both compilers alike
  (`scope_name`/`bind_name`, `c-scope-name`/`c-bind-name`). The probe's
  profile says the file and line of each (`word_at`). What is left, the
  native REPL's definitions, is `TODO.md` §15.

## 16. FX source sizes: the lint

Done as a lint, `fixpt_tidy::fx_size`: at most 1000 lines per `.fx` file and
100 characters per line, met by extracting meaningful subroutines and
splitting files at their seams, never by re-wrapping. The debt list,
`crates/fixpt-tidy/fx-size-debt.txt`, which could only shrink, is empty:
`check.fx`, `compile.fx` and `regcode.fx` were split, and the test programs
and examples brought within the limits. The two generated files (FX-87's
`standard.fx`, FX-91's `fx-module.fx`) are exempt (the user's). Indentation
is `TODO.md` §16.

## 18. The FX-26 evaluator's `set-cdr!` on a global's list (2026-09-29)

In `fixpt eval --fx26-run evaluate`, after `(define xs (listof int @heap)
(cons 1 (cons 2 nil)))` and `(set-cdr! (cdr xs) xs)`, `(car (cdr (cdr xs)))`
failed with "a pair is expected": the write did not reach the list the
global holds. Every other path gave 1. Found writing F11's test
(`native/apply-cyclic.fx`).

The evaluator keeps no state between forms: each form is run after the text
of those before it, and that text held definitions only, so an expression's
write was lost. Now an expression whose effect writes is kept in that text
too (the evaluator has no I/O, so a write replayed does just what it did).
Test `run/evaluator-writes.fx`.

## 19. `eq?`: identity (2026-09-30; PLAN Q5)

`docs/fx26.md`, "Identity": one `eq?`, `(poly ((t type)) (subr pure (t t)
bool))` (the user's choice, after a first version with one test per kind of
mutable object, each a write of its region): exact on mutable objects and
atoms; on immutable data and procedures `#t` means equal and `#f` nothing
(OCaml's `==`, R6RS's `eqv?` on procedures). It reaches bloblets, and the
evaluator has it. And `(eqtable k v kr r)`, made with an `(identity k kr)`
dictionary that only the standard procedures make, its operations writing
the keys' region, hashed by address and restamped by the collection count.
The ports' workarounds are retired, and `equal` and `dynamic` are ported.
What is left is `TODO.md` §19.

What was weighed before deciding, for the record. FX-26 had no identity test,
and it was wanted by:
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

Points either way:
- `eq?` must not reach immutable data (products, sums, frozen and
  `acyclic` lists). The compilers rely on no program being able to tell a
  shared value from a copy:
  - `r_const` makes constant data once;
  - `apply` shares an `acyclic` list (F11);
  - `TODO.md` §17 would share `(list CONST …)`.
- On mutable objects (refs, pairs and bloblets at a region, arrays, i-cells),
  identity is stable across moving collections, so `eq?` could be pure there.
  PLAN Q5 proposed one per kind of mutable object. FX-91's `uniqueof` is the
  narrower choice: identity only where a program asked for it.
- `eq?`-hashed tables need an address hash that survives collections.
  PLAN Q5 has Larceny's design (tablets stamped with GC counters).

## 20. Shape conflicts during inference: part 1 (2026-09-29, both checkers)

`(list 1 (cons 2 nil))`, a real type error, was reported as "argument 2 must
be a t2, which is not yet known here". That is an error about `cons`'s own
type variables, which the user never wrote. Found by the `list` rewrite of
the benchmarks. What happened, in both checkers (`instantiate` in
`infer.rs`, `k-instantiate` in `check-synth.fx`):
1. The expected type is unified with the callee's result first, as a hint:
   `(pairof t1 t2 r)` against `int`.
2. That fails, and the failure is ignored.
3. `nil` fixes nothing, so `t2` stays unknown, and the "not yet known" error
   fires before the result is ever compared with the context, which would
   have said the true thing.

Now, after the first pass over a polymorphic call's arguments, before any
binder can be found unsolved:
- the callee's result is checked against the expected type by outermost
  shape;
- then the arguments found so far, against their parameters.

A conflict is the error, with each unsolved type binder shown as `?`:
`(list 1 (cons 2 nil))` is now "this is a (pairof int ? r), where a int is
expected" (test `a_shape_conflict_is_the_error`). `unify` itself still says
nothing: the check is by outermost shape, `wrong_shape`'s, at the two points
that matter. The rest is `TODO.md` §20.

## 21. Checked once: the front end's register code cached (2026-09-30)

Native start-up was 0.49 s (`docs/performance.md`, "Start-up"): 0.27 s of it
the one Rust check of the whole front end, 0.06 s its compilation to
register code, 0.04 s its run. The front end's register code is now cached,
a heap image in the user's cache directory, keyed by a hash of its text and
of the executable (`docs/performance.md`, "The front end cached"). Our own
code, built with the binary, needs no verifying: the check is there for the
facts the register compiler reads (fields of `extract`, conversions, effect
summaries, `apply` sharing), not for safety. Start-up 0.50 → 0.19 s.
Verifiable code and certificates are `TODO.md` §21.

## 25. Emacs, step 1: `fx26-mode` (2026-10-05; PLAN Q14)

`editors/emacs/fx26-mode.el` and its `README.md`: font-lock for kinds,
effects and `@regions`; the repository's indentation (`define-rec` members
and `tagcase` arms as definitions; re-indenting the front end changes 3% of
its lines, where the source is itself irregular); `run-fx26`, a comint REPL
over a pipe (send definition, region, file); `flymake` over `fixpt check
-`; `eldoc` with globals' types; `fx26-restart-repl`; ERT tests
(`editors/emacs/run-tests.sh`). What `fixpt` does differently for Emacs is
behind `--emacs` (the user's wish): no continuation prompt, and `,at FILE
LINE COL` before a sent form, so its errors name the buffer's file, line and
column. The REPL's code is collected (`NativeMachine::collect_code`) and
old definitions die (PLAN Q13, O2), so a session that reloads on every save
lasts: 300 reloads of a 370-line file, checked. Loaded by
`~/.emacs.d/init.el`, made with the user's leave. Steps 2 and 3 are
`TODO.md` §25.

## 29. Re-runs wait at the REPL (2026-10-05; PLAN Q13 O12)

A redefinition at a type not every use can take made a new global and
checked and ran again, on the spot, every earlier definition using the
name, in both checkers (`Checker::top_defining`, `k-defining`). Over a
`,load` of a file whose later forms use earlier ones, that is quadratic:
redefining form *i* re-ran forms *i+1 … n*, each of which the same load
then defined again. A second load of `okasaki.fx` re-ran 13, one
redefinition re-running 10 forms redefined a few lines later.

Now, at the REPL (the user's plan), re-runs wait (`docs/fx26.md`,
"Redefinition"):
- a redefinition that makes a new global leaves the definitions that use
  the name themselves *out of date*: they keep the old global, neither
  checked nor run again, so nothing is broken and nothing reads a value at
  a type it was not checked at; defining one again brings it up to date;
- after a form that changes what is out of date, the REPL says so: "; out
  of date (1), using what was defined again: `g`; `,rerun-outdated` runs
  them again";
- `,list-outdated` names each, with what it uses that was defined again;
  `,rerun-outdated` defines each again, oldest first, until none is left
  that has not been tried; one that does not check stays out of date,
  usable, saying why;
- both checkers take it as a setting, `Checker::defer_reruns` and
  `check-defer-reruns!`, which `Fx26Session::set_defer_reruns` sets; files
  run by `fixpt eval` and `check` keep the rule as it was.

Measured, 20 `,load`s of `okasaki.fx` in one native REPL: re-runs 133 (399
definitions) → 0, breakages from them (O13's regions) → 0, total 6.4 →
5.3 s (start-up and the first load are 3.5 s; each reload 0.15 → 0.09 s).
Test: `fixpt-cli/tests/dialects.rs`,
`the_fx26_repl_reruns_outdated_definitions_when_asked`.

## 30. Private regions declared again are the same (2026-10-05; PLAN Q13 O13)

`(private-regions @q)` read again, by a second `,load` of the same file,
made `@q` a new private region (`@q.4`), so definitions still typed at the
old one (`@q.1`) and those defined again at the new one no longer fitted
together: a re-run dependent failed until the load redefined it, and a
value made before the load could not be passed to a procedure defined by
it. Now a region the program already has as private, declared private
again, stands for the same one, in both checkers (`top.rs`'s
`private-regions`, `check-program.fx`'s `k-private-region`): a reload is
the same program over the same regions (`docs/fx26.md`, "Redefinition").
Twenty loads of `okasaki.fx` now show only `@q.1`, and its redefinitions
assign their globals (380), but for `expects`, whose inferred type names a
region fresh at each load (`@r.2`), so that it makes a new global (19),
which nothing uses. Test:
`programs/redefine/private-again.fx`, `tests/redefine.rs`
`private_regions_declared_again_are_the_same`, lowered and compiled.

## 31. The bootstrap test's six minutes (2026-10-05; PLAN B2)

`fixpoint_with_words_compiled_by_fx26` (`crates/fixpt-fx26/tests/bootstrap.rs`)
took about 347 s, most of a 9-minute suite. Sampled (macOS `sample`), the
time was all collection: `Heap::collect`, `copy_object` and `memmove`,
called from `collect_for_code` under `run_word_as_is`, a full major
collection at every `%run-word`, 5,428 of them. The cause, from the code
collection of the same day (`4e11a7b`): `collect_for_code` collected the
heap when the code was due to be collected, but only compiling
(`compile_reachable_as`) collected the code and reset the trigger. The
test places its code from elsewhere (`install`, what FX-26's `native.fx`
assembles) and runs words as they are, compiling nothing; once 8 MB was
placed, the code stayed due, and every run collected the heap.

Now `collect_for_code` collects the code right after the heap. The test
takes 19.5 s (one code collection), the suite 3.5 minutes. Test:
`fixpt-native/tests/code_gc.rs`,
`running_placed_code_does_not_collect_at_every_run` (100 major
collections in 100 runs without the fix; at most one with it).

## 39. A checker's ids checked (2026-10-06)

The Rust checker's ids, `TyId`, `ExpId`, `DVar` and a generative type's
number, were made by unchecked casts, `len as u32 - 1`, which past 2^32
entries would wrap round and name an old entry. They are made by
`ast::last_id` now, which fails saying so. Reclaiming the tables, so that
a long session does not grow them without end, is `TODO.md` §39.

## 38. A re-export of a module member inlined, as the member (2026-10-05)

The pilot (`TODO.md` §34) re-exported `table.fx`'s procedures as
`(define table-ref (with tables table-ref))`. Its "no measurable cost" was
the user's doubt, rightly: a call of such a global compiled to a full call
(`global` and `invoke`), where a global defined as the lambda is inlined
behind a guard. A loop calling a one-line procedure, 400 M calls on
register code: 0.68 s direct, 1.06 s re-exported. Two source-level
workarounds were tried and were slower, an eta-expanded wrapper (1.41 s)
and one closing over the module, `(let ((m m)) (lambda …))` (1.40 s):
neither makes the member's value known where it is called.

Now both compilers note, while a top-level `(define m (module …))` is
compiled, each member that is a lambda naming no other member (its word,
parameters, body, and the globals it sees: `module_members`, `modules`;
`c-module-members`, `c-collecting`, `c-modules`); a global defined as
`(with m f)` is then inlined where called as `f` would be, if small, not
calling itself and not staying cellular, behind the same guard, the
global holding the member's closure (`reexport_inline`,
`c-reexport-inline!`). The loop: 0.65 s re-exported. A module inside a
member notes nothing; a module defined again forgets its members. Test
`tests/register_code.rs`, `a_reexported_module_member_is_inlined`,
`programs/run/reexport-inlined.fx`, both compilers. What is left is
`TODO.md` §38.

## 37. A module's values see each other, as a `letrec*`'s (2026-10-05)

Found moving `table.fx` into a module (`TODO.md` §34): a module's `define`
did not see its own name, and its definitions saw only those before them.
The user's intent was `letrec*`: every name a module defines in scope in
all of it, its items made in the order written, nothing reordered (the
author keeps the order), and an item made too soon refused statically.

The rule (`modorder.rs`, the FX-26 checker's `check-modorder.fx`): a
typed lambda (a `define` with a type whose value is a lambda, or a
`define-rec` member) may name any item, earlier or later, as it does not
run when it is made; procedures calling each other need no `define-rec`.
Any other value is made when its item is, so what it names, and what the
lambdas it names name, followed through them, must all be made before it:
otherwise the module is refused, naming the chain, `` `y` uses `get-x`,
which uses `x`, defined after `y` ``. It follows names, not calls, so
`(define v int (if #f (g) 0))` before `g` is refused too; moving `g` up
is the remedy. A lambda's recursion is found by what the typed lambdas
name: each one in a cycle is checked to end with its cycle, as a
`define-rec`'s members are, and says `spin` if that may not.

Downstream, with no reordering: each checker binds the typed lambdas at
their written types first, checks every other item in order, then the
lambdas, in the scope of everything; the module's type lists its values
in written order. The lowering is one `letrec*`. The evaluator opens
every name's cell first and fills them in order. Both compilers make the
items in their slots in order (stack and register code alike); a lambda
naming an item not made yet captures a placeholder, patched as soon as
that item is made (as a `letrec`'s siblings are), and the rule guarantees
nothing runs it before then. Every walk of a module's names (free
variables in both checkers and both compilers, masking, the termination
walk) binds all of them for every item. Tests `modules/forward.fx`,
`modules/mutual.fx`, `modules/own-name.fx`, `modules/made-too-soon.fx`,
`modules/made-too-soon-through.fx`, `modules/named-too-soon.fx`.

How it got here: first built, and committed (`9957fa0`), as only "a typed
lambda definition sees its own name", the parser making it a `define-rec`
of one, from a misreading of "the author keeps the order" as "each item
sees those before it". A version reordering items in the parser into the
order they are made was designed and dropped: the user wanted no
reordering, the rule enforced downstream. Found on the way: `sexp-edit
move` put a top-level definition moved before a `define-rec`'s member
inside the group; it goes before the group now.


## 52. Deep recursion in native code: a copying stack cache (2026-10-07)

The native convention ran on one fixed stack of 2^26 words and trapped
"stack overflow" between 5M and 20M frames of `(+ 1 (down (- n 1)))`,
where Scheme recurses as deep as its heap allows. Now a run's part of the
stack is a cache (`docs/research/deep-recursion.md`, "The first version";
`fixpt-native/src/direct.rs`):

- **Overflow**, at a procedure's entry whose frame passed the cache's
  limit: `common_overflow` keeps the registers and calls out; every other
  frame of the run is copied into the heap as the stack cache's chain, in
  chunks of about 4096 words, each frame as it was on the stack (its link
  its size, its dead words 0); the new frame (with any marks in tail
  position under it) moves to the cache's top, its return address the
  underflow's.
- **Underflow**: a return off the cache's top lands in `common_underflow`,
  which restores frames from the chain, at least one and on to 256 words,
  never ending above a prompt's or a mark's frame its owner pops, nor
  above a mark in tail position, and resumes the innermost.
- **Control** sees the chain as the rest of the stack: an abort finds a
  prompt there and restores from it; `first-mark`, `current-marks` and
  `marks-of` read marks there; a whole continuation is the stack's frames
  in a chunk onto the chain (shared, never changed); a delimited one, the
  frames up to its prompt, copying the chain's part when the prompt is in
  the chain. Putting back a delimited continuation copies its frames onto
  the stack directly when they fit, as before.
- **Sizes**: the cache is half the stack (2^25 words) by default, so
  that what fitted before runs as before; a run's frames may take 2^28
  words in all. `FIXPT_NATIVE_STACK_CACHE` and `FIXPT_NATIVE_STACK_MAX`,
  or `DirectMachine::set_stack_words`, say otherwise. `stack_stats()`
  counts overflows, frames flushed, underflows and frames restored.

| `down` to depth |         before |  after | cellular registers |
| --------------- | -------------: | -----: | -----------------: |
| 5M              |          41 ms |  41 ms |                    |
| 20M             | stack overflow | 426 ms |       about 700 ms |
| 50M             | stack overflow | 1.07 s |        about 2.1 s |

Natively, through `,native`; a frame past the cache costs about 20 ns to
flush and restore. `captures` (a continuation taken and resumed 20 calls
deep, 20 000 times) went from 11.4 to 9.0 ms natively: a continuation is
now one chunk of frames as they were, copied onto the stack in one copy
each, where it was a vector rebuilt a word at a time.

Tests: `deep_recursion_through_the_stack_cache` (`direct.rs`,
`programs/native/deep-control.fx`), on a cache of 4096 words, collecting
every 97 safepoints: values held across 100 000 frames flushed and
restored; an abort to a flushed prompt; a mark read through flushed
frames; a composable continuation of 20 000 flushed frames taken and run
twice; and a mark in tail position under a thunk whose frame overflowed,
replaced, not duplicated (on a cache of 4098 words, where the overflows
fall there: without keeping the mark's frame with the thunk's, 60087, 87
marks too many). `fuel_and_stack_run_out` overflows past 2^20 words.

On the way: `Heap::vector_with` writes each element once, with no barrier
(a new object's stores need none, as `cons`'s); `Heap::obj_words` gives an
object's payload to copy whole.

**Then, Larceny's way, stage 1 (the user's, 2026-10-07): the stack flushed
at every collection.** A collection a native call-out makes first copies
the run's frames onto the chain (`flush_all`), collects with no stack to
read (the chain, the call-out's arguments and its code the roots), then
restores the innermost frames; the code takes its frame from the state
after every call-out. The collector no longer scans frames, nor are
their roots gathered (a `Vec` a frame, every collection: 17 ns a frame);
so the cache is small, 2^16 words, all of it flushed at worst each time.
`(dive D 200000)`, a recursion `D` deep allocating nothing, then 200 000
lists of 100 at its bottom (about 38 minor collections):

| depth `D` | before, ms | after, ms |
| --------: | ---------: | --------: |
|   100 000 |        100 |        47 |
| 1 000 000 |        732 |        88 |
| 3 000 000 |      2 118 |       216 |
| 8 000 000 |      2 935 |       500 |

The cost moves to recursion past the cache that allocates nothing, which
the large cache had kept on the stack: `down` 5M deep 41 → 115 ms, 20M
426 → 455 ms (about 15 ns a frame flushed and restored, whatever the
cache's size, 2^16 to 2^20). Stage 2, in place, removes the flush's copy.

**Stage 2 (2026-10-07): the stack in the nursery, flushed in place.** The
native stack is the heap's now (`Heap::native_stack`): the top 2^26 words
of the nursery's range, which the nursery never allocates into. A flush
makes the run's frames one chunk where they are (`flush_in_place`): its
header (`Heap::vector_in_place`, with an extension word past 2^18
fields) and its fields below the innermost frame, its trailer at the
run's top, each frame's link its size, its return address a fixnum, its
dead words 0. The chunk is then an object of the nursery, and the
collection that follows moves it out: that is the one copy. An overflow
collects, as Larceny's does. Its site says which registers hold values
(`overflow_info`: the arguments, the closure if read, a variadic
procedure's saved arguments), and passes its own code bloblet, since its
frame has not stored it yet. So the cache is the nursery's size again,
2^20 words: a collection per 2^20 words of frames.

On the way, a cost that deep recursion exposed: every minor collection
read the card table a byte per card over the whole old space, so its time
grew with the old space (2.4 ms a collection with 64M words old). It now
reads the table a word, eight cards, at a time, and skips clean words.

| measure                     | stage 1, ms | stage 2, ms |
| --------------------------- | ----------: | ----------: |
| `(dive 1000000 200000)`     |          88 |          65 |
| `(dive 8000000 200000)`     |         500 |         334 |
| `,native down 5000000`      |         115 |          99 |
| `,native down 20000000`     |         455 |         413 |

`down` 50M frames is 300M words, past the default 2^28 the frames may
take (`FIXPT_NATIVE_STACK_MAX`): it ran before only because the old cache,
2^25 words, did not count; given room, 1.05 s. The benchmarks: the same,
back to back. Tests: as before, and the Scheme engine's under
`gc-stress`.

## 53. Native frames as heap objects where they stand (2026-10-07)

The user's ask: make it easy, even trivial, to make a native stack frame a
heap object. Done as part of §52's stage 2, without a header a frame:

- No raw word lives in a frame: register code keeps raw `i64`/`f64` in
  registers only, boxing before a `setstk`
  (`fixpt-native/src/direct/reps.rs:14-16`). Every word of a frame after
  its link is a value but its return address.
- So a run of frames is one object where it is (`flush_in_place`): a
  header and three fields written below the innermost, a trailer at the
  top, and in each frame two words rewritten (the link as its size, the
  return address as a fixnum) and its dead words, by its stack map, made
  0. Nothing is copied.

Set aside: a bloblet header in each frame, stored by its entry (the
first design, in `TODO.md` §53 as it was): one store more a call, for
nothing that the run-as-one-object does not give. It would matter if a
single frame had to be an object alone, which nothing needs yet.

## 55. Bitwise operations on `int` (the user's, 2026-10-07)

The fixed widths had theirs (`i32-and`, `u64-shl` and kin); `int` had
none, so the FX-26 checker's union shapes were lists where `check.rs` has
a mask. Now SRFI 151's names, in both checkers, the lowering, the
evaluator and every machine: `bitwise-and`, `bitwise-ior`, `bitwise-xor`,
`(subr pure (int int) int)`; `bitwise-not`, `(subr pure (int) int)`;
`arithmetic-shift`, left by a positive count and right, rounding down, by
a negative one. Two's complement, of any size: runtime primitives
(`%fx26-bitwise-and` …), fixnums without a big integer, bignums with one;
a left shift past 2^24 bits of a non-zero integer fails. The FX-26
checker's shapes are masks since (`check-unions.fx`). Tests:
`bitwise_on_every_machine` (six machines, bignums and a negative shift),
and the evaluator against the lowering (`tests/evaluator.rs`). Natively
they were call-outs; their fixnum fast path is `DONE.md` §56's.

## 56. Shape predicates in line, natively (Q7's stage 2, 2026-10-07)

Of the shape predicates only `null?` was in line (`eq` with `nil`); the
rest were primitive calls, call-outs from native code, so `lseq` with its
tail a union took 6.6 s against its sum's 4.0 s. Now both native tiers do
them in line, by the value's tag and, for a bloblet, its header's kind
(the word before the suffix, or as far back as the trailer there says;
fields and no trailer, or a large header, still call out): `pair?`,
`exact-integer?` (a fixnum, or a bignum's kind), `char?`, `boolean?`,
`symbol?`, `string?`, `%fx26-array?` (a plain bloblet), `%fx26-procedure?`
(any machine's closure, primitive or continuation); `direct.rs`'s
`shape_fast` under the native convention, register code's `shape_test` at
`prim1`. `int`'s `bitwise-and`, `-ior`, `-xor` and `-not` of fixnums are
in line too (`arithmetic-shift` still calls out). The cells' machines
call out for every primitive, these as the rest.

Back to back with the build before, 10M tests in a loop: `procedure?`
0.32 → 0.17 s natively; a loop of `bitwise-xor` and `bitwise-and` 0.54 →
0.18 s natively, 0.47 → 0.19 s in register code. `lseq` with the union,
6.4 → 2.0 s natively and 6.6 → 3.0 s in register code, where the sum's is
4.0 and 3.0: `scheme-bench/lseq.fx` is converted. Tests: the every-machine
union program's harder cases (a primitive and a continuation as
procedures, a bignum, an array with a large header).

## 57. Mutable bloblets made and written in line, natively (2026-10-07)

`make-bloblet` was `%make-bloblet`, a call-out with a frame around it, and
under the native convention so was every `bloblet-set!`, where `cons` and
frozen bloblets were made in line and register code wrote fields in line.
Found converting `gcbench`'s node to Larceny's one record: 3.0 s against
the three pairs' 1.3. Now a bloblet of no suffix is made from the free
space in both native tiers (its header, fields and trailer, as
`%make-frozen`'s are, but writable; any suffix calls out), and
`direct.rs` writes a field in line as register code's `field!` does (the
trailer's count bounding it, the header's frozen bit refusing it to the
call-out, the card marked).

Back to back with the build before, natively: `gcbench` with its node a
bloblet, children `(union int node)`, 0.60 s against the pairs' 1.18 (and
0.63 against 1.12 in register code), so `scheme-bench/gcbench.fx` is
converted; and ports that make or write bloblets, unchanged: `conform`
3.70 → 2.02, `hashtable0` 2.04 → 1.31, `maze` 1.33 → 0.98, `set` 1.47 →
1.17; `bv2string`, `nboyer`, `sboyer` level. Their answers the same.
Test: `mutable_bloblets_made_and_written_in_line` (`tests/direct.rs`,
`programs/native/bloblet-tree.fx`), a tree built, its leaves replaced by
younger nodes, summed, collecting every 7 allocations too.

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
- Q7's first stage (2026-10-07) made `pairof` non-`nil` and spells "a
  pair, or none" `(union nil (pairof …))`, `nil` written as a type only
  there so far. Its second stage (2026-10-07) made `nil` a type of its own,
  in unions and where a pair that may be `nil` is expected whose tail is
  no list (instantiation gives the type `nil` there); the value `nil` is
  still polymorphic everywhere else, so the joins and `let`s above remain.
- **Done (2026-10-08).** Both checkers. The value `nil` keeps its `poly`
  type, so instantiation where a type is expected is as before; where
  nothing says which list, it is of the type `nil`:
  - an argument whose parameter neither the expected result nor any other
    argument has solved, heard after all of them (`infer.rs`, the told
    arguments; `k-nil-told`): `(null? nil)` is a `bool`. If the type `nil`
    still leaves the parameter unknown, the error is as before: `(car nil)`;
  - widened at the binder's use (the user's choice, 2026-10-08): a call's
    result `(pairof A v R)`, nothing expected of it, `v` solved to `nil`
    and `A` known, has `v` a `(listof A R)` instead (`widen_nil_tail`,
    `k-widen-nil-tail`), so `(cons 1 nil)` is a `(pairof int (listof int
    R) R)`, a list. Sound because the pair is new: no alias sees its tail
    as `nil` alone, which invariance (a pair can be written) otherwise
    guards; and each argument is checked against its parameter as
    re-solved. Not a subtyping rule: subtyping cannot know a value is new.
    Where a type is expected, it decides: `(pairof int nil R)` expected,
    the tail stays `nil`;
  - an `if`'s branches and a `tagcase`'s arms (`cond`, `case`, `typecase`
    through them), each `nil` the type `nil` before the join, and, if one
    is, each pair one that may be `nil` (`join_with_nil`,
    `k-join-with-nil`): `(if c nil xs)` is `xs`'s type, `(if c nil nil)` a
    `nil`, `(if c (cons 1 nil) nil)` a `(union nil (pairof int (listof int
    R) R))`, which is `(listof int R)` unfolded once (shown so);
  - a `let` of `nil` stays polymorphic; each use of it is one of these.
  - Not done: `(with #%fx nil)` (§46); `(list (cons 1 nil) nil)`, whose
    element binder the first argument solves to a pair that `nil` is not
    (a binder solved by the join of its arguments, not the first, would
    do); and a `let` of a new pair, unannotated, puts it in a fresh region,
    so `(let ((x (cons 1 nil))) x)` is no `(listof int @heap)` (any
    allocation's, not `nil`'s).
  - Tests: `tests/bidirectional.rs`
    (`nil_is_of_the_type_nil_where_nothing_says_which_list`, and
    `a_type_nothing_determines_is_an_error` now with `(car nil)`).

## 64. The reader's module types, shown, are megabytes (2026-10-08)

Since the reader and the parser are module files made by `reader.fx`, the
front end's top level holds their instances: `make-reader`,
`parser-top-module`, `parser-exps-module`, `parser-module`. Each one's type,
as both checkers show it for the form's line, is about 1 MB (290 KB,
540 KB, 946 KB, 948 KB), for two reasons. Each module holds the one below
as a value, so each type holds the one below's whole type; the
`parser-top` one holds `parser-exps`'s, and `parser`'s and the reader's
again. And types the parser defines show written out (`(mu %4 (sumof
(e-var …` inside `top`), not by name, though a small module's datatypes
keep their names; perhaps because they mention `syn` through a `select`, and
so are not noted closed (`k-closed-named`) and are copied by substitution.
The checker written in FX-26 builds those strings by appending, so its
check of the front end went from 1.0 s to 6.4 s (`fixpt bench --front-end`,
"fx check"), most of it there (sampled: `Heap::string_points_into`); the
Rust checker is barely slower (614 to 646 ms). Neither user programs nor
session start are affected (0.15 to 0.18 s).

**Done (2026-10-08).** Why the names were lost: a `select` of a global
module is linked to what it names (`link_global_select`,
`k-link-global-select`), so types through it are shared and keep their
names; a `select` of a module's item was resolved by copying instead, at
each resolution, so `exp` in `top`, in each constructor's signature and in
its own description were all copies, and only one could be named. Now an
item checked before the rest of its module (`early_modules`), bound once
for all of it, is linked as a global is (`fixed_slots`, `k-fixed`). The
largest type shown is 104 KB, from 948 KB; the checker written in FX-26
checks the front end in 1,056 ms (1,032 before the move). Before that, on
the way: substitution's and `k-finitize`'s memos became hash tables, not
lists (quadratic on a large type), and naming a type while showing it
uses a tree made once per type shown (`k-atree`). Not done, not needed
now: an upper file holding only the instance just below.

## 67. A front-end error reported at the user program's position (2026-10-08)

While the rewritten evaluator was being written, an error in the front end
(`eval-core.fx`, a recursive `define*` without `spin`) was reported as
`crates/fixpt-fx26/tests/programs/unions/more-shapes.fx:21:1`, the program
being run, not the front-end file and line. `--fx26-run evaluate` checks the
front end and the program together; the front end's spans should name its
own files (as the cellular span keys have since 5b46108). Reproduce by
breaking a front-end file, then make the error name it.

**Done (2026-10-08).** The register-code path (`front_end_as_register_code`,
which `--fx26-run evaluate` and `cellular` take) checked the joined front
end with `?`, so its spans, offsets into that text in `FileId(0)`, were
shown by the CLI's `located` against the user's file. Now an error checking
the front end is `front_end_error`'s: its message placed by
`front_end_location` (`the front end, eval-core.fx:434:39: …`), its span in
`FRONT_END_FILE`, no file of the user's, which `located` shows as the
message alone; loading failures there are `front_end_failure`'s, likewise.
Test: `bootstrap.rs`, `an_error_in_the_front_end_is_placed_in_its_files`.

## 61. Fixed-width operations in the FX-26 evaluator (2026-10-08)

`--fx26-run evaluate` has none of the fixed-width operations (`u32+`,
`int->u32`, `i64<` …): `programs/sizes/fixed-width-literals.fx` fails
there with "unbound variable `u32+`", while the lowering, cellular, native
and register machines give 8. Found while testing `i32`/`u32` below `int`
(a5f0979); it predates that. Add them to the evaluator's table of
primitives (`eval-prims.fx`, since the rewrite), with the same wrapping as the runtime's, so every
path runs a fixed-width program alike; then a test that runs one on the
evaluator. No native speed at stake (the evaluator is a reference path),
so only as much as agreement needs.

**Done (2026-10-08).** `eval-prims.fx`, `ev-width-prims!`: for each width,
its 19 operations and `int->T`, `T->int`, as integers kept in the width's
range, every result wrapped as the runtime's `Width::wrap` wraps it;
`quotient` and `remainder` truncating, by zero "division by zero"; shifts
by the count's low bits, right arithmetic. `native/fixed-width-ops.fx`
(every operation at the edges of each type, by checksum) gives the same on
the Rust, native and register machines, the lowering, `--fx26-run
cellular` and the evaluator; it and `sizes/fixed-width-literals.fx` (8)
are in `evaluator.rs`'s `test_programs`.

## 66. Local type inference: bounds from both sides (the user's, 2026-10-08)

Found by the evaluator's rewrite: `(array-ref bs i)`, `bs` an `(arrayof int
@v)`, checked where a `val` (a union with `int` in it) is expected, is
refused. The expected result fixes `t := val` before the argument is seen,
where synthesizing `t = int` from the argument and then subsuming `int ≤ val`
would succeed (`eval-prims.fx` writes `(the int …)` for now). The user's
idea: let each side contribute bounds, a lower bound from the arguments and
an upper one from the expected type, narrowing until they meet, then check
that a solution exists. That is Pierce and Turner's local type inference
(TOPLAS 2000; from memory): gather `S ≤ t ≤ T` for each variable from the
arguments and the expected result, then pick the least solution where `t`
is covariant in the result, the greatest where contravariant, and refuse
when it is invariant and the bounds differ. Here `(arrayof t)` is invariant,
so the argument gives `int ≤ t ≤ int`, the result `t ≤ val`, and `t = int`
solves both. Dolan's biunification (MLsub, POPL 2017; from memory) is the
same flow of bounds, made principal. Both checkers, agreeing; regions and
effects as variables too (an effect has the same lattice shape). First
measure what it costs the front end's check, and collect the places where
the front end writes `the` or `proj` only to steer instantiation, which
this would remove.

**Stage 1 done (2026-10-08): bounds in both checkers.** A type binder keeps
a lower bound (the arguments, joined), an upper one (the expected result,
met) and an exact one (inside a pair, array, reference, i-cell or mark key:
invariant); a binder fixed, or whose bounds have met, tells the arguments
still to be checked what they are, as the expected type did, and one
bounded only from above lets an argument say what it is first (a variable
its type, a call its own result checked against the bound). Polarity flips
in a subroutine's parameters. `infer.rs`, `Bounds`; `check-bounds.fx`.
Tests: `bidirectional/bounds.fx` (42), `unions/bounds-apart.fx` (refused). Four
refused programs changed their messages, in both checkers alike
(`regions/knot-through-two-regions.fx` is refused by its list's element
type now, before the knot rule, since the pair's contents fix it). Cost:
none measured, the same front-end text checked by both checkers in
2.45–2.50 s before and after. Then refined (the user's: a binder is known
only once its bounds narrow to a point): one with a lower bound alone is no
more known than one with an upper bound alone, so an argument whose
parameter mentions either bounds it rather than being told (a variable its
type; a call, checked against the upper bounds where there are some, else
what is known so far, so that it is still told its regions, its own
result).

**Done (2026-10-08), stage 2: the annotations it makes unneeded.** Tried,
one at a time and on both the checker before and the one after, each
`(the T (f …))` whose `T` names no region and each operator `(proj f …)`
naming none, in the front end, the test programs, the benchmark ports and
the research examples. What bounds made unneeded, and was taken out: two,
both in the evaluator, `(the int (array-ref bs …))` (`eval-prims.fx`) and
`((proj eq? val) a b)` (`eval-values.fx`). Already redundant before, and
left as written (perhaps documentation, perhaps not; the user's to
decide): 12 `the`s in the front end (10 in `eager-reader.fx`, one each in
`check-holds.fx` and `eval-prims.fx`), and 17 `the`s and 63 operator
`proj`s in the programs (most in `mllang-bench/fx/mlton/DLXSimulator.fx`,
`(proj ia-nth u32)` and kin). Not removable, as they name a region or a
place (`acyclic`) under an alias, which bounds do not choose: those in
`check-print.fx`, `check-subtype.fx`, `check-terminate.fx` and `native.fx`
(`reverse`'s result region there is fixed by nothing else).

