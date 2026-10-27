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

## 34. Private regions shared by two files: is the licence still sound? (the user's, 2026-10-05)

**Answered (2026-10-16): no longer a question.** `private-regions` is
gone from the language (refused now, "unbound variable"): the front end
moved into module files of their regions (`module-parameters`), and the
reader's licence rests on its type, not on regions no one else can name:
`parametric_licence` checks that each entry point of `make-eager-reader`
and `make-reader` touches only the regions it is given, whichever they
are (`licence.rs`). The front end is checked as a program of its own
(its own checker, `compile_program_as`) and loaded under its own prefix
(`READER_PREFIX`), so a user's program names none of its regions or
globals, and is handed nothing of it; the REPL's speculation of the
user's own expressions licenses only what masking left, effects on fresh
regions. So no file can share a region with the reader's and observe it.
Of the items found moving the front end into modules, below: a module's
type and value of one name are now kept apart (`(define-type x int)
(define x int 1)` in a module checks); `layout.fx` and its kin are module
files the conductor loads. The last of them, a second top-level
`define-type` of a name, taken silently, is below.

**A second `define-type` of a name (found 2026-10-05; done 2026-10-16):
warned of, not refused (the user's).** It miscompiles nothing, and
recompiles nothing: a whole program's name defined twice is not declared
ahead, each type sees the definition before it, and every value the
last, in both checkers and every compiler alike, so a use cannot take
one for the other; the REPL's redefinition keeps the old meaning for
what was checked under it (`f` taking an `int` still does after `t`
becomes `bool`). What it costs is a refusal far away, with a message
naming `t` that means the second. So `fixpt` warns, at the second
definition: `check` a line, both checkers' (`types_defined_again`,
`k-types-again`), and `run` and `eval` on the standard error,
`` warning: `t` is defined as a type more than once; every value sees
the last `` (`dialects.rs`, `a_type_defined_twice_is_warned_of`). The
REPL's rule is unchanged; a module, a form or a file, refuses it as
before.

Found checking that: a module file defining a name twice was refused by
both checkers at different places, neither in the file (the Rust one at
the `load-module`, the FX-26 one at a position in the file taken for one
in the program). Both now say it as the file's other errors, at the
load, `` in `m.fx`, 1:1: … ``, the file being the module, as a `module`
form's is said at the form (`modules/load-defined-twice.fx`).

The question as it was asked:

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

## 62. Literals for `int->u32` and `int->i32` in existing sources (2026-10-11)

Since a5f0979 a literal in range is an `i32` or `u32` where one is
expected. The benchmark ports converted by hand; now `md5.fx` writes 72
of its constants as literals (all), `DLXSimulator.fx` 33 of 35 and
`psdes-random.fx` 4 of 5, each kept only where both checkers still agree,
both compilers still agree, and the program gives the same answer
(`"59ebddd335d8defbcaf5b76c08c64278"`, 477019433, 2419669511); the three
left have no type expected there (a `let`'s value, an `array-set!`'s).
Not "the same code": the cellular words called `%fx26-int->u32` on each
literal at run time, which a literal does not need. Their comments say
so. The tests about the conversion keep it (`fixed-width-ops.fx`,
`fixed-width.fx`, `flat-ints.fx`).

## 63. `i64` and `u64` below `int`, with literals (2026-10-11)

Literals of each fixed width, the 64-bit ones past a fixnum included,
came with kayak's request (2026-10-11, `docs/fx26.md`). Now the
subtyping too: an `i64` or `u64` is the exact integer it stands for, so
it is an `int` wherever one is wanted, as an `i32` or `u32` is (`check.rs`'s
base rule, `k-base-below?`). The worry was native code, which keeps one
raw in a register: `direct/reps.rs` already boxes a raw register where an
instruction wants a value, a bignum past a fixnum, so nothing else
changed; every other machine has it as the integer already. Test:
`programs/native/i64-as-int.fx` (on every machine; natively, with
collections, in `i64_and_u64_raw_in_registers`).

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

## 68. The front end as modules linked by a conductor (the user's, 2026-10-08)

The front end is 57 files joined into one program, each a `(define
X-module (module …))` followed by a wall of top-level re-exports (1,733
names), which later files use as globals. Instead: `conductor.fx` makes
each module once and passes it the modules it depends on; a module names
what it uses of them, at its top, `(define name (with dep name))`.

Decided with the user (2026-10-08):
1. **Types in files of their own.** A module's datatypes, type aliases and
   effects move into `X-types.fx`, a module file of no state (of the
   module's regions, if it has some). The module loads it, and so may any
   client: loads of a stateless file are interchangeable, FX-26's types
   being structural. Only stateful modules are made once and passed.
2. **Signatures beside them.** A module's interface as its clients use it,
   `(define-type X-sig (moduleof …))`, lives in its types file; width
   subtyping (M4) lets it list only what the clients use. Several such
   files, not one.
3. **A converted module** is a module file defining `make`, a `lambda`
   over its dependencies, each typed by a signature; the conductor applies
   it. Converted from the last file backwards, so that each one's clients
   are converted before it, and its wall goes; only the names Rust calls
   stay at top level, re-exported by the conductor.

Phase 1, the types out, one module at a time; phase 2, the conversion.

- Phase 1: `eager-reader-types.fx` (2026-10-08), the reader's effects,
  aliases and `syn`, which `eager-reader.fx` loads at its regions.
- Phase 1: `parser-types.fx` (2026-10-08), the parser's effects, `exp`,
  `top`, `presult`, the trees' lists and the loaded files' types, loading
  the reader's types (not the reader) for `syn`.
- Phase 1: `table-types.fx` (2026-10-08), the tables' type families,
  which the `tables` module loads. It found the FX printer showing a
  family in a nested module's type by its own name, `(desc bucket bucket)`,
  where the Rust one shows its `dlambda`: fixed (`k-show-comp`).
- Phase 1: `check-types-types.fx` (2026-10-08), the checker's 45 core
  types and effects (`k-ty`, `kstate`, `checks` ...), moved by a script
  that takes a module's type items out and imports what they use from the
  types files before it.
- Phase 1: the types of `check-env`, `check-print`, `check-unions`,
  `check-holds`, `check-read`, `check-syntax`, `check-subst`,
  `check-generative` and `check-resolve` (2026-10-08), each in
  `X-types.fx` (`check-effects`, `check-proving` and `check-read-descs`
  have none). `check-read-types.fx`, which read descriptions, is renamed
  `check-read-descs.fx`, so every types file is `X-types.fx`.
- For phase 2 (2026-10-08): in a module, `(define x (with m x))` of a
  module `m` in scope but not one of its items (a `lambda`'s parameter,
  what a converted file is given) was refused as `x` using itself: the
  order check knew a `with`'s names only for early items. Now a module
  in scope binds its values' names there too, in both checkers
  (`hazard_items`; `k-outer-mods`). Test: `modules/linked.fx`, a module
  made of one it is given, typed by a signature from a file of them.
- Phase 2, the pilot (2026-10-08): the evaluator. `eval-types.fx` holds
  its types and the signatures of its own two modules as the others use
  them; `eval-values.fx`, `eval-prims.fx` and `eval-core.fx` are module
  files, each `make` over what it uses, typed by signatures beside the
  types of the modules given (`check-types-sig`, `tables-sig`,
  `check-env-sig`, `check-resolve-sig`); `conductor.fx`, last of the front
  end, makes them in order, passing the top-level modules of the files
  not converted yet, and names `run-checked` and `run-program` for Rust.
  What it found:
  - `evals` now says `spin`: what the evaluator is given is a module of
    procedures over `val`, which a procedure may be given itself in, so a
    call of an imported one is not known to end (`may_spin`, a recursive
    type through a parameter). Honest for an evaluator; the checker's own
    types have no procedures in them, so its modules will not feel it.
  - A `proj` given an effect re-exported by `select`, `(proj f evals)`,
    did not resolve it, in either checker: fixed (`check.rs`, `Proj`;
    `check-expect.fx`, `k-select-fun`).
  - A constructor imported from a types file, `(with eval-types o-unit)`,
    is not known code, so a call of one may `spin` where its own module's
    would not. Later, perhaps: an import of a known procedure from a
    module as written is known.
- Cost (2026-10-08, `fixpt bench --front-end`, fx M words, the
  deterministic measure; times swing with the machine's load): 215 before
  §68, 257 after the types files, 322 after the evaluator. Most of it
  printing: the FX checker shows each top-level form's type, building the
  string by appending (about 40 words a character), and module types had
  grown, holding their types modules as values and the evaluator's
  intermediate modules being bound at top level (2.1 MB shown). Now each
  types file is loaded just before its module, not inside it, and the
  conductor makes its modules in one `let*`, naming only what Rust calls:
  1.3 MB shown, 297 M words. Left: every load of a types file is checked
  again, and compiled again (`check-types-types.fx` 12 times, nesting the
  parser's and the reader's): next, one check and one compiled body per
  stateless file, shared by its loads.
- Decided with the user (2026-10-08), and done: **`load-input`** and
  **shared loads**. `(load-input "f")` is a file of one expression, its
  value (Sheldon's `input`); `load-module` stays. Every load of a path is
  one value, made once: the first defines a hidden global, `%shared:` and
  the path from the program's directory (`input:` before it for a
  `load-input`), before the form that loads it, and each load is that
  global, which loaded files may see (`parse_load`; `parse-loaded`,
  `parse-tops`). So making it must be pure, but for reading globals:
  state is made by applying a `lambda` the file gives. Supersedes "two
  loads, two modules" (b98e670) for values; abstract types are still
  named by their variable. The driver reads each path once
  (`supply_loaded_in`). The evaluator's three files are now `load-input`
  files, a `let*` of the types files they use around the `lambda` that
  makes the module, and `make` is gone. Cost: 241 M words (from 297).
- Where the rest went (2026-10-08, measured back to back against the
  commit before §68): with the FX checker's lines off, 168.3 M words
  then and 170.5 now, the check 985 ms then and 1035 now. The whole
  regression was printing: 47 M words before §68, 71 M after, as module
  types and the hidden `%shared:` definitions (0.72 MB of the 1.9 MB
  shown) are large. No compile reads the lines, so only a driver that
  does makes them (`check-lines!`; `fixpt check`, the REPL, the agreement
  tests): compiling the front end is 170.5 M words, the FX check about
  1.0 s, from 215.7 and 1.15 s before §68.
- The printer, for the drivers that read lines (the user's, 2026-10-08:
  "build text at most once"): `k-show-ty` puts a type's pieces on a list
  and joins them once (`k-pieces-string`), where each node appended its
  children's text again; a cycle's `(mu %d …)` is known from the depths
  met again below, not by searching the text shown (`k-mentions-token?`,
  gone); and the tree of the scope's `define-type` names is kept across
  lines while the scope and what its types resolve to stay
  (`k-atree-now`; `k-links` counts the links made from the types a kept
  tree may hold), where it was made again for each line. With lines on
  (`FIXPT_BENCH_LINES=1 fixpt bench --front-end`): 237.6 M words to 189.1
  and the FX check 1265 ms to 1120; printing costs 18.6 M words, from 67.
- The hidden definitions of loaded files (`%shared:…`) have no line in
  either checker (2026-10-09): the program does not name them, and their
  types are as large as the modules they hold. A definition that loads
  one still says, in its effect, that it reads it. `fixpt check` on the
  front end shows 1.17 MB, from 1.9; with lines on, 182.5 M words and
  the FX check 1070 ms.
- Phase 2, the back end (the user's order, 2026-10-09: the native
  assembler and what it uses; then register code; then the compiler,
  `standard.fx` and `layout.fx`; then the checker, backwards; a commit a
  file). `native.fx` (2026-10-09): a `load-input` file whose module has
  state (the assembler's arrays), made by the conductor of `arm64-module`,
  `layout-module` and `native-layout-module`, each typed by a signature of
  the names it uses (`arm64-sig`, `layout-sig`, `native-layout-sig`, made
  from their printed types); its own types in `native-types.fx`, with
  `native-sig`. The two layouts are generated, so their signatures are in
  files beside them, written by hand. 171.8 M words, from 171.0.
- `native-layout.fx` (2026-10-09): no state and nothing given, so a plain
  module file, its items only, which the conductor loads; its generator
  (`fixpt_native::cellular::fx26_module`) writes it so, not wrapped in a
  module re-exported.
- `arm64.fx` (2026-10-09): no state and nothing given, but types of its
  own, so a `load-input` file whose value is the module, its types file
  loaded around it, `(let ((arm64-types …)) (module …))`; the conductor
  loads it for `native.fx`. `tests/arm64.rs`, which called the encoders as
  the front end's globals, compiles a program loading the file and naming
  them. It found the compilers disagreeing on a load passed where a
  narrower module is expected, the FX-26 compiler finding what a place is
  narrowed to by the place, shared by a load's hidden definition and its
  use: each now has a place of its own (`0c08e72`).
- Phase 1 for register code and the compiler (2026-10-09): the types of
  `compile`, `compile-lift`, `compile-exps`, `compile-plan`, `regcode`,
  `regcode-exps`, `regcode-helpers`, `regcode-modules`, `regcode-entry` and
  `compile-programs`, each in `X-types.fx`, loaded before its module
  (`compile-twins`, `regcode-core`, `layout` and `standard` have none).
  172.7 M words, from 171.1.
- `compile-programs.fx` (2026-10-09), after its inlining was split out as
  `compile-inline.fx` (by extraction, to stay under 1000 lines with its
  imports): a `load-input` file whose module has state, given eleven
  modules, each typed by a signature of the names it uses, kept in the
  module's types file and grown as clients convert (`mksig.py`): types,
  effects and constructors come from the types files, values from the
  modules; a name both a type and a value is imported as both. The
  conductor names its six entry points for Rust and `bootstrap.fx`.
  173.4 M words, from 172.7.
- Converted since, a commit each, as above (the tools: `to_input3.py`,
  `mksig.py`, `lib_move.py`, `conductor_add.py`, `conductor_export.py` in
  the session's scratch space): `compile-inline.fx`, `compile-twins.fx`,
  `regcode-entry.fx`, `regcode-core.fx` (its size debt raised by its
  imports alone, 1125 to 1415 lines: the user's, 2026-10-09),
  `regcode-modules.fx`, `regcode-helpers.fx`, `regcode-places.fx` (split
  from `regcode-exps.fx` to stay under 1000 lines), `regcode-exps.fx`,
  `regcode.fx` (two definitions of `compile-lift.fx` outside its module
  moved into it first), `compile-plan.fx`, `compile-exps.fx` (its state
  split out first as `compile-state.fx`, to stay under 1000 lines),
  `compile-state.fx`, `compile-lift.fx`, `compile.fx`, `standard.fx`
  (generated: a plain module file the conductor loads), `layout.fx` (the
  same). That ends the back end.
- Phase 1 for the rest of the checker (2026-10-09): the types of
  `check-modules`, `check-subtype`, `check-calls`, `check-dependent`,
  `check-bounds`, `check-infer`, `check-terminate`, `check-test-facts`,
  `check-letrec`, `check-synth`, `check-modorder`, `check-module-rules` and
  `check-program` in `X-types.fx` files, and the printer's two newest in
  `check-print-types.fx`. Then the checker's files, from the last
  backwards; `check-rules.fx`, the checker's one recursive group, gets a
  size debt entry for its imports alone, as `regcode-core.fx` (the user's,
  2026-10-09).
- Checker converted (a commit each): `check-program.fx` (its proofs
  split out first as `check-proofs.fx`; the parser's procedures it uses,
  which `reader.fx` names at top level, from `parser-module`, typed by
  `parser-sig` in `reader-types.fx`), `check-proofs.fx`,
  `check-rules.fx` (its size debt: 1346 lines, its imports),
  `check-module-rules.fx`, `check-modorder.fx`, `check-synth.fx`,
  `check-facts.fx`, `check-letrec.fx`, `check-test-facts.fx`,
  `check-terminate.fx`, `check-sc-graphs.fx`, `check-close.fx`,
  `check-infer.fx`, `check-binders.fx`, `check-bounds.fx`,
  `check-data.fx`, `check-dependent.fx`, `check-calls.fx`,
  `check-expect.fx`, `check-subtype.fx`, `check-sub-env.fx`,
  `check-modules.fx`, `check-modules-read.fx`, `check-errors.fx`,
  `check-kinds.fx`, `check-mask.fx`, `check-resolve.fx`,
  `check-generative.fx`, `check-read-descs.fx`, `check-read-helpers.fx`,
  `check-proving.fx`, `check-subst.fx`, `check-syntax.fx`,
  `check-read.fx`, `check-holds.fx`, `check-unions.fx`,
  `check-print.fx`, `check-print-parts.fx`, `check-env.fx`,
  `check-effects.fx`, `check-types.fx`.
- The FX checker's cost of converted files (2026-10-09): checking the
  front end had grown from about 1.0 s to 1.46 s over phase 2. Profiled
  (`probe_profile_check`, 4.8 G cells to 7.2 G), three walks along lists
  that converted files make long: a name's lookup inside a loaded file
  walked the bindings made since it began (`k-bound-since`, now each
  binding's depth kept, `k-depths`); a `with`'s names were found along a
  list of every `with` (now by where it starts too, `k-with-index`); and a
  subtype question looked along its trail of every pair compared (now
  counted by pair, `k-strail-count`, the trail looked along only where a
  pair is counted). 1.46 s to 1.20 s. Left: `k-has-id?` (9%), and the
  Rust checker, whose time grew too (630 to 800 ms).
- Phase 2 finished (2026-10-09): the checker, the tables and the reader.
  `table.fx` is a module file of no state the conductor loads;
  `reader.fx` stays at top level, as Rust finds the reader's entry points,
  `make-reader` and the parser's results' constructors there by name, but
  names only what Rust, `bootstrap.fx` and the conductor use (84
  re-exports gone). The front end joined is `reader.fx` and
  `conductor.fx`; every other file is built in, loaded by the conductor or
  by the files it makes. Splits on the way, by extraction, to stay under
  1000 lines with the imports: `check-sub-env.fx`, `check-modules-read.fx`,
  `check-read-helpers.fx` (the 43 leaves of `check-read-descs.fx`'s knot,
  moved to its front first) and `check-print-parts.fx`; `check-rules.fx`'s
  debt 1358 lines, its imports alone. Found on the way: a load cycle hangs
  the Rust checker (`TODO.md` §71). Compiling the front end: 207.6 M
  words, from 171.0 at the start of phase 2; what that costs, and what
  §69 and §70 win back, is the profiling pass left in `TODO.md` §68.

## 69. `(extend e0 e1)`, FX-91's (the user's, 2026-10-09)

FX-91 combines modules with `(extend e0 e1)` (report §2.3.5, p. 15): a
module of the values and types of both, `e1`'s where both have a name;
here `e0`'s in its order, then `e1`'s others. Both parsers make it a
module of two hidden items, `%extend-0` and `%extend-1`, the two modules;
both checkers (`Checker::extended`, `k-extended`) give it the type of the
one and note it made of their values by path, value `j` of the module
that is value `k` (`reshape_path`, `k-reshape-path`: a reshape's position
from 2^40 on). A module given where fewer values are wanted was already
made into one of that type (a reshape), so every compiler and the
evaluator had the rest: each follows a path where it took a position
(`cellular.rs`, `regcode.rs`, `lower.rs`; `compile-state.fx`,
`regcode-modules.fx`, `eval-core.fx`). An `extend` itself given where
fewer values are wanted is made so at once, the two reshapes composed.
A module whose type has abstract types is not extended, yet (any such,
a global bound to one included): what the two's abstract types become in
the one is to decide. `extend` is a keyword now, as `module` is; the
evaluator's procedure of that name is `bind1`. Tests:
`modules/extend.fx`, `extend-not-module.fx`, `extend-abstract.fx`.

`(include m)` (2026-10-09), an item: `m`'s values and types the module's
own, one bucket with its definitions and other `include`s, a name given
twice refused, never shadowed. Both parsers (`with_includes`,
`with-includes`) make a module's `include`s one hidden item first,
`%include`, a module of hidden items `%include-0`, … (the modules
included, made before the module's items and seeing none of them), and
put each own item's value in `(with %include …)`, a lambda's body so that
it stays a lambda, its place the item's (the compilers find facts by
place). Both checkers (`Checker::included`, `k-included`) give the bucket
the type of the one, and the module the type of its own values and the
bucket's, each made by path as `extend`'s are: nothing new in a compiler
or the evaluator. Not yet: an `include`'s types in scope inside the
module, and a module whose type has abstract types. `include` is a module
item's keyword now. Tests: `modules/include.fx`, `include-twice.fx`,
`include-own-twice.fx`, `include-not-module.fx`, `include-abstract.fx`.

`(hide item …)` (2026-10-09), an item: items the module's own see but not
in its type, so helpers do not crowd its signature; `(hide (include m))`
uses a module without giving its values on. Both parsers read a `hide`'s
items as the module's own (its `define-datatype`s expanded), and mark each
name one defines by a type of its own, `%hidden:name` (a type, so that no
compiler or the evaluator makes a value of it); a hidden `include` is
`%hinclude-k` in the bucket, whose names the checker marks. Both checkers
(`Checker::hiding`, `k-hiding`) leave the names marked, and the marks, out
of the module's type, and make the module of the values left by position:
the ascription done for you, a reshape. A hidden abstract type in a type
shown is refused, for now (the user's, 2026-10-09: the safe,
forward-compatible choice while the feature is tried), as `` `v`'s type
mentions `t`, which is hidden in this module ``; a hidden `define-type` is
in what it abbreviates already. Tests: `modules/hide.fx` (a datatype, a
`define-rec` and an `include` hidden), `hide-include.fx`, `hide-unseen.fx`,
`hide-escape.fx`.

`extend`'s `e1` sees `e0`'s values (2026-10-10), as FX-91 §2.3.5 says
("The expression e1 has access to the bindings of e0"): the hidden
`%extend-1` is `(with %extend-0 e1)`, so `e0` is made once and `e1`'s own
shadow its names inside `e1`; `e0`'s values keep their own, an `e1` name
of theirs taking their place only outside. The `with` is at no
expression's place (the `extend`'s start, of no width), since the FX-26
checker keeps facts by place; an `e0` not a module is still said of
`extend`. Types and effects of `e0` in `e1`: `TODO.md` §69. Test:
`modules/extend-sees.fx`.

Abstract types in `include` and `extend` by name (2026-10-10): a module
bound to a name `m` has its abstract types as `m..t`, the variables its
binding made (`name_module`); `included` and `extended` (`k-inc-module`,
`k-extend-side`) give each as a description of that variable, an alias,
not an abstract type of the result's own. So the values of `(include m)`
and of `m` are one another's both ways, and an `extend` whose `e1` has a
`t` of its own captures none of `e0`'s values' types (FX-91's rule does:
`docs/research/sheldon-combining-modules.md` §5). The module cannot leave
`m`'s scope, as `m..t` cannot. A hidden item (`%extend-0`, …) keeps the
names its module has, so `extend`'s `(with %extend-0 e1)` sees `m..t`. A
module not bound to a name: `` `include` takes a module with abstract types
by its name ``, likewise `extend`. Tests: `modules/include-abstract-alias.fx`,
`include-abstract-escape.fx`, `include-abstract.fx`,
`extend-abstract-alias.fx`, `extend-abstract.fx`.

Then a module with abstract types that is not a name (2026-10-10): its
abstract types the new module's own, each a fresh variable
(`abs_taken`, `k-abs-own`), one substitution over every side and the
module's own items; the values by path as before. Not the splicing of
literal text the TODO suggested: at the type level an existential
unpacked and packed again, which covers a `(module …)`, a `(load-module
"f")` and a call alike and changes nothing at run time. In `extend`,
`e1`'s names replace `e0`'s, abstract ones too; one replaced that a kept
value or type mentions is refused. In `include`, a name given twice,
abstract or not, is refused (the Rust checker had missed a description
of the module's own against an included abstract type), and `(hide
(include …))` hides the abstract types as well. Choices:
`CLAUDES_CHOICES.md`. Tests: `modules/include-abstract.fx`,
`include-abstract-made.fx`, `include-abstract-opaque.fx`,
`include-abstract-apart.fx`, `include-abstract-twice.fx`,
`include-abstract-hidden.fx`, `include-abstract-hidden-ok.fx`,
`extend-abstract.fx`, `extend-abstract-replaced.fx`.

`with` shadows (2026-10-10; the user's: "`with` should absolutely shadow
bindings"), as FX-91 §2.3.19's: in `(with m …)`, a type or effect name
`m` gives is `m`'s, whatever it is outside, so `extend`'s `e1`, `(with
%extend-0 e1)`, sees `e0`'s types and effects too. The names are read
before `m`'s type is known, in both checkers: a `with` body's start is a
mark in the description scope (`DScope::With`, `%with:m`), and a name read
past one, bound before it, is `(select m n)` with what it was outside to
fall back to (`with_selected`, `k-with-selected`; an effect name, a
variable of its own, `with_effect_selected`), settled where `select`s are
resolved (`resolve_selects`, `effect_selected`; `k-select-component`,
`k-effect-selected`). Neither: `` `n` is not a type, nor one a module
opened by `with` gives ``. A count of `with` bodies being read keeps names
outside any from looking. Tests: `modules/with-shadows.fx`,
`with-falls-back.fx`, `with-type-missing.fx`, `with-effect-missing.fx`,
`extend-sees-types.fx`.

Then a description function applied, `(f d …)` in a `with` body
(2026-10-10): `((select m f) d …)`, its descriptions read by their shape,
and where `m` does not give `f`, the *application* linked to what `(f d
…)` is outside (`with_applied`, `k-with-applied`; `with_applied` in the
arena, `k-with-apps`), not the `select`, so that `(f int)` and `(f bool)`
in one type each fall back to their own. Type forms are not shadowed.
Choices: `CLAUDES_CHOICES.md`. Tests: `modules/with-shadows-applied.fx`,
`with-applied-missing.fx`.

An `include`'s types inside the module (2026-10-11): they were in scope
already, by `with` shadowing, in an item's declared type and in a
`define-type`; but an item's value, `(with %include e)`, was synthesized,
not checked against the type the item declares, so `(define p (pairof
int int @heap) (cons …))` made its pair at a fresh region and was
refused. A `with` checked against a type now checks its body against it
(`Checker::with_as`; `k-synth-with` given `expected`, its binding in
`k-in-scope-parts`), an error at the body said of the `with` so that a
call's argument's is still "argument 1 is a …" (`k-respanning`). Test:
`modules/include-types-inside.fx`.

The import pass (2026-10-11): the front end's import blocks, `(define x
(with m x))` and `(define-type t (select m t))` for each name a file uses
of a module it is given or a types file it loads, 5,684 lines, became
`(hide (include m) …)`: 637 lines left (check-rules.fx 1,331 to 1,069,
regcode-core.fx 1,403 to 1,130; their size debts lowered). Made possible
by `include` taking a type name twice where it is the same type, and the
types files hiding their module bindings. It found three bugs, fixed: a
frame of more than 511 slots in register code (`add_const`); a file of
`module-parameters` whose `plambda`, `lambda` and module shared one place,
so the FX-26 compiler reshaped the closure (a SIGSEGV running the front
end); and `hide` marking a type and a value of one name alike, so hiding
one hid both (`%hidden:` for types, `%hiddenv:` for values now). Test:
`modules/hide-type-not-value.fx`.


**The bucket made in linear time** (2026-10-11). Measured side by side
with the commit before the pass, checking the front end had become
slower, `check` 575 → 762 ms and `fx check` 1295 → 2127: an `include`'s
bucket was made by looking each name up in a list of those so far (every
value of every hidden include, thousands), and a type given twice was
compared both ways before seeing it was the same type. Now a table of
the names so far in both checkers (`Checker::included`; `k-included`,
`k-saw`), the same type first by identity, and no substitution where
there is nothing to substitute: `check` 555 ms, `fx check` 1475, the fx
phases' allocation 274.9 → 228.7 M words. `hide`'s marks looked up in sets too
(`Checker::hiding`; `k-shown?` by a table), not lists of thousands.

**An included type family applied in a declared type** (2026-10-11):
`(box int @heap)` in a module with `include`s, `box` bound nowhere, is
`((select %include box) int @heap)`, found when the modules included
are typed, as a type's name already was; in both checkers (`parse.rs`'s
type-list fallback, `check-read-descs.fx`'s `k-parse-type-form`). Tests:
`modules/include-family.fx`, `include-family-missing.fx`.
**An include's names bound once, at the module** (2026-10-16, `TODO.md`
§69's cost). Each item's value was `(with %include …)` inside its lambda
(`with_includes`), so every call loaded each included name it uses from
`%include` into a slot (or, in a leaf, a register). Now the module binds
the names its items' `with`s use once, after `%include` is made, and those
`with`s bind nothing, so each lambda captures the names it uses, as the
import lines' were (`Compiler::included_names`, `note_included`; the
FX-26 compiler's `c-note-included!`, `c-included?`): in the cellular
code, the register code and the plan, of both compilers, which make the
same words. From outside an item (`%include` bound there) such a `with`
still reads as one that binds its names, so a walk for free names needs
no list of them. Measured side by side, best of 3, three
rounds alternated, load averages about 2: peval's `fx check` 20.5 →
19.8 ms, `fx words` 12.9 → 12.1; the front end checking itself, on the
same input (the old Rust compiler with the new FX-26 files), `fx check`
2580 → 2510, `fx words` 725 → 709. The FX-26 compiler has more to do in
such modules: each name a lambda captures is looked up in its
environment, a list, past the module's items; so against the old files
too, the front end's `fx words` 702 → 706 (and `fx check` 2550 → 2500).
Found with it: `DONE.md` §104. Test: `modules/include-bound-once.fx`.
**A parameter shadows an included name** (2026-10-16, found with the
last). `(define f T (lambda (x) (+ x y)))`, in a module including one
with a value `x`, added the included `x`, not its argument: the item's
`(with %include …)` is inside its lambda (`with_includes`, so that the
item stays a lambda), where it bound over the parameter, in both
checkers, so on every machine; a parameter of another type was refused.
An included value is the module's, as its own items are (a name both
give is an error), so the parameter wins: a `with` of `%include` binds
none of the names bound since `%include` was (`Checker::with_as`,
`k-include-free`), so its facts leave them out and every compiler binds
the parameter. The compilers no longer leave such an item's `with` alone
(`included_names`, `c-include-with`). Tests:
`modules/include-bound-once.fx` (1366, not 367),
`include-param-shadows.fx`.

## 71. A load cycle is an error, not a hang (2026-10-10)

Found 2026-10-09 (`TODO.md` §68 phase 2): two types files loading each
other through a third made the Rust checker's `parse_load` recurse without
end, past 300 s with nothing said; the FX-26 parser did the same (a stack
overflow). Each parser now keeps the files being read, each with its path
as its load wrote it (`Checker::loading`, `loading-keys`), and refuses a
load of one of them before reading anything, naming the chain: `` a load
cycle: `a.fx` loads `b.fx` loads `a.fx` ``. In Rust the check comes before
`sharing_now`, through which a shared load's own definition reads its
file; it had let a cycle through as well. A file read once and loaded under
two paths is named, in an error inside it, by the path the load being read
wrote (`in-loaded-as`), as Rust names it. And a check in the suite, before
any checker runs, that the module files built in load no cycle, from their
text (`tests/parser.rs`, `the_built_in_files_load_no_cycle`; shown to
catch the cycle of 2026-10-09 when it is put back). Test:
`modules/load-cycle.fx`, a file that loads itself. Two files deep, the
checkers place errors differently, a cycle or not: `TODO.md` §73.

## 72. Say which name a module item captures (2026-10-09)

A module's items scope over all of it (`letrec*`), so an item can capture
a name the module's own code means from outside it, as the conductor's
entry `check-program` captured the module of that name. Both checkers
refused it rightly but said `` `lines` uses `lines`, before it is made ``:
what `(with checker lines)` reaches through the captured name. Now, where
an item's value names, itself, a later item of the module that is bound
outside it too (and is not a module checked first, the module's own as
bound), they say so (`captured` and `capture_said`, `k-captured` and
`k-capture-said`): `` `checker` here is the module's own item, made after
`lines`, not the `checker` bound outside it `` (`this one`, where the item
captures its own name). And where an `include`'s module uses one of the
module's items, the hidden `%include` is not named: `` an `include` uses
`k`, which the module defines: an included module is made before its
items ``. Tests: `modules/capture.fx`, `capture-self.fx`,
`include-uses-own.fx`.

An `include`'s types in scope inside the module (2026-10-09): in a module
with `include`s, a type name nothing else defines is the modules
included's, `(select %include t)`, found when they are typed; the hidden
`%include` is an early item, checked before the module's typed lambdas,
so the select is resolved where a written one would be. The Rust parser
counts the modules being read that have `include`s (`include_scope`); the
FX-26 checker, which reads a module's types as it resolves it, marks such
a module's description scope (`k-include-mark`, `%include-scope`), gone
with it, and `k-type-unknown` reads the mark. A name the modules included
do not give either: `` `t` is not a type, nor one a module included gives
`` (not `%include`, in both checkers' `select` errors). Hidden or not
(`(hide (include m))`), the same; a type shown says what a hidden one
abbreviates. Tests: `modules/include-types.fx`, `hide-include-types.fx`,
`include-type-missing.fx`.

An `include`'s effects in scope inside the module (2026-10-09): an effect
name nothing else defines, in a module with `include`s, is the modules
included's, `(select %include e)`, as for types: the Rust parser's
`parse_effect` on `include_scope`, the FX-26 checker's `k-effect-unknown`
on the `%include-scope` mark. Not given either: `` `e` is not an effect,
nor one a module included gives ``. Tests: `modules/include-effects.fx`,
`include-effect-missing.fx`.

## 73. An error two loads deep, placed alike by both checkers (2026-10-11)

Found making a load cycle an error (§71): where a file loaded by a file
loaded by the program was wrong, the checkers said the same thing but
placed it differently, and neither well: a type error in `deep-b.fx`
(loaded by `deep-a.fx`, loaded by `deep.fx`) was `deep.fx:1:1: in
`deep-b.fx`, 1:15: …` from Rust and `deep.fx:4:1: …` from FX-26 (a line
`deep.fx` does not have); a file not there, two loads deep, `deep.fx:4:1:
cannot read …` from FX-26. A load is made once, at the program's top, so
the file between was not being checked when the error came, and its
place was a position in another file.

Now both say each file on the way, at the program's load: `deep.fx:2:11:
in `deep-a.fx`, 1:11: in `deep-b.fx`, 1:15: …`. Rust keeps each file's
first load site (`Checker::load_sites`) and `in_loaded` walks out from
the error's file; FX-26's `loaded-placed` (`parser.fx`) walks a position
out through the files read, each at its first load (`loaded-first`: a
file loaded again, by a cycle or another file, is placed where it was
first read, in a file read before it, so the walk ends). Both place it at
the load's start (FX-26's parser keeps no more of it). Tests:
`modules/load-deep.fx`, `load-deep-missing.fx`, `load-cycle-two.fx`
(two files loading each other: the first try of this looped there).

## 77. Suffix refs: interior pointers into bloblet suffixes, tag `010` (the user's, 2026-10-10)

The runtime (`docs/object-model.md`, invariant 5 and "Tags, before and
after"). A suffix ref is tag `010`, its owner in bits 3..37 and a byte
offset in bits 37..64; the owner is the word index of the suffix's start
counted from where the heap's memory starts (`Heap::ix`), not the address
a tag-`100` word holds, which is ~44 bits wide: so it fits 34 bits (a
compile-time assertion, `MEM_WORDS < 2^34`) and needs no relocation in an
image. Made checked (`Heap::suffix_ref`: an offset in the suffix, a
suffix below 2^27 bytes, else `NoSuchByte`/`SuffixTooLarge`), projected
(`suffix_ref_add`), read and written by width (`suffix_ref_read`,
`suffix_ref_write`, which refuses a frozen suffix and marks no card).
`is_ref` includes it; the collector forwards the owner as a bloblet pointer
and rebuilds the ref (`copy_out`), so roots, the Cheney scan, minor
collections and the card scan, arenas, reaps and the code area need no
more; the barrier and the remembered-set check test the owner
(`ref_ix`); weak references follow or die with the owner; images rebase
the owner as an index; `copy_graph_from` copies the owner once; `sro`
counts the owner; the verifier checks a live owner whose suffix covers the
offset. Runtime primitives: `%suffix-ref`, `%suffix-ref?`, `%suffix-ref+`,
`%suffix-ref-owner`, `%suffix-ref-offset`, `%suffix-ref-u8`/`-u32`/`-u64`/
`-f64` and each `-set!` (writes only into a program's own bloblets and flat
arrays); printed `#<suffix-ref KIND +OFFSET>`. Compiled code's write
barrier marks a card whatever is stored, so it needed nothing; compiled
code does not dereference one yet. Tests: `fixpt-heap`'s
`tests/suffix_refs.rs` (edges, frozen writes, minor and major collections
with refs in roots, old fields and the nursery, owners' fields kept, arenas
and reaps, weak references, images, graph copies, the verifier), `value.rs`'s
`suffix_refs_encode_their_edges`, `fixpt-scheme`'s
`suffix_refs_read_their_bytes_after_the_churn` and `suffix_refs_cross_an_image`
(also under `gc-stress` with `FIXPT_VERIFY_BARRIER=1`). Docs:
`docs/object-model.md`, `value.rs`'s header, `docs/research/floats.md` Q7.

Bloblet types by width (2026-10-10, the user's plan): `(bloblet (fields T
…) R)` lists at least a bloblet's fields, so one of more fields fits one
of fewer (fields count from the suffix, so each keeps its offset;
compiled code uses no static field count, checked in both back ends), in
both checkers, and inference matches the fields a pattern lists. A field
is forgotten only if no analysis of the wider type needed it
(`Checker::forgettable`, `k-forgettable?`): of a frozen bloblet, data at
its place; of one not frozen, it mentions no region but `R` (and frozen
heap data), stores only in `R`, and holds no procedure nor a type
variable that could be one; so escape, masking, storage, data and knots
all read what a type lists. The FX-26 data walk moved from `check-data.fx`
to `check-sub-env.fx`, which the subtype test is given. Tests:
`bloblet/width.fx`, `width-infer.fx`, and refused, `width-escape.fx`,
`width-frozen-data.fx`, `width-procedure.fx`, `width-variable.fx`,
`width-exact-region.fx`, checked by `tests/bloblets.rs`. Docs:
`docs/fx26.md` (Bloblets).

The kind `flat` and `(blobref B F)`, as types (2026-10-10): `flat` a kind
beside `data`, its descriptions the scalars `f64` `f32` `i32` `u32` `i64`
`u64` or a variable of the kind, not a subkind of `type` (`` `f` is a flat,
not a type ``, also through a family's flat parameter); `(blobref (b type
+) (f flat)) b`, standard generative type 5 in both checkers' one text,
so the safety analyses see a blobref as its owner. FX-26: kind 7, kept in
`k-flats`; `k-parse-flat`, `k-is-flat?` in `check-read-helpers.fx`, with
`k-try-kind` and its kin moved there. Tests: `bloblet/flat-kind.fx`, and
refused, `flat-not-type.fx`, `flat-family-not-type.fx`,
`blobref-not-flat.fx`, `flat-proj.fx`. Docs: `docs/fx26.md` (Bloblets).

The `blobref` operations (2026-10-10): `(blobref-at b off)` and `(blobref+
r d)`, their flat the type checked against's; `(blobref-owner r)`,
`(blobref-offset r)`, pure; `(blobref-get r)`, `(blobref-set! r v)`, of a
scalar, reading or writing the owner's region. Syntax as the bloblet forms
are, in both checkers (`synth_blobref`; `k-blobref-arg`,
`k-blobref-result`), the lowering, both compilers and both register-code
generators; each read or write's layout told the compilers as a fact at
its span; runtime `%fx26-suffix-ref-get` and `-set!`. The evaluator
written in FX-26 refuses them for now. To keep the size debts,
`k-bloblet-op` moved to `check-synth.fx` and `r-bloblet` to
`regcode-helpers.fx`, given the knots' procedures. Tests: `bloblet/
blobref.fx` (every scalar), `blobref-sees-bytes.fx`, `blobref-width.fx`,
and refused, `blobref-unknown-flat.fx`, `blobref-not-scalar.fx`,
`blobref-wrong-value.fx`, `blobref-escape.fx`. Docs: `docs/fx26.md`.

Flat products and arrays (2026-10-10): `(productof (label F) …)` and
`(arrayof F n)` (standard generative type 6, `flat-arrayof`, `n` a
literal) where a flat is wanted, an `arrayof` of literal length a flat
array in a type too; laid out as C does. `(extract r l)` of a blobref to a
flat product, a blobref to the field (its offset a fact past
`BLOBREF_FIELD`); `(blobref-index r i)`, one to an element, its range
checked at run time (`%fx26-suffix-ref-index`). Nothing larger than a word
is copied (the user's rule). Both checkers, the lowering, both compilers,
both register-code generators. Tests: `bloblet/flat-product.fx`,
`flat-no-field.fx`, `flat-index-not-array.fx`, `flat-length-literal.fx`,
`flat-product-of-type.fx`, `flat-no-copy.fx`, `bloblet-errors/
flat-index-range.fx`.

Blobrefs in the evaluator written in FX-26 (2026-10-10): a value form
`o-bref`, owner and offset over the evaluator's bloblets of byte arrays;
every blobref form, `extract` of one included, reading the layouts and
offsets the checker found (its facts copied in at `ev-begin!`). New
standard primitives `f64->bits`, `bits->f64`, `f32->bits`, `bits->f32`, in
both lowerings, the runtime and the evaluator. The evaluator's test runs
`bloblet/` too, every program agreeing with the lowering.

Blobrefs in native code (2026-10-10): `direct.rs` reads, writes, steps and
takes the owner and offset of a blobref in line (`suffix_owner`,
`suffix_get`, `suffix_set`): `ubfx` the owner, `lsr #37` the offset, the
owner's header through its trailer for the bounds, its kind and its
suffix's frozen bit; what it does not do is the primitive's. Those
primitives never collect, in both register-code generators' lists. Test:
`direct.rs`'s `blobrefs_as_the_rust_machine_gives_them`
(`programs/native/blobrefs.fx`, with collections too). A fill-and-sum of
10 million `f64`s: 1.09 s, against 0.92 s for a flat array.

Flat sums (2026-10-10): `(sumof (label F) …)` where a flat is wanted, a
tag then the widest variant at its alignment. With no key the tag is a
byte indexing the owner's fields, which hold the labels (the user's
choice, for sums to interoperate); with a key, `(sumof u8|u16|u32 …)`
(standard generative type 7, `flat-keyed`), numeric labels stored as they
are (the user's: Rust's model, for "flat world" benchmarks); a label may
be 0 now, everywhere. `(blobref-variant! r 'l)` writes the tag (the first
of the owner's fields holding `l`) and gives a blobref to the variant;
`tagcase` on a blobref to a flat sum reads the tag once
(`%fx26-flat-tag`) and gives each arm a blobref to its variant, failing at
run time where no arm has the tag (`%fx26-flat-no-arm`). The layout's code
told the compilers as the `tagcase`'s or `blobref-variant!`'s fact, `w + 8
* numeric + 256 * p`. Both checkers, the lowering, both compilers, both
register-code generators (call-outs, so not in a leaf), the evaluator
written in FX-26; native code calls out. `check-rules.fx`'s debt lowered
to 1331 (`k-in-scope-check` moved to `check-read-helpers.fx`). Tests:
`bloblet/flat-sum.fx`, `flat-sum-key.fx`, `flat-sum-label.fx`,
`flat-sum-name-label.fx`, `flat-variant-literal.fx`, `flat-variant-none.fx`,
`flat-variant-not-sum.fx`, `flat-tagcase-apart.fx`, `flat-tagcase-cover.fx`,
`flat-tagcase-no-tag.fx`, `bloblet-errors/flat-variant-no-field.fx`,
`flat-tagcase-no-arm.fx`, `flat-tagcase-no-field.fx`; natively,
`direct.rs`'s `flat_sums_as_the_rust_machine_gives_them`
(`programs/native/flat-sums.fx`, with collections too).

**In line natively** (2026-10-11). A primitive that never collects, on a
value and a constant, is register code's `prim2imm` rather than a
call-out, in both register compilers (`r_prim`, `r-prim-imm`): a
blobref's step by an `extract`'s or a variant's offset, its read, and a
flat sum's tag (`%fx26-flat-tag`, now counted as never collecting).
`direct.rs` does in line a step by a constant (`suffix_step`), a numeric
key's tag (`flat_tag`, by `ldurb`/`ldurh`/`ldur w`), an `f64` read that
only `f64` operations use, raw (`reps`, as a flat array's element), and
`blobref-index` inside its call-out (`suffix_index`); each falls back to
the primitive, which says why. A shapes loop (a million elements, filled
then summed): 214.9 ms to 65.0 natively. On the way, the FX-26
compiler's inlined bodies lost their blobref facts (`c-resolved-at`).
Test: `direct.rs`'s `flat_keyed_as_the_rust_machine_gives_them`
(`programs/native/flat-keyed.fx`, keys of one, two and four bytes).

**In a leaf** (2026-10-11). Register code's `prim3imm p x k`, `RESULT :=
p(RESULT, x, REGk)`, `x` a constant, for a primitive that never collects
(`fixpt_heap::layout::regcode`, its check, `disasm`, the cellular
convention's `pure_call3`, `direct.rs`, `reps`): `blobref-index` (by
`%fx26-blobref-index`, its operands in that order), `blobref-set!` (an
`f64` taken raw) and `blobref-variant!` (a numeric key's tag written in
line), made by `r_prim3` / `r-prim3`. A flat `tagcase` keeps its blobref
and tag in places (registers in a leaf), a variable's where it is, an
arm's ref in theirs; its no-arm failure is `prim1`; so neither it nor
those operations call out (`r_collects`, `r-bloblet-quiet?`), and a loop
of them is a leaf. A self-call's argument that is its own parameter
stays put (`r-self-temp`). The shapes loop: 10.5 ms natively, the sum
allocating nothing (`docs/performance.md`, "Flat sums and blobrefs in
line"). An index key's tag (the label, the owner's field the byte
indexes) and its variant (the first field holding the label, found by a
short loop) in line too: the shapes with symbol labels 36.0 → 11.2 ms
(10.5 with a numeric key). Tests: `flat_sums_as_the_rust_machine_gives_them`
also fails a label no field holds and a tag past the fields, in line. And
`blobref-at` at a literal offset (`%suffix-ref`, now never collecting):
`prim2imm` in both register compilers, in line natively (`blobref_at`:
the owner's header read for its suffix's length); `blobrefs_as_the_rust_
machine_gives_them` fails one past the end so.

## 78. The best REPL in one short command (the user's, 2026-10-10)

Done 2026-10-11. The fastest FX-26 machine is the default: `fixpt
--dialect fx26 repl`, or `fixpt fx26`, where it took `--fx26-run cellular
--cellular-machine registers --calling-convention native` (the user's
choice: the default, not an opt-in). The machines have names, one
vocabulary for `--fx26-machine NAME`, `fixpt bench`'s columns, the REPL's
banner ("Machine: …") and the docs, which say who generates the code (`rs`
Rust, `fx` FX-26), what code (`scheme`, `ast`, `cells`, `regs`), what runs
it, and, where it is compiled to arm64, the calling convention (`cellcc`,
`nativecc`) (the user's design, 2026-10-11): `fx-regs-rsjit-nativecc` (the
default, `fast`), `rs-scheme-vm`, `fx-ast-eval`, `fx-cells-rsinterp`,
`fx-cells-asminterp`, `fx-cells-rsjit-cellcc`, `fx-cells-fxjit-cellcc`,
`fx-cells-stencils-cellcc`, `fx-regs-rsjit-cellcc`; bench's, made by the
Rust compiler, `rs-…`. The older flags still work and keep their old
defaults when given one by one; a name with them, or an unknown name, is
refused. The names showed a gap: no `fx-regs-fxjit-nativecc` (TODO §81).
The native machine's step limit is said as the others say it. Tests:
dialects.rs's `fx26_machines_by_name`; `on_every_machine` names
`rs-scheme-vm` for its reference. Docs: README (the machines' table),
`fixpt help`, `fixpt bench --help`, the Emacs mode's arguments.

## 82. `scripts/bench-history.py` across the machines' renaming (the user's, 2026-10-11)

The user's script, which turns `git log` into a CSV and a spreadsheet of
`fixpt bench` tables, named each metric by its column header, so every
machine's history split in two at `1567626` (§78's renaming). Now a table
of the run table's old names to the new (`RUN_RENAMED`: `lowered` →
`rs-scheme-vm`, `rust` → `rs-cells-rsinterp`, `hand` →
`rs-cells-asminterp`, `stencils` → `rs-cells-stencils-cellcc`, `compiled`
→ `rs-cells-rsjit-cellcc`, `registers` → `rs-regs-rsjit-cellcc`, `native`
→ `rs-regs-rsjit-nativecc`) is applied to a run table's header as it is
read, before grouping; the compile table's `registers` and `native`,
phases, are left alone. These seven are the only run-table names the
history has. Over the whole log (517 commits), each machine is one series
of 517 commits, one sheet and its two charts. The script is in git now.

## 84. I/O: bytes, the `io` effects, files, the clock, the arguments, the standard input (kayak's request, 2026-10-12)

In five stages, each in both checkers, both compilers, every machine and
the evaluator written in FX-26. What is left is in `TODO.md` §84.

**Stage 1: `u8`, `i8` and bytevectors.**

**`u8` and `i8`**, the fixed-width table as `i32` and `u32` have it
(`u8+` to `u8->int`, 18 operations each), fixnum-shaped: the runtime's
`Width`, both checkers' types, ranges of literals, shapes and subtyping
(an `int`), both lowerings, both register compilers' constant folds, the
evaluator written in FX-26 (`ev-width-prims!`), and native code, which
makes them in line as `i32`'s (`pure_fast`, its wrap now for 8 bits or
32). The base types are made last in both checkers, so no type id before
them moved. Test: `native/small-width-ops.fx`, every operation at a
byte's edges, the same on nine machines and the evaluator; in `direct.rs`
and `evaluator.rs`.

**Bytevectors**, `(bytevectorof r)`, generative type 8: the heap's
bytevector at run time; an array of `u8` at `r` to the safety analyses.
`make-bytevector`, `bytevector-length`, `-u8-ref`, `-u8-set!`, `-copy`,
`-copy!`, `bytevector=?`, `string->utf8`, and `utf8->string`, whose bytes
that are not UTF-8 give `(sum bad k)`, `k` the offset of the first. New
runtime primitives where the Scheme ones would not do (a write gives
unit; spans checked); the evaluator holds one as `(o-bytes …)` and prints
it as the machines do, `#u8(…)`. Tests: `run/bytevectors.fx`,
`run/bytevector-printed.fx`, `regions/bytevector-escapes.fx`. Docs:
`docs/fx26.md`, "Bytevectors" and "Fixed-width integers".

**Stage 2: the `io` effects, `write-out`, `write-err`, `exit` and
`main`** (2026-10-12). `(io k)`, `k` one of `stdin`, `stdout`, `stderr`,
`fs-read`, `fs-write`, `clock`, `args`, `exit`: `Atom::Io` and `a-io`,
read, printed and kept in one order in both checkers, no region (so
never masked), never licensed for speculation; to the compilers each is
"anything else", so no two commute (the user's one ordering rule).
`io-error`, a standard type beside `datum` (`check::STANDARD_TYPES`): a
kind of eight, for a `tagcase`, and the system's description. The
runtime's `World` (`fixpt_runtime::world`): the process's streams, each
write flushed, or captured for a test; the status `exit` asked for.
`fixpt run` calls `main` if it is defined, its integer result's low byte
the status; 70 if the run fails; `exit`'s status at once. The evaluator
written in FX-26 does all of it with the primitives themselves (its
`runs` effect now has every `io` kind). Tests: `tests/programs/io/`
(both checkers), `licence.rs`, `fixpt-cli/tests/io.rs` (five machines:
the streams, `main`'s status, `exit`, a failed run, a broken pipe as a
value). Found on the way: §85.

**Stages 3 and 4: files, the clock and the arguments** (2026-10-12).
`read-file` and `list-dir`, `(io fs-read)`, make what they give at a
region the caller picks; `list-dir`'s names sorted by their bytes, a name
not UTF-8 an `invalid-data` failure; `write-file`, `(io fs-write)`,
replaces a file whole and atomically (written beside it, flushed to the
disk, renamed over it). `clock`, `(io clock)`, monotonic nanoseconds since
the run began, an `i64`; `sleep-until` a time on it. `args`, `(io args)`:
what follows `--` in `fixpt run FILE… -- ARG…`. On every machine and in
the evaluator written in FX-26. Tests: `tests/programs/io/` (both
checkers), `fixpt-cli/tests/io.rs` (five machines, each in a directory
of its own for the files).

**Stage 5: the standard input** (2026-10-12). `read-line`, `(io
stdin)`: the next line with its ending (`\n` or `\r\n`) left off, the
last one even with none, then `eof`; a line not UTF-8 an `invalid-data`
failure, reading going on after it. The `World` reads the process's
standard input, or bytes a test gives. Tests: `tests/programs/io/io-stdin.fx`,
`fixpt-cli/tests/io.rs`'s `the_standard_input_read_by_lines` (five
machines).

## 85. Machines that disagree on a failure (2026-10-12, 2026-10-16)

What is left (one wording for each failure) is in `TODO.md` §85.

**A failing `pure` call no longer dropped.** The lowering claimed
`(pure)`, "its value may be dropped when unused", of every application
whose effect was `pure`, `(error …)`, `(quotient 1 0)` and `(car nil)`
among them, and the bytecode compiler under `rs-scheme-vm` dropped a
`begin`'s non-final one: 3 where every other machine failed. Now the
claim is made only of an application of a total standard operation
(`lower.rs`, `total_operation`: arithmetic on `int`, comparisons, the
shape predicates, `cons`, the fixed widths' and floats' operations but
division, remainder, and a float's conversion to `int`) to variables,
constants, closures or such applications. The bytecode compiler was the
claim's only reader; the register compilers drop nothing (each `begin`
item compiled, its value dropped after) and fold only what succeeds
(`car` of a constant pair, a conversion that fits), so no compiler moves
or drops code that may fail across an `io` effect or anywhere. And the
evaluator written in FX-26 fails the program on an `int` division by
zero, as the machines do, where it failed itself (`int-div`). Test:
`an_unused_failing_call_still_fails_on_every_machine` (six machines).
**One wording** (2026-10-16, the rest). A failure now says the same
on every machine, as native code says it. The lowering (`rs-scheme-vm`)
said Scheme's `error: message: irritants`: now its message alone
(`Session::bare_failures`, on while a lowered program or the evaluator
runs, so the front end's own failures keep theirs), and a `car` or `cdr`
of a non-pair, the one Scheme type check an FX-26 program can fail,
"car or cdr of a non-pair" (`lowered_failure`), not "expected a pair:
()". The evaluator written in FX-26 said "a pair is expected" (now
`as-pair` says the machines' words), and a primitive it calls that
failed (`string-ref`, `substring`, `integer->char`) failed the front end,
`fixpt: … error: cellular word: …`, not the program: now the program's
failure (`run_failure`, shared with the compiled run). The tests no
longer make the wordings one (`one_wording` gone, and the native sweep's
"one contains the other") but compare them as they are. Not a wording:
recursion too deep fails as a stack overflow on the cellular machines
and the evaluator, a step limit on native code and the lowering, which
have no stack limit of their own. Tests: `programs/run/fails-*.fx`
(`car`, `quotient`, `string-ref`, `substring`, `integer->char`, `error`),
on every machine, the evaluator and natively.

## 86. Failure as proof debt: stage 1, measured (2026-10-12)

What is left, stages 2 to 5, is in `TODO.md` §86.

`crates/fixpt-fx26/src/debts.rs` and its example (`cargo run --release
-p fixpt-fx26 --example debts`): each definition of a program checked
with `Checker::record_operands` (the operand types of the polymorphic
standard operations' applications, kept as `NodeFacts::operand_types`;
off otherwise), its debts discharged, owed, passed or stated, and
whether through its calls it may fail. Over the front end and 94 of the
95 benchmark ports: `docs/research/failure-and-blame.md`, section 7,
"Results". On the way, the lowering's `total_operation` (§85) learned
the operations lowered to the identity (`wcell-int` and kin),
`string-hash`, `char-in?`, `wglobal=?`.

## 88. A program's `define-type` of a standard type's name (2026-10-12)

`scheme-bench/bv2string.fx` defines `(define-type bytevector (bloblet
(fields) @heap))`; since `bytevector` became a standard base type
(2026-10-08) its parameters written `bytevector` were the standard type,
and the port no longer checked (found measuring §86). Both checkers now
read a standard type's name as the program's own definition where it has
one, as they already did `nil`, `false` and `nat` (`parse_type_node`,
`k-type-named`). The port checks and gives 0 again. Test:
`bidirectional/shadow-standard-type.fx`.

## 89. Conditions: the escape-only tag (2026-10-12)

What is left, the library of raising and handling, is in `TODO.md` §89.

`(escape-tag A H R)`, generative type 9 (`check::ESCAPE_TAG`), made by
`make-escape-tag`, escaped to by `escape`: a prompt tag at run time (the
same operations in both compilers, the lowering and the evaluator
written in FX-26), never captured with, so its prompts check no bound
`D` on what their bodies do, the strain the examples of
`docs/research/conditions.md` met. Both checkers' prompt rules read a
tag's parts from either kind (`synth_prompt`; `k-tag-parts`, new in
`check-calls.fx`, `check-rules.fx` no longer). Tests:
`control/escape-tag.fx` (a raise through a generic procedure, its effect
inferred, the handler pure but for its globals: `(6 -1 0)` on every
machine and in the evaluator) and `control/escape-tag-not-captured.fx`
(refused). Docs: `docs/fx26.md`, "Control, typed".

**The first library** (2026-10-12): `fx26:conditions.fx`, a module file
built in (`STANDARD_MODULES`, beside the front end's, resolved by
`built_in_module`), which a program loads by name: `handle` (a body
given a fresh region's escape tag, by rank-2 polymorphism, which both
checkers accept), `with-handler` (a body given a fresh region's key whose
mark is the handler) and `raise` (the handler called where `raise` is;
else a panic). A restart is a handler escaping to a `handle` around it.
Tests: `run/conditions.fx` (`(4 6 -1)` on every machine and in the
evaluator); `docs/research/examples/conditions/library.fx` and
`unhandled.fx`. Docs: `docs/research/conditions.md`, section 6b.

**Flat arrays of a length not literal** (2026-10-12, with the user):
`(arrayof F n)`, `n` a size, runs to the end of its owner's suffix. Both
checkers: the flat readers take a size (and a type's `arrayof` is a flat
array whenever its second part is written as a size); only a product's
last part may be one, nor an array's element, nor a sum's variant (a
named type read as a flat too, `flat_parts_wrong`); a new blobref may
claim only `finite`; binding one names the length (`name_nat`,
`k-name-nat`), forgotten where given back, refused where a caller would
supply it (`size_walk`, `k-size-walk`); a size binder is solved from a
generative type's size argument (`unify_ds`, `k-unify-descs`,
`k-descs-open?`). `blobref-index` into one is told `FLAT_TO_THE_END`
(`fixpt_heap::layout`), and the run time, native code (the whole element
within the suffix) and the evaluator written in FX-26 bound it by the
suffix. Tests: `bloblet/flat-unsized*.fx` (a record's samples summed,
`10.0`, on every machine; five refusals),
`bloblet-errors/flat-unsized-range.fx`. Docs: `docs/fx26.md`.

**`blobref-length` and bounds shown** (2026-10-12, N5c's part of §77):
`(blobref-length r)`, a flat array's length, a `(nat n)` of its length,
a new form in both parsers, both checkers, both compilers, the lowering,
the evaluator and the run time (`%fx26-suffix-ref-length`, as
`blobref-index`'s code says it). A natural's size now includes a
variable's array's length (`nat_size`, `k-nat-size`), so a test against
it teaches `i < n`; a `blobref-index` whose index the facts so show is
recorded (`NodeFacts::in_bounds`: `n - (i + 1) >= 0`, by
Fourier–Motzkin where needed), and §86's debts count it discharged.
Tests: `bloblet/flat-bounds.fx` (`(5 3 5)` on every machine) and
`indices_shown_in_bounds`.

**A new blobref's flat whole in the suffix** (2026-10-12, §77): what a
blobref's type said of its flat was not checked against the suffix: a
`(blobref o (arrayof f64 10))` made over 8 bytes had `blobref-length` 10,
and an index below 10 was recorded in bounds (and its debt discharged)
yet failed at run time; only the first byte was checked where a blobref
was made. Now `blobref-at` and `blobref+` check the bytes the flat takes
(`Checker::note_fits`, `flat_least_size`: of an array that runs to the
end, none of its elements) with `%fx26-suffix-fits`, after `%suffix-ref`
and `%suffix-ref+`, in both checkers, both compilers, the evaluator, and
natively in line (`suffix_fits`); field and variant steps need none, the
flat holding them whole. The FX checker's blobref helpers moved to
`check-blobrefs.fx` (`check-read-helpers.fx` was at the 1000-line limit).
Found by an audit of whether reads could skip the owner's header. Tests:
`bloblet-errors/flat-past-suffix.fx`, `flat-step-past-suffix.fx`.

## 90. The native convention: a redefinition that breaks what it calls (the system76 team's report, 2026-10-12)

Under `--fx26-machine fx-regs-rsjit-nativecc`, `redefine/knot-spin.fx`
ended with "check: `h` is broken, since `f` was redefined … define it
again to use it", where every other machine went on. `native_define`
(`session.rs`) checks a definition (`check_only`), which redefines `f`
and breaks `h`; then checks its value again, as an expression to
compile, and (the native compiler declining) the definition again as
cellular code. The new `f` calls `h`, so those later checks, seeing `h`
broken, refused it. Fixed as the team proposed: a front-end entry,
`check-hold-breaks!` (`check-program.fx`, `FRONT_ENTRIES`), which on sets
aside the breaks the last check made (the broken list as that check
began, `k-broken-began`), and off puts them back after any the checks
between made; `native_define` turns it on once its check succeeds, and
`run_checked` off when the definition is done, on every path
(`Session::hold_breaks`). `h` is still broken after. Checking the value
before the definition would give a recursive `define*` its old type;
deferring the dependents' re-checks would leave them their old types.
Nothing caught it: the only test that ran `knot-spin.fx` natively was
`tests/direct.rs`'s every-program report, which is ignored. Test:
`a_redefinition_breaking_what_it_calls_natively` (`tests/redefine.rs`,
which fails without the fix).

**Heap arrays' lengths: `narrayof`** (2026-10-12, N5c's part of §77, the
user's offer): `(narrayof T n R)`, an array of `n` elements;
`(arrayof T R)` is one of length `finite`. `Ty::Array` and FX's
`ty-array` carry the length: subtyping forgets it (`size_le`), inference
unifies it, substitution, printing, the polarity walk (F8) and F4's rule
(one parameter's own length may be `finite`) know it, in both checkers.
`array-length` is `(narrayof t n r) → (nat n)`; a `make-array` or
`rmake-array` of a natural's size is an array of that size, kept by
`the` (`Checker::array_sized`, FX `k-sized`); a variable bound to an
array of a length not known is given its own (`name_nat`,
`k-name-nat`); `(array-length a)` is a natural's size (`nat_size`,
`k-nat-size`). An `array-ref`/`array-set!` of a variable's array whose
index the facts show below its length is recorded in bounds, and the
debts tool counts it discharged: in the ports, 34 of 732 (31 writes, 3
reads; none before). Tests: `sizes/narrayof-lengths.fx`,
`narrayof-wrong-length.fx`, `narrayof-not-known.fx`,
`narrayof-escapes.fx`.

**A blobref's length named where it is bound, as `finite`; `blobref-length`
in line** (2026-10-12, §77): a procedure of a blobref to an array that
runs to the end of the suffix could not pass its own parameter on: the
parameter's length, named where it is bound, was not `finite`, and a
blobref is invariant in its flat. Such lengths (`to_end_sizes`,
`k-to-end-sizes`) now mean what `finite` does inside a blobref's flat
(`Checker::sub`'s generative case, FX `k-to-end-forgot`); a literal length
does not, nor another blobref's. Natively, `%fx26-suffix-ref-length` never
collects, in line (`suffix_length`): 9.4 → 3.2 ns an element in a loop
over a million `i64`s. Measured and not done: leaving out the checks a
proof makes needless (at most 15% more, `TODO.md` §77). Tests:
`bloblet/flat-unsized-recur.fx`, `sizes/flat-literal-not-to-end.fx`,
`sizes/flat-to-end-not-another.fx`.

## 91. Each native stack frame a bloblet; `f64`s raw in frame slots (the user's, 2026-10-12)

The bloblet format exists for objects that hold both values and raw bits,
and a frame is one (`docs/object-model.md`). Measured first: no float
benchmark was ported, so four were (`mllang-bench/fx/`: `mlton/mandelbrot`,
`mlton/matrix-multiply`, `benchmarksgame/spectralnorm2`,
`benchmarksgame/nbody`); in `mandelbrot` about 85% of the native run was
`f64` handling, every `f64` that reached a frame slot boxed (a `let`'s, a
loop's) and unboxed when read back. In three stages:
- **Stage 1** (`a1fbde2`): every native frame laid out as its bloblet
  will be, a header word below its link (`x29` still at the link, the
  code's frame offsets unchanged; `push_frame`, `pop_frame`); the runtime
  walks frames as regions, from each header word.
- **Stage 2**: the stack cache's chain of flushed frames is linked
  `native-frame` bloblets (a new kind) in place of chunk vectors: a
  flush stamps each frame's header where it is (`native_frame_in_place`),
  a copy makes one with a trailer (`native_frame_with`); `Pos` is a frame
  and where it resumes, `Rec` its fields; the chain's word count is kept
  in the state (`cont_words`) and each continuation's data.
- **Stage 3**: `f64`s raw in frame slots. `reps::raw_slots` takes each
  slot apart into webs (its writes and reads joined where a write reaches
  a read, one variable's each) and keeps raw a slot all of whose webs are
  an `f64`'s by the program's types (a read used by an `f64` operation, or
  a write of what one made); what is stored there is unboxed, a read used
  otherwise (a loop's total, returned) boxed there. Raw slots go after the
  frame's values, the code bloblet and the closure, as its bloblet's
  suffix, never traced; the stack map numbers values only, and carries the
  frame's field count above `MAP_BITS` (48), for a flush (`frame_shape`).
Natively (`rs-regs-rsjit-nativecc`, at the ports' first sizes), before →
after: `mandelbrot` 81.3 → 31.2 ms (17.0 → 4.2 M words), `matrix-multiply`
79.6 → 26.1 (16.1 → 0.2), `spectralnorm2` 32.6 → 17.1 (14.4 → 7.2;
`eval-a`'s result is still boxed: raw arguments and results are next),
`nbody` 31.4 → 14.6 (6.4 → 2.6). Whole runs at the ports' sizes: 1.85 →
0.89 s, 1.85 → 0.75, 3.32 → 1.91, 2.07 → 1.20; the other 42 ports the
same answers, within a few percent but `merge`, 0.66 → 0.73 (`TODO.md`
§91); `captures` 8.6 → 11.2 ms (frames a word larger, and objects).
Tests: `programs/native/raw-slots.fx`,
`raw_slots_through_the_stack_cache_and_collections` (raw words through a
small stack cache, collecting every 7 words; a slot an `f64`'s, then an
`int`'s).

**Raw `f64` results** (2026-10-12): a procedure returns an `f64` raw to a
caller that takes it so, told by the caller's return address. A call
whose value only `f64` operations use (`reps::raw_refs`, now of
`invoke` and `invokeself` too) puts a mark there, `movk xzr, #0xf64f,
lsl #48`, which does nothing, then a branch to an unbox, then a branch
on (`take_raw_f64`); a `return` of a raw `f64` (`raw_return`) loads the
word at its return address and, the mark there, returns 8 past it, raw;
else boxes, as before. Every other return (a callee's that does not
know, a stub's, an underflow's, a continuation's, a call from Rust)
comes to the mark and the value is unboxed: nothing else changed. A
`flatarray-ref` just before a `return` returns an `f64` element so, the
others as they were. Natively, full sizes: `spectralnorm2` 1737 →
1277 ms, 320.2 → 0.2 M words (`eval-a`'s result); the other float ports
the same (their boxes are arguments'). Test:
`programs/native/raw-returns.fx`, `raw_returns_to_every_kind_of_caller`
(raw to raw and to value-keeping callers, a polymorphic callee's boxed
`f64` taken raw, flat arrays' `f64` and `i64` elements returned, through
the stack cache and collections; a return 4 past the mark fails it).

**Raw `f64` arguments, to procedures known where they are called**
(2026-10-13, the user's: no masks). A procedure takes a parameter raw
that only `f64` operations use (`reps::raw_params`; a call's operand,
which takes either, `Demand::Any`, no evidence and no use against); its
entry unboxes those, for a caller that passes values. A call of itself
(`invokeself`), or of a procedure bound as compiled (a global whose cell
has not been written since, or a lambda-lifted procedure), passes them
raw and enters past that unboxing (`raw_entry_skip`, the same bytes for
each); every other call passes values, as before. A global written since
is called through its cell, the raw arguments boxed first; the overflow
at a frame's entry boxes the raw argument registers around it. Nothing
is said at run time: what a call passes, the compiler knows of both
ends. (The first version, 6ec7f7e, passed a mask in `X9` to any callee,
with raw entries and adapters for the polymorphic case: dropped, as
complexity that would not pay.) Natively, full sizes: `mandelbrot` 693 →
346 ms, 83.9 → 0.0 M words (`loop2`'s calls of `loop3`); `nbody` 130 →
120 M words (`put` takes its `v` as a value: only `flatarray-set!` uses
it). Test: `programs/native/raw-args.fx`,
`raw_args_between_every_kind_of_caller_and_callee`, which fails with the
entry's unboxing left out or a known call entered at the entry. Not
caught by it: the boxing around an overflow (the collector passes over
raw bits outside every space) and before a call through a cell written
since (no test program redefines such a global).

**A slot that holds an `f64` and an `int` in turn, split** (2026-10-16,
the user's: "the analysis fix for nbody"). `nbody` boxed about 60
`f64`s a step, and not where `docs/research/raw-scalars.md` guessed
(`put`'s `v`): `put` is inlined in `pairs`, and its `v` went into a frame
slot that the loop's next `j`, an `int`, used too; a slot is raw only if
every variable in it is an `f64`, so every `f64` stored there was boxed.
`reps::split_slots` now gives such a slot's `f64` webs a slot of their
own, past the frame's others, which `raw_slots` keeps raw (a frame of at
most 64 slots), before the native compiler reads a procedure's register
code (`register_cells`); register code itself, and both compilers that
make it, unchanged. `nbody` natively, full size, alternated three times:
1.29 → 0.67 s, 134.5 → 14.5 M words with start-up (the run alone about
1.05 → 0.43 s, 130 → 10 M words). The other 45 ports the same answers,
times and allocation (old and new binaries side by side). Tests:
`reps::tests::a_slot_of_an_f64_and_an_int_is_split`; `raw-slots.fx`'s
`reuse`, such a slot, now split. Found on the way, left (`TODO.md`
§91): the run's remaining 10 M words are `advance` passing `dt` raw to
`pairs`, made native a form before, so called through its cell.

**Raw `f64` arguments to a procedure made native a form before**
(2026-10-16, found fixing `nbody`'s slots). A call passed raw only to a
callee known where it is compiled, and a global's procedure was known
only while its value was still cellular; one an earlier compile had made
native was called through its cell, its raw arguments boxed. Now such a
global, if its code takes some parameters raw, is bound as a procedure
compiled here is: under the global's count of writes, the native closure
the cell holds is entered past its unboxing, the arguments raw; written
since, through the cell, boxed, as before. What it takes raw comes from
the code itself (`Compiling::native_params`): its field 2 is the cellular
word it was compiled from (`CODE_SOURCE`), whose register code gives the
mask its own compile found (`register_params`); code a program sealed
(`seal-code`, its suffix frozen) is never taken for it. A callee that
takes nothing raw stays called through its cell: binding every native
global cost `tailfib` and both `boyer`s 5–20% (the guard's loads on
every call, and the mask found again at every call site before it was
kept per compile). Natively, full sizes, old and new alternated, best of
3: `nbody` 0.68 → 0.63 s, 14.5 → 4.5 M words (the run's own: none);
`mandelbrot` 0.98 → 0.59 s, 87.5 → 3.7 M words (`loop2` calling
`loop3`, a form before: the 83.9 M words of 6ec7f7e's note had come back
with each definition made native as defined). The other 44 ports the
same answers and times. Test: `programs/native/raw-args-across-forms.fx`
(raw to a procedure made a form before; that procedure redefined to take
fewer raw, the same call then through the cell; a caller compiled after,
binding the new one), in `native_session_adapters_aborts_and_stack_maps`.


## 92. Concurrency: processes and `par` (kayak's request, 2026-10-13)

The first of kayak's three stages (`TODO.md` §92). A region's handle was
its position in one stack of live places, and ending one ended every
newer: wrong once tasks interleave (A enters `r1` and waits, B enters
`r2`, A leaves `r1`, and `r2` would end). Now a handle is a slot of its
own, the lowest free, and each task has a stack of the slots it entered
(`heap/regions.rs`): entering, leaving and counting places are the
current task's (`task_new`, `task_switch`, `task_end`, `tasks_reset`). An
abort, or a whole continuation resumed, ends the current task's places
past the depth its prompt noted (`regions_exit_to`); `%region-exit`
ends a handle and what its task entered after it, and nothing if the
handle is not the current task's. Machine code's table of current chunks
is indexed by slot, as it was by position. Test: `fixpt-heap`'s
`tasks_end_their_own_regions_in_any_order` (two tasks' arenas and reaps
interleaved, one ended first, the other's kept through collections) and
`an_abort_ends_only_the_current_tasks_regions`.

**Processes and `par`** (stages 2 and 3, kayak's request, 2026-10-13;
`docs/research/processes.md`, `docs/fx26.md`, "Processes and `par`").
- **Forms**, derived in both parsers (`processes.rs`, `parser-forms.fx`):
  `spawn`, `send`, `receive`, `par`, `icell-get`, `icell-put!`, each a
  call of a procedure of `fx26:processes.fx`, a scheduler written in FX-26
  over prompts, through the hidden global of its load; `%sched`
  (`fixpt_runtime::sched`) its runtime part: the run queue, mailboxes,
  I-cells' waiters, a message's copy (`Heap::copy_within`). Each node an
  expansion makes has a place of its own (the FX-26 compiler finds facts
  by place).
- **Types and effects**, in both checkers: `(addr M R)`, `(inbox M r)`,
  `(process M E)` (generative types 10 to 12); `(send R)`, `(receive R)`,
  `(init R)` (P4, within `(write R)`), `nondet` (M3). The library's
  procedures typed as the forms see them (`library_type`, the standard
  `%processes:` entries), and they and `%sched` seen only by module files
  built in.
- **Rules**: `spawn`'s (`synth_spawn`, `k-spawn-te`): every free variable
  of a process's body, and its messages, transmissible (H1,
  `untransmissible`); what it does beyond its own place what a process may
  do (`crossing_atom`), that the spawn's effect, with `nondet` for I/O.
  `par`'s (`synth_par`, `k-par-te`): no branch escapes, no two interfere
  (P5, `interference`; `par2`'s, nested).
- **Runtime**: I-cells of a kind of their own, always in the heap, read
  by waiting (Q3/P6); a process's own place a reap on its own task's
  stack; the program runs the others when it waits and after each
  `spawn`, `send` and `icell-put!`; a deadlock an error; a failure in a
  process fails the form, the scheduler begun again. Natively, a built-in
  module file is defined from its text in the program's convention
  (`built_in_load`), and the FX-26 parser told it is made
  (`syn::set_shared_made`), so a capture never crosses into cellular code.
- **The evaluator** written in FX-26 runs the library, with `%sched` a
  primitive and the machines' I-cells; it replays sends between forms.
- **Tests**: `tests/processes.rs` (twelve programs in
  `programs/processes`, each every way it runs; answers under twenty run
  queue orders; arrival order seen to vary; the interference table cell by
  cell in both checkers; a deadlock; a failing process), and the programs
  in the every-program tests of `checker.rs`, `compiler.rs` (every
  machine) and `evaluator.rs`. The full suite; the new tests under
  `--profile checked`.


**`pselect`** (the user's, 2026-10-13; `docs/fx26.md`, "`pselect`").
`(pselect ((icell-get c) x body …) ((receive box) y body …) …)` waits
until one arm's wait is ready, and runs that arm: Tokio's `select!` over
futures that only wait. Expanded in both parsers (`select_expansion`,
`select-form`) into the scheduler's events: `cell-event`,
`mailbox-event`, `or-event`, and `sync`, which gives the chosen arm's
number, `nondet`; generative type `(event e)` (13, `check::EVENT`). A task
that waits gives each event one waker that runs only once. Named
`pselect` because `select` is a module's component in types and effects.
Found on the way: a parse error in any process form (`par` too) aborted
to a prompt tag no prompt had (`parser-forms.fx` made its own instance of
`parser.fx`); its forms now fail through the caller's `pfail-at`. Tests:
four programs in `programs/processes` (a cell chosen, a server stopped by
a cell, a deadlock, a malformed arm), every way they run.

**`pselect`'s deadline arm** (the user's, 2026-10-13; `docs/fx26.md`,
"`pselect`"): `((sleep-until t) u body …)`, ready once the clock reaches
`t`, `(io clock)`; event `clock-event`. The runtime keeps the timers
(`fixpt_runtime::sched`, operations 18 to 21): when the first task waits
and no task can run, it sleeps until the earliest, and the wakers due run
(`main-wait`, for `icell-get` and `receive` as for `pselect`). The first
task's own `pselect` registers a waker that does nothing, so that its own
deadline is among them. And **the fired-waker leak**, fixed with it: an
event's registration now gives back how to take the waker away again
(operations 20, 22, 23), and `sync` takes it from every event once one has
fired, so a loop that waits on one cell many times leaves nothing behind,
nor is a deadline passed over slept for. Tests: three programs in
`programs/processes` (a deadline reached by a process, a message before a
30 s deadline, the first task's own), every way and under 20 schedules;
`processes.rs`, `a_deadline_passed_over_is_not_waited_for` (fails, having
slept 30 s, with no removal).

**`race`, best effort** (the user's, 2026-10-13; `docs/fx26.md`,
"`race`"): `(race e1 … en)`, the value of a branch that finished, nested
`race2`s in both parsers. Both checkers (`synth_race`, `k-race-te`): each
branch cancellable (no write, fill, send, I/O, `goto`, `comefrom`, or
effect variable), no two interfering (`par`'s table), one type (the
wider), and `nondet`. The scheduler cancels a loser that has not finished
(`%sched` operations 24 and 25, a list of tasks cancelled, cleared as each
ends): it ends instead of starting, or instead of resuming from its next
wait, its places with it. With it, the first task, waiting, runs the
others one at a time until what it waits for is ready (`main-wait`), not
all of them first. Tests: six programs in `programs/processes` (a cell
chosen, three computations of one answer, a loser stopped at its wait,
which would otherwise spin for ever; a write, two types, two receives
refused), every way and under 20 schedules; both checkers on each.

**H3: copying against sharing, measured** (`docs/research/processes.md`,
"H3"; `docs/research/processes-h3.fx`): a message costs about 0.87 µs
whatever its size, and 9 ns a word copied, after the copier's map stopped
hashing with SipHash (`WordHasher`, one multiply a word), which had made
it 22: 10,000 cells 443 → 179 µs. Building the data costs a ninth of
copying it. Decided: copy; share only if large messages turn out common.

**The cost of a switch, a third less** (the actors note's A4;
`docs/research/processes.md`, "The cost of a switch"): a message to a
waiting process, its two switches, 890 → 585 ns. A profile found the
runtime's bookkeeping a third of it: each `%sched` operation interned
`#u` and its state's global's name, by SipHash, and the prompt tag's sum
looked its kind up by name. Now `Heap::intern_static` finds a name the
runtime asks for at every turn by where it is kept, the symbol table
hashes with `WordHasher`, and the kinds are constants.

**`self` and the `sendable` kind** (`docs/fx26.md`, "The forms" and "What
a process may hold"). `(self box)`, a form, is the process's own address
at its place, `(addr M r)`, from its mailbox (the same mailbox at run
time); test `programs/processes/self.fx`, a process counting down by
messages to itself. `(m sendable)`, `data ≤ sendable ≤ type`, a binder
that takes only a transmissible type, so that a server may be polymorphic
in its messages: a variable of it is transmissible, and each
instantiation is checked to be (`check_bounds`, `k-check-sendable`). The
FX-26 checker's transmissibility rules moved from `check-processes.fx` to
`check-data.fx`, before the binders' check that needs them. Tests:
`sendable.fx` (an echo server for any sendable `m`), `sendable-type.fx`
(the same of kind `type`, refused), `sendable-ref.fx` (a reference given
to one, refused).

**Q2: preemption at fuel polls, on every machine** (the user's,
2026-10-14; `docs/fx26.md`, "Running"; `docs/research/processes.md`, item
7). Each machine's fuel given out in time slices (`sched::SLICE`, 2^16
polls; `FIXPT_SLICE` for testing); at a slice's end the runtime decides
(`sched::preempt_due`: a task wherever the scheduler's prompt is on the
machine's own stack; the first task if another could run) and the machine
calls the scheduler's `preempt` there: a task parks itself, apart from the
run queue so that `drain` ends; the first task runs one other. Per machine:
the bytecode machine at an instruction boundary (`VmFrame::Discard`); the
Rust cellular machine, the arm64 ones (interpreter, both JITs) and the
stencils at a cell boundary, the polls moved so that each is one, through a
trampoline word (`call 0`, `drop`, `exit`), the arm64 ones and stencils
leaving and coming back in from the state; register code (cellular
convention) at its entry and loops, the live registers pushed (a liveness
pass) and resumed by its resume table; the native convention from a frame
of the poll's own, mapped as a procedure's, through which a capture and a
restore go as any; the evaluator written in FX-26 from a poll of its own.
A task is not preempted until the call of `preempt` made at its poll has
returned, nor from its wait's capture until it is resumed, nor again until
it has had a slice (the heap's per-task `quiet`, a depth and a grace;
each machine says when its call returned: `sched::preempt_done`).
Preemption made the scheduler's check-then-act sequences races, each found
with tiny slices and fixed: a waker given for what is already ready runs at
once (a message arriving between a task's check and its wait was lost);
`race`'s winner fills its cell in one step (`ICELL_OFFER`, 34); the first
task, finding nothing to run, looks once more before it says deadlock (its
own preemption may have run what it waited for). And memory growing as the
scheduler was preempted within itself, a livelock (the slice spent before a
task went on), and two resumers of one task. Tests:
`fixpt-cli/tests/preempt.rs`, a spinner, two processes allocating while
preempted, and the same at a slice of 7 polls, on each of the nine
machines; `processes.rs`, `a_spinning_process_is_preempted`, four ways.
By hand: every program of `programs/processes` on each machine at slices
of 3, 7 and 13 polls, and with `--gc-every 10` on register code.


**`append` and `string-append` as `vsubr`s** (the user's, 2026-10-13;
`docs/fx26.md`, "Variadic procedures"): called with any count, a call the
runtime's primitive of that count, and as a value `%vlambda`'s closure over
the operation on its list of arguments, as `list` is, in both compilers,
the lowering and the evaluator written in FX-26 (which had no `append`).
`append` at one region, the last list shared. Test:
`programs/native/variadic-standard.fx`, on every machine.
Then used in FX-26's own sources: the reader's `str3` and `str5`, three
and five strings joined, gone for `string-append` of any count (20 calls),
and 17 nested `string-append`s flattened; no nested `append` was found.


**What loads the scheduler, found where expressions are (2026-10-14).**
The loads' scan (`syn.rs`, `load_modules_in`), which reads the program's
module files for the parser written in FX-26 before it parses, took any
list headed by a form's name as that form: a binding `(self x)` loaded the
scheduler, a file the Rust checker never read, so every file read after
it was numbered otherwise, and the front end compiled by the compiler
written in FX-26 with the Rust checker's facts failed (`regcode-core.fx`'s
`self` had been renamed `itself` for it). Now the scan looks only where
the parsers find expressions: not a name bound or a parameter, a type or
an effect, a `tagcase`'s or `typecase`'s arm's tag, a `cond`'s clause as a
whole, `spawn`'s box. `regcode-core.fx` binds `self` again. Test:
`syn.rs`, `the_scheduler_is_loaded_by_forms_only`; and the whole suite with
`self` bound.

**A cancelled task that waits ends at once (2026-10-14).** A cancelled
task (a `race`'s loser, a task of a monitored process that failed) ended
only when it next ran: one waiting for a cell never filled stayed, a task
and its places, until the run ended, and a deadline it waited for was
still slept for. Now each wait hands the scheduler how to take its waker
back (`suspend`'s `register` gives it: `ICELL_UNWAIT`, `MAILBOX_UNWAIT`, a
`pselect`'s `undo-all`), kept with the task (`WAITING`, 40) until it is
woken (`WOKEN`, 41); a cancel, and a failure's handler, then end each
cancelled task that waits (`REAP`, 42; `reap`), its waker taken back. A
resumer that runs after (its waker fired, and queued, before the cancel)
does nothing: each wait's `alive`, cleared by the reaping, says so, since
the task's number may be another's by then. Test:
`programs/monitors/cancelled-waits.fx`: a monitored process fails while
its other branch waits for a deadline ten minutes away; a wait for what
no task will fill is a deadlock at once (it slept for the ten minutes).

## 93. Cellular code calling native code, where the native convention declines (2026-10-13)

**Typed calls of native closures.** On the REPL's machine a form the native
convention declined runs as cellular code on the arm64 cellular machine;
a typed call (`tcall`, `ttailcall`) there was not checked, the checker
having said its callee is a closure, and a global holding a native closure
was entered as a cellular one: the code bloblet's first field read as a
word's entry, a crash. Now a typed call checks for a cellular closure as an
untyped one does, in both assemblers (`fixpt_native::cellular`,
`native.fx`), and anything else goes to the Rust machine (`control::run`
leaves a native closure to it), which calls native code. Test:
`direct.rs`, `typed_calls_of_native_code`.

**Its cost to assembling words, mostly recovered** (2026-10-14, the
user's). In line at every typed call, the closure test and the call-out
made peval's words 40% slower to assemble (`fx arm64` 4.75 → 6.80 ms,
`arm64` 0.28 → 0.32). Now a typed call in a word tests only whether its
callee's code is in the code area (`State::code_lo`, the comparison native
code makes: one load and a compare after the closure's code, which the
call loads anyway), and if it is, jumps to the machine's own routine for
the cell, through the routine table: the state at a cell's start is that
routine's (the cell consumed, nothing yet done, the fuel not yet taken),
and the routine has the call-out in line. Seven instructions a typed call,
none a word: `fx arm64` 4.93 ms, `arm64` 0.28 (measured back to back, three
times). A call-out stub at each word's end was tried first: its branches
did not reach in the front end's largest word (half a million
instructions), and the stub, as long as the call-out, cost a small word as
much as the call-out in line.

**A standard operation as a value is never inlined.** Register code
inlines small globals' bodies into later forms (`inlines`), but a standard
operation as a value is a closure of a word only the stack code of the
form that names it makes (`standard_word`, made afresh for each form). A
later form inlining such a body declined as a whole, and ran as cellular
code: on the REPL's machine `(define f … (let ((g +)) (g a b)))` then `(f 1
2)` was the crash above. Now such a body has no room to be inlined or
specialized (`room`, `c-room`, both compilers): the call stays a call. Test:
`direct.rs`, `typed_calls_of_native_code` (its second half).

**A far field is native code (2026-10-14).** The native convention read
and wrote a field with one `ldur`/`stur`, whose offset reaches 256 bytes:
field 31. Past it, it declined, so a module of more than 31 members ran
as cellular code. Found when the scheduler's module (`fx26:processes.fx`)
grew to 32: declined, its waits captured up to the prompts native callers
set, which cellular code cannot (`TODO.md` §93), and every program that
waited failed on the REPL's machine. Now a field to 4095 bytes away (511)
is reached through its address in x16, one `sub` more. Test: `direct.rs`,
`far_fields_are_native_code`.

**Captures and marks that cross machines (2026-10-14).** A capture in
cellular code (a procedure the native convention declined) up to a prompt
native code set failed, "no prompt for this tag", and so did the reverse,
native code capturing up to a cellular prompt: each machine walked only
its own frames. Marks were the same: `current-marks` and `first-mark` saw
only the running machine's. Now a machine in a call of another's code is a
*boundary* (`fixpt_runtime::crossing`, one stack of them per thread,
innermost last, since the calls nest strictly): the native convention's
call of cellular code (`call_foreign`) and the Rust machine's call of
native code (`call_native`). A capture that finds no prompt in its own
machine takes all of that machine's frames, then each boundary's out to
the prompt, innermost first. Each piece is a continuation of its own
machine's frames with the piece inside it as its *inner* one (a native
continuation's seventh value; a cellular one's `CONT_INNER`): given a
value, it puts its frames back, then calls its inner one with the value
where the call between the machines was, and resumes with what that
returns. Native code taken past a boundary resumes where the stub's call
returns, with a continuation procedure of its own (`continuation_bloblet`,
call-out 7, `REINSTATE`); a cellular machine's, in tail position, returns
the value. Marks read past the running machine go on through the
boundaries, and `marks-of` reads a crossing continuation's inner pieces
first (the Rust machine reads a native one's through
`crossing::foreign_marks`). Test: `programs/native/captures.fx`, in
`direct.rs`'s `deep_recursion_through_the_stack_cache` (a small stack
cache, collecting often): through three machines, in tail position at each
boundary, 20 000 deep, marks, and an abort from inside a crossing
continuation to the prompt outside it.

**Whole continuations that cross machines (2026-10-14).** A `cwcc`
continuation taken in native code and given a value from below a call
into cellular code was put back within the run that was running, so the
cellular frames between were kept, and the value came back to them: 107
where 6 was right, and a value of the wrong kind reached arithmetic in
one case. (One taken in cellular code escaped to it, as `NativeExit::
Throw` had, but could not be put back from another run.) Now a whole
continuation where machines are nested is every machine's frames out to
the bottom machine's, whose piece is whole (`crossing::capture_whole`,
the boundaries' `capture_whole`; a bottom run with no frames of its own
still a whole piece, of none, which returns from the run). Given a value
anywhere but the bottom machine, it is thrown out through the boundaries
to it (`reinstate`'s throw, `call_foreign`'s and the Rust machine's
`call_native`'s), which puts its piece back in place of its frames and
calls the pieces inside, as a delimited crossing's are. The evaluator
written in FX-26 has `stay-cellular` (as the identity). Test:
`programs/native/whole-captures.fx`, in `direct.rs`'s
`deep_recursion_through_the_stack_cache` (a small stack cache,
collecting often): taken in either, thrown from the other through frames
of both, 200 crossings deep; and kept, then called again after `cwcc`
returned, from either; by hand, called again from a later form.

**Preemption in cellular code native code called (2026-10-14).** A poll
in cellular code that native code called asked to be preempted only for
the scheduler's prompt in its own frames, which are never where it is: so
such code (a procedure the native convention declined) ran on, starving
the others, until it returned to native code or waited. Now a poll asks
the boundaries out from it too (`crossing::reachable`, each boundary's
`has_prompt`, asked before `preempt_due`, which must not walk them), in
the Rust machine and in native code a machine called; and the Rust
machine, nested, calls a native `preempt`. The capture `preempt` makes
crosses the machines, as any does. Two faults the resumption showed:
the frames `reinstate` puts back before it calls a continuation's inner
piece have no stub's frame on top, so that boundary now says where they
resume (`Foreign::resume`), where a capture had dropped the innermost;
and a poll before the call of the word `call_value` made (preempted
there) has that word's frame as the piece's bottom, which a capture had
skipped as the return into its `exit`; now skipped only when it is
(`nested_floor`), or each resumption would keep one more. Tests:
`programs/preempt/spinner-cellular.fx` (each machine; the old binary
waits for ever) and `allocating-cellular.fx` (each machine, every 7th
poll), and the tiny-slice sweep (slices 3, 7 and 13) over every process,
monitor and preemption program on every machine.
**Calls between the machines too deep, a stack overflow** (2026-10-16,
`TODO.md` §93). Each call between native and cellular code nests a few
Rust frames on the thread's stack, so recursion alternating between them
a few million deep (on the CLI's 256 MB thread) crashed the process,
"thread has overflowed its stack", where recursion within one machine
fails as a program does or goes on through the heap. Now each call
between them first asks whether the Rust stack has 256 KiB left
(`crossing::room`, from the thread's stack bounds by `pthread`), and if
not fails it, a stack overflow: in the Rust machine's `call_native` and
native code's `call_foreign`. The session goes on after. The evaluator
written in FX-26, which recurses on its own machine's stack, already
failed so (`captures.fx`'s 20 000-deep case: "cellular word: stack
overflow"). Test: `programs/native/crossing-overflow.fx`, on a thread of
16 MB, in release and checked builds.

## 94. Process monitors (kayak's request, 2026-10-14)

`(spawn-monitored watcher on-failure (box M r) body …)`: a process whose
failure (`error`, a trap) is a message to `watcher`, `(on-failure
message)`, not the form's failure (`docs/fx26.md`, "Monitors"). In both
parsers and both checkers (`synth_spawn_monitored`, `k-spawn-monitored-te`:
`spawn`'s rule, the watcher an address, `on-failure` a `(subr pure
(string) W)`, and `(send R)`). Kayak's questions, answered: a normal exit
sends nothing; a watcher that has ended has the message unread; `par`'s
branches fail as the `par` does (the process); a `race` branch that fails
is lost, the race failing only if all do; a failed process leaves nothing
half built that another can see (it shares only what cannot be written,
and its places end with it); the payload is the message string.

Built as groups: a monitored process's first task begins one (`MONITOR`,
35) and its `par` and `race` branches join it (`INHERIT`, 36); a `race`
branch is a group of its own. At a failure each machine asks
`sched::task_failed`: in a group with a handler, and with the scheduler's
prompt on the machine's stack, the rest of the group is cancelled, the
failure kept, and the machine aborts to the prompt as a waiting task does:
the bytecode machine from `dispatch_condition`; the Rust cellular machine
from its loop; the arm64 ones and the stencils from their run loops
(`control::abort_on`); the native convention from its common trap
(`Callout::Failed`, `abort_to`); the evaluator written in FX-26 from its
`efail` (`TASK_FAILED`, 38). The scheduler's `run-task` then gives the
group's handler the message (`TAKE_FAILURE`, 37). Tests: `programs/monitors`
(a worker's `error`, a trap, a `par` branch, two failures and one
message, a `race` branch lost, a `race` all lost, two refusals), every way
and under ten schedules (`processes.rs`), and on each of the nine machines
(`fixpt-cli/tests/preempt.rs`).

**A `race` in a process that fails is cancelled with it (2026-10-14).** A
`race` branch's group was a group of its own and nothing more, so when the
process running the race failed, its branches ran on: unseen (a branch
does nothing another could see), but for as long as they took. Now a
branch's group is made inside the current task's (`BRANCH_GROUP`, 39;
`fork-race-branch`), and a failure cancels its group and every group inside
it. Test: `programs/monitors/race-cancelled.fx`, whose branches would
count a billion each: once the process fails, a wait for what no task will
fill is a deadlock at once (it ran out of steps before).

## 95. Byte input and terminal modes (kayak's request, 2026-10-14)

For an interactive program written in FX-26, such as a front end that
edits a line as it is typed (`docs/fx26.md`, "I/O"). Under `(io stdin)`:
`read-byte`, a `u8` or `eof`; `read-bytes bv start end`, waiting for one
byte, then as many as have come, how many or `eof`; `stdin-ready?`. A new
kind, `(io terminal)`: `terminal-raw`, `terminal-restore`, `terminal-size`
(`(productof (rows int) (columns int))`), each `not-a-terminal`, not a
failure, when the standard input is none. A `pselect` arm `((read-byte) b
body …)`, in both parsers (its wait has no operand: `#u` stands for it,
at the wait), over the scheduler's `stdin-event` (ops 43-45); when no task
can run, the scheduler sleeps until the input is ready or the earliest
deadline (`timers_wait`).

Kayak's questions, answered:
- **Restoring: a form or a pair?** A pair of operations, and `fixpt` puts
  the terminal back however the run ends (failed, `exit`, or done; and the
  REPL after each form). A form would not help a failure: FX-26 unwinds
  nothing on the way out, and a monitored process that fails leaves the
  others running, raw.
- **Wait on a byte, or on input ready?** On input ready: a `pselect` arm
  is ready once a read would not wait, then reads, so `x` is the byte (or
  `eof`). `stdin-ready?` asks without waiting.
- **A change of size: a message, or ask again?** Ask again: cheap, and a
  front end asks as it redraws. A message would need signals, a later
  member of the family.

Built: the runtime reads the standard input itself (`tty`, the crate's
one module of system calls, `libc` as `fixpt-native` has it), one buffer
for lines and bytes, so they mix. Raw mode is the usual one but for
output, left as it was so that a newline still begins a line. Tests:
`programs/io/io-bytes.fx`, `io-terminal.fx`, `io-terminal-unsaid.fx`
(both checkers); `programs/processes/pselect-key.fx` (every way),
`pselect-key-arm.fx` (refused, both parsers' words); `fixpt-cli/tests/
io.rs`: `the_standard_input_read_by_bytes`, `a_process_waits_for_a_key`
(a key after the wait began, the end, the deadline), on five machines,
and by hand on the other four; by hand on a pseudo-terminal (`script`):
raw mode, no echo, ^C a key (3), and the terminal back in canonical mode
with echo after a program that failed while raw.

## 96. The evaluator ran every definition again with each form (found 2026-10-14)

The evaluator written in FX-26 (`fx-ast-eval`) was given, with each form,
the text of every definition before it (and of every expression that
wrote), and ran them all again: it kept no state between forms, and
rebuilt it by replaying, which was sound while nothing replayed could be
seen. With I/O and processes it could: a definition that wrote, then four
forms, wrote six times; a process a definition spawned ran once per later
form. Found testing `read-byte` (§95). The user suggested not running
again what does I/O; but the values of what was not run again would be
missing (a process's address), so the evaluator now keeps its state.

Each form is checked after the forms before (`check-more`, as the
compiler's forms are) and run once with the globals they made
(`run-checked-more`, `Session::eval_form`). What the checker says of a
place (an `extract`'s offset, a module to reshape, a `with`'s values) the
evaluator looks up when the code runs, perhaps long after, in a closure
or a process an earlier form made; so each form's positions begin past
every text given before (`syn::eval_more_with_fx26_evaluator`, the reader
and the loads' scan given a base, as module files are), and the facts
of every form are kept together. A whole program
(`eval_with_own_evaluator`) still begins again. Test: `fixpt-cli/tests/
io.rs`, `each_form_runs_once` (`programs/io/once.fx`: a definition and an
expression that write, a process a definition spawned, then `main`), on
five machines; the old evaluator wrote `define x` seven times.


## 97. Code bloblets a program makes and runs (kayak's request, 2026-10-14)

Still open in `TODO.md` §97; done so far:
- **`load-input` form by form** (found 2026-10-14, fixed the same day).
  The Rust parser defines each loaded file's hidden global first, with the
  form `(define %shared:K (load-input "P"))`, whose load, while it parses
  that definition (`sharing_now`), is the file's module. The session gives
  that form to the front end written in FX-26 on the machines that check
  each form with it, whose parser read the load as any other: the file's
  `input`. The hidden global became the file's value, and the program's
  own `(with %shared:K input)` failed ("unbound variable `input`", or
  "`with` opens a module, and … is a int"). On the native-convention
  machine the refusal was a decline, so the form ran another way, which
  hid it. Now both parsers read a definition of a hidden global
  `sharing_now` (Rust: `Checker::sharing`; FX-26: `parse-define`, moved to
  `parser-top.fx`, and `sharing-now` in `parse-loaded`), and the native
  machine declines a `load-input`'s such definition, whose initializer
  alone is the file's `input`, not its module (a `load-module`'s alone is
  its module). Tests: `modules/load-input.fx` and
  `load-input-built-in.fx` (the arm64 encoder), in every run mode, whole
  and at the REPL (`fixpt-cli/tests/modules.rs`).
- **Expressions with identities; facts keyed by them, not by place**
  (the user's decision, 2026-10-15, on `docs/research/loads-and-places.md`,
  option C). Every node of the FX-26 front end's trees (`exp`, `kx`)
  carries where it starts and ends and `k`, which of the expressions there
  it is: 0 for the first in a walk that takes each before what is in it,
  1, 2, … for those a parser made there besides. Numbered after the parse
  (`parser-ids.fx`; the Rust trees alike, `ids.rs`), so that the two
  parsers need not build in one order; `tests/parser.rs` compares the
  trees, `k` included. The checker's facts, the compiler's tables (one of
  them keyed by `a·2²² + b`), the evaluator's, the words a body made, and
  the Rust checker's facts handed to the FX-26 compiler are keyed by the
  identity, a product `k-at`. The Rust compiler finds the word a body made
  by its `ExpId`, not its span, as the FX-26 one by its identity: a
  module's `up-` and `down-` conversions share a span and now have a word
  each.
- **The places invented for made expressions, gone** (2026-10-15): in both
  parsers a made expression is at its origin's span, the form or the
  binding, branch or arm it was made for (`extend`'s `with`, a
  parameterized file's `lambda`, a `load-input`'s `input`, a quote's
  `%quote`, `nil` and vector, `spawn`'s, `par`'s, `race`'s and
  `pselect`'s pieces), where each had a place of its own, of no width or
  cut from another's, so as not to collide. The Rust compiler's plans,
  liftings, specialized copies and effect summaries are keyed by
  expression, not span (`Checker::effect_summaries_by_exp`).
- **Facts as a datatype** (2026-10-15): a fact is a `k-noted`
  (`check-env-types.fx`: `n-datum`, `n-summary`, `n-conversion`,
  `n-apply-shares`, `n-frozen-define`, `n-plain-fx`), built so by both
  checkers (the Rust one's as sums, `syn::rust_facts`), not an integer
  whose range said its kind. And a body kept to be inlined holds what was
  found of its `extract`s and `tagcase`s in their nodes (a field of
  `e-extract` and `e-tagcase`, -1 until then, as `e-bloblet`'s), not in
  where they start (`c-resolved-at`, gone).
- **A load is its key, as Sheldon's `input`** (2026-10-15): a hidden
  global's definition is `(define %shared:key (%loaded "key" "path"))`,
  `%loaded` the module of the file its key (the path resolved, `input:`
  before it for a `load-input`) names, in both parsers wherever it is
  read; no longer a load that meant the module only to a parser in a state
  of its own (`sharing_now`, `sharing-now`, gone). The native machine no
  longer declines a `load-input`'s hidden global.
- **The native-convention machine says where the checkers disagree**
  (found 2026-10-14, fixed 2026-10-15): a definition the Rust checker
  took and the one written in FX-26 refused was "declined" and run another
  way, which hid the `load-input` bug; it is now an error saying the two
  disagree (`native_define_in`). No test program makes one.
- **What an operation takes, a datatype too** (2026-10-15, the user's
  rule: an encoding only behind an abstraction, never a bare integer whose
  bits mean things): a `k-datum` (`parser-types.fx`: `datum-field`,
  `datum-blobref-field`, `datum-layout`, `datum-array`, `datum-fits`) and
  Rust's `check::Datum`, where an `extract`'s field past `2^40` meant a
  blobref's offset and an array's length and size were `n << 32 | size`
  (`BLOBREF_FIELD`, gone). Nodes hold theirs typed (`e-bloblet`,
  `e-extract`, `e-tagcase`), `e-bloblet`'s field index no longer doubling
  as it. The run time's array operand, still one integer, is made and
  taken apart in one place each: `layout::array_operand`,
  `array_operand_parts` and `ARRAY_OPERAND_LENGTH_SHIFT`/`SIZE_BITS`
  (machine code's too), and `parser-types.fx`'s `k-array-operand`.
- **A reshape's positions, a datatype** (2026-10-15): `k-pick`
  (`check-env-types.fx`: `pick-value k`, `pick-path k j`) and Rust's
  `check::Pick`, where a path was a position past `2^40`, `2^40 + (k <<
  20) + j` (`RESHAPE_PATH`, `reshape_path`, `k-reshape-path`, gone), taken
  apart with its constants written out in the FX-26 compiler, register
  code and evaluator.
- **Calls compiled by the convention their type says** (the user's
  question, 2026-10-14; done 2026-10-15). Both checkers note each call's
  convention at its operator (`NodeFacts::call_conv`, `n-call`). Stack
  code calls a `cellular` callee by `tcall`, which no machine checks (the
  Rust one, the oracle, traps on anything else); register code's `invoke`
  names the convention (`regcode::CONVS`, `rconv-…`): `cellular`, called
  with no look on the register machine; `native`, natively its code called
  with no look (`direct.rs`), and called out to the foreign stub with none
  where `cellular`; `fx`, looked at, as are the calls a compiler makes
  itself (a lifted procedure's, `apply`'s, a specialized copy's). For
  that to be sound a value is what its type says: in the cellular
  convention every closure is cellular; in the native one, every closure
  cellular code makes (where the native compiler declines) is made in it,
  an adapter over it (`nclosure`; `%region-nclosure`, in the closure's
  own place; `ncallcc` and `ncallcomp`, a continuation), the adapters
  sharing one code bloblet so that one is known by it (`Heap::adapted`):
  the native compiler compiles what one adapts, cellular code calling one
  calls what it adapts with no crossing, a `letrec`'s patch writes through
  it (`%fx26-adapted`), and the routines given a procedure take a native
  one as cellular code (`as_cellular`). Cellular code's calls typed
  `native` still look: the callee may be such an adapter, which it calls
  through what it adapts rather than by crossing to native code and back.
  Sessions, tests and the bench that run code natively type it so (the
  oracle's trap found four that did not). Native `closures` 21 → 20 ms.
  Tests: `what_cellular_code_makes_is_native` (`made-native.fx`),
  `a_place_holds_its_closures_adapter`.
  Fixed on the way (2026-10-14), found by made procedures: on the arm64
  cellular machines a typed tail call of a native closure stopped ("no
  routine is numbered 40": the Rust machine made the call, then returned
  from the word, which `run_routine` took for an error), and register code's
  `invoke` crashed on one (it read the callee's word's twin); now the return
  is made, and `invoke` calls a native closure out to the Rust machine
  (`programs/made-code/typed-calls.fx`).
- **`(import m name … (type name …) (effect name …))`** (2026-10-15, the
  user's; `docs/fx26.md`, Modules): what a module gives, by name, defined
  where it is, each as `(define x (with m x))`, `(define-type t (select m
  t))`, `(define-effect e (select m e))` would; expanded as it is read, in
  both parsers (`Checker::expand_import`, `parser.fx`'s `expand-import`),
  wherever a definition may be. The front end's 1176 one-line imports are
  236 lines of `import` (`parser-exps.fx` 999 → 845 lines, `check-rules.fx`
  1041 → 1025, its debt lowered). `sexp-edit` knows it (an `import`
  defines its values and uses its module); `fx26-mode` highlights it.
- **The declaration as data a generator reads** (2026-10-15, the note's
  step 6). `(load-input "fx26:convention.fx")` reads a declaration's
  clauses, as `native-convention` gives them, into a `convention`
  (`convention-types.fx`): a product of the registers, the values' tags,
  immediates, kinds and header fields, closures, code, frames, the
  state's fields by name, the routines (each its entry's offset, its
  inputs' registers, its output, whether it may collect; `overflow`'s and
  `trap`'s own), fuel and the barrier. Reading is total, then the value
  is printed back, and a declaration it does not print back to is
  refused at the first clause that differs (`cv-read`: `ok` or
  `refused`). `cv-native` is fixpt's own. A generator takes a
  `convention` rather than numbers copied out of fixpt. Tests:
  `programs/made-code/generated.fx`, `frames.fx`'s procedure made from
  the convention by the arm64 encoder written in FX-26, word for word
  the code `frames.fx` writes out, and run on all nine machines
  (`code_made_from_the_convention_read_as_data`);
  `programs/modules/convention-read.fx`, three refusals. The evaluator
  written in FX-26 gained `substring` and `char-numeric?`.
- **Primitives reached through fields, not numbers** (2026-10-15, the
  user's question why kayak would need fixpt's numbering). A program puts
  the primitive, a procedure value, in a field of the code bloblet it
  makes, and the code calls it as any procedure; no routine calls a
  primitive by number, and "primitives by name" is no longer to decide
  with kayak (`declared-conventions.md`, "Primitives, through fields").
  Test: `programs/made-code/linked.fx`, `(* x x)` by `*` in field 0, a
  hundred thousand calls with `poll` among them, then a procedure of the
  program's own, on every machine and stressed. Fixed on the way: the
  bytecode VM's `*` is its primitive object, which native code's
  `foreign` refused ("a call of what is not a procedure"); a simple
  primitive now runs as it is (`cellular::call_value`).
- **A bloblet made by made code: the `bloblet` routine** (2026-10-15).
  At the state's field `bloblet`, as `cons` is: from `blr`, the suffix's
  bytes in `x1` and the count of fields in `x2`, fixnums; a stub's frame
  and call-out 9 (`common_bloblet`, `Callout::Bloblet`), which may
  collect; a plain bloblet in `x0` (kind `bloblet`, its trailer field 1,
  the rest the fixnum 0, its suffix zero), as `%make-bloblet-filled`
  makes; for sizes that refuses, the trap (`a primitive failed`). The
  declaration states it, `(makes (kind bloblet) (trailer 1) zeroed)` and
  `(traps-when-refused 3)`, and a `convention` holds it. Test:
  `programs/made-code/allocated.fx`, `(pack s k)` made from the
  convention: `s` and `k` stored in the fields, each store marking its
  card; twenty thousand kept across collections; a size of -1 refused;
  on every machine and stressed (`a_bloblet_made_by_the_routine`).

## 98. The reader's types apart, and one-shot continuations (kayak's requests, 2026-10-15 and -16)

- **Request A: the reader's types split** (2026-10-15). Kayak's survey
  of the front end found 68 files stopping at `eager-reader-types.fx`,
  for `state`, `cont` and `state-rest`: the eager reader's coroutine
  states, which hold composable continuations, which KFX refuses. They
  are now in `eager-reader-states.fx`, which only `eager-reader.fx`
  loads; `eager-reader-types.fx` (`syn` and its relatives, the cursors,
  the reader's effects) mentions no continuation. Nothing else used them:
  `reader.fx` takes `state` from the eager reader's module, and every
  other file that loads the types checks and runs without them. Further,
  so that kayak can use the parser as written with a reader of its own:
  the parser loaded `eager-reader.fx` for `syn->datum` alone, which is
  now in `syn.fx`; the parser loads the types and `syn.fx`, and no
  reader. `reader.fx` loads the eager reader itself, so the reader's
  licence names two makers, `make-eager-reader` and `make-reader`
  (`licence.rs`, `READER_MAKERS`). What still reaches a composable
  continuation, through its loads: the eager reader and `reader.fx`;
  the evaluator written in FX-26 (`eval-types.fx` and the files loading
  it, and `conductor.fx` through them), whose continuation values are
  FX-26's own; and the scheduler, `processes.fx`.
- **Request B: one-shot composable continuations** (2026-10-15).
  `call-with-oneshot-continuation`, typed as the composable capture is,
  gives a `(oneshot T A D R)`: resumed once, the rest of the prompt's body
  as a composable one's; resumed twice, the failure "a one-shot
  continuation resumed twice", the same on every machine, which defines
  the meaning (`docs/fx26.md`, "Control, typed"). One-shot is in the type:
  a flag on `Ty::Composable` (`once`) and on the checker written in
  FX-26's `ty-comp`, read and printed as `oneshot`; neither it nor
  `composable` stands for the other; a subroutine where one is wanted, as
  a composable one is. Not checked statically (affine types). At run
  time: routines `callone` and `ncallone` (the native convention's),
  `callcomp`'s with the continuation they take marked `Shots::Once`,
  where every machine checks it on a resume (`Heap::take_shot`): the Rust
  word machine (the others call out to it), the native word machines'
  `control.rs`, and the native convention's `direct.rs`, whose
  continuation's data is now always eight values (`NATIVE_CONT_LEN`);
  the Scheme lowering wraps the continuation in Scheme
  (`%fx26-call/one`); the evaluator written in FX-26 keeps a flag of its
  own beside the machine's one-shot continuation (`o-once`), so it fails
  as it fails. Nothing captured is copied for it. Tests:
  `run/oneshot-once.fx` (43) and `run/oneshot-twice.fx` on all nine
  machines (`fixpt-cli/tests/one_shot.rs`) and through both compilers;
  `control/oneshot-*.fx`, both checkers alike
  (`a_one_shot_continuation_is_its_own_type`). Our own code: the
  scheduler (`processes.fx`) takes a waiting task's continuation one-shot,
  as it resumes it once. The eager reader's stay composable: the line
  editor resumes a kept checkpoint again after an edit (`fixpt-scheme`'s
  `eager.rs`), so they are resumed more than once.
- **Request C: the reader's working types apart** (2026-10-16). Rerun
  after A, kayak's survey found the 70 files loading
  `eager-reader-types.fx` stopping at `cursor`, a type abbreviation that
  mentions itself: a recursive structural type, which KFX refuses (Rust
  has no recursive aliases; KFX keeps recursion to datatypes). `cursor`,
  `cursors`, `result`, `word` and `atom-in`, the reader's own working
  state, are now in `eager-reader-states.fx` beside `state`; nothing
  outside `eager-reader.fx` used them (the parser imported `result` and
  did not use it). `eager-reader-types.fx` holds `syn`, `syns`, `chars`,
  `data`, `context`, `closers` and the reader's effects. A refactor only.

## 99. A wait for a key sometimes ends at its deadline (found 2026-10-15)

Not fixpt's: the test's. `a_process_waits_for_a_key` starts its 27 runs
from 27 threads, and on macOS Rust's `Command` makes a child's pipes and
only then marks them close-on-exec, so a child another thread starts in
between inherits them. The input-end case's pipe, so inherited by the
no-input case's child (which lives a second, to its deadline), stayed
open after the feeder closed it, and the program saw no end before its
own deadline: exit 1, nothing on stderr. Traced: the scheduler waits for
the input and the deadline together, and `poll` reports a closed pipe at
once; on `fx-regs-rsjit-cellcc` the program starts about 300 ms in, as
the input is closed, the window. Fixed in `fixpt-cli/tests/io.rs`: every
child is made under one lock (`spawned`, `output`), which also keeps a
broken pipe broken (`a_failed_write_is_a_value`). Before, 2 runs in 15
and 2 in 20 failed; after, none in 60. Other test binaries pipe to
children their tests make in parallel too; there an inherited pipe only
delays an end, which no test there times.

## 100. Our own FX-26 code in `->*` (the user's, 2026-10-16)

`(->* (T…) T)` (`docs/fx26.md`, the kernel's table) was tried on the whole
front end, then done (the user's, 2026-10-16): every definition typed `(subr EFFECT …)`
whose value is a `lambda` (3,259 of them, `define*` among them) rewritten
to `->*`, then each that does not check put back.

- **What it found.** 16 put back, all values a module makes by calling
  its own lambda (`ev-prims-made` calling `ev-int-prims!`, say), which
  `->*` refuses. Of 3,946 module lambdas, 2,160 kept their effect; 1,639
  were found narrower: `(read @globals)` became the globals read, 1,139
  times; `spin` dropped 383 times (procedures the termination checker
  shows end); and region atoms (`alloc`, `read`, `write` of `@t`, `rs`,
  `rm`, `@k`) dropped where a broad name (`checks`, `kstate`) was written
  as a signature. 147 read more globals precisely than `define*` found.
- **Not to convert:** `processes.fx` and `conditions.fx`. `%sched` and
  `%processes:` say nothing of what the tasks they run do (a program
  cannot name them, `check::built_in_only`), so what `->*` finds there is
  too small; the effects written (`sched`, `any`) are the truth.
- **What it costs.** The compiled front end runs no faster or slower
  (`fixpt bench`'s compile table, back to back). Checking it costs more:
  loading it without the cache 0.95 → 1.10 s (+16%, Rust), the bootstrap
  tests 72.5 → 86.2 s serially (+19%), from finding what each procedure
  does and proving more of them end. (Before 07861e28 and cc9a7c33, +54%
  and +40%.)
- **Found and fixed on the way:** 43d00eef (a tried form left `->*` ids
  behind; a module's `->*` type lost its mark where its imports are
  resolved), e1b8e5af (a module's group noted once per member).
- **Done:** converted mechanically (`(subr E P R)` to `(->* P R)`; load;
  put back the definition the first error names; again). 21 files 40
  lines shorter, none longer; `regcode-core.fx`'s debt 1124 → 1122.

## 101. Benches taken on a busy machine, taken again (the user's, 2026-10-16)

**Done (2026-10-17): no change in time was real.** Each commit and its
parent built side by side in scratch worktrees, then `fixpt bench` (best
of 3) three times over in rounds, the commits in order so each ran next
to its parent; every run began with a 1-minute load average below 2
(1.24 to 1.94), and each column is the best of the three rounds. The
commits' messages stay as they are; their quiet numbers are here.

Sums over the eight programs (the run table, ms) and over the nine
(`check`, `fx check`, s), parent → commit:

| commit     | `rs-regs-rsjit-nativecc` | `rs-cells-rsjit-cellcc` | `check`       | `fx check`    | real?                    |
| ---------- | ------------------------ | ----------------------- | ------------- | ------------- | ------------------------ |
| `38df01e2` | 54.7 → 54.4              | 297.6 → 293.6           | 14.58 → 14.36 | 31.98 → 31.75 | no                       |
| `093e036c` | 54.4 → 54.4              | 293.6 → 297.0           | 14.36 → 14.38 | 31.75 → 31.84 | no                       |
| `cf95f5cb` | 54.4 → 55.0              | 297.0 → 303.1           | 14.38 → 14.47 | 31.84 → 32.20 | no (each within 2 %)     |
| `26fad166` | 55.1 → 55.0              | 364.6 → 362.4           | 14.40 → 14.45 | 31.97 → 32.13 | no: not "a tenth over"   |
| `fd7c4751` | 53.7 → 54.0              | 286.6 → 286.2           | 13.92 → 13.99 | 30.70 → 30.85 | no                       |
| `cc9a7c33` | 54.2 → 54.1              | 288.1 → 288.4           | 13.83 → 13.87 | 30.74 → 30.96 | no                       |
| `4b592b9b` | 54.4 → 54.4              | 287.6 → 292.5           | 14.02 → 13.94 | 30.76 → 30.79 | no                       |
| `ba534007` | 53.6 → 53.8              | 349.4 → 352.0           | 14.32 → 13.87 | 31.51 → 30.74 | no                       |
| `bb3f5709` | 53.9 → 53.9              | 288.2 → 290.6           | 13.98 → 13.82 | 29.83 → 29.97 | no                       |

Every other column moves as little, but `rs-cells-stencils-cellcc`,
whose sum varies by up to a fifth from round to round of one build (417
to 509 for `38df01e2`): noise, there.

What the load did. Against these, the tables in the messages of the
commits benched at a 1-minute load of 4 or more (`38df01e2`, `093e036c`,
`26fad166`) run 10 to 17 % high in every column; those at about 3
(`cf95f5cb`, whose 5- and 15-minute loads were 6, and the three
borderline ones), 3 to 8 % high, as are their parents', so each
message's comparison with its parent was fair. The 1-minute load is the
one that counts, and even 3 costs a few percent.

The last two rows (2026-10-17, evening), the threshold to bench again
lowered to a 1-minute load of 3 (the user's): `ba534007` and `bb3f5709`,
benched at 2.95 to 3.13, taken again likewise, every run begun below 2.
`ba534007`'s compile phases a few percent lower are its parent's rounds
varying (`check` 14.33 to 15.06). Its message's table ran 10 to 15 %
high, its parent's 2 to 3 %, so read side by side they show a slowdown of
about a tenth that is not there; `bb3f5709`'s ran 2 to 12 % high, its
parent's 2 to 10 %.

Found on the way, not chased (interpreted machines' constant factors,
not native speed): `rs-cells-asminterp` and `rs-cells-rsjit-cellcc` on
the programs that allocate are bimodal across unrelated commits, `lists`
53 or 84 ms on `asminterp`, `closures` 72 or 93, the same words
allocated and collections made: `4b592b9b`'s fast, `595df377`'s (a checker
and CLI change only) slow, today's fast again. A layout of the Rust
side of the cellular machines' allocation, most likely; register code
and native code do not move.

## 102. A nursery not collected while native code calls a global closure (found 2026-10-16)

**Fixed (2026-10-16): a poll collects.** Found measuring the integrator
for `docs/research/raw-scalars.md` (`docs/research/examples/
raw-scalars/`): with the integrand a closure kept in a global and passed
as a value, the run made 3 minor collections and the words in use grew
without bound (121.6 M words at 300 reps, about half the run's time in
memory touched); made afresh each rep, 102.

Why: native code collects only in a call-out that is not quiet, where
the frames are walkable and the registers hold nothing live. Making a box
past the nursery's end is a quiet call-out (`BoxF64`: at any
instruction, live values in registers), and so is a poll's (`Poll`), so a
loop whose only allocation is boxing for a call through a procedure value
never collected; the closure made afresh supplied a call-out that did.

Now `Callout::Poll` is not quiet: a poll that ends a time slice collects
if a collection is due. Its frame already held what is live, mapped as a
procedure's (`emit_poll`; `common_poll`, for code a program made), since
it may call the scheduler's `preempt`, which may collect. Slices are
`sched::SLICE` (65 536) polls, so the collection comes soon after the
nursery fills. Tried and dropped: also ending the slice at once from a
quiet call-out that found a collection wanted (the fuel back in the
reserve, two instructions at every call-out): no faster (0.73 s against
0.74). The integrator's `value` variant at 300 reps: 1.35 → 0.74 s, 3 →
116 minor collections, 121.6 → 2.4 M words in use at most; `closure`
0.80 → 0.73 s. The 46 ports: the same answers and times. Test:
`programs/native/quiet-boxes.fx`, `quiet_boxes_are_collected_at_the_next_poll`
(2 M boxes: 2 collections or more while it runs; 1 with a poll quiet).

## 103. `remainder` by a constant not in line (found 2026-10-16)

**Fixed (2026-10-16).** Found with §102, measuring the integrator:
`(remainder i 2)` in a loop was a call-out, `prim %fx26-remainder`, which
saved the frame and called the runtime, about 20 ns an iteration, more
than the rest of the loop; `quotient` and `modulo` were already
`prim2imm`, in line natively. `%fx26-remainder` now never collects
(`fixpt_runtime::never_collects`, and the FX-26 compiler's
`r-never-collects?`, so both make `prim2` and `prim2imm` alike), and
native code does it in line as `quotient`: of two fixnums, a divisor not
zero, `sdiv` then `msub`, the remainder always a fixnum (the least by −1
too); else the primitive's, a bignum's or zero's. The integrator's first
version, which picked its weight so, 20 reps: about 0.16 → 0.07 s the
run alone. Test: `remainder_in_line_as_the_rust_machine_gives_it`
(`programs/native/remainder.fx`: each sign, a constant divisor and not,
the least fixnum by −1, a bignum, by zero). The 46 ports: the same
answers and times (three use `remainder`, none in a hot loop).

## 104. A prompt tag held across a collection at a capture across machines (found 2026-10-16)

**Fixed (2026-10-16).** Found with §69: `deep_recursion_through_the_stack_cache`
failed, `captures.fx`'s second list giving "no prompt for this tag", once
§69's files changed what the front end, loaded into the same heap,
allocated (the program's code was the same). A capture in cellular code
whose prompt is in the frames of the native code out from it
(`Machine::capture_across`) runs a safepoint first, and kept `proc_`
across it on the data stack but the tag in a Rust local: a collection
there that moved the tag (a major one, here) left the frames out, put
back as the heap had kept them, holding it where it now was, and the
search (`crossing::capture`) looking for where it had been. The tag is
kept on the data stack too now. Test:
`a_tag_moved_at_a_capture_across_machines_finds_its_prompt`
(`programs/native/capture-across-collecting.fx`: such captures under 0
to 3 cellular frames, collecting at every safepoint, so that some
capture's safepoint is a major collection's; it gave "no prompt" before).

## 113. A memory test of the x86_64 box (the user's, 2026-10-17; settled 2026-10-24: the memory)

One `fixpt` run in about 8,000 fails on the x86_64 box (a Threadripper
3990X), most likely a hardware fault, not `fixpt`'s. It was found as one
failure of `modules.rs`'s `module_programs_run_alike_in_every_mode`,
then hunted with `fixpt --fx26-run cellular eval load-input.fx` (in
`crates/fixpt-fx26/tests/programs/modules`) run some 40,000 times. Each
failure is a word that is right but for one high bit set:
- three fixnum cells of a register word, which `assemble_register_word`
  reads as 5 + 2^57, 5 + 2^54 and 17 + 2^57;
- a code-space offset with bit 63 set, in `install_bytes`;
- the first failure, a `char` that is no character, which fits a high
  bit set in a byte of a Rust string.

Why the hardware:
- the one failure recorded by `rr record --chaos` does not replay: `rr`
  says the replay diverged. All 25 passing recordings replayed;
- nothing in the heap, the compilers or the code they make sets single
  bits in a word's top bits;
- address randomization is not needed: one failure in 5,000 runs came
  with it off (`setarch -R`).

Against it: bit 57 of a fixnum came twice. And every failure came while
other work loaded the box (load averages 150 to 600, memory nearly full,
swap in use).

For it, on the arm64 Mac (2026-10-23, an M-series with 18 cores, the
commit after f6ffaaf4): the same program run 40,000 times, 14 at a time,
with no failure. 30,000 on `fx-regs-rsjit-cellcc` (register code, whose
`assemble_register_word` read the bad cells) and 10,000 on the default
`fx-regs-rsjit-nativecc`, each from `crates/fixpt-fx26/tests/programs/modules`
as `fixpt --machine M eval load-input.fx` (the command line since
2026-10-22; `--fx26-run` is gone), its output compared with a first
run's. At the box's one in 8,000, five failures were to be expected;
none comes by chance less than 1% of the time (e^-5). So a `fixpt` fault
would have to be one of x86_64's code alone.

Settled (2026-10-24, the user's): the box's memory was faulty over that
time. Left open only were the next steps, now not needed: the memory
test with the box idle, and in software, checking a word's cells when
the front end writes them and again when `assemble_register_word` reads
them. What had been planned for them:

To do, with the box idle: MemTest86+ booted from USB, or `memtester`
over most of its memory. See whether the memory runs at a factory
overclock (XMP/EXPO). The kernel has no EDAC memory controller here
(no `/sys/devices/system/edac/mc/mc0`), so corrected or single-bit
errors are not logged. If the memory passes, the next step is in
software: check a word's cells when the front end writes them, and
again when `assemble_register_word` reads them, to see whether the bit
is set at the write or after it.

## 114. `webs` is quadratic in a procedure's instructions (found 2026-10-22)

**Fixed (2026-10-22).** The native convention's representation pass
splits each frame slot into webs: its writes and reads, joined where a
write reaches a read. Both versions, Rust's `webs`
(`fixpt_native::direct::reps`) and FX-26's `nr-webs` (`native-reps.fx`),
searched back from each read with a fresh `seen` array as long as the
procedure: O(reads × instructions). They now go a slot at a time over
the procedure's basic blocks. Where a slot is live and some write of it
has been, every write that reaches there reaches a read, so one web
holds them: the blocks where the slot is live (back from the blocks that
read it first, through blocks that do not touch it), those of them a
write reaches, and a union-find of each block's start and the slot's own
reads and writes. A slot's work is its own accesses and the blocks where
it is live. The FX-26 version is in a file of its own,
`native-reps-webs.fx`, as `native-reps.fx` would have passed 1000 lines.

Done by instruction, not block, a slot at a time was slower than the
search: the front end's largest register words are module bodies, one
block of 7,000–8,100 instructions with 600–800 slots, some 255 slots
live at each instruction. By block, on the largest (8,102 instructions,
795 slots), the FX-26 split (`nr-split-slots`, `webs` with the
`demands` and `reps_of` it runs) lowered on the bytecode VM: 40.8 s →
4.1 s. `native_reps`, the pass as register code, every word: 92 → 32 s,
with the webs now compared too.

Test: `native_reps` compares the two versions' webs on every register
word of the front end (`Facts::webs`, `nr-web-names`: by instruction,
the first instruction of its web, whether an `f64`'s, whether read).
Before, it compared only what webs decide (raw slots, the split), and
the front end has few `f64`s, so the webs themselves went mostly
unchecked; a wrong partition now fails it. While the change was made,
`webs` also ran the old search and asserted the same partition: on all
the front end's words (168,576 accesses joined), the native tests, and
the four `f64` benchmarks (`nbody`, `spectralnorm2`, `matrix-multiply`,
`mandelbrot`) on `fx-regs-rsjit-nativecc` and `fx-regs-fxjit-nativecc`.

## 127. Syscalls (kayak's request, 2026-10-26)

One extension, so that runtimes written in FX-26 gain capabilities without
further changes to the language: `define-syscall`,
`define-optional-syscall`, `syscall-available?` and the effect `(io sys)`,
with a declared type compared with the runtime's as canonical text
(`docs/fx26.md`, "Syscalls"). Kayak's request is
`docs/research/syscalls.md`, Fixpt's copy, whose last section, "What
Fixpt does", records what differs from it and the open questions decided.

- **Both checkers**, each the other's twin (`syscall.rs`; `check-program.fx`
  and `check-print.fx`), compared on what they accept and each refusal
  (`tests/checker.rs`, `syscall_declarations_alike`). A declaration expands
  into two ordinary definitions, so every machine runs it as it runs any:
  `fixpt_runtime::syscall` holds the runtime's table and its three
  primitives; the evaluator written in FX-26 has a table of its own.
- **Fixpt's syscalls**: `code:exec-view/1` (always -1: a flat array moves
  when collected), `code:page-words/1`, `code:flush/1` (nothing to flush).
- **Containment**: `fixpt --syscalls`, or a module file built in.
- **Tests**: `fixpt-cli/tests/syscalls.rs`, `programs/syscalls/` on every
  machine, alike: the three called; an optional one absent (`#f`, a call's
  failure); a required one missing, and one at another type (its message
  shows the canonical form: aliases expanded, effects sorted and deduped,
  regions renamed); an ordinary program's declaration refused.
- **Not yet**: the FX-26 compiler's entry for trees the Rust checker
  checked (`compile-program`, `fixpt compile`'s comparison) refuses a
  declaration, having no canonical form to expand it with.


## 128. Every procedure's code runs (kayak's request, 2026-10-26)

Native code calls any procedure as it calls native code, with no test of
what it is: the convention's `closures` clause is `(code-always-runs)`
(`docs/research/declared-conventions.md`). Kayak's request is
`docs/research/code-stubs.md`, Fixpt's copy, whose last section, "What
Fixpt does", records what differs from it and the open questions decided.

- **The code area in two parts** (`fixpt-heap`'s `heap/code.rs`): below
  `code-lo`, every cellular word, its suffix a stub that enters `foreign`,
  and the stub the other kinds of procedure share at their field 2 (the
  VM's closures, primitives and continuations, and cellular
  continuations, whose layouts change by a field); from `code-lo`, native
  code. Images carry the area (format version 8); graph copies keep code
  code; process messages share it.
- **The compilers** drop the test: the Rust ones on arm64 and x86_64, the
  one written in FX-26 on x86_64, byte for byte the Rust one's still.
- **Code written to the older clause** runs, unchanged: both checkers
  accept it, a word is below `code-lo` as before, `foreign` takes a native
  closure too, and the convention read as data keeps the older test's
  field.
- **Tests**: `made-code*/stubs.fx` on every machine (a primitive, a
  continuation, a closure kept cellular, with no test; the VM's
  continuation refused by `foreign`); the stub's bytes against both
  assemblers; words and images in `code_area.rs`.


## 129. `attempt`: a failure caught at a cancellable body (Heist's request, 2026-10-26)

Heist, the editor on FX-26 (`~/Dev/LangPlay/heist`), needs a command that
does `(car nil)` to end with a message and leave the editor running. It
carried this in its subtree of Fixpt (`FIXPT-CHANGES.md` there, F1).
`(attempt e on-failure)` is `race2` with one branch (`attempt1`,
`processes.fx`): a failure in `e` gives its message to `on-failure`.

- **`e` is held to `race`'s rule**, that nothing it does is left half
  done (`cancellable`, `k-cancellable`, factored out of `race`). So its
  body is a task's boundary, and §86/§89's "`error` is caught only at a
  task's boundary, never in place" stands.
- **On all twelve machines**, both checkers agreeing (`programs/attempt`,
  `preempt.rs`). `attempt1` is in the `k-built-in-only` table.
- **A hazard Heist's harness found**: the scheduler's prompt tag is kept
  once in the runtime's state (`%sched` 12 and 13). A session that runs
  the evaluator written in FX-26 after a compiler, or a compiler after
  it, fails at `(race 1 2)` with "a prompt tag is expected".
  `programs/attempt`'s evaluator way has a session of its own
  (`common::with_own_eval`); a real run uses one way.
- **Not yet**: a richer failure value than the message; heap exhaustion
  caught; an `attempt` cancelled from outside (`C-g`, §106).


## 130. The evaluator's failed task kept quiet (Heist's request, 2026-10-26: a bug)

Heist's F2. On `fx-ast-eval` only, a monitored task that fails stays the
current task until `run-task` takes its failure (op 37). If the
evaluator's tick fell in that window, `preempt` suspended to a prompt that
was just left: "no prompt for this tag". It is older than `attempt`:
`race` branches and monitored processes fail the same way. Now
`op::TASK_FAILED` (`sched.rs`) makes the failed task quiet when the tag is
returned. The reproduction is `programs/attempt/evaluator-after-failure.fx`.


## 131. `type-at`: the checker's type at a place in a program text (Heist's request, 2026-10-26)

Heist's F3, for the editor's `C-c t`: `type-at : (subr (io fs-read)
(string int) string)`. It checks the text with the session's checker
(`record_types`, `typeat.rs`) up to the form the place is in, and gives
`"START END TYPE"` or `"error START END MESSAGE"`, in characters.

- **A primitive**, `%fx26-type-at` (509, after the syscall primitives),
  through a hook the session installs (`Runtime::type_at`), since the
  checker is above `fixpt-runtime`. The evaluator written in FX-26 calls
  the host's. Whether it should be a syscall instead is open (`TODO.md`
  §131).
- **Named types printed by their names**: printed with no names
  (`Checker::print_expanded`), then each named type's text put back,
  longest first, families applied to named types too: `(subr pure
  ((actor frame) command) (msg buffer))`, as written.
- **On all twelve machines**, alike (`programs/typeat/basic.fx`). On
  Heist's own program (220 KB): 69 ms near its start, 0.5 s near its end.
- **Not yet**: text past an error; the instantiations and effects at a
  place (R10's flow analysis).


## 132. Programs run beside this one: `(io process)` (Heist's request, 2026-10-26)

Heist's F4, for `M-x compile`, `grep`, `M-!` and `shell`. A twelfth I/O
kind, `(io process)` (code 11, after `(io sys)`), and six primitives:
`process-start` (a program, its arguments, a directory;
`(sumof (started int) (failed io-error))`), `process-output` (what it
wrote since asked, never waiting), `process-status` (`running`, `exited`,
`signalled`, `unknown`), `process-write`, `process-close-input`, and
`process-signal` (to its group).

- **The runtime**: a table of processes in `World`. A thread per process
  reads its output and error, as one pipe, decoding UTF-8. Each process
  gets a session of its own (`setsid`, in `tty.rs`), so a shell cannot
  take the editor's terminal.
- **FX-26 proper, not a syscall**: the types (`listof string`, `sumof`)
  cannot cross as a syscall's (§127).
- **On all twelve machines** (`programs/process/basic.fx`), both checkers
  agreeing.
- **Not yet**: a `pselect` arm (`TODO.md` §132); a pseudo-terminal;
  environment variables; output and error apart.

## 133. Queries by type and effect: `,query` and `fixpt query` (2026-10-27)

At the REPL and from the command line, which definitions of a program
have an effect (`effect (write @ed)`), mention a type (`uses T`), give one
(`returns T`; without needing one, `constructs T`; only for one,
`transforms T`), take one for nothing back (`consumes T`), or may write what one holds (`mutates T`): each with its
type and its place, module items too (`docs/fx26.md`, "Queries";
`fixpt_fx26::query`).

- **The program checked again**, its sources each a file of its own, so
  that a place is a file's line and column: the REPL keeps what it
  defined, form by form and file by file, where each was.
- **Giving and needing, as the customer given a value sees it**, by
  polarity, and a `T` given *tolled* when reaching it means calling a
  procedure whose arguments oblige the customer to make one, and a `T`
  taken a *trade* when the exchange gives one back: so `((() -> T) (T ->
  unit) -> unit) -> unit` constructs and consumes, and `((T -> T) -> unit)
  -> unit` only transforms, though each mentions `T` once each way.
- **A type named at a program's end** has a module's effects and types
  selected before the module was known put in, as `type-at` prints them.
- **Tests**: `fixpt-cli/tests/query.rs` on `programs/query/` (seven shapes
  of procedure; effects, definite and may; mutation through a procedure
  returned), and at the REPL.
- **Local names bound to a polymorphic definition instantiated** so that
  it answers, where it does not as it is: `(let ((wipe (proj clear!
  @ed))) …)`. Calls and other unnamed uses are left out: hundreds of `car`
  at a list of ropes, on Heist's editor, said nothing.
- **Named types printed once a question**: `typeat::Namer`, the table of
  names made once, not for each type printed (16 s to 2.2 s for 280
  answers on the editor).
- **`around CONTEXT`**: the local names in scope at a place
  (`FILE:LINE:COL`), or bound in a definition, a module's item or a file,
  that answer: a lambda's parameters, a `let`'s and `letrec`'s names.
- **Not yet**: a `tagcase` arm's names and a `typecase`'s among the
  locals; an entry the REPL holds (`,pending`) among the sources.

## 134. A procedure type's parameter is named `(x : T)` (the user's, 2026-10-27)

- **`(x : T)`** names a parameter in a `subr`, `->` or `->*` type, for
  later types to select from (`(subr pure ((c : sig) (select c t)) int)`)
  and a specification's clauses to name (`(-> ((n : int)) int (requires (>
  n 0)))`). `(h T)` is always `h` applied. Before, `(h T)` was a named
  parameter whenever `h` was not a type name known where it was read, so
  a family an `include` or a `with` gives, known only when the module is
  typed, was taken for a name: `(box thing)` became a parameter `box` of
  type `thing` (Heist's problem A). FX-91 has no such ambiguity, every
  parameter of its `subr` being named; Typed Racket writes `[x : T]`.
- **Errors that say what to write**, at the parameter: where what follows
  names `h`, `` `(c …)` applies `c`, but `(select c t)` after it names `c`:
  to name a parameter, write `(c : type)` ``; where nothing does and `h` is
  no family, `` `n` is not a description function: … ``. In a module with
  `include`s or a `with` body, `(h T)` that nothing after names is the
  family applied.
- **Printed** as written, `(x : T)`, in a type with a specification.
- **Migrated**: Fixpt's FX-26 programs, tests, `assert` and `assume`, and
  the reference docs (`fx26.md`, `fx26-grammar.md`).
- **Tests**: `modules/include-family-param.fx` (Heist's), `param-misnamed*.fx`.

## 135. Heist's module problems B, D and E (2026-10-27)

From Heist's report (`docs/research/derived-signatures.md`, "The problems
Heist found"); A is §134.

- **B: a `with` of a module a `let` binds to one written there** binds
  that module's values in its body, for the check that an item names
  nothing made after it: `(define f (lambda () (let ((m (module (define f
  …)))) (with m (f)))))` named `m`'s `f`, but was refused as using itself.
  The values are those the module's type will give: none hidden, and none
  known if it has `include`s (then, as before, every name counts).
  `free_into_in` and `k-free-in` carry them by where the `let` bound the
  name, so a name bound again inside is not mistaken for it
  (`modules/with-local-module*.fx`).
- **D: a module file's `include`s** give their types by name in its items,
  in the FX-26 checker as in Rust's: the mark that says a module includes
  others looked at the module's first item, which in a file is the one that
  says the file, so every file with an `include` whose items named an
  included type was refused there, with or without `module-parameters`
  (`modules/include-in-file.fx`, `include-in-params-file.fx`). Found with
  it, not fixed: a file's item using an included *value* compiles to other
  words in the compiler written in FX-26 (`TODO.md` §133).
- **E: `fixpt run`'s loads** are from each program file's directory, as
  `fixpt eval`'s and `,load`'s are; it had used the current directory.
  The docs said neither that nor that a loaded file's own loads are from
  its directory, and now say both (`fixpt-cli/tests/run_loads.rs`).

## 136. A file's module type: `load-moduleof` and `load-input-moduleof` (2026-10-27)

Heist's request (`docs/research/derived-signatures.md`), the user's names.

- **`(load-moduleof "file" arg …)`** is the type of the module a
  `load-module` of the file makes given `arg …`; **`(load-input-moduleof
  "file" arg …)`**, of the module a `load-input` file's value makes. The
  arguments take the value's type apart: a `poly`'s descriptions, a maker
  of no parameters applied, a procedure's parameters each a module's name
  where the types after select from it. What is left must be a module's
  type. A file that is a function of the modules it uses types each by the
  file that makes it, with no signature written out or kept in step.
- **Abstract types are binders**, not shared and not fresh constants: a
  parameter of the type stands for its argument's (the user's question,
  the research note's Q2), so modules a maker makes twice stay apart.
- **Loaded as loads are, in one order**: a form's type loads first, then
  its expressions', in each parser (`type_loads`, `type-loaded`, which
  makes them `(%type-made %shared:key "file" arg …)` for the FX-26 checker)
  and in what the driver reads for the FX-26 front end (`syn.rs`), so the
  hidden globals, and the files' places, are the same in both.
- **A `define-type` of one is read in order**, not ahead with the other
  types, since its file's hidden global is defined before it.
- **The FX-26 checker's reading in a file of its own**,
  `check-read-made.fx`, before the types' reader, which gives it its
  description reader; `check-program.fx`'s own copies of `k-has-name?` and
  `reverse` dropped for room.
- **Stage 0's fixed cost unchanged**: 12.23-12.30G cycles against
  12.18-12.29G; 28.37G instructions against 28.32G.
- **Tests**: `modules/load-moduleof*.fx`, over `module-files/made-*.fx`.
