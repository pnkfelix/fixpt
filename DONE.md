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
