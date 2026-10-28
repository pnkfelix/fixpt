# `stage`: FX-26's `eval`

Design note, 2026-10-28, from a discussion with the user: what FX-26, Fixpt
and kayak would have to change for a running program to read, check and
run code it is given, as Scheme's `eval` does. Wanted by Heist's editor
(`TODO.md` §105; Heist's `docs/fx26-for-yank.md`, R4): the init file,
`M-:`, `C-x C-e`, and commands, keymaps and hooks defined by user code at
run time. Nothing here is implemented. "Decided" below marks the user's
answers (2026-10-28) to the first draft's open questions.

## The claim

The language changes little: forms that check code against a type and an
effect, one effect atom, and, for definitions that last, one kind of value
(sessions). It does not need a top effect (`PLAN.md`'s item 5, `any`) or a
type of every value (§108's alternative). In Scheme `eval` is unsafe
because nothing checks what it runs. FX-26 has a checker to call at the
time the code arrives, so the caller says what type and effect it accepts,
and the checker holds the code to them. Contrast `native-procedure`
(`docs/fx26.md`, "Code a program makes"), which *trusts* code at a stated
type and so carries `(io native)`. Staged code is trusted nowhere.

Fixpt has most of the machinery already, in the REPL. Kayak's difficulty
is not the language but the boundary between the Rust its programs become
and the engine that would run the new code.

## The forms

**Decided: the name is `stage`**, not `eval`: the form does not run the
code, it makes it ready to run, a stage in the sense of multi-stage
programming. It is two steps, which may also be written apart:

```
(expand m text)                          ; => (sumof (ok expanded) (failed stage-failure))
(install m T e (p body) (why else))      ; e : expanded
(stage m T text (p body) (why else))     ; expand, then install
```

- `text` is a `string`, or a `datum`, so that a program builds code
  without printing it first.
- **`expand`** reads `text` and expands its macros (below), giving
  `expanded`: kernel syntax with its spans, opaque to the program. Its
  effect has `spin`.
- **`install`** checks `e` as the body of a `(lambda () …)` of type `T`,
  compiles it, and runs `body` with `p : T` bound to that procedure. `T`
  is a procedure type of no parameters, `(subr E () R)`, written at the
  form. Its effect has no `spin` (below).
- On failure, `else` runs with `why : stage-failure`, a sum of a read
  error, an expansion error, a refusal, and (for sessions) a redefinition
  refused; each with its message and a span in `text`. Nothing is printed
  on the side.
- `m` is a module, a value of a `moduleof` type, and is the code's
  environment: `text` is expanded and checked as if in `(with m …)`, over
  the standard bindings (`#%fx`). Nothing else of the program is in scope.

```
(define editor-api
  (module
    (define insert! (subr (maxeff (write @buf) (io terminal)) (string) unit) …)
    …))
(define-type command (subr (maxeff (write @buf) (io terminal) spin) () unit))
(stage editor-api command "(lambda () (insert! \"hi\"))"
  (c (add-command! "say-hi" c))
  (why (show-failure why)))
```

### Why forms, not procedures

The static checker knows `T` and `m`'s type at the form, so it can give
the checker that runs later their descriptions as literals, as it gives
`native-procedure` its `T`. Types need not exist as values at run time,
and no `typeof` or reflection is added.

### Variables `T` and `m` take from around the form

A type, region or effect variable that `T` or `m`'s type names from an
enclosing `poly` or `plambda` is, to the checker that runs later, a rigid
one: known to exist, its instance unknown. This is sound by parametricity:
code that checks against an abstract `a` works for every `a`. So `stage`
in a polymorphic procedure passes no types at run time. The same holds
for `m`'s abstract types (`m..t`): the code sees them abstract, as any
code outside `m` does (Sheldon's opacity, `first-class-modules.md`).

### What the staged code may do, and why `any` is not needed

`PLAN.md`'s item 5 proposed `any`, "for code meant to grow with the
language, as an interpreter's `eval` does", and stopped at which regions
it would cover. Here the caller names the bound, `E`, and the checker
enforces it. So nothing is unmaskable and nothing reaches regions the
caller did not name. Consequences:
- At an `E` without `spin`, only code the checker shows ends is accepted.
- Control effects are region-indexed (`goto` and `comefrom` on `r`), so
  `E` bounds them too: code cannot capture past a prompt it was not given.
- `(io k)` atoms are in `E` or the code does no such I/O.

### What the forms themselves do: the `stage` effect

**Decided: making code is an effect a type shows**, to try. A new atom,
`stage`, beside `spin` and `nondet`: a procedure that expands or installs
code says so. Like `spin` and the `io` atoms it has no region, so nothing
masks it. `install` and `stage` have it; `expand` does not (it makes
syntax, not code) but has `spin`.

How viral it is, is what trying it is to find out. The expectation: it
reaches the procedures that take code from the user (the editor's `M-:`,
its init file's loader, a REPL) and their callers up to the command loop,
and not the commands themselves, which run code already installed. A
command that installs code (`C-x C-e`) carries it, as it should: its type
then says that it changes what the program can run. If it reaches much
further, the alternatives are to fold it into an `io` atom, `(io code)`,
or to drop it as allocation is dropped.

What it is not: `nondet` (installing is deterministic, given `text` and
`m`'s type) or a reason to keep a form whose result is unused (an
`install` whose procedure no one holds may be dropped, as an allocation
may). The compilers may treat it as "anything else", as the `io` atoms.

### Termination: `expand` may spin, `install` may not

**Decided:** static analysis and compilation are assumed to end. A check
or compile that does not is a bug in the checker or compiler, not
something a type should carry, so `install`'s effect has no `spin`.
Expansion is different: macros (below) are a language, and `syntax-rules`
alone is enough to write a macro whose expansion never ends. So `expand`
has `spin`, and `stage`, being both, has it too. A program that wants the
one step it cannot bound kept apart from the one it can writes `expand`
and `install` apart.

The assumption is the user's for now: both checkers are programs.
Whether they could be shown to end (the size-change analysis the
checkers do for programs, `terminate.rs` and `check-sc-graphs.fx`, turned
on the checker written in FX-26) is not needed for this design.

### Interruptible

**Decided: checking must be interruptible.** Ending is not ending soon:
a large init file, or one large form, may take seconds to check, and the
editor must stay responsive and `C-g` must stop it. So `expand` and
`install` run as tasks the scheduler preempts, as any task that runs long
is (`docs/fx26.md`, "Running": fuel in time slices of polls), and each is
**cancellable** in `race`'s sense: until it gives its result back, it has
written nothing the program can see. A `race` of an `install` against a
key or a clock then cancels it, leaving nothing behind, and `attempt` may
wrap either. For sessions (below), the definitions a step makes are kept
apart and committed as one write when it ends, so cancelling before then
leaves the session as it was.

This weighs on the implementation more than anything else here: the
checker that runs must poll. See Fixpt and kayak below.

### Faults

A refusal is a value, above. A fault in running `p` is not the forms'
business: `p` is an ordinary procedure, and the caller runs it how it
runs anything that may fail. If `E` is cancellable, `attempt` catches it
in place. An editor command writes, so it is not; that is §106's question
(each command as a monitored task), not a new one. This is why `install`
gives back a procedure rather than running the code: it would otherwise
need a catch of its own, which `attempt`'s rule refuses for code that
writes.

## Macros

**Decided:** `syntax-rules`, or an extension of it, preferably with
explicit syntax classes (Racket's `syntax-parse`, Culpepper and Felleisen,
ICFP 2010); procedural macros as late as possible. FX-26 has no macros yet
(`docs/fx26.md`, "Open questions", "Syntax"); the Scheme engine has R7RS
`syntax-rules` and SRFI 211's procedural transformers
(`docs/macros.md`). For this design:
- `expand` is where macros run, which is why it, and not `install`, has
  `spin`. A pattern-based expander needs no evaluator at expansion time,
  so `expand` needs nothing of `m` but its macros' definitions; a
  procedural one would run code there, with an effect of its own to state.
- `m` gives macros as well as values and types: a module item
  `define-syntax`, and a `moduleof` entry for it. That is how the editor
  gives user code `define-command`, `define-key` and `define-major-mode`.
  Until FX-26 has macros, these are procedures over tables, and a
  `datum` given to `stage` lets a program generate code meanwhile.
- A syntax class is a type of syntax; whether an `expanded` should carry
  more of its type than "kernel syntax" is open.

## Sessions: definitions that last

`M-:` and the init file need definitions one evaluation makes to be seen
by the next, and redefined.

```
(make-session m)                         ; (sessionof R), allocated at R
(session-stage s T text (p body) (why else))
(session-define s text (why else))       ; top-level forms: `define`, `define-syntax`, …
```

- A session's own globals follow `docs/fx26.md`'s "Redefinition", with
  re-runs waiting, as at the REPL (out of date, `,rerun-outdated`'s
  equivalent a procedure).
- `m`'s names are not the session's globals: a module's definitions are
  never redefined, so user code may shadow the host's procedures but not
  replace them. What user code may change is what `m` gives it to change
  (a reference, a table of commands).
- The session's type does not grow. The host never sees what user code
  defined at a static type; it reaches user code only through values of
  types it chose (`p`, or procedures user code stores in tables `m`
  gives it, §105: hooks and keymaps of one type).
- `session-stage` and `session-define` have `stage`, and write the session
  (`(write R)`), once, at the end (above).

Heist's R4 "Done when" is then: `(session-define s "(define (f (x
string)) (host-insert! x))")`, then `(session-stage s (subr … () unit)
"(lambda () (f \"hi\"))" …)`, the host keeping `p`, and a refusal coming
back as `why`. A fault is §106's.

### The program's own top level as `m`?

`TODO.md` §105 offered two ways: (a) the editor is the session, as Emacs
is an image, user code seeing and redefining the program's globals; (b)
the front end as a library. The forms above are (b)'s meaning, with (a)'s
machinery underneath. Recommended. Giving user code the whole top level
(a `(current-globals)`) would make every global redefinable while the
program runs. The compilers could then never treat a known global's value
as fixed, as the native tier's direct calls do, without a way to undo
that. Deferred unless an editor needs it; a module of what user code
should see is also the better interface.

## Fixpt

What exists:
- The REPL checks a form against live globals, compiles it with the
  machine the program runs on, and keeps redefinition's rules
  (`Checker::defer_reruns`, `check-defer-reruns!`).
- The front end is FX-26 modules (`reader.fx`, the checker), and §97
  runs code a program made.
- Module types, `with`, and module parameters, in both checkers.

What is wanted:
1. The forms in both checkers: `T`'s and `m`'s types given to the run-time
   checker as data, which `.fasl` files' interface encoding (`fasl.md`)
   may already serve; and the `stage` atom.
2. **A checker that can be interrupted.** On the machines that run
   FX-26 code, the checker written in FX-26 is a program like any other,
   preempted at its polls and cancelled by `race`, so it is the one to run.
   The Rust checker, called through a hook (as `type_at`,
   `fixpt-fx26/src/typeat.rs`, asks for a type), polls nothing; it would
   have to run on a thread of its own, the task waiting on it and
   cancelling it by a flag it checks. Running the FX-26 checker is the
   simpler, and its speed (Heist's start-up is mostly checking, DONE §147)
   is then this design's cost.
3. A hook through which a program's machine compiles what was checked:
   the new code is compiled by the same machine as the program, so the
   host's values and the new code's are one representation. R4's worry,
   a typed bridge between the evaluator's `val` and compiled values, does
   not arise.
4. Refusals as values: today a refusal is a message the driver prints.
5. Sessions: globals of their own, apart from the program's, which the
   REPL's globals are not; definitions committed at a step's end.

## Kayak

KFX's rule is that every construct maps to something in Rust, and a KFX
program has no compiler at run time. So `stage` in KFX means a call into
an engine embedded in the program: `kayak-fx26` (`fx26/*.kfx`), whose
checker and engine can already be included in a unit, as its REPL is.
Its checker is KFX made Rust, so to be interruptible it must poll, as
the code the engine runs does, or run on a thread of its own, as Fixpt's
Rust one would.

The new code runs as that engine's values; the host's are Rust's. Every
value that crosses, `m`'s and `p`'s, crosses by a conversion its type
decides:
- data is copied (or, frozen, shared, if the engine can read Rust's);
- procedures are proxies, in each direction: the host's in `m` called by
  the engine, and `p` called by the host;
- data at a region that can be written cannot be copied (the two sides
  would diverge) and is proxied or refused.

FX-26 already draws such a line once: **transmissible types**
(`docs/fx26.md`, "What a process may hold"), what may cross into a
process. KFX would refuse a `stage` whose `T` or `m` it cannot carry
across, which keeps its rule that it may refuse an FX-26 program, never
reinterpret it. **Decided: deferred** — whether that is the transmissible
class, or a class of its own (a writable region a process may not hold,
`stage` might hold by proxy), is answered when kayak builds it, by what
its engine can share with Rust. Nothing in Fixpt's part depends on it:
Fixpt has one representation and needs no class. Until then a program
meant for both keeps `T` and `m` transmissible, which is safe under either
answer.

Before any of it, two things Heist's R4 lists:
- the engine's state is global, one instance in a process, where a
  session wants one each;
- the checker's refusals are panics; they must be values.

## Still open

1. **How viral `stage` is,** found by trying it in Heist; the fallbacks
   above if it is too much.
2. **Syntax classes and `expanded`'s type,** when FX-26's macros are
   designed.
3. **Kayak's boundary class,** deferred above.
