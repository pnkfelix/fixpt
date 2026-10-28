# `eval` for FX-26 programs

Design note, 2026-10-28, from a discussion with the user: what FX-26, Fixpt
and kayak would have to change for a running program to read, check and
run code it is given, as Scheme's `eval` does. Wanted by Heist's editor
(`TODO.md` §105; Heist's `docs/fx26-for-yank.md`, R4): the init file,
`M-:`, `C-x C-e`, and commands, keymaps and hooks defined by user code at
run time. Nothing here is implemented.

## The claim

The language changes little: one form that checks code against a type
and an effect, and, for definitions that last, one kind of value
(sessions). It does not need a top effect (`PLAN.md`'s item 5, `any`), a
type of every value (§108's alternative), or macros. In Scheme `eval` is
unsafe because nothing checks what it runs. FX-26 has a checker to call
at the time the code arrives, so the caller says what type and effect it
accepts, and the checker holds the code to them. Contrast `native-procedure`
(`docs/fx26.md`, "Code a program makes"), which *trusts* code at a stated
type and so carries `(io native)`. `eval` trusts nothing, and so needs no
such effect.

Fixpt has most of the machinery already, in the REPL. Kayak's difficulty
is not the language but the boundary between the Rust its programs become
and the engine that would run the new code.

## The form

Checking and running are two steps, as `confirm` (`confirmation.md`) puts
failure in the type rather than trapping:

```
(eval m T text (p body) (why else))
```

- `text` is a `string`, or a `datum`, so that a program builds code
  without printing it first.
- `T` is a procedure type of no parameters, `(subr E () R)`, written at
  the form. `text` is read as an expression, checked as the body of a
  `(lambda () …)` of type `T`, compiled, and `body` runs with `p : T`
  bound to that procedure.
- Otherwise `else` runs with `why : eval-failure`, a sum of a read error,
  a refusal, and (for sessions, below) a redefinition refused; each with
  its message and a span in `text`. Nothing is printed on the side.
- `m` is a module, a value of a `moduleof` type, and is the code's
  environment: `text` is checked as if in `(with m …)`, over the standard
  bindings (`#%fx`). Nothing else of the program is in scope.

```
(define editor-api
  (module
    (define insert! (subr (maxeff (write @buf) (io terminal)) (string) unit) …)
    …))
(define-type command (subr (maxeff (write @buf) (io terminal) spin) () unit))
(eval editor-api command "(lambda () (insert! \"hi\"))"
  (c (add-command! "say-hi" c))
  (why (show-failure why)))
```

### Why a form, not a procedure

The static checker knows `T` and `m`'s type at the form, so it can give
the checker that runs later their descriptions as literals, as it gives
`native-procedure` its `T`. Types need not exist as values at run time,
and no `typeof` or reflection is added.

### Variables `T` and `m` take from around the form

A type, region or effect variable that `T` or `m`'s type names from an
enclosing `poly` or `plambda` is, to the checker that runs later, a rigid
one: known to exist, its instance unknown. This is sound by parametricity:
code that checks against an abstract `a` works for every `a`. So `eval`
in a polymorphic procedure passes no types at run time. The same holds
for `m`'s abstract types (`m..t`): the code sees them abstract, as any
code outside `m` does (Sheldon's opacity, `first-class-modules.md`).

### Effects, and why `any` is not needed

`PLAN.md`'s item 5 proposed `any`, "for code meant to grow with the
language, as an interpreter's `eval` does", and stopped at which regions
it would cover. Here the caller names the bound, `E`, and the checker
enforces it. So nothing is unmaskable and nothing reaches regions the
caller did not name. Consequences:
- At an `E` without `spin`, only code the checker shows ends is accepted.
- Control effects are region-indexed (`goto` and `comefrom` on `r`), so
  `E` bounds them too: code cannot capture past a prompt it was not given.
- `(io k)` atoms are in `E` or the code does no such I/O.

The form's own effect is the checking and compiling: `spin` (the checker
is a program; whether it can be shown to end is not this note's question),
allocation in the heap, and making code. Whether making code is an effect
a type shows, or as invisible as allocation, is open. Checking is
deterministic, given `text` and `m`'s type, so it is not `nondet`.

### Faults

A refusal is a value, above. A fault in running `p` is not the form's
business: `p` is an ordinary procedure, and the caller runs it how it
runs anything that may fail. If `E` is cancellable, `attempt`
(`docs/fx26.md`) catches it in place. An editor command writes, so it is
not; that is §106's question (each command as a monitored task), not a
new one. This is why the form returns a procedure rather than running the
code: `eval` would otherwise need a catch of its own, which `attempt`'s
rule refuses for code that writes.

## Sessions: definitions that last

`M-:` and the init file need definitions one evaluation makes to be seen
by the next, and redefined.

```
(make-session m)                       ; (sessionof R), allocated at R
(session-eval s T text (p body) (why else))
(session-define s text (why else))     ; a top-level form, `define` and the like
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
- `session-eval` and `session-define` write the session (`(write R)`).

Heist's R4 "Done when" is then: `(session-define s "(define (f (x
string)) (host-insert! x))")`, then `(session-eval s (subr … () unit)
"(lambda () (f \"hi\"))" …)`, the host keeping `p`, and a refusal coming
back as `why`. A fault is §106's.

### The program's own top level as `m`?

`TODO.md` §105 offered two ways: (a) the editor is the session, as Emacs
is an image, user code seeing and redefining the program's globals; (b)
the front end as a library. The form above is (b)'s meaning, with (a)'s
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
1. The form in both checkers: `T`'s and `m`'s types given to the run-time
   checker as data, which `.fasl` files' interface encoding
   (`fasl.md`) may already serve.
2. A hook through which a program's machine asks its session to check
   and compile (as `type_at`, `fixpt-fx26/src/typeat.rs`, asks for a type): on the native
   machines, the Rust checker and compiler; on the evaluator written in
   FX-26, its own. The new code is compiled by the same machine as the
   program, so the host's values and the new code's are one
   representation. R4's worry, a typed bridge between the evaluator's
   `val` and compiled values, does not arise.
3. Refusals as values: today a refusal is a message the driver prints.
4. Sessions: globals of their own, apart from the program's, which the
   REPL's globals are not.

## Kayak

KFX's rule is that every construct maps to something in Rust, and a KFX
program has no compiler at run time. So `eval` in KFX means a call into
an engine embedded in the program: `kayak-fx26` (`fx26/*.kfx`), whose
checker and engine can already be included in a unit, as its REPL is.
The new code runs as that engine's values; the host's are Rust's. Every
value that crosses, `m`'s and `p`'s, crosses by a conversion its type
decides:
- data is copied (or, frozen, shared, if the engine can read Rust's);
- procedures are proxies, in each direction: the host's in `m` called by
  the engine, and `p` called by the host;
- data at a region that can be written cannot be copied (the two sides
  would diverge) and is proxied or refused.

FX-26 already draws this line once: **transmissible types**
(`docs/fx26.md`, "What a process may hold"), what may cross into a
process. Proposed: a sibling class, the types that may cross the eval
boundary, and KFX refusing an `eval` whose `T` or `m` falls outside it,
which keeps KFX's rule that it may refuse an FX-26 program, never
reinterpret it. Fixpt need not restrict to it, having one representation;
a program meant for both keeps to it. Whether the two classes are one is
open: a writable region a process may not hold, `eval` might hold by
proxy.

Before any of it, two things Heist's R4 lists:
- the engine's state is global, one instance in a process, where a
  session wants one each;
- the checker's refusals are panics; they must be values.

## Open questions

1. **Names.** `eval` for a form that does not run the code? `check-code`,
   `compile-in`? `eval` says what it is for.
2. **Making code as an effect.** Whether a type shows that code was made
   (a code area grows, and is collected with what holds it, `code-stubs.md`).
3. **Is the checker's termination worth stating?** If it could be shown,
   the form would not need `spin`; a program that evaluates at a deadline
   uses `race` regardless.
4. **One boundary class or two**, transmissible and evaluable, above.
5. **Macros.** R4 leaves `define-command` and the like to procedures over
   tables first; `datum` input lets a program generate code meanwhile.
6. **Time slices** (R4's 5): `p` runs as any procedure does, so `race`
   against a clock and §106's cancellation answer it, unless the checking
   itself must be cut; a large init file might want that.
