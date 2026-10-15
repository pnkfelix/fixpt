# Loads, hidden globals, and facts by place: a review

The user's question (2026-10-15), after `TODO.md` §97's `load-input` bug:
the hidden globals of loaded files, and the reshaping of modules, sound
error-prone; should that part of fixpt be redesigned? This note says how
they work, what has gone wrong with them, why, and what could replace
them. Nothing here is decided.

## How loads work now

Every load of a path is one value, made once (`TODO.md` §68, decided
2026-10-08). A load is a *hidden global*, `%shared:K`, `K` the file's key
(`input:` before a `load-input`'s, then the path as resolved):

- **The Rust parser** (`parse.rs`, `parse_load`), at the first load of a
  key, makes a definition of its own, the *form*
  `(define %shared:K (load-module "P"))` (or `load-input`), and checks it
  with `top_defining` while the key is in `sharing_now`, the one state in
  which that load means "the file's module" rather than a load of it. The
  definition is *hoisted*: it runs before the form that loads the file.
  Every load is then the global (`load-module`) or the global's one item,
  `(with %shared:K input)` (`load-input`).
- **The front end written in FX-26** does the same in its own way: the
  Rust side reads each file once (`syn.rs`, `supply_loaded_in`) and gives
  the texts, at positions a billion apart per file (`LOAD_BASE_STEP`);
  the parser (`parse-loaded`) puts each new key's definition in
  `shared-pending`, which `parse-tops` places before the form.
- **The session** (`session.rs`), at the REPL and on the machines that
  check form by form, runs each hoisted definition as a form of its own:
  written back to text and given again to whichever front end and
  machine runs it. `shared_made` remembers which keys this session has
  made, so that the FX-26 front end is told not to make them again (base
  −1).
- **The checkers** let `%shared:` names through a loaded file's hidden
  scope, require the definition to be pure ("a loaded file is one value
  …"), and print no line for it. The compilers treat it as any global.
- **`module-parameters`**: the hidden global is a `plambda` over a
  `lambda` of no arguments, so each client's application makes a fresh
  module; each of the three at a place of its own.

## Reshaping

A module is a product of its values, by position. Where one is given
where a `moduleof` of fewer values, or the same in another order, is
expected, the checker records each wanted value's position in the given
module (`expect`: Rust `Checker::reshape`, FX-26 `k-reshape`), and the
compilers build the narrower product there. `extend`, `include` and
`hide` (§69) make reshapes too, by *paths* encoded as positions
(`RESHAPE_PATH`, `2^40 + (k << 20) + j`). The meaning is simple and
sound. What is fragile is how it is found again:

- **The Rust front end keys facts by expression** (`ExpId`):
  `NodeFacts.reshaped`, conversions, and the rest.
- **The FX-26 front end keys them by place**, an expression's start and
  end in the text (`k-reshapes`, `k-with-index`, the conversions
  `k-convert-at` notes, the effect summaries), and the FX-26 compiler,
  evaluator and register code look them up by place (`c-reshape-at`,
  `ev-reshape-in`). Rust's facts handed to the FX-26 compiler are turned
  into places too (`syn.rs`).

So two expressions must never share a place, and every expression the
parsers *make*, rather than read, needs a place invented for it.

## What has gone wrong

| when      | what                                                               | the cause                                                |
| --------- | ------------------------------------------------------------------ | -------------------------------------------------------- |
| `0c08e72` | a load given where a narrower module was wanted: the wrong reshape | the hidden definition and its use, one place             |
| DONE §69  | SIGSEGV: a parameterized module's closure reshaped                 | `plambda`, `lambda` and module, one place                |
| `7989f6f` | the FX-26 compiler slow on modules                                 | every reshape searched, by place, per expression         |
| `5b39a90` | `load-input` form by form: "unbound variable `input`"              | the hidden *form* means the module only in `sharing_now` |
| `5b39a90` | hid the above on the native machine                                | a checker's refusal taken as a decline                   |
| `5b39a90` | (first try) the scheduler cellular, not preempted                  | hidden definitions run per machine, differently          |

Two causes account for all but the fifth, which is a policy (see the
end):

1. **Facts by place.** Places are the FX-26 front end's identities for
   expressions, but they are not unique: made expressions have none of
   their own, and the fixes invented them (the load's keyword span for
   `input`, a zero-width `lambda`, positions a billion apart per file, a
   REPL form's positions past every earlier text, `2^40` for paths).
   Every new way of making an expression is a new chance to collide.
2. **A definition carried as source text whose meaning depends on the
   reader's state.** `(define %shared:K (load-input "P"))` is the file's
   module only to a parser in `sharing_now`; read anywhere else it is the
   file's value. It travels as text between front ends, and the session
   runs it differently on each machine (and the native machine compiles
   its initializer alone).

## Options

**A. An explicit form for a hidden definition.** The hoisted definition
becomes an internal form whose meaning is fixed, say
`(%loaded K "P" input?)`, meaning the file's module wherever it is read:
both parsers, both checkers, the lowering, the evaluator and the native
machine's definition path (which would compile it as what it is, or
decline it, by its form). `sharing_now`, `sharing-now` and the `%shared:`
prefix tests go. Small (both parsers, the session's hoisting, the native
path); removes cause 2; does nothing for cause 1.

**B. Loads that are not globals.** The session keeps a table of loaded
files, each made once (its key, its module's type, its value); a load is
an expression of its own, `Loaded(K)`, typed from the table and lowered
to a reference to the entry; nothing is synthesized or hoisted. Removes
cause 2 entirely, and the hoisting order with it. Large: a new
expression in both front ends, every compiler and machine, the REPL's
redefinition, images (a table to save), and `module-parameters`; and
what it gains over A is mostly that the hidden definition is not a
global, which is not what has broken.

**C. Expressions with identities in the front end written in FX-26.**
The FX-26 parser numbers each expression it makes (a field of the
expression, as Rust's `ExpId` is an arena index), and every fact (reshapes,
withs, conversions, effect summaries) is keyed by that number, not by
place; places stay only for messages. Removes cause 1: made expressions
need no invented places, and collisions cannot happen. Large but
mechanical: the expression datatype gains a field in the parser, the
checker's fact tables change key, the compiler, evaluator and register
code look facts up by it, and the Rust side's facts handed to the FX-26
compiler are keyed the same way. It also makes the reshape index's speed
fix unnecessary, and is what the two front ends agreeing would want
anyway: both keyed by expression.

## Recommendation

**A now, C next, B not.** A is small and removes the bug class that
appeared this week, whose cause is wholly in the hidden definition's
form. C is the deeper fix: three of the six were places, the slowness among
them, and
places will keep colliding as long as the FX-26 front end keys facts by
them; but it touches every FX-26 phase, so it deserves its own plan,
steps and measurements (the FX-26 checker's time on `peval` is the one to
watch). B changes the most and fixes nothing A and C leave.

Independently: the native machine should not treat a checker's refusal
as a decline (`TODO.md` §97); a refusal there is a disagreement between
the checkers, which the test suite should see.
