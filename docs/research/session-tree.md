# A tree of session states: what isolating them takes

`TODO.md` §260. Raised 2026-11-12 by the user, while looking at
`compiler::every_program_compiled` (41 s alone): 455 programs, each given a
fresh `Fx26Session` (about 20 ms in a debug build) and, for its lowered
run, a fresh Scheme session that evaluates the prelude and `runtime.scm`
from source (about 20 ms more), so that no program sees another's
definitions. Could sessions instead be forks of one ready session, cheaply;
or could the session's imperative state be a tree of levels, like FORTH's
vocabularies, one pushed for each program and left after it? Probably a
non-starter, the user's judgement; kept for its pitfalls.

## A session shares nothing safely as it is

Checking in a session updates it, and not only with leftovers: a REPL's
checker accumulates by design (each checked `define` enters its global
environment with its type; macros, loaded modules and shapes are recorded;
the type arena grows, inference variables and their unifications too), so
that a later form sees the earlier ones. Shared across programs, a name a
program uses without defining could find another's, or one's definition
refuse another's.

The one place a session is shared between programs today shows what it
costs: `Fx26Session::compile_with_own_compiler_showing`, which
`common::with_own` serves every program, resets what would carry over by
hand before each (`shared_made` cleared, `processes_forgotten`,
`own_begun`, the entry `compile-forget-globals!`), and carries some of the
checker's state on deliberately (`read_state`, `keep_state`). Isolation
there is an audit, written as resets, not a property.

## A heap shared is no isolation

A session's globals live in its heap (each interned symbol a global slot,
a `define` a write there), as do the prelude's mutable objects and the
session's tables: two sessions on one heap see each other's definitions
and mutations. A copy is a heap of its own.

## A tree of levels for names

Each level a map of definitions and a parent; a child pushed for each
program, siblings unseen by each other, a child seeing its ancestors where
it does not shadow them: FORTH's wordlists and search order, Smalltalk's
namespaces, a layered REPL. The choice that decides isolation is what a
write to an inherited binding does:

- it updates the ancestor's (FORTH): siblings see it; no isolation;
- it makes a binding in the child (copy-on-write by name): isolation, of
  names.

Of names only. Two things get past it:

- **Code is linked to cells.** Compiled code refers to a global's cell,
  found once as it is linked, not to its name as it runs. A procedure
  compiled in the parent writes the parent's cell however a child calls
  it: a prelude procedure that counts would count across siblings, the
  names copy-on-write or not.
- **The heap's objects.** What the shared levels refer to (a table, a
  counter, the expander's records) is changed where it is; a tree of
  bindings versions none of it.

Isolation by construction needs copy-on-write of all the mutable state,
which is at the heap's level: an image of a ready session, mapped
privately as the front end's cache already is (`heap/splice.rs`: the
static area's immutable half shared read-only, its mutable half the
process's own copy of each page written). A level is then a snapshot, the
tree a tree of snapshots. What lives outside the heap (the `Checker`, the
Scheme engine's prepared code and expander state, the session's own
records) needs a way of its own, a copy at least; some of it refers into
the heap by address, which a heap mapped elsewhere would move.

## Shallow binding, again

A tree of levels with moves between them is Baker's question ("Shallow
binding in Lisp 1.5", 1978): deep binding (a chain of levels searched
outward) makes moving to another node a pointer's change; shallow binding
(a slot per name holding its binding now, `fixpt_scheme::env::Env` since
2026-11-12) makes a lookup one probe, but moving means rerooting: the
bindings undone to the common ancestor and redone down the other side.
`Env` is the Scheme expander's lexical scopes at compile time, nested
strictly and never moved between, the case where shallow binding costs
nothing; it is not this. And since code is linked to cells, a global's
name is looked up only as code is compiled and linked: a deep chain of
levels would do for names. What a tree of levels costs is the state the
names lead to, above.
