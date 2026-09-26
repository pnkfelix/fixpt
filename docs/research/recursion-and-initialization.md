# Recursion, initialization and redefinition: the options

Notes from a discussion with the user on 2026-09-26, while M13 made calls
known. The references are from memory, except the two papers in
`docs/research/papers/`, which were downloaded at the user's request:

- Dreyer, "A Type System for Well-Founded Recursion", POPL 2004;
- Reynaud, Scherer and Yallop, "A Practical Mode System for Recursive
  Definitions", POPL 2021.

## The problem

FX-26 builds recursion by backpatching, and a program can observe it.

- **A recursive `define`** gets its global cell before its expression
  runs, so that earlier forms can call it. The cell holds a closure that
  traps ("called before it was defined") until the definition stores the
  real one.
- **A `letrec`** makes a box per name holding that trapping closure. It
  closes each value over the boxes, then fills them.

Nothing stops an initializer, or an earlier top-level form, from calling
into the group before the fill. So the failure is a run-time trap, and
the procedures' types (`pure`, say) do not mention the imperative
initialization they depend on. The user asked for "the imperative nature
of mutual recursion" to be made explicit.

A second question is linked to it: what a second `define` of a name
means.

## Redefinition: shadowing or late binding

Today a second `define` makes a **new binding**, as at ML's top level.
Code defined before it keeps the old binding. This is documented in
`docs/fx26.md`, and the REPL prints a note when it happens.

- **For it:** it is sound without re-checking anything, since the new
  definition may have another type. It makes a global as fixed as a
  `letrec` binding once defined, which known calls use (PLAN.md 13e).
- **Against it:** it is not Scheme's REPL, where a redefinition is seen
  by code defined earlier. The user: "maybe not great … but we can work
  with this", as long as the workaround is clear. The workaround is to
  define the dependents again, or to call through a `ref`.

Late binding could come back for redefinitions at the same type. PLAN.md
("Redefinition at the REPL") has the design:

- A same-type redefinition assigns the old cell. Typed calls depend only
  on the type, so they survive it.
- Code that assumed the value (loops, `callk`) records its cell, and is
  patched back to `global g; tcall n`.
- A redefinition at a new type re-checks its dependents.

## The options for recursion

| option                                       | knot visible? | checks at run time                     | new machinery                              | cost                                          |
| -------------------------------------------- | ------------- | -------------------------------------- | ------------------------------------------ | --------------------------------------------- |
| 0. today: hidden backpatching                | no            | trap on early call                     | none                                       | types say nothing of initialization           |
| 1. boxes required (`ref`s)                   | yes           | none needed, but `(read R)` everywhere | none                                       | every signature widens; no known calls        |
| 2. groups of lambdas only (OCaml `let rec`)  | as a group    | none: cannot happen                    | syntactic restriction, explicit groups     | rewrite the bootstrap's top level into groups |
| 3. nullable, then narrowed (union types)     | yes           | nil tests inside the group             | unions, ascription confirmed at run time   | aliasing: old views stay nullable             |
| 4. effects prove well-founded (Dreyer)       | no, but safe  | none                                   | an effect for "uses a recursive name"      | a checker rule; direct style kept             |
| 5. self-passing (structural recursive types) | no knot       | none                                   | recursive record types (may exist already) | an extra argument; calls through a record     |
| 6. I-cells (Id, pH)                          | yes           | read of an empty cell                  | `(icell T R)`, an `(await R)` effect       | the cell type; reads ordered after writes     |

### 1. Boxes required

Mutual recursion goes through `ref`s that the program declares. Filling
them has `(write R)`, and every call through one has `(read R)`. It is
honest, and it is expressible today. FX-26 has no null, so a box starts
with a placeholder procedure, which is what the implementation does
anyway.

The cost is large. The compiler written in FX-26 is almost entirely
mutually recursive top-level procedures. Every one would carry
`(read R)`, and no call through a box could become a known call.

### 2. Groups of lambdas only

This is OCaml's `let rec … and …`. Mutually recursive definitions must be
written as one group, and every binding in a group or a `letrec` must be
a lambda. Then nothing can run before the knot is tied. The trap cannot
happen, and the backpatching becomes an unobservable detail of the
implementation. Top-level forward references outside a group would go.
Programs that want imperative knot-tying write option 1 themselves.

It adds no expressiveness; it rules programs out. Reynaud, Scherer and
Yallop is the careful form of this check for a real language: a mode
system, which replaced OCaml's syntactic one. It admits more than "only
lambdas", such as some recursive data built from constructors.

### 3. Nullable boxes, narrowed after initialization

The user's proposal. It uses structural recursive types, union types
(untagged sums), and Scheme's single domain of disjoint tagged values.

1. The boxes, or a bloblet holding them, have fields of type
   `(or P nil)`.
2. After filling, the program ascribes the narrower type `P`, and a
   traversal confirms it.

Analysis:

- **The check is first-order and sound.** Removing `nil` from
  `(or P nil)` needs only a tag test per field. The `P` part was checked
  statically when each field was written, so no contract wrappers are
  needed for procedures, unlike Typed Racket's general case. Nested data
  needs a traversal, and cyclic data needs a visited set: the usual
  coinductive check.
- **It does not untie the knot.** The closures made during
  initialization captured the bloblet at the nullable type, and still
  hold that view after the check. Freezing the bloblet at the narrowing
  keeps the old view sound, but only as a nullable view. Inside the
  group each procedure still tests for nil at each use; clients outside
  get the narrow type. This is Typed Racket's picture of checked uses
  inside and the promise at the boundary. It is also what the
  implementation does today, with the trapping closure as the nil and
  the call as the test.
- **Disjointness has a limit.** Heap tags tell fixnums, pairs, bloblets
  and closures apart. They do not tell two bloblet types of the same kind
  and layout apart. Unions of those would need bloblets to carry a type
  identity, the metadata the "closures carry their types" idea (PLAN.md)
  also needs.

### 4. Effects that prove recursion well-founded (Dreyer)

Dreyer's type system tracks, with static "names", whether evaluating an
expression might *use* a recursive variable. Forming a lambda that
mentions one is fine; calling it is not. In FX-26 terms:

1. The group's boxes live in a fresh private region ρ.
2. The initializers are checked to have no `(read ρ)` in the effect they
   carry out. Creating a lambda has no effect, since its body's reads are
   latent, so ordinary mutual recursion passes. An initializer that
   calls into the group fails to check.
3. After initialization ρ is never written again. Its reads are then
   treated as reads of a frozen bloblet already are, as no effect, so
   the procedures keep narrow signatures.

This gives a static proof that the trap cannot fire, in direct style,
with no new types. Step 3 is a new checker rule. It cannot be written
with `bloblet-freeze`, because the closures would need the frozen view
before it exists.

### 5. Self-passing, with structural recursive types

Each procedure is written open, taking the group as an argument. The
group is a record whose type mentions itself:

```
G = (record (even (subr pure (G int) bool)) (odd (subr pure (G int) bool)))
```

The record is built from the lambdas at once. They capture nothing, so
nothing needs a value that does not exist yet: no initialization phase,
no nil and no imperative step. Calls become
`((extract g odd) g (- n 1))`. This is Cook's encoding of objects by
self-application.

The cost is an extra argument, and calls that go through the record. If
the record is frozen and known, the compiler can make those known calls
again. FX-26 has recursive type definitions (`dletrec`, and `define-type`
may mention itself), so this may be expressible today; it has not been
tried.

### 6. I-cells (Arvind; Id and pH)

I-structures are from Arvind, Nikhil and Pingali (TOPLAS 1989). Id had
them, and pH, the parallel Haskell of Nikhil and Arvind, kept them. An
I-cell is written once, and a read of an empty cell waits until it is
filled.

- **It is the current implementation, made explicit.** The trapping
  "undefined" closure is an I-cell: filled once, never changed, and
  trapping if read early. As a type, `(icell T R)`, the knot is visible
  in the source.
- **The "frozen after initialization" property is built in.** A filled
  cell never changes, so every read that returns gives the same value.
- **There is no null, no union and no strong update.** The cell has type
  `T` throughout; only "not yet" is possible, never "wrong type". A
  second write is an error.
- **Reading an empty cell** traps in a sequential program. Nothing else
  can fill the cell, so the reader would wait forever. In a concurrent
  one the reader suspends: its continuation, captured by the machine's
  control routines, waits on the cell, and the write resumes it. So
  I-cells are also the dataflow synchronization primitive for the
  concurrency story that FX-26 lacks (PLAN.md: processes and functions).
- **LVars** (Kuper and Newton, FHPC 2013) generalize them from "empty or
  full" to any lattice of values that only grow, and keep reads
  deterministic.

**The effect of a read.** It is tempting to call a read `pure`: every
read that returns gives the same value. In pH's non-strict dataflow
semantics, moving a read earlier is harmless, since it just waits. In
FX-26's eager, sequential semantics it is not. `pure` lets an optimizer
move code, and a read moved above the write that fills its cell would
deadlock.

So a read carries a new effect, `(await R)`:

- It conflicts with writes to `R`, so a read stays after the write that
  fills its cell.
- It commutes with other `(await R)`s, so reads may be reordered and
  merged among themselves.
- It is masked like any effect on a region nothing outside can name.

This is roughly what Dreyer's names track, reached from the dataflow
side.

**For the compiler:** a filled cell never changes, so a call through one
can become a known call once it is filled. The code can be patched when
the cell is written, the same mechanism as the reversion for late
binding.

## What was done (2026-09-26)

Options 2 and 6 together:

- **I-cells** were prototyped: `(icell T R)` with `(await R)`. A procedure
  that ties a knot in a private region stays `pure`.
- **Implicit backpatching is gone** (the user: "remove the implicit
  backpatching in both define and letrec").
  - A `letrec` binds only lambdas, and compiles without boxes: each
    closure is made with a placeholder for a sibling not yet made, then
    patched.
  - `define-rec` is a top-level group of the same kind.
  - Nothing is declared ahead: a definition sees only those before it,
    and a lambda's definition sees itself.

  The FX-26 sources were reordered by a script, so that every definition
  comes after what it uses. It found 260 uses before definition and 19
  mutually recursive groups, which became `define-rec`s; the largest is
  the checker's core, with 25 procedures.

## Chosen to prototype first: I-cells

The user chose this, after the others were laid out. It:

- keeps the implementation we have;
- makes the knot visible;
- adds only one type and one effect;
- gives concurrency a primitive.

The prototype is described in PLAN.md.
