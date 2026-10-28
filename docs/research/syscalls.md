# Syscalls: one FX-26 extension through which each runtime extends itself

Fixpt's copy of kayak's request (`docs/research/syscalls.md` in kayak's
tree, 2026-10-26, beside kayak `2a2dd4a`): the request as it came, then,
in "What Fixpt does", what Fixpt implemented and where it differs. That
section is the record; the definition is `docs/fx26.md`, "Syscalls".

Status: a design, 2026-10-26, for Fixpt to implement first (FX-26
extensions land in Fixpt before kayak uses them), then kayak. Agreed with
the user in conversation; the details below are this note's proposal, for
the Fixpt team to adjust as they implement it (and to say so here, or in
their copy).

## Why

Every capability a runtime written in FX-26 (or KFX) has needed so far has
been an extension of the language, implemented by Fixpt first: `%sched`
for the scheduler, `seal-code` and `native-procedure` for code a program
makes, and next an executable view of a range of a flat array, which
kayak's tier 1 (Fixpt's cellular machine, ported to KFX) needs in order to
run code a program makes the way Fixpt's heap does (`exec_view` of the
code area's range of `mem`, `fixpt-memmgmt/src/exec.rs`).

Instead: FX-26 gains one extension, a **syscall interface**, through which
a program calls a capability its runtime provides by name, at a type both
sides state. Capabilities are then each runtime's own, added without a
change to the language. Fixpt-first applies once, to the interface.

The rule that keeps this from becoming a back door: **what a portable
program needs in order to mean something stays in FX-26; syscalls are for
building runtimes.** Ordinary programs cannot declare them (see
"Containment").

## The form

    (define-syscall name "host-name" type)
    (define-optional-syscall name "host-name" type)

- `name` is bound, in the scope a `define` would bind it, to a procedure
  of `type`.
- `"host-name"` is the runtime's name for the capability: a namespace, a
  colon, a name, a slash and a version, e.g. `"code:exec-view/1"`. A
  capability's type never changes under a name; a new type is a new
  version (`/2`). Any runtime may implement any name, provided it gives
  it exactly the type the name has: so a capability several runtimes
  share (like `code:exec-view/1`) has a neutral namespace, and one only
  one runtime has, that runtime's (`kayak:`, `fixpt:`).
- `type` is a `subr` type, `(subr E (T …) R)`, or a `poly` over regions
  only of one, `(poly ((r region) …) (subr E (T …) R))`. No type
  binders (no `(t type)`) for now.
- `E` must include the syscall effect, `(io sys)` (a new `io` atom), so
  that every use of a syscall shows in the types of what uses it.
  (Dropped, 2026-10-27, at Kayak's request: `E` is what the declaration
  says, `pure` among them; `docs/fx26.md`, "No `(io sys)` required".)
- Each `T` and `R` must be a type that crosses (below).
- `(syscall-available? name)`, `name` a syscall the program declared,
  is a `bool`: whether the runtime gave it at load (always `#t` for a
  required one, since the program would not have loaded otherwise).

### Types that cross

As `native-procedure`'s do, kept small: `int` (a fixnum's range; a
syscall given or giving more fails), `i64`, `u64`, `bool`, `char`,
`unit`, `string` (copied), `(flatarrayof i64 r)` and `(bytevectorof r)`
(passed in place, not copied). More only when a capability needs them.

## The canonical form of a type

The program's declared type and the runtime's are compared as text: each
side prints the type in one canonical form, and the two strings must be
equal. This makes the runtime's check a string comparison, so no runtime
needs a type parser or a type checker, and the form must therefore be
part of FX-26's definition, printed alike by every implementation.

The canonical form of a type:

1. Every name a `define-type` (or a module's type) introduced, expanded
   to what it names, recursively. A generative type, a datatype or an
   abstract type cannot appear (it crosses no runtime boundary).
2. Effects: a `maxeff` flattened (nested `maxeff`s and named effects
   expanded), its atoms deduplicated and sorted by their canonical text
   (byte order); one atom printed alone, not in a `maxeff`; none printed
   `pure`.
3. Region binders renamed in the order of the `poly`'s binder list:
   `r1`, `r2`, …, and every use with them.
4. Printed with one space between items, no other whitespace, and the
   type syntax's own keywords (`subr`, `poly`, `region`, `flatarrayof`,
   …), as FX-26's checker prints types elsewhere.

For example, `(poly ((buf region)) (subr (maxeff (io sys) (write @buf) (read @buf)) ((flatarrayof i64 buf) int int) i64))`
is, canonically,
`(poly ((r1 region)) (subr (maxeff (io sys) (read r1) (write r1)) ((flatarrayof i64 r1) int int) i64))`
(the exact spelling of a region variable in an effect, `r1` or `@r1`, is
whatever FX-26's printer already uses; the point is that it is fixed).

Equality only, no subtyping: a program that wants a looser type wraps
the syscall in a procedure of that type.

## The check, at load

The compiler checks the declaration alone, never against a runtime: the
form, the type's shape, the effect, the types that cross, and where the
declaration is (below). It then records, in what it compiles, for each
declaration: the host name, the canonical type, and whether it is
required. A program is compiled once and may run on any runtime, so
whether a runtime has a syscall is a question for when it runs.

When a runtime loads a program (for KFX compiled to Rust, when the
program starts), for each declaration:

- **Required** (`define-syscall`): the runtime has the host name at the
  same canonical type, or the load fails, naming both:
  - `syscall NAME ("HOST"): this runtime has none`
  - `syscall NAME ("HOST"): declared TYPE; this runtime's is TYPE`
- **Optional** (`define-optional-syscall`): the load succeeds whatever
  the runtime has; where it has none at that type, `syscall-available?`
  is `#f`, and a call fails with
  `syscall NAME ("HOST"): not available on this runtime`.

Every runtime does exactly this, so a program behaves alike on all of
them. A runtime keeps, for each syscall it provides, its host name, its
canonical type (as text, written by hand or by the implementation's own
printer at build time) and its implementation.

## Containment

A syscall can do what the language cannot check (the first hands out a
view of memory to execute), so ordinary programs must not declare them.
A `define-syscall` or `define-optional-syscall` is accepted only:

- in a module file built into the implementation (as `%sched` is
  accepted only in `fx26:` files today: Fixpt's `built_in_only`,
  `check.rs`), or
- in a program its driver was told is a runtime's, by an explicit flag
  (e.g. `--syscalls`); kayak's tier 1 is compiled so.

Anywhere else: refused, `syscalls are declared only by a runtime's own
code`. The `(io sys)` effect then makes every procedure that reaches a
syscall say so in its type. (No longer: each is found by its
declaration, 2026-10-27.)

## The first syscalls: an executable view, and flushing it

What kayak's tier 1 needs, so that its code area is a range of its heap's
own flat array, as Fixpt's is a range of `mem` (`native.md`, decision 3):
code bloblets that the machine's ordinary accessors and collector see as
heap objects, their fields written through the array, their code run
from a second, read+execute mapping of the same pages.

    (define-optional-syscall exec-view "code:exec-view/1"
      (poly ((r region)) (subr (maxeff (io sys) (write r)) ((flatarrayof i64 r) int int) int)))

`(exec-view a start n)`: words `start` to `start + n` of `a` mapped a
second time, read+execute; the result is the distance in bytes from the
array's address to the view's (the same for every word of the range).
Fixpt's `ExecView`, `exec_view` (`fixpt-memmgmt/src/exec.rs`). Fails
(the result -1) unless:

- the runtime keeps `a` at an address that never changes (kayak-rt's
  reserved flat arrays; a Fixpt heap's flat array, which a collection may
  move, is not one: Fixpt may give -1 there, or provide it only for
  arrays it pins);
- `start` and `n` cover whole pages (a page's words: `code:page-words/1`
  below);
- no word of the range was written yet: the view replaces the range's
  pages with shared ones, zero, as they were (as Fixpt's code area does,
  `code.rs`, "before anything is written there").

    (define-optional-syscall page-words "code:page-words/1"
      (subr (io sys) () int))

The words in one page of this machine (512 on x86_64 Linux, 2048 on arm64
macOS).

    (define-optional-syscall flush-code "code:flush/1"
      (poly ((r region)) (subr (maxeff (io sys) (read r)) ((flatarrayof i64 r) int int) unit)))

`(flush-code a start n)`: the instruction cache made to see words
`start` to `start + n` of `a`'s view as written (Fixpt's `flush_code`,
`ExecView::flush`). A no-op where the machine needs none.

How tier 1 calls code there (a native procedure kayak already makes, a
stub entered with the machine's registers in a flat array), and how its
collector marks code bloblets in place, are kayak's, not part of this.

## What each side does

**Fixpt** (first):
- the forms `define-syscall`, `define-optional-syscall`,
  `syscall-available?`; the `(io sys)` atom; the containment rule;
- the canonical printer, as above (and its definition written into
  FX-26's definition wherever Fixpt keeps that);
- the record of declarations in what it compiles, and the check at load,
  with the messages above, on every one of its machines;
- its own syscall table: `code:exec-view/1`, `code:page-words/1`,
  `code:flush/1` where it can give them (its heap's flat arrays move:
  -1, or pinned arrays, as it chooses), and none other needed;
- tests: a program declaring a required syscall its runtime lacks (load
  fails, both messages), one at another type, an optional one absent
  (`syscall-available?` `#f`, the call's failure), a declaration in an
  ordinary program (refused), and the canonical form's cases (aliases,
  effect order, region renaming).

**Kayak** (after the pin moves):
- the same in kayak's checker (`kfx/`), which is shared by KFX and the
  engine, and in KFX (restricted to what KFX can emit);
- kayak-rt's syscall table, and the check at program start;
- the engine's table (none at first; later, perhaps, the terminal and
  the standard input, out of the engine's core);
- tier 1's code area on `code:exec-view/1`: then `seal-code`,
  `native-procedure`, `native-code?` as Fixpt's `fx-cells-rsinterp` has
  them, and Fixpt's `made-code-x86_64/*.fx` programs on tier 1.

## Open questions

- Whether `(io sys)` should be one atom or one per namespace
  (`(io sys code)`), so that a type says which capabilities it reaches.
- Whether the record of declarations is per program or per module file
  (a runtime's library declaring them once, its users importing them).
- Whether `syscall-available?` should also take a host name, for a
  program that asks without declaring (likely not: declaring is the
  point).

## What Fixpt does (2026-10-26)

All of the request, on all of Fixpt's machines, in both checkers (each the
other's twin, compared by `tests/checker.rs`, `syscall_declarations_alike`).
Where it differs, or says more:

1. **A declaration is two definitions** (`fixpt-fx26/src/syscall.rs`;
   `check-program.fx`, `k-define-syscall`), which every machine runs as it
   runs any:

       (define %syscall-available:NAME bool (%syscall-available? HOST TEXT))
       (define NAME T (lambda ((x1 P1) …) (the R (%syscallN LABEL HOST TEXT x1 …))))

   `TEXT` the canonical form, `LABEL` `syscall NAME ("HOST")`, every part of
   `T` canonical; for a required one, the first is `(begin
   (%syscall-require LABEL HOST TEXT) #t)`. So "the record of declarations
   in what it compiles" is these definitions, the host name and the
   canonical text in them as literals, and no runtime needs more than three
   primitives (`fixpt_runtime::syscall`, `%fx26-syscall-require`,
   `%fx26-syscall-available?`, `%fx26-syscall`). A `poly` value must be
   pure, so the required check is the first definition's, not the
   procedure's.
2. **The check at load is the declaration's own run**: a top-level form,
   it runs before any form after it, and after any before it. Fixpt has no
   load phase apart from running a program's forms in order; a runtime's
   declarations come first, as its other definitions do. A heap image
   (`fixpt build`) keeps the definitions as they ran, so its checks ran
   when it was built: an image runs on the Fixpt that made it.
3. **`syscall-available?` names the first definition**: both parsers read
   `(syscall-available? NAME)` as the variable `%syscall-available:NAME`,
   which the checkers refuse, unbound, as "`syscall-available?` takes the
   name of a syscall declared"; so `syscall-available?` is no procedure,
   and needs no state of the checker's at a use.
4. **Containment.** `--syscalls` is the driver's flag (`fixpt --syscalls
   …`; `Checker::syscalls`, `check-syscalls!`). A module file built in is
   allowed too, but a declaration is a top-level form and a module file is
   an expression, so none can hold one yet: a runtime's library declares
   its syscalls as a program's top-level forms.
5. **What the declaration may say**, beyond the request's (each refused
   with its own message, alike in both checkers):
   - the host name: a namespace and a name of lower-case letters, digits
     and `-`, then a version, a number from 1 with no leading 0;
   - a `poly`'s regions are the only ones its type may name (`@k`, `heap`,
     a frozen region: refused), since a constant region means nothing to
     another runtime;
   - the effect's atoms: reads, writes and allocations of those regions,
     `io` effects, `spin` and `nondet`; and it must hold `(io sys)`;
   - the program's own convention, and no specification;
   - at most six arguments (`%syscall0` to `%syscall6`).
6. **The canonical form**: region variables print as their names, `r1`,
   with no `@`; atoms sort by their text byte by byte, which for these
   (ASCII) is FX-26's `string<?`.
7. **Fixpt's table** (`fixpt_runtime::syscall::SYSCALLS`): all three.
   `code:exec-view/1` always gives -1: a collection moves a flat array, and
   Fixpt pins none, so it never keeps one at an address that does not
   change. `code:flush/1` does nothing, since no view is made.
   `code:page-words/1` is the system's page size over 8.
8. **The evaluator written in FX-26** (`fx-ast-eval`) is a runtime of its
   own, with its own table (`eval-prims.fx`): the same three, giving the
   same answers (its page's words asked of the runtime it runs on), so
   every machine answers alike (`fixpt-cli/tests/syscalls.rs`).
9. **Not compiled from the Rust checker's trees**: the FX-26 compiler's
   entry for a program the Rust checker checked (`compile-program`, which
   `fixpt compile` and the bootstrap's tests use) has no canonical form to
   expand with, and refuses a declaration, saying so. What runs a program
   (the REPL, `fixpt run`, `eval`) checks it with the checker written in
   FX-26 (`compile-checked`), which expands it.

The open questions, decided:

- **`(io sys)` is one atom.** The `io` kinds are a fixed family, ordered
  alike in both checkers (`IoKind`, `k-io-kind-name`); one per namespace
  would make it open. A type says that it reaches the runtime; which
  capability, its declaration says.
- **Per program.** Each program declares what it calls; a runtime's
  library declares its own, in the program that loads it (4 above).
- **`syscall-available?` takes only a name declared**, no host name:
  declaring is the point.

