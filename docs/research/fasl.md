# `.fasl` files for FX-26

A design note, 2026-10-28; nothing here is implemented. The user's
direction: a `.fasl` is compiled for fast loading of a file's types,
procedures and data, gives the same interface its `.fx` gave, and stays
as decoupled from the files it loads as the `.fx` was; a `load-module`
stays a load, not made eager. What a file depends on is recorded in its
`.fasl`, by digest, so that a stale one is found. This note answers how
a `.fasl` relates to the files it loads and to the globals of the program
that loads it, after Larceny (`~/Dev/LangPlay/accomplice`) and
`separate-compilation.md`, whose stages S3 and S6 this is a form of.

## What Larceny does

A Larceny `.fasl` is a file of Scheme data, read by the ordinary reader
with four extensions (`src/Asm/Shared/makefasl.sch`):
- a compiled top-level form is `(#^P(code constants #f))`, a list whose
  operator is a literal procedure and which has no arguments, so that
  `load` evaluating it runs the form; uncompiled forms may be mixed in;
- `#^B"…"` is a bytevector (the code);
- **`#^Gname` in a constant vector is a global's cell.** The reader calls
  `(global-name-resolver)` on the name (`src/Lib/Common/reader.sch:2221`),
  which `load` binds to `(environment-get-cell env name)`
  (`src/Lib/Common/load.sch:167`): the cell of that name in the
  environment the file is loaded into, made if absent. "The linker is
  implicit in the loader." Nothing else in a `.fasl` names a global.

So compiled code never holds a global's index or address, only its cell,
and the cell is found by name at load. A redefinition later writes the
same cell, which every loaded form shares. Larceny checks nothing at link:
a Scheme global has no type.

## What fixpt has to start from

- **Compiled code already reaches a global by its cell.** The FX-26
  compiler's global is a `wglobal`, made by `make-global n`, which knows
  its name (`compile-programs.fx`, `c-push-global`); words refer to it as
  a constant. That is Larceny's cell: a `.fasl` writes it as its name.
- **A load is one hidden global**, `%shared:path` (or `%shared:input:path`),
  defined before the form that loads it; each load is a reference to it.
  A loaded file sees the standard environment and the `%shared:` globals
  of what it loads, and nothing of the program (`docs/fx26.md`, "Modules").
  So a module file's code links to `%shared:` cells alone.
- **A load's abstract types are named for the file** (`x.fx..t`), so that
  every load of a file, from any file, has the same ones. Identity by path
  already, as `separate-compilation.md` S3 asked for.
- **Making a loaded file's module is pure but for reading globals**, and
  the globals it can read are its own loads'. A file with state is a
  `lambda` that its client applies.
- **Images** carry heap graphs with code (`save_native_front_end`).

## The design

### A `.fasl` is three parts

1. **The header: what it was made from.** The digest of its own text; the
   sections of code it has (below); the fixpt build (the
   front end's cache key); and, for each file it loads, the path and that
   file's interface stamp (below).
2. **The interface, as s-expressions**: what `load-moduleof` of the file
   gives, its parameters (`module-parameters`, kept as written, as the
   user suggested, so that a client's `(load-moduleof "f" args …)` takes
   them apart as now), its abstract and generative types and their
   representations, effect and type abbreviations, and the facts its
   clients' checking uses (known lambdas, conversions, lemmas). Printed by
   the checker in a canonical form both checkers read and the agreement
   tests compare, as `standard.rs`'s entries are. Its digest is the
   file's **interface stamp**.
3. **The code and data**: the file's compiled top-level forms and the
   constants they hold, as a heap graph (procedures, code bloblets,
   literals), with every `wglobal` written as its name, Larceny's `#^G`.

Checking a client needs only part 2; running it needs part 3. Each is
read only when wanted.

### Loading a client: the files it loads stay loads

When the driver meets `(load-module "b.fx")` in `a.fx`, and `a.fasl` is
fresh, it does not read `b.fx` and does not check it. It needs, at once,
only `b`'s interface, for `%shared:b.fx`'s type: read from `b.fasl`'s
part 2 (or checked from `b.fx` and its `.fasl` written, if there is none
or it is stale). `b`'s code is linked when `%shared:b.fx` is first
needed. Since making a loaded module is pure and reads only its own
loads, making it at first use instead of before the loading form is
unobservable, so it can be lazy (Larceny is not: its `load` runs every
form). That is the decoupling asked for: `a.fasl` holds none of `b`.

### Linking to globals: by name, with types

`a`'s code refers to globals by name. At load, each name resolves to the
loading session's newest cell of that name, as Larceny's resolver does
and as `c-global-find n -1` finds now; a name with none gets a fresh,
unset cell. For a module file, the names are `%shared:` ones and the
standard environment's, so this links the files a program loads.

For a **top-level** file (`fixpt run a.fx b.fx`, `,load`), which sees the
globals defined before it, Larceny's untyped link is not enough: `a.fasl`
was checked assuming each global it uses had some type. So its header
also lists, for each global it reads or calls, the name and the type it
was checked against (the import table of C10,
`type-and-effect-directions.md`). The link check is the redefinition
rule's (`fits_old`, `docs/fx26.md`, "Redefinition"): the session's type of
the name must fit the one assumed, or `a` is checked again from source.
For its own definitions it gives the session their types, as checking
them would have. Effects that name globals (`(read (globals f))`) name
them by the same names, so they are linked too.

### When a `.fasl` is stale

A digest of the source is not enough on its own: `a`'s checking read `b`'s
interface, which depends on `c`'s, and an inlined or folded member of `b`
(`TODO.md` §42) depends on `b`'s implementation. So:
- `a.fasl` is fresh if `a.fx`'s digest matches, the build matches, and each
  file it loads has the interface stamp recorded (checked recursively,
  each file's `.fasl` checked once per session);
- an interface stamp covers what clients use, so changing a body of `b`
  without changing its type or what it lets be inlined leaves `a` fresh
  (the cutoff of S4). Until folding across files records what it folded,
  the stamp includes the folded members' values.
- For a top-level file, the fit of its import table is the check, not a
  digest.

### `include`

`(include m)` takes a module's name, and copies names into scope; the code
of `a` still reaches `m`'s members through `m`'s value (the `%shared:`
cell, a parameter, or a global). So `include` makes no eager load
either. What it adds is dependence on `m`'s interface, which `a` records
already as a stamp. A module parameter's included names (`module-parameters`
with a module binder) are the client's argument's, so they are in the
parameter's type, in `a`'s interface, not in a stamp.

## What it costs

- **A canonical interface printer and reader**, both checkers, agreeing
  byte for byte: effects sorted (the FX-26 checker's atom order differs
  from Rust's), generative types by path, and the structural naming of
  aliases (DONE §149) kept so interfaces stay short.
- **Serializing the code graph** with names for cells: a graph copy as
  `save_native_front_end` does, cells replaced by symbols, and the reverse
  at load. Native code is carried as bloblets as the front end's cache
  carries it, each native section naming its machine and convention.
- **Checker state per file**: today a program is one stream of forms, and
  the hidden `%shared:` globals land in it. Checking a file from its
  dependencies' interfaces, not their forms, is the step from "flattened
  program" to "units" (S3).
- **The facts keyed by position** (`separate-compilation.md` S2) must be
  keyed by file, or inlining across a `.fasl` boundary is wrong.

## Decided (the user's, 2026-10-28)

1. **Beside the `.fx`**: `a.fasl` next to `a.fx`, as Larceny and Chez put
   them; a policy kinder to version control may come later. They are not
   meant to be checked in.
2. **Native code in the `.fasl`, and cellular words too** (the user's: "it
   would be slick if our `.fasl` files supported both"), by a codegen
   policy given to `compile-file`, not every variant made:
   - **The default, two tiers a procedure**: its cellular word, with the
     register-code twin in it (8), which any machine falls back on and
     from which native code is made again; and native code for the
     machine `compile-file` runs on (here, `fast`: x86_64, nativecc).
   - **Later, as options**: native code for more targets (an
     architecture and a convention, for a tree the Mac shares), or words
     alone, a small `.fasl` each machine compiles natively at load. The
     format leaves room for a list of native parts; the first version
     makes one.
   - A loader with no native code of its own in a `.fasl` takes the words
     and compiles them, as it would a source's compiled words, but not
     checked again: a `.fasl` of another machine is slower to load, not
     stale.

   Much of it comes from the code area's uniform representation (the
   user's point; `docs/research/code-stubs.md`): every procedure's code is
   a bloblet, cellular words in the stubbed part with a suffix that enters
   `foreign`, native code in the other. So a `.fasl` of code bloblets
   holds either kind, and a loader puts each bloblet in its part with no
   case for which. What is not free: the stub's bytes are an
   architecture's (`jmp [r15 + 288]` on x86_64), so a word's stub is
   written as a mark and made at load; and native code is one target's,
   so a loader of another uses the words. The stub is the tiering patch point the stubs note
   names: a word whose native code the loader can use has its stub made a
   jump to it, so words and native code are one procedure's two tiers,
   not two sections. The native compiler takes some 580K cycles a procedure
   (`TODO.md` §126); compiling the front end natively was 2.9G cycles of a
   16.8G load, and keeping its native code took a 6-line program from
   0.55 s to 0.15 s on the arm64 Mac. Register code is no third tier
   (8).
3. **Any file**, not module files alone: `,load` takes any file, so a
   top-level file's `.fasl` has its typed import table from the first.
   A `.fasl` begins with a marker, `#fasl(…)`, saying it is one and what
   it assumes of the context that loads it (the build, the sections of code
   it has, what kind of file it was: top-level, module, `load-input`,
   `module-parameters`), so that `load-module`, `load-input` and `,load`
   know what they have before reading the rest.
4. **Made by an explicit command**: `,compile-file` at the REPL, or a
   `(compile-file …)`, to be settled; never as a side effect of a run.

5. **A load finds one by the source's path, because staleness is
   checked** (the user's: opportunistic only if checked; else a path
   with no extension that dispatches). `(load-module "foo.fx")` uses
   `foo.fasl` beside it when it is fresh, and the source when not, so no
   program changes to use compiled code. Fresh by digest (the source's,
   and its loads' interface stamps), not the write date, which a checkout
   or a copy changes without changing the text; a write date and size
   matching those recorded can let the digest be skipped, as `git`'s index
   does, if hashing the source shows in a profile.

6. **A stale `.fasl` met: the source, with a warning** (the user's), as
   Larceny's `require` does ("loading source in favor of stale fasl
   file", `src/Lib/Common/require.sch:36`, by write date where this uses
   the digests). The warning names the `.fasl` and why it is stale (its
   source changed, or which load's interface did). It is not rewritten: a
   `.fasl` is made only by its command (4).

7. **Made by any of three**: `,compile-file` at the REPL, `(compile-file
   …)` in a program, and `fixpt compile-file` at the shell (the user's:
   all three), the same work behind each.
8. **Register code travels with its word.** The `fx-regs-*` machines,
   the default among them, run register code (PLAN.md 13h′), which is not
   a third kind beside words and native code: it is each word's twin
   (`compile.fx`, `c-registers`; `compile-twins.fx`), kept in the word, made
   only when the compiler is asked. So `compile-file` always makes the
   twins, and a `.fasl`'s words serve every machine: the cellular ones run
   them, the register ones compile their twins natively.
