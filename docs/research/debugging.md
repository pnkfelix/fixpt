# Debugging compiled FX-26: `lldb`, or a debugger of our own

Research note, 2026-10-05, answering the user's question: what would it
take for the code `fixpt` compiles at run time to work with `lldb`; and,
asked next, whether to do that or write a debugger of our own. What is
marked *verified* was tried on this machine, against that day's build
(`lldb-2103.0.34.103`, Xcode's). What is marked *(from memory)* was not
checked against a source while writing; this note was written offline.

## 0. The answer, up front

- **`lldb` already walks through compiled code** (verified, §1). The
  native convention keeps arm64 frame records, and the entry trampoline
  links the native stack to the Rust one, so a backtrace from a loop deep
  in compiled FX-26 code reaches `main`. Every compiled frame is a bare
  address: what is missing is names, then source lines, then values.
- **Names are a bounded job** (§2.1): register each piece of code through
  the GDB JIT interface, as an in-memory Mach-O object with a symbol
  table. A few hundred lines in `fixpt-native`. Lines and values (§2.3,
  §2.4) are projects: the compilers would have to carry source spans to
  each instruction, and `lldb` would need formatters for tagged values.
- **A debugger of our own can know far more, and cover every machine**
  (§3): the runtime already has the registry of code, the frames' stack
  maps, the printers for values, and the checker's types. It needs a way
  to stop and resume (fuel is nearly one), and source spans carried through
  the compilers, which both paths need.
- **They are not exclusive, and the work overlaps** (§4). Spans through
  the compilers serve both. Names for `lldb` cost little and stay useful
  for what our own debugger cannot see: bugs in the runtime, the
  collector, or the code generators themselves.
- **Recommendation** (§5): names for `lldb` first (cheap, helps debug
  `fixpt` itself); then spans through the compilers; then decide, with the
  REPL as the front end of our own debugger if we build one.

## 1. What works today (verified)

A program that recurses five frames and then loops, run as

```
fixpt --dialect fx26 --fx26-run cellular --cellular-machine registers \
      --calling-convention native --step-limit none eval spin.fx
```

and attached to with `lldb -p PID -o "thread backtrace all"`:

```
frame #0: 0x0000000300000088              go, the loop
frame #1: 0x000000030000071c              deep (five times)
…
frame #6: 0x00000001139d805c              the entry trampoline
frame #7: fixpt`fixpt_native::direct::run + 752
frame #8: fixpt`fixpt_native::direct::DirectMachine::call + 192
…                                         on to main
```

Why it works:

- **Frame records.** A native procedure with a frame saves `x29`/`x30`
  with `stp` and sets `x29 = sp` (`crates/fixpt-native/src/direct.rs`,
  the convention's table at the top). A leaf without a frame keeps its
  return address in `x30`, which `lldb` handles at the innermost frame.
- **The seam.** The trampoline (`trampoline()`, `direct.rs`) makes a
  frame record on the Rust stack, sets `x29` to it, and only then moves
  `sp` to the native stack. The first native frame's link is the
  trampoline's record, whose link is Rust's. Call-outs to Rust
  (`common_foreign`) make a record too.
- **Two code regions.** Compiled words are in the heap's code area
  (`0x3…`); the machine's own code (trampoline, common trap, stubs) is in
  the `CodeSpace` (`0x1…`). Both are plain executable memory to `lldb`.

Not verified: breakpoints set in compiled code. The code has a writable
and an executable view (`fixpt-memmgmt/src/exec.rs`, `mach_vm_remap`);
`lldb` writes breakpoints through the task port, which should not care.

Cellular and register code are a different case: they run threaded on the
machine's own stacks, not as arm64 frames. In them `lldb` sees only the
machine's routines (`docol` and kin), never the procedures.

## 2. The `lldb` path

### 2.1 Names: the GDB JIT interface

*(from memory)* GDB and LLDB both read a process-wide linked list of
in-memory object files, rooted at a global named `__jit_debug_descriptor`,
and break on an empty function `__jit_debug_register_code` that the
process calls after each change. Each entry is an object file of a format
the debugger reads: on macOS, Mach-O. LLDB's support is the `JITLoaderGDB`
plugin; this `lldb` shows `plugin.jit-loader.gdb.enable = default`, and
*(from memory)* the default is off on Darwin, so an `.lldbinit` would say
`settings set plugin.jit-loader.gdb.enable on`. To confirm with a first
test.

What it needs from us:

- **A registry.** Nearly there: `crates/fixpt-native/src/faults.rs` keeps
  each installed piece's address, length and name, today only under
  `FIXPT_FAULTS`. Make it always on, or on with a flag.
- **Mach-O writing.** A header, one `LC_SEGMENT_64` with a `__text`
  section at the code's real address (no slide), an `LC_SYMTAB`, a symbol
  per entry point (`fx:go`, `fx:deep`, `fixpt:trampoline`, the stubs).
  The bytes need not be copied in: the section can name the address
  alone. A few hundred lines; `fixpt-native` already hand-encodes arm64,
  this is the same kind of work.
- **Unregistering.** When code is freed (the collected code area, PLAN
  "A collected code area"), its entry must leave the list. Breakpoints in
  it are lost then, as they would be anywhere code is replaced.

What it gives: `bt` with names, `b fx:go`, `disassemble -n fx:go`,
`image lookup -a ADDR`. This is what perf tools and other JITs use the
same interface for *(from memory: V8 and LLVM's ORC/MCJIT register this
way)*.

### 2.2 A stopgap: an `lldb` Python script

A day's work: `command script import tools/fixpt_lldb.py`, giving
`fx-where ADDR` and `fx-bt`, which read the registry out of the process
(an exported symbol pointing at it) and name each frame. No object
files, no plugin setting; names in our commands only, not in `bt`.

### 2.3 Source lines

`bt` showing `okasaki.fx:131`, and stepping by line, need a DWARF line
table per object: address ranges to file and line. The work is upstream
of the debugger:

- **Spans stop at the checker today.** The arena has a span for every
  expression (`Arena::span_of`), used for errors and effect summaries
  (`crates/fixpt-fx26/src/syn.rs`). Neither compiler carries them into
  register code or cells, and `fixpt-native`'s code generators know
  nothing of them.
- **What carrying them means.** Each register-code instruction, and each
  cell, would record the span of the expression it came from; each
  machine instruction would inherit its register-code instruction's. Both
  compilers, the Rust one and the one written in FX-26, to keep them
  agreeing, and the FX-26 one's output is a list the machine assembles,
  so it would grow a span per instruction too.
- **Optimisation blurs it.** Inlining, specialization, join points and
  common subexpressions move code across spans. DWARF can say "inlined
  from" (`DW_TAG_inlined_subroutine`); a first version can just take the
  span of the outermost expression.

### 2.4 Values

DWARF can say where each variable is: arguments in `x1`–`x8`, values
live across a call at `[x29, #24 + 8n]`, the frame's stack map at
`[x29, #16]`. But a value is a tagged word; `lldb` would print
`0x0000000000000054` for the fixnum 42 unless taught otherwise. That is
an `lldb` Python package of data formatters (synthetic children for
pairs, closures, products), reading our tags. Variable names, and types,
need the compilers to carry them too.

### 2.5 What `lldb` will never see well

Cellular and register code (§1). A script could walk the machine's own
stacks there, but at that point it is our debugger, written in Python
against `lldb`'s API.

## 3. A debugger of our own

### 3.1 What we already have that `lldb` does not

- **Every machine, alike.** Cellular, register and native code are all
  ours; one debugger can stop and show a frame in each, where `lldb` sees
  only native frames.
- **Frames we can read.** Native frames carry their stack maps (the mask
  of traced slots, `[x29, #16]`), which say which slots hold values; the
  cellular machine's stacks are already walked as roots by the collector.
- **Values printed as FX-26 prints them**, and their *types*: the checker
  knows each variable's type and effect, which no DWARF formatter would.
  A stopped frame could show `xs : (listof int @q)`, not a word.
- **The REPL as the front end**: `,break go`, `,bt`, `,frame 2`,
  `,locals`, `,step`, `,continue`, beside `,disassemble-asm` and
  `,apropos`. Nothing to install, the same in a built executable.

### 3.2 What it needs

- **A way to stop and come back.** Fuel is nearly one: native code checks
  `x28` on entry and on every loop's back edge, so setting fuel to zero
  stops any loop at its next check. Today running out *abandons* the
  run (the common trap leaves through the saved Rust stack pointer,
  `direct.rs`). To debug, the fuel trap would instead call out to Rust,
  as `common_foreign` does, leaving the native stack in place, and return
  to continue. That is also an interrupt (`^C` sets fuel to zero) and
  a profiler's sampling point.
- **Breakpoints.** Two ways, both ours to choose:
  - patch the code: write a call to a break stub over the first
    instruction of the procedure, keeping the original to step over; or
  - recompile: compile the procedure again with a check at each point
    where a break may go (a debug build of one procedure, swapped in by
    the same mechanism that redefines a global; the guards of guarded
    inlining already know how to fall back when a global changes).
- **Spans through the compilers** (§2.3), for "where am I" in source
  terms. The same work `lldb` lines need.
- **Stepping.** By recompiling with a check per expression (a cellular
  word per expression already exists in effect: the cellular machine has a
  step loop), or by breakpoint at the next expression's code.

### 3.3 What it gives up

It cannot debug `fixpt` itself: a bad code generator, a collector bug, a
corrupted heap, a crash. Those are the bugs `lldb` is for, and the ones
the project has had most of (`docs/performance.md`, PLAN's B1 and Q1).
Our debugger would sit on top of a runtime that must already be sound.

### 3.4 Precedents *(from memory)*

- **SBCL and the Lisp machines' heirs**: their own debugger in the REPL,
  backtraces from the compiler's own frame layout, `(debug 3)` making
  code keep what the debugger needs. GDB sees SBCL's frames poorly.
- **Chez Scheme**: an inspector over continuations and closures, with
  source information kept when compiled for it.
- **Racket**: `errortrace` instruments code by recompiling it with marks
  at each expression; the stepper and DrRacket's debugger the same way.
  Continuation marks are what it uses, and FX-26 has them.
- **The JVM, V8**: their own debugging protocols (JVMTI, the Chrome
  DevTools protocol), and the GDB JIT interface beside them for native
  profilers and debuggers.

The pattern: a language runtime's own debugger for the language, and
names handed to the native debugger for everything under it.

## 4. Where the two overlap

| Work                                          | `lldb` | ours  |
| --------------------------------------------- | ------ | ----- |
| A registry of compiled code (exists, gated)   | needs  | needs |
| Names in Mach-O objects, JIT interface        | needs  | —     |
| Spans carried through both compilers          | lines  | needs |
| Fuel trap that calls out and resumes          | —      | needs |
| Breakpoints                                   | free   | needs |
| Formatters for tagged values                  | needs  | free  |
| Types of variables                            | —      | free  |
| Cellular and register code                    | —      | free  |
| Bugs in the runtime and code generators       | yes    | no    |

## 5. Recommendation

1. **Names for `lldb`** (§2.1), with the registry always on. Cheap, and
   it serves the debugging we do most: of `fixpt` itself. First test:
   the JIT loader enabled, `bt` naming `fx:go` in §1's program.
2. **Spans through the compilers** (§2.3), whichever debugger follows:
   both need it, and errors at run time would gain a source location too
   (today a trap reports which word, not where in it).
3. **Then decide**, with the user. If the debugging that matters is of
   FX-26 programs, our own, in the REPL (§3), starting with the resumable
   fuel trap, which also gives `^C` and sampling. If it is of `fixpt`,
   `lldb` lines (§2.3) and formatters (§2.4).

## Sources

- Verified on this machine: the backtrace in §1 (`lldb -p`), and `lldb
  --batch -o 'settings show plugin.jit-loader.gdb.enable'`.
- This repository: `crates/fixpt-native/src/direct.rs` (the convention,
  `trampoline`, `common_trap`, `common_foreign`, `TRAPS`),
  `crates/fixpt-native/src/faults.rs`, `crates/fixpt-native/src/
  codespace.rs`, `crates/fixpt-memmgmt/src/exec.rs`,
  `crates/fixpt-fx26/src/syn.rs`.
- From memory, unchecked: the GDB JIT interface's names and protocol;
  LLDB's `JITLoaderGDB` and its Darwin default; the precedents of §3.4.
