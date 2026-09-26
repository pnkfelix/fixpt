# Copy-and-patch with Rust-compiled stencils, on arm64 macOS

Research note, 2026-09-25. It asks whether copy-and-patch compilation, with
stencils written in Rust and compiled by **stable** rustc, would be a good
complement to the hand-written arm64 encoder planned for `fixpt-native`
(PLAN.md, Phase A′). The target is arm64 macOS (Mach-O) first.

Every claim is marked as one of:

- **[verified]**: checked on this machine (rustc 1.95.0, LLVM 22.1.2,
  `aarch64-apple-darwin`, cargo 1.95.0, Apple `objdump`/`otool`/`nm`), with
  commands given in §7;
- **[read]**: taken from a cited source and not reproduced here.

## 0. Summary

- **Stable Rust works for this [verified].** A `no_std`, `panic=abort` file of
  `#[no_mangle] extern "C"` functions, compiled with `rustc --emit=obj`, gives
  usable stencils. A 120-line hand-written Mach-O reader in `build.rs`
  extracts their bytes and relocations. Only already-cached crates (`libc`)
  were used, and nothing was fetched.
- **End to end on this Mac [verified].** Stencils were copied into `MAP_JIT`
  memory and their holes patched: two constants, a call to an `extern "C"`
  Rust function, and continuations. Write protection was toggled per thread
  and the instruction cache invalidated. Two chained programs then returned
  the right answers.
  - Chaining is continuation-passing style: trailing branches were dropped so
    control falls through.
  - One run put the region 16 GB away from the host code. That exercised the
    branch veneers.
- **The main gaps against clang are tail calls and the calling convention**:
  - Stable Rust has no guaranteed tail call (`become` is unstable) and no
    `preserve_none`/GHC calling convention (`extern "rust-preserve-none"` is
    unstable) [verified].
  - The workaround is to rely on LLVM's ordinary sibling-call optimisation, and
    to have the build script reject any stencil whose continuation is not a
    plain `B` [verified]. The cost is that stencils calling into the runtime
    save and restore callee-saved registers around the call [verified].
- **Precedent**: `logicaffeine-forge` does Rust-stencil copy-and-patch, with
  the same gates, on Mach-O, ELF and COFF [read].
- **Recommendation**: keep the hand-written encoder for the Phase A′ core
  (NEXT, entry and exit, call glue). Treat copy-and-patch as the likely way to
  build a baseline compiler later, in M10 or step 11 of M12. The deciding
  measurement is when `docs/performance.md` shows hot primitives dominated by
  the cost of calling out to Rust. The patcher is small and could itself be
  written in FX-26 later.

## 1. How copy-and-patch works

### 1.1 The technique (Xu & Kjolstad, OOPSLA 2021) [read]

- **Stencils** are pre-compiled binary fragments, each implementing one
  operation. They have **holes**: missing constants, addresses and jump
  targets.
- **Code generation** looks up a stencil in a table, copies its bytes, and
  patches the holes.
- **Holes are extern symbols.** Stencils are written as C++ functions that
  refer to `extern` symbols. "Since extern variables in C++ are by definition
  defined outside the current module, this forces Clang to emit information
  into the object code that identifies the locations of those missing values."
  The build tool reads the object file's **relocation records** to find them.
- **Continuation-passing style.** "Control is passed directly to the next
  operation instead of being returned to the parent operation." The
  continuation is a tail call, which Clang lowers to a jump.
- **Fall-through.** Stencils are laid out so that a stencil's final jump
  usually targets the next copy. "As these jumps are fruitless, the stencil
  copy simply elides them."
- **The GHC calling convention** has all parameters in registers and no
  callee-saved registers. It gives register pinning for free: passing a value
  to the continuation leaves it in a fixed register.
- **Code model.** On x86-64, stencils must be compiled with a code model that
  suits them, because "Clang by default assumes that the address of an extern
  symbol fits in signed 32 bits."
- **Scale and results.**
  - The WebAssembly library has 1666 stencils in 35 kB.
  - Code generation is "two orders of magnitude faster than LLVM -O0", and the
    code runs 14% faster than -O0 for the high-level language.
  - On WebAssembly it is 39–63% faster than Liftoff.

Sources: <https://arxiv.org/abs/2011.13127>,
<https://fredrikbk.com/publications/copy-and-patch.pdf>,
<https://dl.acm.org/doi/abs/10.1145/3485513>. A tutorial is at
<https://transactional.blog/copy-and-patch/tutorial>.

### 1.2 CPython's JIT (`Tools/jit`, PEP 744) [read]

- **Stencils** come from one C template (`Tools/jit/template.c`), compiled
  once per micro-op.
- **Holes** are symbols named `_JIT_*`: `_JIT_OPERAND0/1`, `_JIT_OPARG`,
  `_JIT_TARGET`, `_JIT_CONTINUE`, and 16- and 32-bit variants. `_stencils.py`
  maps them to `HoleValue`s (CODE, DATA, GOT, OPARG, OPERAND0/1,
  JUMP_TARGET, ZERO, …).
- **Continuations** are `__attribute__((musttail)) return jump(...)`, with
  stencils in `__attribute__((preserve_none))`. The README says Clang is
  required "because it's the only C compiler with support for guaranteed tail
  calls (`musttail`)". The officially supported version is currently LLVM 21.
- **Clang flags** (`_targets.py`):
  - on every target: `-Os -fno-builtin -fno-stack-protector -std=c11
    -fno-unwind-tables -fno-asynchronous-unwind-tables`, plus
    `-Xclang -mframe-pointer=reserved`;
  - `aarch64-apple-darwin` adds nothing target-specific;
  - `aarch64-linux-gnu` adds `-fpic -mno-outline-atomics`;
  - `x86_64-linux-gnu` adds `-fno-pic -mcmodel=medium
    -mlarge-data-threshold=0 -fno-plt`.

  The fetch summarised these lists; they were not re-checked character by
  character.
- **Mach-O arm64 GOT loads.** `ARM64_RELOC_GOT_LOAD_PAGE21/PAGEOFF12` are
  handled as GOT holes: CPython keeps its own small GOT in the stencil's data.
- **GOT relaxation.** `Python/jit.c`'s `patch_aarch64_33rx` relaxes a GOT
  `adrp`+`ldr` pair into one of:
  - `movz reg, X; nop` when the value is below 2^16;
  - `movz`/`movk` when it is below 2^32;
  - `adrp`/`add` when the page delta fits;
  - a PC-relative literal load otherwise.
- **Long branches.** `patch_aarch64_trampoline` patches a 26-bit branch
  directly when it is in range (±128 MB). Otherwise it routes the branch
  through a 16-byte trampoline (`ldr xN, 8; br xN; .quad target`). PRs
  [#123872](https://github.com/python/cpython/pull/123872) and
  [#131041](https://github.com/python/cpython/pull/131041) added this.
- **A trampoline register bug.** Issue
  [#157510](https://github.com/python/cpython/issues/157510) reports that the
  trampoline used `x8`, which AAPCS64 reserves for the indirect result
  address. The fix is `x16`: "The AAPCS64 only allows a veneer to alter x16,
  x17 and the flags". Our experiment's veneer uses `x16` for the same reason.
- **W^X on macOS.** `jit.c` does not use `MAP_JIT`. It maps RW, writes, then
  calls `mprotect(RX)` and `__builtin___clear_cache`. §4.3 confirms locally
  that this is allowed on Apple Silicon without the Hardened Runtime.
- **`preserve_none` on aarch64.** Benchmarks were reported to show "no wins on
  aarch64", moderate wins on x86-64 and big wins on i686. This comes from a
  search summary of the CPython discussion (python/cpython#115802), not
  re-verified. It suggests the missing convention costs less on arm64.

Sources: <https://github.com/python/cpython/tree/main/Tools/jit>,
<https://github.com/python/cpython/blob/main/Python/jit.c>,
<https://peps.python.org/pep-0744/>, <https://lwn.net/Articles/970397/>.

### 1.3 Deegen and LuaJIT Remake [read]

- **Stencils from LLVM IR.** Deegen compiles bytecode semantics written in C++
  to LLVM IR. It rewrites the IR (GHC calling convention, unified function
  prototypes) to get around the two main problems with `musttail` at C/C++
  level, then compiles to objects and reads the relocations: "at runtime, we
  can act as the linker".
- **Hot/cold splitting and fall-through.** Deegen splits hot and cold code
  into separate sections with an assembly-level pass. A "jump-to-fallthrough"
  pass reorders blocks so that dispatch jumps become fall-throughs.
- **Constant ranges.** A constant-range analysis keeps runtime constants in
  `[1, 2^31 − 2^24)` on x86-64. This prevents miscompilation from what LLVM
  assumes about symbol addresses. The same hazard shows up in Rust in §3.5.
- **Results.** LuaJIT Remake's generated baseline JIT is reported to have
  negligible start-up cost and to run about 360% faster than PUC Lua.

Sources: <https://sillycross.github.io/2023/05/12/2023-05-12/>,
<https://sillycross.github.io/2022/11/22/2022-11-22/>,
<https://arxiv.org/abs/2411.11469>,
<https://compilers.stanford.edu/software/deegen/>.

## 2. Rust precedent [read]

**`logicaffeine-forge`**
(<https://docs.rs/logicaffeine-forge/latest/logicaffeine_forge/>, release
note <https://logicaffeine.com/news/release-0-10-0-copy-and-patch-jit/>) is
the closest match found.

- **Build.** "build.rs compiles the `#![no_std]` `stencils/int_stencils.rs`
  (94 hand-written `logos_stencil_*` fns) with `rustc --emit=obj`". It then
  extracts code and relocations with the `object` crate, normalising across
  Mach-O, ELF and COFF.
- **Holes** are "undefined `extern` symbols … LLVM cannot fold".
- **Two build gates.** The first is "leaf purity": "a reloc to a non-hole
  symbol is an error". The second is "tail calls": "each continuation site
  must decode as an unconditional `b`/`jmp`".
- **arm64 macOS** uses `mmap(MAP_JIT)`, `pthread_jit_write_protect_np`
  toggling and `sys_icache_invalidate`.
- **Relocations handled:** Branch26, Page21, PageOff12, GotPage21,
  GotPageOff12, Rel32, GotRel32, Abs64.

Its source was not inspected. The design we reached independently in §4 has
the same shape and the same two gates. Other copy-and-patch projects found are
in C or C++: <https://github.com/clflushopt/copy-and-patch-jit>,
<https://github.com/Kimplul/copyjit>, <https://github.com/PRL-PRG/rcp>.

## 3. What stable rustc offers

### 3.1 Relocation and code models [verified]

- **Available models.** `rustc --print relocation-models` lists `static pic
  pie dynamic-no-pic ropi rwpi ropi-rwpi default`. `--print code-models` lists
  `tiny small kernel medium large`.
- **On Mach-O arm64, `static` and `pic` give identical stencils.** Undefined
  extern data symbols are reached through the GOT
  (`adrp`+`ldr` = `GOT_LOAD_PAGE21` + `GOT_LOAD_PAGEOFF12`). Calls and tail
  calls to undefined functions are `BL`/`B` with `BRANCH26`.
- **`-C code-model=large`** turns every call and continuation into
  `adrp`/`ldr`/`br x3` through the GOT: indirect and slower. Do not use it.
- **`-C code-model=tiny`** fails: "tiny code model is only supported on ELF".
- **Recommendation:** `-C relocation-model=static -C code-model=small`.
  Handle GOT loads in the patcher (as CPython does), and reach far targets
  with veneers.
- **No `-fno-plt`/`-mcmodel=medium` style tuning is needed.** Rust has no
  stable way to mark an extern symbol hidden or dso-local (`#[linkage]` and
  `-Z default-visibility` are unstable). On Mach-O this does not matter,
  because GOT loads are easy to patch.

### 3.2 `no_std`, `panic=abort`, panics [verified]

- **The setup.** `#![no_std]` with a `#[panic_handler]` (a `loop {}`) and
  `-C panic=abort` compiles to a bare object. The panic handler lands at
  offset 0 as local `ltmp0` and is not copied.
- **Anything that can panic breaks leaf purity.** A slice bounds check
  produces a `BL core::panicking::panic_bounds_check` and a `PAGE21/PAGEOFF12`
  pair to a local `l_anon…` constant (the panic location). The build gate in
  §4 rejects both.
- **Stencils must therefore be panic-free.** Use `get_unchecked`, `wrapping_*`
  arithmetic and explicit checks that branch to an error hole. Checked
  arithmetic is not an option here.
- **The host side.** Rust functions that stencils call must be `extern "C"`.
  Since Rust 1.81 a panic escaping an `extern "C"` function aborts rather than
  unwinding into JIT frames, which have no unwind info
  (<https://blog.rust-lang.org/2024/09/05/Rust-1.81.0.html>) [read].

### 3.3 Tail calls [verified]

- **`become` is not available.** It gives `error[E0658]: become expression is
  experimental` (tracking issue
  <https://github.com/rust-lang/rust/issues/112788>). The tracker reports the
  RFC is not yet accepted. It is waiting on the semantics of indirect and
  by-move arguments, and on "good LLVM support of all supported targets" [read].
- **`extern "rust-preserve-none"`** gives `error[E0658]: … experimental`
  (issue #151401). No GHC or `preserve_none` convention is reachable on stable.
- **The workaround: sibling-call optimisation plus a gate.**
  - At `-O`, LLVM turned every `_JIT_CONTINUE(...)` in tail position into a
    plain `B` (`BRANCH26` on opcode `0x14000000`), even in stencils with a
    frame. It restores callee-saved registers, then branches.
  - At `-C opt-level=0` it emits `bl _JIT_CONTINUE; …; ret`.
  - When a local's address escapes, `-O` also emits `BL`. The `st_escape`
    test in §4 hit this, and the gate rejected it.
  - So the build script must check that every continuation relocation sits on
    a `B`, and fail the build otherwise. That makes a missed tail call a build
    error, not a stack leak.
- **Signature discipline.** All stencils share one `extern "C"` signature, so
  LLVM can always do the sibling call. Up to 8 integer arguments go in
  `x0`–`x7`, and a return pair in `x0`/`x1`; these are the pinned VM
  registers.
- **What is lost without `preserve_none`.** A stencil that calls a runtime
  function must keep its live pinned values in callee-saved registers across
  the call. `st_call1` spent 4 instructions on it:
  `stp x20,x19 / stp x29,x30 / add x29 / mov x19,x1`, plus the matching
  restores. CPython's own measurements suggest `preserve_none` buys little on
  aarch64 (§1.2).

### 3.4 `extern "C"`, `#[no_mangle]`, holes [verified]

- **Stencils** are `#[unsafe(no_mangle)] pub unsafe extern "C" fn st_*(…)`,
  so their symbols are `_st_*`.
- **Holes are undefined externs** in an `unsafe extern "C" { … }` block:
  - continuations and calls: `fn _JIT_CONTINUE(acc: u64, env: *mut u64) ->
    u64;` and `fn _JIT_CALL(x: u64) -> u64;`;
  - constants: `static _JIT_OPERAND: u8;`, whose *address* is the value, read
    as `(&raw const _JIT_OPERAND) as u64`.

  Mach-O prefixes them, so they appear as `__JIT_*`.

### 3.5 Hazard: LLVM reasons about hole addresses [verified]

A hole's value is an address as far as LLVM knows, so LLVM assumes it is
non-null and aligned:

- `if (&raw const _JIT_OPERAND) as u64 == 0 {…}` was folded away entirely.
- With `static _JIT_OPERAND8: u64`, the expression `addr & 7` was folded to
  the constant `0`.

This is the hazard Deegen guards with its constant-range analysis. There are
two fixes:

- **Declare value holes as `u8`,** which removes the alignment assumption,
  **and never patch in 0**. This alone is fragile.
- **Launder the address through an empty inline-asm barrier.** This is
  stable, and it verified:
  ```rust
  let mut k = (&raw const _JIT_OPERAND) as u64;
  core::arch::asm!("/* {0} */", inout(reg) k, options(pure, nomem, nostack, preserves_flags));
  ```
  It costs no instructions, and the compare against zero survived.

### 3.6 Helper calls and stack probes [verified]

- **Stack probes are inline, not calls.** A 70 000-byte frame compiled to
  `sub sp, sp, #0x1000; str xzr, [sp]` probing, with no `___chkstk_darwin`.
- **Libcalls do appear.** Whole-array zeroing called `_bzero`,
  `ptr::copy_nonoverlapping` called `_memcpy`, `f64 %` called `_fmod`, and
  `u128 /` called `___udivti3`.
- **`#![no_builtins]` (stable crate attribute)** stopped LLVM turning a
  hand-written zeroing loop into `_bzero`. It does not remove libcalls for
  explicit copies, float remainder or 128-bit division.
- **The policy:** an allowlist of such symbols, resolved at patch time to
  addresses taken in the host (`libc::memcpy`, …), and reached through veneers.
  Everything else is rejected.
- **The machine outliner** (`OUTLINED_FUNCTION_*`) would be a non-hole `BL`.
  It did not appear at `-O` or `-Oz` here. `-C llvm-args=-enable-machine-outliner=never`
  is accepted by stable rustc as a guard.
- **Flags a stencil build should pass:** `-C panic=abort -C opt-level=3
  -C relocation-model=static -C code-model=small -C debuginfo=0`, with
  `#![no_std]`, and `#![no_builtins]` where useful.
  - `-C llvm-args` is a stable flag, but what it accepts is LLVM-version
    dependent.
  - rustc also emits `__compact_unwind`, `__eh_frame` and
    `LC_LINKER_OPTIMIZATION_HINT`. They are ignored; only `__TEXT,__text` is
    copied.

## 4. The experiment (arm64 macOS, end to end) [verified]

The scratch project is at `/private/tmp/claude-501/cnp/e2e`, outside the
repository. It depends only on `libc = "0.2"`, which resolved to the cached
0.2.189 with `cargo build --offline`.

- **`stencils/st.rs`**: five stencils sharing
  `extern "C" fn(acc: u64, env: *mut u64) -> u64`.
  - `st_add_const`: acc += K.
  - `st_call1`: acc = rt(acc).
  - `st_store_env`: env[K] = acc.
  - `st_div_env0`: two continuation sites.
  - `st_exit`: `ret`, back to the host.
- **`build.rs`**, about 120 lines:
  - runs `$RUSTC --edition 2024 --crate-type lib --emit obj -C opt-level=3 -C
    panic=abort -C relocation-model=static -C code-model=small -C
    debuginfo=0`;
  - parses the Mach-O by hand: `mach_header_64`, `LC_SEGMENT_64` sections,
    `LC_SYMTAB`/`nlist_64`, and `relocation_info`;
  - finds each stencil's extent as its symbol up to the next symbol in
    `__text`;
  - generates a Rust table of `code: &[u8]` and `holes: &[Hole]`;
  - enforces three gates:
    - every relocation is `extern` and names a `__JIT_*` hole;
    - every kind is BRANCH26 or GOT_LOAD_*;
    - every `_JIT_CONTINUE` site is a `B`.
- **`src/main.rs`**, about 160 lines, is the patcher:
  - `mmap(PROT_RWX, MAP_PRIVATE|MAP_ANON|MAP_JIT)`;
  - `pthread_jit_write_protect_np(0)`, copy and patch, then
    `pthread_jit_write_protect_np(1)`, then `sys_icache_invalidate`.
    `sys_icache_invalidate` is declared by hand: `libc` 0.2.189 has `MAP_JIT`
    and `pthread_jit_write_protect_np` but not this function.
  - **BRANCH26**: patched directly when within ±128 MB, otherwise through a
    veneer `ldr x16, #8; br x16; .quad target`.
  - **GOT_LOAD_PAGE21/PAGEOFF12**: patched to a deduplicated 8-byte slot in
    the same region, holding the constant or function address.
  - **Fall-through**: a trailing `b CONTINUE` is dropped when the next stencil
    follows immediately.

Extracted stencils (`stencils.txt`, generated by `build.rs`):

```
_st_add_const [0x4..0x14) 16 bytes
   +0x0000 GOT_LOAD_PAGE21      __JIT_OPERAND    insn=90000008   adrp x8
   +0x0004 GOT_LOAD_PAGEOFF12   __JIT_OPERAND    insn=f9400108   ldr  x8,[x8]
   +0x000c BRANCH26             __JIT_CONTINUE   insn=14000000   b
_st_call1 [0x14..0x38) 36 bytes
   +0x0010 BRANCH26             __JIT_CALL       insn=94000000   bl
   +0x0020 BRANCH26             __JIT_CONTINUE   insn=14000000   b
_st_div_env0 [0x38..0x50) 24 bytes      two CONTINUE sites (+0xc, +0x14)
_st_exit [0x50..0x54) 4 bytes           ret
_st_store_env [0x54..0x64) 16 bytes     GOT_LOAD pair + CONTINUE
```

Run output, with `FAR=1` asking `mmap` for a region 16 GB from the host text:

```
JIT region at 0x502190000; rt_mul3 at 0x10219e234; distance 16383 MB
prog1(7) = 18496  (expected 18496) OK         # ((x+5)*3+100)^2
prog1(0) = 13225  (expected 13225) OK
prog1(1000) = 9703225  (expected 9703225) OK
prog1: 92 bytes, 4 tail branches dropped, 2 veneers
prog2(acc=20, env0=4) = 5, env[2]=20  OK      # env[2]=acc; acc/=env[0]
prog2(acc=20, env0=0) = 0, env[2]=20  OK
prog2: 36 bytes; slots used 3
```

- **Without `FAR`,** the region landed within 1 MB of the host code and no
  veneers were needed.
- **The emitted code** was disassembled by wrapping the bytes in `.byte`
  directives, assembling with the local `clang -c -arch arm64`, and running
  `objdump -d`. It shows the stencils back to back:
  - `adrp/ldr/add` for constants;
  - `bl` to a veneer for the runtime call;
  - an internal `b` in `st_div_env0` that now reaches the next stencil;
  - no trailing jumps.
- **The gates were tested** on a copy of the project:
  - adding a slice-indexing stencil failed the build with `reference to
    …panic_bounds_check is not a hole`;
  - adding a stencil whose local's address escapes failed with `continuation
    is not a tail branch (B); rustc did not tail-call`.

## 5. arm64 Mach-O specifics

### 5.1 Relocation types

The enum is from `mach-o/arm64/reloc.h` in xnu [read]:
<https://github.com/apple-oss-distributions/xnu/blob/main/EXTERNAL_HEADERS/mach-o/arm64/reloc.h>.
The patch rules are those of `Python/jit.c` and our patcher [verified for the
first and third].

| type | insn | patch |
|---|---|---|
| `BRANCH26` (2) | `B`/`BL` | `imm26 = (T − P) >> 2`, bits 0–25; ±128 MB, otherwise a veneer (x16/x17 only) |
| `PAGE21` (3) | `ADRP` | `d = (T>>12) − (P>>12)`; `immlo = d & 3` in bits 29–30, `immhi = d >> 2` in bits 5–23; ±4 GB |
| `PAGEOFF12` (4) | `ADD`/`LDR`/`STR` imm12 | `T & 0xfff`, scaled by the access size (bits 30–31 of LDR/STR; 128-bit SIMD needs `opc` too), in bits 10–21 |
| `GOT_LOAD_PAGE21` (5) / `GOT_LOAD_PAGEOFF12` (6) | `ADRP` + `LDR Xt` | as above, but T is a slot holding the value; can be relaxed to `movz`/`movk`, `adrp+add` or `ldr literal` (CPython `patch_aarch64_33rx`) |
| `ADDEND` (10) | — | precedes PAGE21/PAGEOFF12 and carries an addend in `r_symbolnum`; not seen here |
| `UNSIGNED`/`SUBTRACTOR` (0/1) | data | only in data sections and `__compact_unwind`; not copied |
| `POINTER_TO_GOT`, `TLVP_*` | — | not produced by stencils; reject |

`relocation_info` packs `r_symbolnum:24, r_pcrel:1, r_length:2, r_extern:1,
r_type:4` [verified by parsing]. `LC_LINKER_OPTIMIZATION_HINT` can be ignored:
it only helps `ld64` relax `adrp` pairs.

### 5.2 W^X, `MAP_JIT`, the instruction cache

Apple's porting guide
(<https://developer.apple.com/documentation/apple-silicon/porting-just-in-time-compilers-to-apple-silicon>)
says [read]:

- "Apple silicon enables memory protection for all apps, regardless of whether
  they adopt the Hardened Runtime."
- The `com.apple.security.cs.allow-jit` entitlement "is required only when an
  app adopts the Hardened Runtime capability".
- `pthread_jit_write_protect_np` toggles write versus execute for `MAP_JIT`
  pages per thread. It is unavailable once the
  `com.apple.security.cs.jit-write-allowlist` entitlement is used; that
  entitlement pairs with `pthread_jit_write_with_callback_np`.
- "Always call `sys_icache_invalidate` before you execute … On Apple silicon,
  the instruction caches aren't coherent with data caches."

Local probes (`src/bin/wx.rs`, an ad-hoc linker-signed binary without the
Hardened Runtime) [verified]:

- `mmap(RWX)` without `MAP_JIT` fails with `EACCES`.
- `mmap(RW)`, write, `mprotect(RX)`, `sys_icache_invalidate` and call works:
  f(21) = 42. This is CPython's approach.
- `mprotect` back to RWX without `MAP_JIT` fails with `EACCES`.
- `MAP_JIT` + `pthread_jit_write_protect_np` works (§4).

What this means for fixpt:

- **The toggle is per thread and cheap.** It fits the object model's "seal"
  step. Other threads keep executing while one thread writes.
- **Code and mutable fields.** A code bloblet whose fields must stay writable
  after sealing cannot share a `MAP_JIT` page with executing code while it is
  being written, except on the writing thread. This is the page-aligned-suffix
  question PLAN.md keeps open.
- **A signed, hardened app** would need the `allow-jit` entitlement.

## 6. Extracting stencils without the network

- **No object-file parser is cached.** `~/.cargo/registry` has no `object`,
  `goblin` or `mach*` crate; it has `libc` 0.2.177–0.2.189 [verified]. Adding
  `object` would need the network, which was out of bounds here, and it would
  be a new dependency.
- **The toolchain has no `llvm-objdump`.** The `llvm-tools` component is not
  installed. Apple's `/usr/bin/objdump`, `otool` and `nm` are present. They
  are fine for inspection, but a build script should not depend on them.
- **A hand-written reader is reasonable** [verified]. The one in §4 covers
  `mach_header_64`, `LC_SEGMENT_64`/`section_64`, `LC_SYMTAB`/`nlist_64` and
  `relocation_info`, in about 60 lines of parsing. It needs only `std`, so it
  can live in `fixpt-native`'s `build.rs` with no `unsafe`.
  - An ELF reader for Linux would be another 80–100 lines; `SHT_RELA` gives
    explicit addends, which is easier.
  - The `object` crate becomes worthwhile only when COFF, multiple
    architectures and DWARF all matter.
- **Consistency.** The build script uses `$RUSTC`, so stencils always match the
  toolchain building the rest of the workspace.
  - `rust-toolchain.toml` pins the channel, not a version. A new stable may
    change stencil code; the gates turn structural regressions into build
    errors.
  - Snapshot tests of stencil sizes and hole lists would catch silent
    changes.

## 7. Commands used

```sh
# single-file stencil objects (scratch: /private/tmp/claude-501/cnp)
rustc --edition 2024 -O -C panic=abort -C relocation-model={pic,static} \
      -C code-model={small,large,tiny} --emit=obj -o st.o st.rs
objdump -d -r --no-show-raw-insn st.o      # disassembly with relocations
otool -l st.o                              # load commands
nm -m st.o ; nm -u hz.o                    # symbols; undefined helper symbols
rustc … -C llvm-args=-enable-machine-outliner=never …   # accepted
# end to end
cd /private/tmp/claude-501/cnp/e2e && cargo build --offline && ./target/debug/cnp
FAR=1 ./target/debug/cnp                   # force veneers
cargo run --offline --bin wx               # W^X probes
```

## 8. Judgement for fixpt

### Benefits over a hand-written encoder (for larger primitives)

- **Primitives are written once, in Rust**, and get LLVM's instruction
  selection and register allocation within the stencil. There is no
  hand-encoding of `udiv`, overflow checks or float operations, and no second
  implementation to keep in sync with the Rust runtime.
- **Code generation is fast**: memcpy plus bit-field patches. The paper and
  CPython show it is competitive as a baseline tier.
- **The runtime patcher is tiny** and needs no `unsafe` beyond what
  `fixpt-native` already plans: map, toggle, invalidate, call. It is just
  bytes and bit fields, so it could later be written in FX-26, with the stencil
  table carried as data in the heap image.
- **The build machinery doubles as a test oracle.** The same `build.rs`
  object reader can check the hand-written encoder's output against LLVM's
  encoding of the same instructions.

### Costs and risks

- **No control over the pinned-register ABI.** Without `preserve_none` or GHC
  on stable, the VM registers are whatever the C ABI assigns to argument
  positions (`x0`–`x7`), and runtime calls spill callee-saved registers. The
  NEXT loop and the frame layout want exact control, which the hand encoder
  gives.
- **Tail calls are not guaranteed.** They are gated at build time, but a
  compiler upgrade can break the build: that is a correctness failure caught
  early, not a silent one.
- **Hole semantics are subtle.** LLVM's non-null and alignment assumptions
  (§3.5) need the asm barrier or careful typing. Stencils must also be
  panic-free and stay within an allowlist of libcalls.
- **Mach-O first means each new target needs its own reader and patch
  rules.** Linux arm64 would need ELF, plus `-mno-outline-atomics`-style care
  (CPython uses it); the Rust equivalent was not investigated.
- **Position dependence after patching.** GOT-load constants and veneers are
  PC-relative, so a moved code bloblet must be re-patched, or its holes
  relaxed to a form that moves with it:
  - `ldr xN, literal` (±1 MB) to a slot inside the same bloblet;
  - branches to veneers inside the bloblet.

  This fits bloblets well: literals at a fixed offset from the suffix,
  possibly in the fields at negative offsets, move with the code. Heap
  pointers held in tagged fields could even be scanned and updated by the
  collector. Our experiment used a shared slot area, not this layout.
- **The trust base grows.** The stencil source is `unsafe` Rust compiled
  outside the workspace lint (`unsafe_code = "deny"`). It belongs to
  `fixpt-native`'s audited surface, and each stencil's `unsafe` needs its rule
  stated, as PLAN.md A1 asks.
- **Debuggability is poor.** JIT code has no unwind info or symbols. Backtraces
  through it need frame pointers, which stencils do keep on Darwin: `stp x29,
  x30` and `add x29` appear.
- **Tension with PLAN.md A2.** A2 rejects "copies of Rust-compiled code,
  whose position independence and extent Rust does not promise". That is
  right: Rust promises neither. Copy-and-patch replaces the promise with
  **verification of the object file actually produced**:
  - the extent comes from the symbol table;
  - every external reference must be a relocation to an allowed hole or
    helper;
  - every continuation must be a `B`.

  This is sound for what it checks. A stricter gate would also decode each
  stencil's internal branches to confirm they stay in range; that was not
  implemented.

### Recommendation

1. **Phase A′ unchanged.** Build the hand-written arm64 encoder for NEXT,
   entry and exit, and the call glue. It needs exact register and frame
   control, it is the stage-0 oracle for the FX-26 encoder, and it is small.
2. **Do not add copy-and-patch now.** Call Rust primitives through `extern "C"`
   from encoder-generated code first. This is the baseline to measure against.
3. **Adopt copy-and-patch when either condition holds:**
   - `docs/performance.md` shows hot primitives (generic arithmetic,
     comparisons, vector and string access, type tests) dominated by call
     overhead, or needing constant specialisation. Stencils give inlined,
     LLVM-quality bodies without hand-encoding them.
   - A baseline compiler from threaded or bytecode bloblets to native code is
     wanted (M10, or M12 step 11 as a fast tier).
4. **When adopting it:**
   - put the stencils in a `fixpt-native/stencils/` file compiled by
     `build.rs` with the flags in §3.6;
   - keep the hand-written Mach-O reader (ELF later);
   - enforce the three gates plus a libcall allowlist;
   - use the asm barrier for value holes;
   - make holes position-independent within a bloblet (§8, position
     dependence), so that code can move with its bloblet.

### Open risks

- A future rustc or LLVM could stop sibling-calling some stencil shape, or
  start outlining or splitting cold code. The gates catch this; fixing it may
  need stencil rewrites.
- `become` and `rust-preserve-none` may stabilise, which would make things
  better. Their timing is unknown (tracking issues #112788 and #151401).
- Distribution under the Hardened Runtime needs the `allow-jit` entitlement.
  A `jit-write-allowlist` build would forbid `pthread_jit_write_protect_np`.
- Not investigated:
  - arm64e (pointer authentication);
  - BTI landing pads (a concern if JIT pages are mapped with BTI on Linux);
  - atomics lowering (`outline-atomics`) on Linux.

## Addendum (2026-09-25): `become` on the installed nightly

*Verified locally.* The machine has `nightly-aarch64-apple-darwin` installed
(`rustc 1.97.0-nightly (82bee9650 2026-05-09)`), so this needed no download.
`#![feature(explicit_tail_calls)]` and `become` work for exactly the shape a
threaded-code inner interpreter needs: primitives as
`extern "C" fn(ip, sp, acc) -> i64`, each ending in `become` to the next code
pointer loaded from the program.

- A direct-threaded program of `LIT 40, LIT 2, ADD, EXIT` computes 42.
- A chain of 5,000,000 primitives runs without overflowing the stack. That
  happens only if every `become` is a real tail jump.
- At `-C opt-level=3`, `NEXT` is Forth's two instructions:
  ```
  _next:  ldr x3, [x0], #8
          br  x3
  ```
  `ADD` is `ldr x8, [x1, #-8]!; ldr x3, [x0], #8; add x2, x8, x2; br x3`,
  and `LIT` is six instructions ending in `br x3`. None has a frame or a
  call.
- At `-C opt-level=0` the tail call is **still** a tail call: the frame is
  torn down and the function ends in `br x3`. Ordinary tail-call
  optimisation never happens at `-O0`, so this is the language's promise,
  not the optimiser's.

The command was `rustc +nightly -C opt-level={0,3} -C panic=abort t.rs`,
with the assembly read by `--emit asm`.

**Consequence.** With `become`, the tail calls between stencils are
guaranteed by the language, so the build-time machine-code check is a second
line of defence rather than the only one. The recommendation is to confine
nightly to the stencils: `fixpt-native`'s build script compiles the stencil
sources with `rustc +nightly`, and the rest of the workspace stays on
stable. Pinning an exact nightly date in `rust-toolchain.toml` would make
rustup download that toolchain, so the stencil build uses the installed
`nightly` and records the version it found.
