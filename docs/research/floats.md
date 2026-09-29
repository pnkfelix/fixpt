# Floating point in FX-26

Design note, 2026-09-29. For review before any code. The user's framing:
"We can do native f32 pretty easily. I'm not sure what to do about f64 …
do we try to embed those into the layout? Not clear how best to do it,
beyond leveraging bloblet in some way."

## The recommendation, in brief

- **`float` (IEEE binary64) comes first**, because every benchmark that is
  blocked needs binary64 and none needs binary32. `f32` is cheap and comes
  later, with `i32`/`u32`, since it uses the same trick.
- **The uniform representation of a `float` is the boxed flonum we already
  have**: a bloblet with no fields and an 8-byte suffix, two words, pointed
  at the double. It works unchanged on every machine, in the collector,
  in heap images and in the Scheme lowering.
- **Native code keeps floats raw wherever the types say so**, and boxes
  them only where one escapes into a uniform position. FX-26 knows
  statically that a value is a `float`, so the compiler never tests a tag.
  Floats are raw in `d` registers, in frame slots left out of the stack
  map's mask, in the suffix of a new monomorphic array type
  `(f64array R)`, and as arguments and results in `d0`–`d7` on a
  procedure's second entry (worker/wrapper, as in GHC).
- **No NaN-boxing, and no lossy short floats.** NaN-boxing leaves about
  53 bits of patterns for everything that is not a double. Our references
  need only 37 of them, so JSC-style offset doubles could keep our
  pointers, low tags and bloblets. But fixnums would shrink from 61 bits to
  49, and every integer operation would take about four more instructions,
  on every machine. That is paid to speed up code whose types are unknown,
  and FX-26 has little such code (worked out in 2b).
  An immediate encoding for a range of exponents that loses no precision
  (Spur's SmallFloat64, "float self-tagging") fits our tags. It would take
  the last free tag, `010`, and it would help only the cellular machines
  and polymorphic code. It is kept in reserve.
- **Polymorphism stays uniform.** Code polymorphic over `(t type)` sees
  boxed floats. The raw representations are reached only through
  monomorphic types (`float`, `f64array`) and a procedure's second entry.
  So no type ever has two layouts, and neither checker needs a rule about
  representation. Specializing polymorphic code for floats, and GHC-style
  representation kinds, come later if measurements ask for them.

## Where we are

- **Values** (`crates/fixpt-heap/src/value.rs`) are 64-bit words with a
  3-bit low tag: `000` fixnum (61-bit), `001` pair, `010` reserved (kept
  for a header pointer or a locative, `docs/object-model.md`), `011`
  immediate (subtag in bits 3–7, payload in bits 8–63; subtags 0–8 in
  use), `100` bloblet, `101` trailer, `110` header, `111` forwarding. A
  reference is the object's address with the tag in its low bits.
- **Flonums already exist** for the Scheme engine: `Heap::make_flonum`
  (`crates/fixpt-heap/src/heap.rs`) allocates kind 5, `flonum`
  (`layout.rs`), as a bloblet with *F* = 0 and *B* = 8. It is
  `[header][double]`, and the pointer (tag `100`) points at the double.
  So the double is 8-byte aligned, and native code can unbox it with a
  single `ldur d0, [x1, #-4]`. Larceny wasted a word to get the same
  alignment (Larceny's `doc/LarcenyNotes/note2-repr.html`, "Figure 6:
  Flonum"). A bloblet gets it for free.
- **Printing and reading** of flonums already exist for Scheme:
  `format_flonum` (`crates/fixpt-runtime/src/num.rs`) prints the shortest
  string that reads back to the same value, and the reader parses
  `+inf.0`, `-inf.0` and `+nan.0` (`crates/fixpt-read/src/reader.rs`).
- **FX-26 has no float type.** `+` is `(subr pure (int int) int)`
  (`crates/fixpt-fx26/src/standard.rs`). FX-87 had `float`, `fl+`, `fl<`,
  …, `sin`, `sqrt`, `int->float`, and `floor : (float) int`
  (`crates/fixpt-fx87/src/standard.fx`), with `int` a subtype of `float`.
  `docs/divergences.md` records two FX-87 float quirks: `1.0` reads as an
  `int`, and `floor` has to return an exact integer.
- **Native frames have stack maps** (`docs/research/generational-gc.md`
  §1). The header word at `[x29, #16]` is a fixnum mask of the slots
  traced, and "a slot outside the mask may hold anything: an untagged
  integer, a float, an address".
- **Taking a continuation** copies a frame's slots into a traced vector,
  and "copies a dead slot as the fixnum 0". That is the one place where
  raw slots do not yet work: see the collector, below.
- **Types reach code generation.** Cellular words are compiled from
  checked trees (`crates/fixpt-fx26/src/cellular.rs`, and `compile.fx`,
  which must make the same words). Register code (`regcode.rs`,
  `regcode.fx`, which must also agree) is compiled from the same trees,
  and the native compiler (`crates/fixpt-native/src/direct.rs`) compiles
  register code. A float operation can be chosen by type at the first of
  those steps.
- **The native convention** (`direct.rs`): arguments in `x1`–`x8`, the
  result in `x0`, every register but the pinned ones lost across a call,
  and anything live across a call kept in the frame.

## What the blocked benchmarks need

| benchmark                                         | float use                                                       | needs, for good native speed                       |
| ------------------------------------------------- | --------------------------------------------------------------- | -------------------------------------------------- |
| Larceny `fibfp`                                   | recursion on a float argument, float result                     | floats passed raw between calls (S3)               |
| Larceny `sumfp`, `mbrot`; ML `mandelbrot`         | loops over float locals                                         | raw locals (S1)                                    |
| Larceny `mbrotZ`                                  | complex numbers (`make-rectangular`)                            | a pair of floats: products or two locals (S1, S5)  |
| Larceny `fft`; ML `fft`, `spectralnorm`           | vectors of floats, `sin`                                        | flat float arrays (S2), raw locals (S1)            |
| Larceny `simplex`, `pnpoly`                       | vectors of floats (`simplex` has 2-D ones)                      | flat float arrays (S2)                             |
| Larceny `nucleic`; ML `nucleic`                   | 3-vectors and 12-float transforms, `sin`, `cos`, `atan`, `sqrt` | flat arrays (S2), or flat records (S5); calls (S3) |
| Larceny `ray`; MLton `ray`, `raytrace`            | records of floats, `sqrt`                                       | calls (S3), products (S5)                          |
| ML `nbody`                                        | mutable records of floats (OCaml keeps them flat)               | flat arrays (S2); the port keeps the bodies in one |
| ML `almabench`, MLton `barnes-hut`, `tsp`, `zern` | arrays, records, trig                                           | S1–S3                                              |

Every one of them runs, boxed, at stage S0. S1 and S2 make most of them
free of allocation. The stages are defined below.

## 1. `f32`

**The representation: an immediate.** Put the 32 bits in the upper half of
a word, under the immediate tag with a new subtag (9):

```text
bits 63..32   the binary32 value
bits 31..8    zero
bits 7..3     subtag 9
bits 2..0     011, immediate
```

- The collector sees an immediate and never traces it. No machine
  allocates for an `f32`, the cellular machines included.
- **The immediate subtag costs one instruction**, compared with keeping
  the bits fixnum-shaped (tag `000`), which is `PLAN.md`'s plan for
  `i32`. In return the word describes itself, to the printer, to `datum`
  and `equal?`-like code, to the heap verifier and to the Scheme engine.
  Native code keeps an `f32` in an `s` register and boxes it only when it
  escapes, so the extra instruction is off the hot path. (The same
  question should be asked of `i32`: see the open questions.)
- **arm64 costs.**
  - Box: `fmov w9, s0; lsl x9, x9, #32; add x9, x9, #0x4b`. The constant
    `0x4b` is not a logical immediate, but it is a 12-bit add immediate.
  - Unbox from a register: `lsr x9, x9, #32; fmov s0, w9`.
  - **Unbox from memory is free**: `ldr s0, [addr, #4]` loads the upper
    half of a slot or field directly, since arm64 is little-endian.
  - `fmov` between the general and the floating-point register files is a
    single move (a few cycles on Apple cores, and not dependent on
    memory).
- **Semantics.** IEEE 754 binary32, round to nearest even, and no traps.
  - `f32` to `float` is exact. `float` to `f32` rounds (`fcvt s0, d0`).
  - `fl32=` is the IEEE comparison: `NaN` is unequal to itself, and
    `-0.0` equals `0.0`. It is never a comparison of words.
  - Printing is the shortest string that reads back as the same *binary32*
    value, which is not what printing it as a double would give.
- **The Scheme lowering** has no binary32. There an `f32` is a flonum whose
  value is exactly representable in binary32, and every operation rounds
  its result to binary32 (a primitive, `%round-f32`). For `+`, `-`, `*`,
  `/` and `sqrt` this gives exactly the binary32 result, because a double
  has at least 2·24 + 2 bits of precision, so rounding twice is harmless
  (Figueroa 1995). Transcendentals must call the binary32 functions
  themselves (Rust's `f32::sin`) on every machine, the lowering included,
  since `(f32)sin(x)` differs from `sinf(x)`.
- **Arrays**: `(f32array R)`, 4 bytes an element in a suffix, as `f64array`
  below.

Nothing in the blocked benchmarks uses `f32`, so it is not first.

## 2. `float` (binary64): the options

### a. Boxed flonums, with type-directed unboxing

The uniform representation is the existing flonum bloblet: 16 bytes, one
allocation per result that escapes.

- **Cost of a box in native code**: an inline bump of 16 bytes, as `cons`
  is made inline now. That is about six instructions plus a branch to the
  call-out that collects: store the header, `str d0, [top, #8]`, and form
  the pointer with its tag. Unboxing is one `ldur`. The nursery makes
  short-lived boxes cheap to reclaim, but they still fill it: `fibfp`
  on 35.0, boxed, allocates 44.8 M boxes, 717 MB a run (see (b)).
- **What static types add.** A compiler never needs a tag check, since
  `(fl+ a b)` has `float` operands by type. Larceny, which has no static
  types, does a two-level dispatch on every generic `+` (`note3-arithmetic.html`) and runs
  representation inference to remove some of it
  (`src/Compiler/pass3rep.sch`, `iasn.imp2.sch`'s `.+:flo:flo`). Chez
  Scheme 10 unboxes flonums locally within a procedure, and uses type
  recovery to learn which values are flonums (Chez Scheme 10.0.0 release
  notes, §2.4, "Compiler improvements"). FX-26 gets that knowledge from its checker for free.
  So **local unboxing** (raw within a procedure, boxed at its boundaries
  and in data) is simple here: a value of type `float` lives in a `d`
  register, or in a frame slot outside the mask, from where it is made to
  where it escapes.
- **Where it escapes, it is boxed**: stored in a field of a uniform
  container, passed to or returned from a uniform position, captured by a
  closure, or held in a global's cell.
- **Regions do not help much.** A float, like a product, is in no region,
  and making one is pure. Its box can go anywhere, and the nursery is the
  right place for short-lived ones. (The MLKit boxes reals in regions,
  but its regions are inferred for every value. FX-26's places are
  explicit, and nobody should have to write a place for arithmetic.)

### b. NaN-boxing, worked out

Revised 2026-09-29, at the user's request, from the engines' current
sources, which were fetched and read for it (see Sources).

**The space NaN-boxing has to work in.** A binary64 value is a sign bit, an
11-bit exponent and a 52-bit fraction.
- **What counts as a NaN.** A value is a NaN when the exponent is all ones
  and the fraction is not zero. That gives 2 · (2^52 − 1) = 2^53 − 2 bit
  patterns.
- **Quiet and signalling.** The fraction's top bit (bit 51) is the quiet
  bit. There are 2 · 2^51 quiet NaNs and 2 · (2^51 − 1) signalling ones.
- **What the hardware produces.** Arithmetic creates only one NaN of its
  own: `0x7FF8_0000_0000_0000` on arm64, and `0xFFF8_…` on x86. But with
  arm64's default-NaN mode off (`FPCR.DN = 0`, the default) an operand's
  NaN passes through, quieted, with its payload.
- **So one canonical NaN must be reserved.** Every double that is boxed
  and might be a NaN of unknown origin must be canonicalized first:
  SpiderMonkey's `JS::CanonicalizeNaN` does this, and so does JSC's
  `purifyNaN`. Unknown origin covers the result of any operation that can
  make a NaN, a load from an `f64array`, and `bits->float`. On arm64
  that is an `fcmp` and an `fcsel` per box.
- **What is left over.** Every other NaN pattern is free for non-doubles:
  about 2^53 patterns, **53 bits of information in all**. Pointers,
  integers, immediates and tags must share them, where today they share
  2^64.

The two encodings in use:

| encoding                                                  | doubles                                                                                                | pointers                                                                                          | integers                                            | tags                                                                                                                                                                                 |
| --------------------------------------------------------- | ------------------------------------------------------------------------------------------------------ | ------------------------------------------------------------------------------------------------- | --------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| offset doubles: JSC; "NuN-boxing" in Melançon et al. §1.3 | the bits plus 2^49 (`DoubleEncodeOffset`), so top 16 bits run from `0x0002` to `0xFFFC`; NaNs purified | raw, top 16 bits zero (48 bits); low bits free: `OtherTag` 0x2, `BoolTag` 0x4, `UndefinedTag` 0x8 | `int32` under `NumberTag` = `0xFFFE_0000_0000_0000` | the top 15 bits split pointers/immediates, doubles and ints; the region of 2^49 patterns under `0xFFFE`–`0xFFFF` holds only 32-bit ints; immediates are "invalid pointers" 0x02–0x0a |
| pure NaN-boxing: SpiderMonkey `PUNBOX64`                  | raw; every word ≤ `JSVAL_SHIFTED_TAG_MAX_DOUBLE` is a double; NaNs canonicalized                       | 47 bits (`JSVAL_TAG_SHIFT` = 47), in the low bits of a negative quiet NaN                         | `int32` (`JSVAL_INT_BITS` = 32)                     | a 5-bit tag above the 47; its top bit is set in every non-double tag, so 4 bits (16 tags) are usable                                                                                 |
| pure NaN-boxing: LuaJIT `LJ_GC64`                         | raw                                                                                                    | 47 bits                                                                                           | zero-extended `int32` (only in `LJ_DUALNUM` mode)   | "the upper 13 bits must be 1 … the next 4 bits hold the internal tag"                                                                                                                |

The sum is the same for both. A negative quiet NaN has 64 − 13 = 51 free
bits, where the 13 are the sign, the exponent and the quiet bit:
- a **pure** scheme spends 4 of the 51 on a tag and 47 on a pointer;
- **offset doubles** give 2^49 patterns to pointers and immediates (top 15
  bits zero) and 2^49 to integers (top 15 bits ones), and leave further
  NaN ranges unused.

**Integers.** All three engines keep only 32-bit integers in a value. JSC's
region `0xFFFE`–`0xFFFF` would hold 49 bits. If integers took half of all
the free patterns, the ceiling would be 52 bits. With one-instruction tests
the realistic figures are 49 (offset doubles) or 50 (pure, with one payload
bit telling integer from not).

**Two quirks of naming.**
- SpiderMonkey's own comment calls its 32-bit mode `NUNBOX32` ("NaN
  unboxed"); Melançon et al. use "NuN-boxing" for JSC's offset doubles. This
  note uses the second.
- Melançon et al. describe the offset as `0x0001_0000_0000_0000` (2^48).
  JSC's header says 2^49, and 2^49 is what `JSCJSValue.h` defines.

**Could fixpt's memory map make room?** It already has room, even for the
pure scheme.
- **How big the heap's range is.** The heap is one reservation, `mem`
  (`crates/fixpt-heap/src/heap.rs`): two semispaces of 2^31 words, the
  arenas' 2^31, the reaps' 2^31, the nursery's 2^30 and the code area's 2^27.
  So `MEM_WORDS` = 9,797,894,144 words, 73 GiB, 2^33.19.
- **So a reference relative to the base needs 37 bits**, counting its tag:
  a word index needs 34 bits, and a byte offset needs 37, whose low 3 bits
  are where our tags already sit.
- **An absolute reference needs 47 bits.** On macOS on arm64 user addresses
  lie below `0x0000_7FFF_FE00_0000` (xnu, `osfmk/mach/arm/vm_param.h`,
  `MACH_VM_MAX_ADDRESS_RAW`). If the reservation were mapped at a fixed
  address below 2^40, absolute addresses would need only 40 bits, and no
  base register.

Pointers are therefore not the obstacle. What is at stake is the **fixnum
width**, and the **cost of integer operations**. Each kind of word must
fit into the 53 bits of patterns left over. Either pointers or integers
must then carry a pattern in their high bits:
- **Offset doubles leave pointers alone.** For fixpt, every word but a
  fixnum would stay as it is, with the top 15 bits zero. That covers pairs
  (`001`), bloblets (`100`), immediates (`011`), trailers (`101`), headers
  (`110`) and forwarding words (`111`). Bloblet pointers keep pointing at
  suffixes, `field_off(k) = -(4 + 8k)` still folds the tag into the load,
  and inline allocation, the card table and the crossing map are all
  unchanged. Fixnums move under `0xFFFE`, with 49 bits.
- **Pure boxing puts every reference under a prefix.** Each dereference
  would then clear the prefix, and add the base if references are
  relative: one or two instructions on every field access, in code that is
  mostly lists and trees. It would give 50-bit fixnums, and is rejected for
  that cost.

What adopting offset doubles would change:

| part                                                                                       | change                                                                                                                                                                                                                            |
| ------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `value.rs`, `layout.rs`, and the generated `layout.fx`                                     | fixnums become `0xFFFE_…` plus 49 bits; `FIXNUM_BITS` becomes 49; tag `000` is freed; `is_ref` must also test that the top bits are zero; a double is its bits plus 2^49                                                          |
| the heap's parse (Cheney scan, crossing map, backward scan, verifier)                      | a double's low bits are arbitrary, so "a header" becomes "low bits `110` **and** top 15 bits zero"; the same holds for trailers and forwarding words. Invariant 4 holds under the refined test. One more compare per word scanned |
| inline allocation, card table, bloblet pointers, `field_off`                               | unchanged                                                                                                                                                                                                                         |
| native compiler (`direct.rs`) and register code                                            | every fixnum operation and constant is re-encoded (below); the overflow checks move from 61 to 49 bits; the 64-bit tag constants are made with `movz`/`movk`                                                                      |
| cellular machines: Rust, hand arm64, stencils, `native-compiled`, `registers`, `native.fx` | every fixnum routine is rewritten, and `native.fx` must still match the Rust machine instruction for instruction                                                                                                                  |
| the front end written in FX-26                                                             | it computes machine words as `int`s. With 49-bit ints, a header whose suffix is 64 KiB or more (*B* sits in bits 32–63), and the new `0xFFFE…` constants, no longer fit, so `i64`/`u64` would have to come first                  |
| the Scheme engine (`fixpt-runtime/src/num.rs`)                                             | bignums begin at 2^48 instead of 2^60; flonums become immediate, so the kind `flonum` goes. This is the one place NaN-boxing helps a dynamically typed program, and the Scheme engine's speed is not a goal                       |
| heap images                                                                                | a new format version: the encodings of fixnums and doubles change                                                                                                                                                                 |
| FX-26's `int` and `nat`                                                                    | overflow traps at ±2^48 instead of ±2^60                                                                                                                                                                                          |

Would 48–50-bit fixnums be acceptable?
- **The benchmarks, yes**: none needs more than 48 bits.
- **The language, maybe**: an `int` that traps at 2^48 is still an honest
  `int`.
- **The front end, not without `i64`**, because it computes 64-bit machine
  words.
- **32-bit ints plus a boxed or raw `i64`**, the JavaScript engines'
  choice, would break more existing FX-26 code. Hashes, instruction
  encodings and the layout's words all use more than 32 bits.

**Costs per operation on arm64**, on the hot path, excluding branches not
taken:

| operation                                           | today: low tags, boxed flonum                 | offset doubles (JSC-style, 49-bit fixnums)                                                                    | self-tagged, one tag (`010`)                                          |
| --------------------------------------------------- | --------------------------------------------- | ------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------- |
| fixnum `+` with overflow check                      | `adds`, `b.vs`: 1 + branch                    | `lsl` ×2, `adds`, `b.vs`, `asr`, `orr`: about 5 + branch (int32 would be `adds w`, `b.vs`, `orr`: 2 + branch) | unchanged                                                             |
| field load                                          | `ldur x, [p, #-(4+8k)]`                       | unchanged                                                                                                     | unchanged                                                             |
| float from a uniform word                           | `ldur d, [p, #-4]`: 1 load                    | `sub` (2^49 in a register), `fmov`: 2                                                                         | `ror`, `sub`, `fmov`, and a test for the boxed case: about 4          |
| float to a uniform word                             | inline bump: about 6, plus 16 bytes allocated | `fcmp`/`fcsel` (canonical NaN), `fmov`, `add`: 4, nothing allocated                                           | `fmov`, `add`, `ror`, `tst`, `b.ne` to box: about 4, rarely allocates |
| float operation where types are known (S1–S3 below) | none: raw in `d`                              | none: raw in `d`                                                                                              | none: raw in `d`                                                      |
| "is it a pointer?" (collector, dynamic code)        | `and`, `cmp`                                  | and a top-bits test                                                                                           | unchanged: `010` is not traced                                        |

**What a float-heavy benchmark allocates.** `fibfp` on 35.0 makes 29.9 M
calls. The 14.9 M that are not leaves each compute three floats, which is
44.8 M floats, 717 MB of boxes a run (Larceny's input runs it 10 times):
- boxed everywhere (S0), and with raw locals (S1), they are all
  allocated, because they cross calls;
- with worker/wrapper (S3), none are;
- NaN-boxing and self-tagging allocate none, and need no compiler work to
  get there.

`sumfp` and `mbrot` allocate nothing from S1 on. Floats stored into
products (`nucleic`, `ray`) are boxed until S5, where NaN-boxing would
never box them.

Melançon et al. measured exactly these R7RS float benchmarks on an Apple
M2 (Fig. 9, geometric means relative to NuN-boxing):
- Bigloo with NaN-boxing: 0.90× on float benchmarks, 1.00× on the rest;
- Bigloo with one self-tag: 1.25× and 0.97×;
- Gambit with one self-tag: 1.05× and 0.91×.

They also found that under Gambit's bump allocator and copying collector
(like fixpt's nursery), eliminating boxes gained little: "Gambit
execution time slightly increases on many float benchmarks" compared with
boxed floats (§4.5). Their Fig. 5 shows why one tag suffices. Almost
every float the R7RS benchmarks compute lies between 1.1e-19 and 3.7e19,
or is 0.0. The one-tag variant (§2.4) covers those, plus ±Infinity and
NaN, and "about 90%" of the floats in a wider survey.

**Where FX-26 does not know types statically:**
- polymorphic code over `(t type)`;
- the cellular machines, whose speed does not count;
- the Scheme lowering and the Scheme engine;
- `datum`.

Everywhere else, S1–S3 get raw floats from the types, at no cost to
integers or pointers.

**Pros and cons for FX-26:**

| criterion                                  | type-directed unboxing, boxed flonum as the uniform rep (recommended)                   | NaN-boxing, offset doubles                                                                                                        | self-tagged floats on tag `010` (on top of the recommendation)       |
| ------------------------------------------ | --------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------- |
| floats in monomorphic native code          | raw (S1–S3)                                                                             | raw, the same work needed                                                                                                         | raw (S1–S3)                                                          |
| floats in polymorphic code, data, cellular | a 16-byte box each, in the nursery                                                      | no allocation; 2–4 instructions to encode or decode                                                                               | no allocation for 1.1e-19 … 3.7e19, 0, ±inf and NaN; boxed otherwise |
| fixnums                                    | 61 bits, `adds` + `b.vs`                                                                | 49 bits (or 32); about 4 more instructions per operation, on every machine                                                        | 61 bits, unchanged                                                   |
| pointers and field access                  | unchanged                                                                               | unchanged (offset doubles); prefix stripping if pure                                                                              | unchanged                                                            |
| collector                                  | precise; raw suffixes; raw frame slots outside the mask                                 | precise, every word describes itself; one more compare per word parsed                                                            | precise; `010` untraced                                              |
| raw frame slots and continuations          | needs the continuation-capture change                                                   | not needed for floats (any double is a legal value); still needed for `i64`                                                       | as the recommendation                                                |
| the Scheme engine                          | boxed flonums, as today                                                                 | immediate flonums                                                                                                                 | immediate flonums in range                                           |
| engineering                                | native compiler, both register-code compilers, an `f64array` kind, continuation capture | the tag scheme, the parse, every machine's fixnum routines, `native.fx`, images, the Scheme engine; `i64` first for the front end | a tag, and an encode/decode routine per machine                      |
| what it costs to back out                  | little: local to the compilers                                                          | a rewrite back                                                                                                                    | little                                                               |

**Verdict.** NaN-boxing is feasible here: offset doubles keep our pointers,
tags and bloblets, and our references need only 37 bits. But it buys
unboxed floats only where FX-26 does not care about speed. It charges for
them where FX-26 spends its time: in integer arithmetic on every machine,
in the fixnum range, and in the front end's own code. So it is still not
recommended. The objection is to the **integers**, not the pointers,
which the first draft of this note got wrong. Self-tagging on tag `010`
covers the same benchmarks' floats, and costs integers nothing. It
remains the reserve if uniform float traffic ever shows in native
profiles.

### c. Raw f64 where the types say so

This is the recommended approach, extending (a). It follows OCaml, MLton,
GHC and SML/NJ, each in part:

- **In registers and frames.** Raw in `d` registers, and in frame slots
  that the stack map leaves out. The types say which slots hold floats,
  so no analysis is needed beyond the liveness pass the stack maps already
  run.
- **In arrays: a new type `(f64array R)`.** A bloblet with no fields, of
  kind `f64array`, whose suffix is the elements: 8*n* bytes, with the
  length read from the header's *B*.
  - `(f64array-ref a i)` is a bounds check and
    `add x9, xa, xi, lsl #3; ldur d0, [x9, #-4]`.
  - A store needs **no write barrier**, since it stores no pointer. By
    contrast, a boxed float stored into an `(arrayof float R)` needs an
    allocation and the six-instruction card mark.
  - This is SML's `Real64Array` (the Basis Library's `MONO_ARRAY`), OCaml's
    `floatarray`, and Chez's `flvector`.
  - It is a type of its own, not a different layout for
    `(arrayof float R)`. OCaml lays out `float array` flat, so every
    polymorphic `Array.get` must check at run time which layout it has.
    OCaml's manual says so (`floatarray` "more efficient than … float
    array, which require an extra dynamic check"), and it offers
    `--disable-flat-float-array` to turn the layout off (LexiFi, "About
    unboxed float arrays"). A separate type costs no dynamic check and no
    rule in either checker, and polymorphic code never meets it.
- **As arguments and results: worker/wrapper.** A procedure whose declared
  type has `float` parameters or result gets two entries in its code
  bloblet:
  - the **wrapper** is the uniform one, the procedure's value, which every
    unknown and polymorphic caller uses: it unboxes, then falls through;
  - the **worker** is at a fixed offset, and takes floats raw in `d0`–`d7`
    and returns one in `d0`.

  Known calls (a lifted `letrec`, a loop, a procedure calling itself, a
  global whose value is native code) go to the worker. This is GHC's
  worker/wrapper transformation over `Double#` (Peyton Jones & Launchbury
  1991; Gill & Hutton 2009). The procedure's type stays the same, so the
  checkers are untouched. It is decided from the declared type alone, so
  both register-code compilers can agree on it mechanically.
- **In products and sums, later.** A structural type such as
  `(productof (x float))` must have a single layout, because
  `(productof (x t))` with `t := float` is the same type and polymorphic
  code reads it uniformly. Leroy's coercions (POPL 1992) would copy at
  each instantiation. That is sound for FX-26's immutable products, but
  it is deep: a list of such products would have to be copied as well.
  OCaml's answer is the one that fits: a *declared* record whose fields
  are all `float` is flat, and a record with a type parameter is uniform
  even when the parameter is `float`. For FX-26 that is a **generative
  type** (`define-generative`, `define-datatype`) whose declaration fixes
  which fields are raw floats. The bloblet does the rest: traced fields
  in *F*, floats in the suffix, and the collector needs nothing new.
- **Polymorphism.** Code polymorphic over `(t type)` is compiled once,
  uniformly, and sees boxed floats. The alternatives:

  | approach                                     | who                                                     | for FX-26                                                                                                                                                                         |
  | -------------------------------------------- | ------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
  | box at polymorphic boundaries (uniform code) | OCaml, SML/NJ, Larceny, Chez                            | **the default**: nothing new, and worker/wrapper covers known calls                                                                                                               |
  | coercions at instantiation                   | Leroy 1992; Shao & Appel 1995 (SML/NJ)                  | not needed while polymorphic positions are uniform                                                                                                                                |
  | monomorphize                                 | MLton (whole program), Rust                             | FX-26 is incremental (REPL, redefinition), so not whole-program; but every `proj` is an explicit instantiation, so specializing a *chosen* procedure at `float` is possible later |
  | kinds that say a representation              | GHC (`TYPE 'DoubleRep`, levity polymorphism, PLDI 2017) | a kind such as `(t rep64)`, over `float`/`i64`/`u64`, compiled once per representation; only if generic code over raw scalars is ever wanted                                      |

### d. Floats in 61 bits

- **Losing precision** (for example a 61-bit float with a 50-bit mantissa):
  rejected. The benchmarks check IEEE results. Native code computes in
  full binary64 registers, so a value would change when it was boxed,
  and the machines would stop agreeing with one another and with Larceny's
  answers.
- **Losing range, not precision.** Spur's SmallFloat64 (Squeak/Pharo) keeps
  the full 52-bit mantissa and 8 of the 11 exponent bits, about ±10^±38,
  plus ±0 as a special case. The sign is rotated to the bottom and the
  tag goes in the low 3 bits; values outside the range are boxed (Béra,
  "64 bits Immediate Floats", 2018). "Float self-tagging" generalizes
  this with several tags chosen so that the common exponents need no
  allocation. It was implemented in two Scheme compilers, with "nearly
  all" float allocation removed and a negligible cost elsewhere (Melançon,
  Serrano & Feeley, OOPSLA 2025).
  - For us it would take tag `010`, the last free one, which is reserved
    for a header pointer or a locative. Encoding would be a rotate, a
    subtract, a range check and a branch to a boxing path; decoding would
    be a shift, a compare and add for zero, and a rotate.
  - It helps only where floats are uniform: the cellular machines (whose
    speed does not count, `PLAN.md`) and polymorphic code. **Kept in
    reserve**, to be measured if polymorphic float code turns out to
    matter. The collector's side is trivial: `010` would be one more tag
    it does not trace.

### Precedents at a glance

| system              | uniform float                       | unboxed where                                                                                   |
| ------------------- | ----------------------------------- | ----------------------------------------------------------------------------------------------- |
| Larceny             | boxed, 16 bytes (a word of padding) | nowhere; representation inference removes dispatch, not boxes                                   |
| Chez Scheme 10      | boxed                               | locally within a procedure; `flvector`                                                          |
| Racket CS           | Chez's                              | Chez's (Racket CS runs on Chez Scheme)                                                          |
| OCaml               | boxed                               | let-bound locals; flat `float array` (dynamic check) and `floatarray`; all-float records        |
| MLton               | none after monomorphisation         | everywhere: whole-program monomorphisation and flattening                                       |
| SML/NJ              | boxed                               | type-based representation analysis (Shao & Appel); `Real64Array`                                |
| GHC                 | boxed `D# Double#`                  | `Double#` everywhere strictness and worker/wrapper reach; representation-polymorphic kinds      |
| V8                  | boxed `HeapNumber`, 31/32-bit Smis  | `PACKED_DOUBLE_ELEMENTS` arrays; in-object double fields dropped with pointer compression (-3%) |
| SpiderMonkey        | NaN-boxed (`PUNBOX64`), int32       | JIT registers                                                                                   |
| JavaScriptCore      | offset doubles (+2^49), int32       | JIT registers; Int52 inside the JIT                                                             |
| LuaJIT              | NaN-tagged (`LJ_GC64`), int32       | trace registers                                                                                 |
| Spur (Pharo/Squeak) | immediate SmallFloat64 in range     | JIT registers                                                                                   |

## 3. The language

**Types.** `float` is binary64. FX-87 and FX-91 called it that, and
`f64` could be an alias. `f32` is binary32. Both are base types, and both
are `data`. Beside them, `(f64array R)` and `(f32array R)` are array types
in region `R`, with `make-`, `-ref`, `-set!` and `-length` operations,
polymorphic in the region only, and with the same effects as
`arrayof`'s. Their `-length` is a `nat`, so that loops over them need no
`spin`.

**No subtyping between `int` and `float`.** FX-87 had `int ≤ float`. Here
it would change representation (a fixnum into a box), and it would lose
precision past 2^53, which 61-bit fixnums reach. Conversion is written
out: `(inexact i)` or `int->float`. On arm64 that is `scvtf`, correctly
rounded.

**Literals.**
- `1.5`, `1e10`, `.5`, `2.` and `+inf.0`, `-inf.0` and `+nan.0` are
  `float`. This ends FX-87's quirk that `1.0` is an `int`.
- A decimal literal checked against `f32` should be converted from its
  text to binary32 directly. Going through binary64 first is a double
  rounding that *can* differ for decimal input. The reader already keeps
  an atom's text whole, and checking knows the expected type.
- Whether `1` may be checked as a `float` is an open question.

**Operations.** Separate names, as FX-87 and R6RS's `(rnrs arithmetic
flonums)` have them. Both checkers stay simple, and `+` stays
`(subr pure (int int) int)`.

| group         | operations                                                                                                               | arm64                                                                        |
| ------------- | ------------------------------------------------------------------------------------------------------------------------ | ---------------------------------------------------------------------------- |
| arithmetic    | `fl+ fl- fl* fl/ flabs flneg flsqrt flmin flmax`                                                                         | `fadd fsub fmul fdiv fabs fneg fsqrt fmin fmax`                              |
| comparison    | `fl= fl< fl<= fl> fl>=`, `nan? infinite? finite?`                                                                        | `fcmp`, then `b.eq b.mi b.ls b.gt b.ge` (`mi`/`ls` are false when unordered) |
| rounding      | `floor ceiling truncate round`, `float` to `float`, as R7RS; `round` to even                                             | `frintm frintp frintz frintn`                                                |
| conversion    | `inexact`/`int->float`; `exact`/`float->int`, which traps unless integral and within 61 bits; `exact-floor` and the like | `scvtf`; `fcvtzs`/`fcvtms`, then a range check                               |
| between sizes | `float->f32` (rounds), `f32->float` (exact)                                                                              | `fcvt`                                                                       |
| elementary    | `exp log sin cos tan asin acos atan atan2 expt`                                                                          | a call-out to Rust's `f64` methods                                           |
| text          | `float->string` (shortest round-trip), `string->float`                                                                   | runtime primitives                                                           |
| hashing       | `float-hash`, of the bits, with `-0.0` taken as `0.0` and every NaN as one                                               | inline                                                                       |

**The numeric tower.** There is none to have. `int` and `float` are
distinct static types, so R7RS's exact/inexact contagion never arises.
`exact` and `inexact` keep their R7RS names, as the conversions. R7RS's
`floor` of a float is a float, which avoids FX-87's divergence;
`exact-floor` names the combination. Without rationals, `exact` of `2.5`
cannot be `5/2`, so it traps, as integer overflow traps.

**Printing and reading.**
- Printing is shortest round-trip (Steele & White 1990; Ryū, Adams 2018).
  Rust's formatting already does it, and `format_flonum` uses it.
- Correctly rounded reading needs big arithmetic in its slow cases
  (Clinger 1990), and FX-26 has no bignums. So both readers (the Rust one,
  and `eager-reader.fx`) recognize the token and call one runtime
  primitive, which is Rust's correctly rounded `str::parse::<f64>`. The
  two readers then agree bit for bit, and so do the constants the two
  compilers put in words.
- A REPL value of type `float` is a flonum and prints itself. An `f32`
  prints itself too, since it has a subtag.

**Equality and hashing.** `fl=` is IEEE equality. Nothing in FX-26
compares floats by identity. Tables take their own hash and equality, so
a table keyed by floats uses `float-hash` with `fl=`, or with a bitwise
equality if the program wants `NaN` to be findable. `acyclic?` and the
`data` kind treat floats as leaves.

**Effects.** Floating-point operations are `pure`.
- The rounding mode is fixed at round to nearest even. Exception flags are
  never observable, and nothing traps: `(fl/ 1.0 0.0)` is `+inf.0`.
- `FPCR` stays at the platform's default: no flush to zero, and the
  default-NaN mode off. The entry into native code need not touch it.
- A rounding-mode or FP-flag effect (a region-like `fpenv`) is possible
  later, but nothing asks for one.
- **The optimizer is constrained the same way on every machine:** no
  reassociation, no contraction of `a*b + c` into `fmadd` unless it is
  written (`flfma`), and no folding of anything but correctly rounded
  operations. Elementary functions are folded only by calling the same
  runtime primitive the program would call.

  That is what keeps every machine giving the same bits, which the test
  suite depends on. NaN payloads are the one exception: never printed,
  and unspecified if `float->bits` is ever offered.

**`spin` and sizes.** A float never counts down: `x - 1.0` equals `x` for
large `x`, and comparisons with `NaN` are all false. So size-change
termination treats float parameters as unrelated, and float comparisons
teach no size facts. `fibfp` says `spin`, and a loop over a float with an
`int` counter needs none. `float->int` gives an `int`, not a `nat`.

**What both checkers and both compilers need** (the Rust ones and the
ones in FX-26, which must agree):
- **Checkers** (`check.rs`, `check.fx`): the base types `float` and `f32`,
  and the type constructors `f64array` and `f32array`, with their region
  argument; literal typing; the new constants' types in both standard
  tables (`standard.rs`, `standard.fx`); `data` membership; no size facts
  from floats. There are no new rules: everything is a constant with a
  monomorphic type, as `+` is.
- **Cellular compilers** (`cellular.rs`, `compile.fx`): a routine per
  operation, over boxed floats, with no tag checks, and float literals as
  constant data made once. The two already agree by construction on which
  routine a standard name becomes.
- **Register-code compilers** (`regcode.rs`, `regcode.fx`, in step with
  each other): float registers and float instructions (S1), and the
  worker/wrapper entries (S3). These are decided by type alone, so the two
  can agree instruction for instruction.
- **The evaluator written in FX-26** (`evaluator.fx`): the operations, on
  its own values.
- **The lowering** (`lower.rs`): Scheme's flonum operations (`fl+`, …) as
  integrable primitives. `f32` operations are lowered as a flonum
  operation followed by `%round-f32`.

## 4. The recommended design, staged

Each stage is committed and tested on its own, with the benchmark table
in the commit.

**S0: `float` everywhere, boxed.**
- **Language and tools:** the language side above, in both checkers, both
  compilers, the evaluator, the lowering and both readers.
- **Machines:**
  - Every machine uses the flonum bloblet.
  - Cellular routines unbox, compute and box.
  - Native code does the same inline: `ldur d`, the operation, then an
    inline box, whose allocation slow path is the existing call-out.
  - Elementary functions are call-outs.
- **Result:** every benchmark in the table runs, with the same answers as
  Larceny, OCaml and MLton. This is the stage to port them at.

**S1: raw floats within native procedures.**
- **Register code:** float registers (`FREG1`… and a float accumulator), and
  instructions that load or store a float from a frame slot, a boxed
  float or an `f64array`, operate, compare and branch, and box.
- **Native compiler:** register code's float registers go to `d16`–`d31`
  and the arguments' `d0`–`d7`. A float live across a call is stored raw
  in a slot the mask leaves out. A box is made only at an escape.
- **The register allocator's convention:** every `d` register is lost
  across a call, as every `x` register is today, so nothing changes.
- **The Rust boundary:** AAPCS64 makes `d8`–`d15` callee-saved. The entry
  from Rust into native code must save them if native code may use them.
  It is simpler for native code never to allocate `d8`–`d15`. Call-outs
  into Rust clobber `d0`–`d7` and `d16`–`d31`, so a float live across a
  call-out is in a frame slot like any other value.
- **An inline box's slow path** is a safepoint: the float being boxed
  goes into the machine's state before the call-out, and comes back from
  there.
- **The collector** needs one change: see below.
- **Result:** `sumfp`, `mbrot` and `mandelbrot` become free of
  allocation.

**S2: `(f64array R)`** (and `(f32array R)`, whose layout is the same, at 4
bytes an element).
- **Machines:** a kind, raw suffix, and nothing new for the collector, the
  heap images or the barrier. Cellular routines box on `-ref`. Native code
  loads and stores raw, with a bounds check against *B*.
- **Result:** `fft`, `spectralnorm`, `simplex`, `pnpoly`, `nbody` and most
  of `nucleic`. Their ports use `f64array` where the original uses a
  vector of floats, and say so in the header.

**S3: floats in the calling convention (worker/wrapper).**
- **Convention:** floats in `d0`–`d7` and the result in `d0` at the
  worker entry. The wrapper is the procedure's value. Known calls, and
  calls through a global whose value turns out to be native code (the
  kind check native calls already do), go to the worker.
- **Adapters:** the cellular/native adapters (`%fx26-convert`) and calls
  from cellular code use the wrapper, which is uniform, so they need
  nothing new.
- **Result:** `fibfp`, and the small float helpers of `nucleic` and `ray`.

**S4: `f32`, with `i32`/`u32`**, which share the trick of the upper half.

**S5, if measurements ask for it:**
- flat generative records (raw float fields in the suffix);
- `float` globals kept raw, in a cell's suffix;
- specialization of a chosen polymorphic procedure at `float`;
- `i64`/`u64` on the same raw slots and registers (`x`, not `d`);
- self-tagged immediate floats for the uniform representation.

### Implications, by part

| part                      | what changes                                                                                                                                                                                                                                                                                                                                                                                      |
| ------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| tags                      | none for `float`; immediate subtag 9 for `f32`. Tag `010` stays reserved                                                                                                                                                                                                                                                                                                                          |
| heap and collector        | none for boxes or `f64array`: both are raw suffixes, which the Cheney scan and the crossing map already skip. The nursery absorbs boxes that die young. Stores of raw floats need no card mark                                                                                                                                                                                                    |
| stack maps                | a raw float slot is simply outside the mask. **Continuations must change**: capture now copies a slot outside the mask as fixnum 0, which would lose a live raw float. A captured frame should become the planned bloblet of its own kind: traced slots as fields, and every other slot, link and return address copied raw into the suffix. Then the mask need not tell dead slots from raw ones |
| the foreign call-out      | leaves native frames in place and follows their masks, so it is unaffected                                                                                                                                                                                                                                                                                                                        |
| register allocator        | a second register class (`d16`–`d31` for temporaries, `d0`–`d7` for arguments), all caller-saved; the frame-slot liveness pass extended to float slots, which are never put in the mask                                                                                                                                                                                                           |
| native calling convention | S3: `d0`–`d7` and `d0` at the worker entry; the wrapper unchanged                                                                                                                                                                                                                                                                                                                                 |
| cellular machines         | tagged stacks unchanged: boxed floats, `f32` immediates. Only routines are added. Not fast, but not asymptotically slow either                                                                                                                                                                                                                                                                    |
| register-code machine     | boxed, like the cellular ones, until its twins retire (native-conventions step 6)                                                                                                                                                                                                                                                                                                                 |
| Scheme lowering           | Scheme flonums; `f32` by rounding each operation                                                                                                                                                                                                                                                                                                                                                  |
| heap images               | nothing: floats are bits in suffixes                                                                                                                                                                                                                                                                                                                                                              |

## Open questions for the user

1. **Names.** Is `float` (FX's) the type, with `f64` as an alias? Are
   `fl+` and the rest the operations, or should `+` be resolved by type
   when checking? Resolving it would be a new kind of rule in both
   checkers.
2. **Integer literals in float positions.** Should `2` check as a `float`
   where one is expected (a literal only, not a subtype)? The ported
   benchmarks write `2.`, so neither choice blocks them.
3. **`exact` of a non-integral float.** Trap, or give the nearest integer?
   And should `floor` and the like return a `float` (R7RS), with an
   `exact-` variant, or an `int` (FX-87)?
4. **Arrays.** Is `(f64array R)` as a type of its own acceptable, or should
   `(arrayof float R)` be flat, OCaml-style, at the cost of a dynamic check
   in polymorphic array code?
5. **`f32` and `i32` as immediates with a subtag** (self-describing, one
   more instruction to box), or fixnum-shaped, as `PLAN.md` has `i32`?
   Both should get the same answer.
6. **Order.** S0 then S1 and S2 unblock and speed up the most. Should S3
   wait for measurements of `fibfp`-like code?
7. **Tag `010`.** Keep it reserved for locatives, or give it to
   self-tagged floats later?

## Sources

In this repository:
- `crates/fixpt-heap/src/value.rs`, `crates/fixpt-heap/src/layout.rs`,
  `crates/fixpt-heap/src/heap.rs` (`make_flonum`, `alloc`);
- `docs/object-model.md`, `docs/research/generational-gc.md`,
  `docs/research/native-conventions.md`, `docs/fx26.md`,
  `docs/divergences.md`, `PLAN.md` ("Fixed-width integers");
- `crates/fixpt-native/src/direct.rs`, `crates/fixpt-runtime/src/num.rs`,
  `crates/fixpt-fx87/src/standard.fx`, `crates/fixpt-fx26/src/standard.rs`;
- `scheme-bench/PORTING.md`, `mllang-bench/SOURCES.md`.

Larceny (read-only, `~/Dev/LangPlay/larceny`):
- `doc/LarcenyNotes/note2-repr.html` (flonums);
- `doc/LarcenyNotes/note3-arithmetic.html` (generic arithmetic);
- `src/Compiler/pass3rep.sch` (representation inference);
- `src/Compiler/iasn.imp2.sch` (flonum primops);
- `src/Rts/layouts.cfg`;
- `test/Benchmarking/R7RS/src/{fibfp,sumfp,fft,mbrot,mbrotZ,nucleic,ray,simplex,pnpoly}.scm`.

Online, read-only:
- Chez Scheme Version 10.0.0 Release Notes, February 2024, §2.4
  "Compiler improvements" (local unboxing of floating-point operations,
  type recovery):
  <https://cisco.github.io/ChezScheme/release_notes/v10.0/release_notes.pdf>.
  Flvectors: the 10.1.0 release notes, §2.14 "New flonum operations"
  (10.0.0): "Mutable flonum vectors cooperate with local unboxing":
  <https://cisco.github.io/ChezScheme/release_notes/v10.1.0/release_notes.html>.
- M. Flatt et al., "Rebuilding Racket on Chez Scheme (Experience Report)",
  ICFP 2019.
- OCaml manual, "Interfacing C with OCaml" (flat float arrays,
  `Double_array_tag`, `floatarray`): <https://ocaml.org/manual/5.5/intfc.html>;
  `Float.Array`: <https://ocaml.org/manual/5.5/api/Float.Array.html>;
  LexiFi, "About unboxed float arrays":
  <https://www.lexifi.com/blog/ocaml/about-unboxed-float-arrays/>.
- X. Leroy, "Unboxed objects and polymorphic typing", POPL 1992; "The
  effectiveness of type-based unboxing", TIC 1997.
- Z. Shao and A. W. Appel, "A type-based compiler for Standard ML", PLDI
  1995. The SML Basis Library, `MONO_ARRAY` (`Real64Array`).
- MLton, "Monomorphise" ("eliminates polymorphic values and datatype
  declarations by duplicating them for each type at which they are
  used"), the guide's source at commit
  `aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37`:
  <https://raw.githubusercontent.com/MLton/mlton/aa2fd1ad9b91375903a4253cfcf1ea5ef2754f37/doc/guide/src/Monomorphise.adoc>.
- S. Peyton Jones and J. Launchbury, "Unboxed values as first class
  citizens in a non-strict functional language", FPCA 1991. A. Gill and G.
  Hutton, "The worker/wrapper transformation", JFP 2009. R. Eisenberg and
  S. Peyton Jones, "Levity polymorphism", PLDI 2017.
- V8, "Pointer compression in V8" (double-field unboxing disabled, -3%;
  Smis): <https://v8.dev/blog/pointer-compression>.
- O. Melançon, M. Serrano, M. Feeley, "Float Self-Tagging", OOPSLA 2025,
  arXiv:2411.16544v3 (1 Aug 2025): <https://arxiv.org/abs/2411.16544>;
  DOI <https://doi.org/10.1145/3763108>. Read for this note:
  - §1.2–1.3, NaN-boxing and NuN-boxing;
  - §2.4, one tag;
  - Fig. 5, the float profile of the R7RS benchmarks;
  - Fig. 9, times relative to NuN-boxing, on an M2 among others;
  - §4.5, bump allocation.

  Their compilers: Bigloo at commit 5b1118, and Gambit v4.9.7 at commit
  768900.
- C. Béra, "64 bits Immediate Floats" (Spur's SmallFloat64):
  <https://clementbera.wordpress.com/2018/11/09/64-bits-immediate-floats/>.
- JavaScriptCore, `Source/JavaScriptCore/runtime/JSCJSValue.h`, WebKit
  commit `be0094718dcc8f7b99f46d6eda275e98db5d7c56` (2026-09-29). It has
  the encoding comment, `DoubleEncodeOffset` (2^49), `NumberTag`
  `0xfffe000000000000`, and `OtherTag`/`BoolTag`/`UndefinedTag`:
  <https://github.com/WebKit/WebKit/blob/be0094718dcc8f7b99f46d6eda275e98db5d7c56/Source/JavaScriptCore/runtime/JSCJSValue.h>.
- SpiderMonkey, `js/public/Value.h`, mozilla-firefox/firefox commit
  `b19257565e8888d9f58be316c93af04a8590eb15` (2026-09-26). It has the
  NaN-boxing comment, `JS_PUNBOX64`, `JSVAL_TAG_SHIFT` 47,
  `JSVAL_TAG_MAX_DOUBLE` `0x1FFF0`, `JSVAL_INT_BITS` 32, and
  `CanonicalizeNaN`:
  <https://github.com/mozilla-firefox/firefox/blob/b19257565e8888d9f58be316c93af04a8590eb15/js/public/Value.h>.
- LuaJIT, `src/lj_obj.h`, branch v2.1, commit
  `faaf663340347a78b22ed94c63c24fe090bd9784` (2026-07-27), the comment on
  "Internal object tags" (`LJ_GC64`: 13 high bits set, a 4-bit itype,
  47-bit payload):
  <https://github.com/LuaJIT/LuaJIT/blob/faaf663340347a78b22ed94c63c24fe090bd9784/src/lj_obj.h>.
- xnu, `osfmk/mach/arm/vm_param.h`, `MACH_VM_MAX_ADDRESS_RAW`
  `0x00007FFFFE000000` on macOS. This is apple-oss-distributions/xnu `main`
  as fetched on 2026-09-29, whose latest commit was then
  `f6217f891ac0bb64f3d375211650a4c1ff8ca1ea`:
  <https://github.com/apple-oss-distributions/xnu/blob/main/osfmk/mach/arm/vm_param.h>.
- S. Figueroa, "When is double rounding innocuous?", ACM SIGNUM
  Newsletter 30(3), 1995.
- W. Clinger, "How to read floating point numbers accurately", PLDI 1990.
  G. Steele and J. White, "How to print floating-point numbers
  accurately", PLDI 1990. U. Adams, "Ryū: fast float-to-string
  conversion", PLDI 2018.
- Arm, *Procedure Call Standard for the Arm 64-bit Architecture* (AAPCS64):
  `v0`–`v7` for arguments and results, and `d8`–`d15` callee-saved.
