# The object model: bloblets

Draft, 2026-09-25. Being implemented as M12 Phase A; see `PLAN.md` §11.

This document proposes one new kind of heap object, the **bloblet**. It could
eventually represent almost every other kind. It is also the layout the FX-26
interpreter and compiler, written in FX-26, will build on. So it is shared
between the Rust part of the system and the FX-26 part, and it must be
specified precisely enough for both.

The garbage collector stays in Rust. So does a bootstrap interpreter.

## Where we are

`crates/fixpt-heap/src/value.rs`, inherited in outline from Larceny. A value is
one 64-bit word with a 3-bit tag:

```text
000  fixnum        61-bit signed
001  pair          index of a 2-word car/cdr cell (no header)
010  object        index of a header word
011  immediate     #f, #t, (), unit, eof, characters, …
100  reserved
101  reserved
110  header        never a value; starts an object
111  forwarding    only during a collection
```

A header is `[len:40][type:16][unused:5][110]`. The type decides, through
`ObjType::payload_is_scanned`, whether the payload is traced (vectors,
records, closures) or raw bits (strings, bytevectors, flonums, bignums). So
the collector has to know every type. Code is `[name, arity, consts,
bytecode]`, and the bytecode is a separate bytevector reached through a
field.

## The bloblet

```text
          ┌────────┬─────────┬─────────┬─────┬─────────┬─────────┬──────────────────────┐
          │ header │ field   │ field   │  …  │ field   │ trailer │ suffix: raw bytes    │
          │  110   │ tagged  │ tagged  │     │ tagged  │   101   │ (never traced)       │
          └────────┴─────────┴─────────┴─────┴─────────┴─────────┴──────────────────────┘
 offsets   −(F+1)    −F        −F+1            −2        −1       0 ▲
                                                                    │
                          every tagged pointer to the bloblet points here
```

- The **header** gives the number of tagged fields, *F*, and the length of the
  suffix in bytes, *B*. The object occupies `1 + F + ⌈B/8⌉` words, and the
  suffix is padded to a whole word.
- **Fields** are ordinary tagged values, traced like a vector's elements.
- The **suffix** is raw bytes: characters, bytecode, native code, float bits,
  bignum limbs. It is never traced, so it can hold no pointers.
- A **bloblet pointer** (tag `100`) points at the start of the suffix: the
  boundary between the last field and the first byte.

### The hard invariants

What the system must maintain, and what the collector relies on:

1. **Every bloblet starts with a header word**, and the header gives *F* and
   *B*.
2. **Every one of the *F* fields is a tagged word.** Padding counts: filler
   before the suffix, for alignment, is a tagged word counted in *F*.
3. **Every tagged pointer to a bloblet points at the start of its suffix.** An
   untagged program counter may point into the middle of the suffix. The
   collector does not trace it, so it must always be derivable from a traced
   bloblet pointer: stored as an offset from one, never as an absolute address
   that outlives a collection.
4. **No field ever has the header tag.** This holds already: no constructor
   produces tag `110`. Together with 1 and 2, it makes the *backward scan*
   sound. From a bloblet pointer, step back over tagged words until one has tag
   `110`: that is the bloblet's own header, and nothing earlier can be mistaken
   for it.

### The fast path: the trailer

A well-formed bloblet ends its fields with a **trailer** (tag `101`) at offset
−1. It says where the header is, so neither code nor the collector has to scan
for it. The trailer is a field like any other: it is counted in *F*, and its
tag says "not a pointer", so tracing skips it as it skips a fixnum. The
collector needs no special case for it.

The trailer is **not** a hard invariant. A bloblet without one is still correct,
and the backward scan (invariant 4) finds its header. A bloblet has a trailer
when it is worth one: anything reached by a bloblet pointer often, and code
above all.

**Its contents are reserved.** All that is committed to is the tag, and the
purpose: a bloblet's own trailer lets the header be found without a scan. The contents are reserved *to the runtime*:
the collector is the one reader, and today it stores the distance in words
from the trailer back to the header (`layout.rs`, `T_DISTANCE`). No program
may read or write a trailer.
How it encodes that, and what else it holds, is deliberately left open. The
distance back to the header, the kind, and a hash of the field layout are
all candidates. Until something needs one of them, nothing may rely on any
bit of a trailer beyond its tag.

### Fields are addressed from the suffix

The canonical name of a field is its **negative offset from the suffix**: −1
is the trailer, −2 the field before it, and so on. Header-relative indices
exist, and the collector uses them, but programs should not.

That is what makes **extension by prepending** work. A bloblet cannot grow in
place under a copying collector, so extending one means building a new bloblet
with the same suffix and more fields *in front*. Every existing field keeps
its negative offset, so code that loads field −*k* works unchanged in the
extended bloblet. Code can be written against fields that do not exist yet,
added later by whoever extends it.

## Code

The motivating case. A code bloblet is
`[header][metadata and constants…][trailer][bytecode or native code]`, and a
code pointer is a bloblet pointer, pointing at the first instruction. Everything
the code needs is at a fixed negative offset from where it starts:
- its constants;
- its name, arity and frame layout;
- its source map;
- the facts the checker proved about it (`docs/fx26.md`, the `%fx-note`
  claims).

For native code, those are PC-relative loads, as SBCL reaches its constants.
For bytecode, they are loads at a fixed negative index. A closure is a bloblet
whose fields are the code pointer and the captured variables.

Return addresses point *inside* code, not at its start, so (invariant 3) they
are not tagged pointers. A frame keeps the code's bloblet pointer and the return
point as an offset from it, as the VM's frames effectively do now.

### Interpreted and compiled, side by side

The bootstrap interpreter reads bloblets directly, *and* code can keep a
representation of its own. The two are the same design at two stages, as in
Forth's threaded code:
- **Interpreted.** A code bloblet's *fields* are its program: a sequence of
  pointers to other code bloblets, and literals. Its *suffix* is a small
  inner interpreter, Forth's `NEXT`, that runs through those fields in
  order. Until there is native code, the Rust bootstrap interpreter plays
  that part for every such bloblet. It recognises them by kind.
- **Compiled.** The same bloblet, with its suffix replaced by compiled code.
  The fields keep their negative offsets, so whatever relied on them still
  works. A caller holds only the pointer to the suffix, so interpreted and
  compiled code are called alike, and one replaces the other without any
  caller noticing.

Code is therefore compiled **incrementally**, one bloblet at a time, and the
two forms coexist throughout. The interpreted form also puts the program
itself in tagged fields. So the collector traces it with no special case,
and no separate constants table has to be kept in step with it, as bytecode
needs one. And since fields are mutable by default (see "Mutability is per
bloblet"), interpreted code can be inspected and edited as data. The FX-26
interpreter written in FX-26 runs the same bloblets as the Rust one.

### Kept in mind: pinned code and raw return addresses

Not a decision; an option the design should leave open. If code bloblets do not
move, a return address can be a raw pointer straight into the code, not an
offset from a traced pointer, and it survives a collection. V8, the JVM and
.NET keep code in a space that does not move. SBCL has an "immobile space"
that it defragments only when saving an image.

What that would cost:
- **Liveness.** A raw return address is untagged, so it does not keep its
  code alive. And it points into the suffix, which is raw bytes, so the
  backward scan cannot find the header from it. Either every frame still
  holds a traced pointer to its code, or the pinned space keeps a map from
  address to object start, as V8 and SBCL do.
- **Heap images**, which are written as word offsets with no relocation pass.
  Return addresses stored relative to the code space's base would stay
  position-independent, at the cost of one add per return.
- **Moving pinned code anyway.** Pinning could be speculative, with moving
  kept possible. Then moving a code bloblet means finding and rewriting every
  return address into it, in live stacks and in captured continuations. That
  needs every frame's layout to say which words are return addresses. The
  code bloblet's metadata fields are the place for that. Moving should be rare,
  so paying only when it happens is reasonable.

The gain is small while the engine is a bytecode VM, whose PC is already an
index into the suffix. It matters for native code (PLAN.md, M10).

### Mutability is per bloblet, chosen at allocation

Decided 2026-09-25: there is no global immutability. Bloblets are mutable by
default. The effect system makes immutability-based optimisations possible
later without building a constraint in now. But a bloblet can be *allocated* as
immutable, and its fields and its suffix are chosen **independently**. That
is what code generation and caching need: a code bloblet whose metadata fields
stay writable, while its instructions never change once written. Then
instruction-cache coherency is handled once, not worked around on every
write.
- **Two header flags**, "fields immutable" and "suffix immutable". For most
  bloblets they are promises the language keeps, not something the hardware
  enforces. In FX-26 the checker enforces them: a bloblet with immutable fields
  offers no field-writing operation, as `datum` offers none now.
- **Initialising is not mutating.** An immutable bloblet is still written once,
  as it is built. The pattern is: allocate writable, initialise (FX-91 had
  an `init` effect for exactly this), then **seal**, which returns the
  immutable-typed view. For executable code, sealing is also where the
  instruction cache is flushed.
- **Hardware enforcement is by page, so it is a matter of placement.**
  Executable bytes protected W^X must sit on pages nobody writes. "Mutable
  fields, immutable suffix" then means the boundary falls on a page
  boundary: header and fields at the end of a writable page, suffix on a
  protected one. The padding before the suffix is tagged filler, which
  invariant 2 allows. That costs space for small bloblets, so it is an option,
  not a default. The usual design is a separate space that sealed code is
  placed into, which is another reason for such code not to move (see
  above). If it does move, the collector must unprotect, copy, re-protect
  and flush.

So the allocator is given two things, kept apart:

| | what it says | examples |
|---|---|---|
| **layout** | what the bloblet is | kind, *F*, *B*, trailer or not |
| **placement** | where and how it lives | fields mutable or not; suffix writable, sealed or executable; suffix aligned to a word, a cache line or a page |

The kind is the language's business, and the placement the memory manager's.
The default placement, all mutable and word-aligned in the ordinary copying
heap, is what almost every allocation uses.

### Construction

A bloblet must be well-formed at every point where the collector might run.
A primitive written in Rust gets that for free, since it can simply contain
no safepoint. But the FX-26 compiler will generate allocation sequences
itself, and those need a protocol that is safe wherever a safepoint falls.

**The protocol.** Every step leaves the bloblet well-formed, and only two of
them must not be interrupted, each a single store:
1. **Allocate** `1 + F + ⌈B/8⌉` words, whatever they hold, and write the
   header as **`F = 0`, `B + 8F` bytes of suffix**. It is the final size, so
   heap scans stay in step. All of it is untraced suffix, so leftover garbage
   in the words is harmless. *(Atomic: the bump and the header store.
   Nothing may scan between them, or it would take the word where the
   header belongs for the start of a pair.)*
2. **Zero the would-be fields**, with ordinary stores. This can be
   interrupted anywhere. Those words are not traced yet, and a collection
   may move the bloblet meanwhile. Only non-pointers are written, so a
   collection can leave nothing stale. A pointer written there *would* be
   left stale, since the suffix is not traced, which is why this step writes
   zeros and nothing else.
3. **Change the header once**, to the final *F* and *B*: one store.
   *(Atomic.)* Every field is now the fixnum 0, since fixnums are tag `000`,
   so the bloblet is well-formed as what it is meant to be.
4. **Fill** fields and bytes with ordinary stores. A collection between any
   two of them is harmless.

**The field count changes exactly once, from 0 to its final value, and
before the bloblet is published.** Until then only its constructor holds it,
so it is not yet a bloblet to anyone else. After publication the field count
is fixed for the bloblet's life. The constructor's own pointer points at the
suffix start of the `F = 0` layout, and the collector keeps it correct
through steps 1–2. After step 3 the constructor moves it forward *F* words.

The atomic parts are two single stores however large *F* is. The suffix is
never zeroed, since it is never traced: a suffix about to be overwritten,
with bytes copied in, costs nothing extra. Where the allocator happens to
hand out zeroed memory, steps 1–3 collapse into writing the final header
at once. That is an optimisation, not a requirement.

This is the only allocation primitive the runtime needs. The others are
compositions of it and ordinary stores:
- **From given values**, like Scheme's `vector`: allocate, then store each
  value. The fit for FX-26 records, whose fields each have a type of their
  own. The checker must see a record's fields as uninitialised until they
  are stored, and not as fixnums: the `init` effect of "Mutability is per
  bloblet".
- **Filled**, like `make-vector`: allocate, then store `fill` in every field.
  For FX-26 all fields then have `fill`'s type: the vector case.
- **Extended**: allocate *k* more fields than `b`, store the new values in
  front, and copy `b`'s fields and suffix. `b` is untouched.

When the final field count is not known in advance, the contents are
collected in something growable first, a vector or a list, and the bloblet is
built once the count is known.

**Considered, and not chosen: requiring zeroed memory.** Fixnums are tag
`000`, so zeroed memory is already a valid set of fields, and the final header
could be written straight away. But that makes zeroing the allocator's
job, on every allocation or across all of to-space at each flip, and it
zeroes suffixes, which never need it. The protocol above zeroes only the
field words, and only as part of building the bloblet that needs them.

And afterwards, nothing a program does can break an invariant:
- **A field can only be set to a tagged value.** The only words with the
  header or trailer tag are ones the runtime writes itself.
- **The header and trailer are written only by the construction protocol.**
  The header changes once, before publication, and the trailer's contents
  are reserved in any case.
- **The frozen flags are set only by `seal`.**
- **Writing into the suffix cannot malform anything**, since it is never
  traced.

### What this machine allows (measured 2026-09-25)

Checked on the development machine: Apple Silicon, macOS 26.6.2, 16 KiB
pages, an unsigned local binary without the Hardened Runtime. The
experiment is a scratch program outside the repository.

| approach | result |
|---|---|
| a page of fields beside a page made read+execute with `mprotect` | works, but per 16 KiB page: every code bloblet would be padded to a page boundary |
| `MAP_JIT`, toggling write access (`pthread_jit_write_protect_np`) around each field write | works, at **32 ns per field write**, against about 1 ns for a plain store |
| writing a `MAP_JIT` page while in execute mode | the process is killed (`SIGBUS`) |
| **two mappings of the same memory** (`mach_vm_remap`): one read+write, one read+execute | **works**: bloblets pack anywhere; fields are written at full speed through the read+write view; code runs from the read+execute view, and can be rewritten in place with a flush |
| costs | `mprotect` 0.3 µs; instruction-cache flush of 64 bytes 92 ns, of a page 0.67 µs |

The consequences for the design:
- **The MMU cannot give mutability per bloblet.** Its unit is a 16 KiB
  page, and a code bloblet is almost always far smaller.
- **"Mutable fields, immutable code" is real, one level up.** A code space
  is mapped twice. Code executes only through the read+execute view, which
  can never be written, so no address is ever both writable and
  executable. Fields are written through the read+write view. Nothing is
  padded, and nothing changes per page.
- **The frozen bits are promises the runtime keeps**, not hardware
  protection. The runtime refuses the writes, and FX-26's types say the
  same thing statically. A frozen suffix also ends instruction-cache
  obligations: nothing needs flushing again, and compiled code may be
  cached or inlined against it. That is reason enough to keep the bits.
  They are cheap, and they could be reassigned if they turn out not to be
  worth it.
- **Code does not live in the copying heap.** It goes in a separate,
  non-moving code space, mapped twice. That settles "pinned code" for
  native code, and raw return addresses into it become possible.
  Addressing bloblets across the two spaces is decided when code moves
  there (`PLAN.md` §11, Phase A′).
- **Copy-and-patch** with Rust-compiled stencils also works on this machine,
  offline and on stable rustc; see `docs/research/copy-and-patch.md`. The
  hand-written encoder stays the plan for the native core, and
  copy-and-patch comes later, once measurements call for it.

## The collector

**Copying a bloblet reached by a bloblet pointer `p`.** The tag of the word at
`p − 1` decides what to do:
- **`111`**: already forwarded, so the bloblet has moved.
- **`101`**, a trailer: it leads to the header in one step (how is
  reserved; see the trailer).
- **`110`**: the header itself, since the bloblet has no fields.
- **anything else**: a bloblet without a trailer, so the backward scan, O(*F*).

Then:
1. If the header is a forwarding pointer, the new bloblet pointer is the new
   header's address + `F + 1`.
2. Otherwise copy `1 + F + ⌈B/8⌉` words and forward the header.
3. For a bloblet without a trailer, also write a forwarding pointer into the
   from-space word at `p − 1`. The scan is then paid only on the first
   reference, and later ones take the first case. The from-space copy is
   dead, so overwriting its last field is safe. A bloblet with a trailer does
   not need this: its trailer already leads to the forwarded header in one
   step.

So, with a trailer, finding a bloblet's header costs O(1) on every reference.
Without one, it costs O(*F*) once per bloblet per collection, and O(1) after
that.

**Scanning to-space** (Cheney) meets a header, traces the *F* fields (tagged
values; tags that are not pointers, the trailer's among them, are skipped),
and skips ⌈B/8⌉ words of suffix. The collector never needs to know what kind
of bloblet it is looking at. `payload_is_scanned` goes away once every object is
a bloblet.

**Heap verification** gains two checks: every bloblet pointer's backward scan
reaches a header whose `F + 1` matches, and every trailer agrees with its
header. A bloblet with no suffix is pointed at one word past its last field,
which may be the address of the next object's header. The pointer's tag says
which object it belongs to, so verification must go by the tag, not by what
the word there looks like.

## The header

One word, for all but enormous bloblets:

```text
bit  0–2   110            header tag
bit  3–10  kind           8 bits: what the bloblet is to the language
bit  11    large          F is in an extension word just before this one
bit  12    fields frozen  the fields are immutable
bit  13    suffix frozen  the suffix is immutable
bit  14–31 F              18 bits: up to about 262,000 fields
bit  32–63 B              32 bits: up to 4 GiB of suffix
```

A `large` bloblet has *F* too big for 18 bits, so it goes in an
**extension word placed just before the main header**. The extension is
header-tagged, with the reserved kind 255, and holds *F* in 53 bits. *B*
stays in the main header, so a suffix is limited to 4 GiB.

```text
ordinary:  [main header][fields…][suffix]
large:     [extension][main header, large=1][fields…][suffix]
```

Before, not after, so that the fields always start one word after the main
header. Accessors can then find a field without first reading the header's
`large` bit. Both scans still work:
- A linear scan meets the extension word first, sees kind 255, and knows the
  main header follows.
- A backward scan from the suffix stops at the first header-tagged word it
  meets going backward, which is the main header. The main header's `large`
  bit then says the extension is just before it.

Invariant 1 holds, since the object still starts with a header-tagged word.
Almost nothing will ever be large.

## Tags, before and after

| tag | now | during migration | after |
|---|---|---|---|
| `010` | object (points at header) | old-style object | free |
| `100` | reserved | bloblet pointer (points at suffix) | bloblet pointer |
| `101` | reserved | trailer | trailer |

## What becomes a bloblet

| now | as a bloblet |
|---|---|
| vector | *F* elements, no suffix |
| record | record-type descriptor + fields, no suffix |
| bytevector | no fields, *B* bytes |
| string | no fields (or a length field), UTF-32 suffix |
| flonum | no fields, 8 bytes |
| bignum | a sign field, limbs as suffix |
| code | constants and metadata, trailer, code |
| closure | code pointer + captured variables, no suffix |
| box, symbol, port, … | fields, no suffix |

Pairs stay as they are: two words, no header. They are the most common
object, and a header would cost them 50%.

## One specification, two languages

The FX-26 compiler will emit code with hard-coded field offsets, so this
layout cannot live only in Rust. It should be written once, as a table:
tags, header bits, kinds, and the trailer's format. Both the Rust constants
and an FX-26 module would be generated from it, with a test that the two
agree.

On the FX-26 side, a bloblet would get a type along the lines of `(bloblet
(fields T…) R)`, and a code pointer a type of its own. Reads and writes go
through a region, so masking and licences apply to bloblets as to everything
else.

## Precedents

The parts are all known; the combination, as the one general-purpose layout,
is what is new.
- **Forth dictionary entries.** Link and name, then code field, then
  parameter field. An execution token points into the middle, and words such
  as `>NAME` reach the metadata before it.
- **GHC, "tables next to code".** An info table sits immediately before the
  entry code, so one pointer is both the code pointer and, at negative
  offsets, the metadata pointer.
- **SBCL code objects.** A traced section of constants, then untraced machine
  code, with both sizes recorded. On x86-64 the code reaches its constants
  PC-relatively. Function pointers point into the middle of the object, and
  the collector maps them back to its start.
- **Squeak's `CompiledMethod`.** Pointer literals followed by bytecode bytes,
  in one object.
- **Boundary tags** (Knuth). The size of a block recorded at both of its
  ends, so that it can be found from either. That is what the header and the
  trailer are.

## Plan

The staged plan, from this document through to FX-26 bootstrapped, is in
[`PLAN.md`](../PLAN.md), §11 (milestone M12). Phase A there is this
document's.

## Open questions

- ~~**What the trailer holds.**~~ Reserved: only its tag and its purpose
  are fixed. See "The fast path: the trailer".
- ~~**Mutability.**~~ Settled: per bloblet, chosen at allocation, fields and
  suffix independently. See "Mutability is per bloblet".
- ~~**The name.**~~ Settled: **bloblet**, which is unique when searched
  for, where "blob" is not.
- ~~**Strings.**~~ UTF-32, as now.
- **Suffix alignment for native code.** Handled by tagged filler fields, as
  invariant 2 allows. But is 8 bytes enough, or should the header record an
  alignment?
- ~~**The bootstrap interpreter.**~~ Both: it reads bloblets directly,
  interpreting threaded bloblets, and compiled forms replace those one at a
  time. See "Interpreted and compiled, side by side".
