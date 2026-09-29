# Stack maps, a write barrier, a remembered set and a nursery

2026-09-29. The user's list, in their order: "stack maps, write barrier,
remembered set, nursery". It also answers their question: "Can we do
make shift stack maps by formatting the stack like a chain of bloblets?"
Yes: below, each native frame carries a header word that says which of
its slots the collector traces.

## Where things stand

- **One generation.** The heap is a Cheney semispace pair
  (`fixpt-heap/src/heap.rs`), with arenas and reaps beside it
  (`heap/regions.rs`) and a non-moving, mark-swept code area
  (`heap/code.rs`). Every collection copies everything live.
- **Allocation is not a safepoint.** A `Value` stays valid across
  allocation: the active semispace grows in place (each has 2^31 words of
  address space reserved), and objects move only in `collect`, at a
  machine's safepoint, given every root.
- **Native frames are walked by their links** (`fixpt-native`,
  `native_frames`): each frame runs from its frame pointer to its caller's.
  Every word after the link and return address is traced as a value, so
  `save` zeroes every slot.
- **Cellular machines' stacks** are vectors of values (the Rust machine's
  `ds`/`rs`, and the machine-code machines' data and return stacks). The
  collector traces them whole; they have no raw words.

## 1. Stack maps: a frame as a bloblet

A native frame becomes a small bloblet on the stack:

| where           | what                                                   |
| --------------- | ------------------------------------------------------ |
| `[x29]`         | the caller's frame pointer (the link)                  |
| `[x29, #8]`     | the return address                                     |
| `[x29, #16]`    | the header: a fixnum, the mask of the slots traced     |
| `[x29, #24+8k]` | slot `k` of register code, then the code bloblet, then the closure |

The header is a mask, not a count. The native compiler knows which slots
are live at each call, since it can analyse register code: a backward
liveness pass over its slots (`stack k` and `load r k` read slot `k`;
`setstk k` and `store r k` write it; branches, guards and returns are
the edges). Before each instruction that may lead to a collection (a
non-tail call, a call of itself, a call-out, a closure made), a frame
stores the mask of the slots live after it. It adds the code bloblet's
slot, and the closure's if the code reads it. A store is left out where
the same mask was stored earlier on the only path there. A procedure's
frame is walked only while it is in a call, so the header is always one
the code stored.

What it buys:

- **Precision.** A dead slot no longer keeps what it held alive.
- **No zeroing.** `save` no longer clears every slot: a slot not live is
  never read. A slot the analysis finds live at entry (read before any
  write on some path) is still cleared. That would be a register
  compiler's mistake, so it is handled, and the report counts it.
- **Room for raw words.** A slot outside the mask may hold anything: an
  untagged integer, a float, an address. Nothing uses that yet (`i64`
  and `u64` are waiting for it, PLAN.md's "fixed-width integers").

What reads frames follows the header: the collector's walk
(`native_frames`), the foreign call-out that keeps the frames' values
while a cellular machine runs, and taking a continuation. That copies a
dead slot as the fixnum 0, since the vector it goes into is traced. A
control frame (a prompt's or a mark's) has its marker where the header
is, a value no program makes; the walk traces all of such a frame, as
before. A frame of 16 bytes (a stub's, a leaf's slow path) has nothing
to trace.

The cost is at most two instructions (`movz`/`movk`, `str`) at a call
that changes the mask. Against that, `save` loses its `stp xzr, xzr` for
every 16 bytes of frame.

## 2. The nursery

A new area for young objects, its own reserved address range like the
semispaces (and growing in place like them, so allocation stays no
safepoint). Everything the heap's `bump` allocates goes there. So does
machine code's inline allocation: `top_address` and `inline_limit` name
the nursery's top and limit. Regions and the code area are unchanged.

- **A minor collection** runs at a safepoint when the nursery's use
  passes its size (`NURSERY_WORDS`, with a policy for stress tests, as
  `gc_every` is for full collections). It promotes everything live in
  the nursery at once: each object is copied to the end of the old
  semispace, and the copies are scanned there, Cheney's way. Its roots are
  the usual ones (explicit roots, globals, symbols, the machine's), what
  the arenas and live reaps hold (scanned whole), the code area's
  bloblets, and the remembered set. Afterwards the nursery is empty, so
  no old object points into it, and the remembered set is cleared.
- **A major collection** is today's `collect`, with the nursery a second
  from-space. It runs when the old semispace passes its threshold, as
  now.

Promoting everything at once keeps the old space a plain Cheney space,
with no ages to keep. An object that dies just after its promotion costs
a copy. If that shows in the numbers, a survivor space can come later.

## 3. The write barrier and the remembered set: cards

An old object gets a pointer to a young one only by a store into it,
after its promotion. Each such store marks the object's **card** (512
bytes of the heap's address range) in a byte table, one byte per card:

```
lsr  x17, obj, #9        the card of the object's reference
ldr  x16, [state, #cards]  the table, biased by the heap's base
mov  w15, #1
strb w15, [x16, x17]
```

That is four or five instructions, no branch and no call-out. It is safe
anywhere, a leaf included, and idempotent: a loop that stores into the
same object marks one card, however often it stores. The table is as
large as the heap's reserved range needs (one byte per 512 bytes), and
the system commits it as it is written.

A minor collection scans the dirty cards of the old semispace. For each
one it traces every object that overlaps the card, all of its fields, and
then clears the card. To find the first object in a card, the old space
keeps a **crossing map**: for each card, where the first object starting
in it starts. The collector fills it as it copies objects into the old
space, since both kinds of collection place them there in order. Parsing
from that point works because the first word at any object boundary is a
header or a pair's first value (`value.rs`, tag 110 reserved).

Marking the card of the object's reference, not of the field written,
covers both: an object overlaps every card that holds one of its fields
and its reference.

**Where the barrier goes**, everywhere a value is stored into an object
that already exists:

| where                                    | stores                                                                                          |
| ---------------------------------------- | ----------------------------------------------------------------------------------------------- |
| `fixpt-heap`                             | `set_car`, `set_cdr`, `set_box`, `set_bloblet_slot`, `set_bloblet_field`, `set_closure_ref`, `set_slot` |
| the Rust cellular machine                | through those                                                                                   |
| the hand, stencil and compiled machines  | `field!`, `global!`                                                                             |
| the hand register machine                | `setfield`, `setglbl`                                                                           |
| the native compiler (`direct.rs`)        | `setfield`, `setglbl`                                                                           |

A store that initialises an object just made in the nursery needs none
(the heap's constructors write its words directly). A store into an
arena, a reap or the code area needs none, since those are scanned whole
at a minor collection.

## Testing

- **A verifier**, under the stress policy: before a minor collection,
  every pointer from the old space into the nursery must lie in a dirty
  card. It walks the whole old space, so it is for tests only. A missing
  barrier fails there, at the collection after the store, whichever
  machine made it.
- **Stress policies**: a minor collection at every safepoint (the
  nursery's `gc_every`), full collections as now; the suite under
  `--features gc-stress` (for `fixpt-scheme`), and the native and
  cellular runs of `every_test_program_runs_natively_as_cellular` with
  the policy on.
- **Stack maps**: a test that a large object held only by a dead slot is
  not kept by a collection in a later call, and the native tests under
  `gc_every`.

## Order of work

1. Stack maps in the native compiler (this note's §1), with its test.
2. The card table and the barrier in the heap's store methods; the
   crossing map; the verifier.
3. The nursery and minor collections, with the stress policy; then the
   barrier in each machine's `field!`/`global!`/`setfield`/`setglbl`,
   each machine's tests passing under the policy before the next.
4. Measure: the self-compile and the benchmarks, collections and time.
   Then size the nursery.
