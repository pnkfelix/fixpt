# Deep recursion in native code: a stack cache

`TODO.md` §52 and §53. The native convention runs on one fixed stack of 2^26
words and overflows between 5M and 20M frames of a non-tail recursion,
where Scheme recurses as deep as its heap allows. The user's direction
(2026-10-07): a stack cache in the manner of Larceny's; not, for now,
stack segments that never move.

## Larceny's stack cache, as its source has it

Read 2026-10-07 in `~/Dev/LangPlay/larceny/src` (read-only; nothing built
or run). `Rts` is `src/Rts`. Which young heap the ARM (Fence) build uses,
`nursery.c` or `sc-heap.c`, was not settled; both are cited.

**Frames.** A frame has the same size and nearly the same layout on the
stack as in the heap (`Rts/Sys/stack.c:24-76`): a size or header word, the
return address, the dynamic link (garbage on the stack, a pointer in the
heap), the saved `REG0` (the procedure), then the saved registers. In the
heap the return address is a byte offset from the procedure's code
vector; a frame whose `REG0` slot is 0 keeps a raw address into code that
does not move (`stack.c:73-76`).

**Where the stack lives.** At the high end of the nursery, growing down
toward the allocation pointer (`stack.c:9-22`): "the stack pointer is the
heap limit, and vice versa, saving registers". `G_STKP = G_ELIM` at start
(`Rts/Sys/nursery.c:115-120`); free space is `(G_STKP - SCE_BUFFER) -
G_ETOP`, `SCE_BUFFER` 64 bytes (`nursery.c:241`, `Rts/layouts.cfg:154`).

**Flush, in place** (`stk_flush`, `stack.c:129-191`). For each frame: the
size word becomes a vector header (`:150`); the return address an offset,
`retaddr - (codeaddr + 4)` (`:159`); the dynamic links chain the frames
(`:168-171`); the last links to the old `G_CONT` (`:183-184`), and
`G_CONT` becomes the first (`:185-186`). No copying.

**Underflow.** `stk_create` (`stack.c:95-120`) makes a four-word frame at
the stack's bottom whose return address is the stub
`fence_stack_underflow` (`Rts/Fence/fence-driver.c:133-139`, its `REG0` 0
so the address is never translated). A return pops its frame and loads the
caller's return address from the new top (`Asm/Fence/pass5p2.sch:308-360`,
`pass5p2-arm.sch:168-171`): past the last cached frame that is the stub,
so the return path has no test. The stub (`Rts/Fence/arm-millicode.sx:
150-165`) saves the Scheme context and calls `mem_stkuflow` →
`refill_stack_cache` → `gc_stack_underflow` → `stk_restore_frame`
(`Rts/Fence/fence-millicode.c:63-69, 755-762`; `nursery.c:307-314`).

**Restore: one frame, copied** (`stk_restore_frame`, `stack.c:196-252`).
It asserts the cache is empty (`:202`), copies the top heap frame below the
underflow frame (`:221-226`), sets `G_CONT` to that frame's dynamic link
(`:229`), turns the header back into a size (`:236`) and the offset back
into an address (`:243`). The heap frame is only read, never changed: a
multi-shot continuation stays right because each return works on a copy
(re-entering one is `stk_clear; G_CONT = k; stk_restore_frame`,
`nursery.c:330-338`).

**Overflow.** Checked in each procedure's entry (`emit-save0`,
`Asm/Fence/pass5p2.sch`, about 678-694): load `G_ETOP`, decrement `STKP`
by the frame's size, compare, and if below, undo, trap to `$m.stkoflow`,
and retry. The handler (`fence-millicode.c:190-193`) collects: in
`nursery.c:298-305` a full collection, whose `before_collection` flushes
the stack (`:211-216`); in `sc-heap.c:375-385, 446-479` a flush and more
room, then `stk_create` and one frame restored.

**At every collection** the stack is flushed first, and after it a fresh
underflow frame is made and one frame restored (`nursery.c:211-233`): the
collector never walks a stack.

**`call/cc`** (`nursery.c:316-328`): make room, flush, take `G_CONT`,
re-create the stack with one frame restored. Its cost is the live cache,
flushed in place, not a copy of the whole stack.

**Callbacks from C** (`Rts/Sys/callback.c:12-65`): no flush and no new
stack; a 24-byte frame pushed on the current one (failing with "Callback
failed -- stack overflow" when there is no room, `:19-24`), then
`scheme_start`, which plants `fence_dispatch_loop_return` in that top
frame and leaves by `longjmp` (`fence-driver.c:80-130`). Millicode calling
Scheme pushes a save frame returning to `fence_return_from_scheme`
(`fence-millicode.c:902-962`), whose `restore_context` checks for an empty
cache itself, since no return passes the underflow frame there (`:995-998`).

**Costs it counts** (`stack.c:85-89, 140, 190, 275`; `Rts/Sys/stats.h:
145-151`): stacks created, frames and words flushed, frames restored
(`G_STKUFLOW`). Comments: the in-place flush "typically much faster than
copying" (`stack.c:12-13`); underflow "is very expensive" in the
incremental marker's budget (`Rts/Sys/smircy.c:1150`).

## What carries over to fixpt

- fixpt's native frames already almost fit: after the link, each word is a
  value (the stack map, a fixnum; slots, which `reps` never leaves raw,
  `crates/fixpt-native/src/direct/reps.rs:14-16`) or the return address.
  Nothing raw lives in a frame, so §53's frame as a bloblet needs no raw
  suffix: a header in front, the link and return address made values.
- The code area does not move, so a return address may stay an address,
  as Larceny's `REG0 = 0` frames do; an offset from the code is what a heap
  image would need.
- Larceny restores one frame per underflow. Whether to restore more is the
  papers' question (below).

## The literature

Read 2026-10-07 by a research agent; the PDFs are in `docs/research/papers/`
(not committed). Page numbers are the papers' printed ones.

**Hieb, Dybvig and Bruggeman, "Representing Control in the Presence of
First-Class Continuations", PLDI 1990** (https://legacy.cs.indiana.edu/
~dyb/pubs/stack.pdf). The stack a list of segments; a capture splits the
segment at the top frame, the return address there replaced by an
underflow handler's (§4, pp. 6-8). Reinstating copies a segment no larger
than a *copy bound*, else splits off what fits: "An appropriate bound for
a given machine can be determined only by experimentation" (p. 7). Frame
size must be bounded, since one frame is always copied (p. 8). "If stack
overflow can be detected while the system is in a known state, overflow
can be treated as an implicit continuation capture" (§5, p. 9). The check:
one compare against an end pointer set two frames short, leaves and tail
loops skipping it (p. 10). The danger, *bouncing*: a recursion on the
verge of overflow that then loops over and under it makes "the worst-case
cost of recursive procedure calls ... the average-case cost" (p. 4). "99%
of all frames are smaller than 30 words" in Chez's own source (§6, p. 11).
No benchmark tables in the version read.

**Clinger, Hartheimer and Ost, "Implementation Strategies for
Continuations", LFP 1988** (pp. 124-131; the 1999 HOSC version was not
reachable). Strategies: stack, stack/heap, *incremental stack/heap*, and
PC Scheme's chunked stack. Incremental: "When returning through a
continuation frame that isn't in the stack cache, a trap occurs and copies
the frame into the stack cache": one frame per trap, and their
recommendation (§6). On `loop2`, a throw each iteration, incremental took
98.0 s to stack/heap's 83.8, "because it has to copy a frame into the
stack cache each time through the loop" (Fig. 3, 4). The chunked stack, a
small bounded cache copied to and from the heap, "reduces the worst-case
latency". Nothing on deep recursion.

**Bruggeman, Waddell and Dybvig, "Representing Control in the Presence of
One-Shot Continuations", PLDI 1996.** Overflow as an implicit capture
avoids bouncing, "since the entire newly allocated stack must be refilled
before another overflow can occur"; overflow as a one-shot continuation
needs *hysteresis*: "copying up several frames on overflow ... into the
newly allocated stack segment" (§3.2, p. 102). A recursion a million deep
ran "300% faster" with one-shot overflow handling (§4, p. 104). Default
segment 16 KB.

**Cheng, Harper and Lee, "Generational Stack Collection and Profile-Driven
Pretenuring", PLDI 1998.** Stack scanning was 95% of collection time for
Nqueen, 76% for Knuth-Bendix (Table 5); of 1336.5 frames scanned on
average in Knuth-Bendix, 116.9 had changed (§5). The return barrier:
"each time we scan the stack, we change the return address of every n-th
stack frame ... to a special stub function", n = 25; non-local exits
tracked as the shallowest stack pointer reached (§5). Collection time fell
74.3% (Color), 67.5% (Knuth-Bendix).

**Chez Scheme's source** (`s/cmacros.ss`, `c/schsig.c`, current): stack
segments of about 64 KiB; `underflow-limit` 16 words, "how much we're
willing to copy on stack underflow/continuation invocation"; on overflow,
the frames within that window are copied to the new segment. "Since the
cost of invoking continuations is bounded by default-stack-size, it should
not be made excessively large."

**Farvardin and Reppy, "From Folklore to Fact: Comparing Implementations
of Stacks and Continuations", PLDI 2020.** Segments of 64 KB; overflow
copies "until either a maximum of four frames or one-eighth of a
segment's data" (§5.1.1); `ack` took 349,103 overflows segmented, 7 with
doubling (§5.1.2). Native `call`/`ret` over pop-and-jump: 1.02-1.07×
(§5.2.2).

**Larceny on its own underflow** (`src/Rts/Sparc/memory.s`, per the
agent): the handler was inlined in assembly to save "two context
switches, a very significant part of the cost since it is incurred on
every underflow. On deeply recursive code (like append-rec) this fix pays
off with a speedup of 15-50%."

Not verified from primary sources: the 1999 HOSC text; Hansen's 1992 MS
thesis; whether Chez's current source matches the 1996 paper.

## The first version in fixpt (2026-10-07)

A *copying* stack cache, before an in-place one: the native stack stays
where it is (`DirectMachine`'s own memory); a run's cache is a bounded
part of it (`DONE.md` §52 has what it does, and the tests).

- **Overflow** is checked where it was, at a frame's entry (`cmp sp,
  LIMIT`), now against the cache's limit. Past it, every frame of the run
  but the new one is copied into the heap as the chain, and the new one
  moved to the cache's top, returning through the underflow (Hieb, Dybvig
  and Bruggeman's overflow as an implicit capture; Bruggeman, Waddell and
  Dybvig's hysteresis is the cache's size: the cache must fill again
  before the next overflow). Nothing on a call or a return is added.
- **The chain** is chunks of about 4096 words, each frame as it was on the
  stack, its link its size, its dead words the fixnum 0: Larceny's heap
  frame, with fixpt's stack map applied, and close to the in-place format
  §53 wants. Chunks are bounded so that a chain mostly restored keeps
  little more than it needs alive through collections.
- **Underflow** restores at least a frame and on to 256 words (Hieb's copy
  bound; Larceny restores one), a call-out each time.

What it cost, measured (`,native down N`, best of one, the process's
other costs aside): before, 5M frames in 41 ms and 20M an overflow;
after, 5M in 41 ms (the cache is half the stack, so it never fills),
20M in 426 ms, 50M in 1.07 s; the cellular register machine, whose stack
grows as a Rust `Vec`, about 0.7 s and 2.1 s. So about 20 ns a frame
flushed and restored. A first version made one heap object per frame:
75 ns a frame, mostly `malloc` for the vectors it built them from; then 27
ns with the objects written in place; chunks of frames as they were, read
through their payload with no lookups per frame, 20 ns. `captures`, a
continuation taken and resumed 20 calls deep 20 000 times, went from 11.4
to 9.0 ms natively: one chunk copied whole each way.

In place, in the nursery (Larceny's), and the underflow in line, are next
(`TODO.md` §52), measured against this.

## Larceny's design, adopted (2026-10-07)

The user's direction, after measuring what the stack cost the collector
(`TODO.md` §52): a deep stack in the cache was scanned at every collection
(1.4 ns a frame) and its roots gathered first (17 ns a frame), and frames
past it were copied into the nursery and again out of it.

- **Stage 1**: the stack flushed at every collection (`flush_all`), the
  innermost restored after; the collector reads no stack.
- **Stage 2**: the stack in the nursery's range (`Heap::native_stack`),
  flushed in place (`flush_in_place`, `Heap::vector_in_place`): one chunk
  where the frames are, moved out by the collection that follows. An
  overflow collects, Larceny's way; its site names the registers that hold
  values, and its code bloblet. The cache is the nursery's size.
- **Stage 3**, next: the underflow in line, without a call-out.

Measured in `DONE.md` §52 and `docs/performance.md`.

