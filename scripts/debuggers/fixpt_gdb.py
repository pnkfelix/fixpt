"""FX-26's values in gdb, for the code `fixpt` compiles to the native
convention (docs/research/debugging.md):

    (gdb) source scripts/debuggers/fixpt_gdb.py
    (gdb) fx-print $rdi        the word, as FX-26 writes the value it is
    (gdb) fx-frame             the values the selected frame keeps
    (gdb) fx-regs              RESULT and REG1-REG3: rax, rdi, rsi, r8

Each value is written by the program itself (`fixpt_debug_show`), so it is
written as the REPL would; a word that is no value the heap holds is said
so. A frame's values are those its stack map says are live (`[rbp + 16]`),
its slots from `[rbp + 24]`; a leaf procedure has no frame of its own.
Frames are told to gdb once it is here (`FIXPT_JIT_DEBUG=frames` from the
start): attached to a running program, let it go on (`continue`, then
interrupt) before asking of a frame."""

import struct

import gdb

MASK = (1 << 64) - 1
MAP_BITS = 48


def show(word):
    """Word `word` as FX-26 writes the value it is."""
    v = gdb.parse_and_eval("((char *(*)(unsigned long)) fixpt_debug_show)(%d)" % (word & MASK))
    return v.string()


def read_u64(addr):
    return struct.unpack("<Q", bytes(gdb.selected_inferior().read_memory(addr, 8)))[0]


def frame_values(frame):
    """The selected native frame's live values, as (what, word), or why none."""
    rbp = int(frame.read_register("rbp")) & MASK
    older = frame.older()
    # A procedure with a frame of its own sets rbp to it, its caller's kept
    # in it; a leaf leaves its caller's (as the frames gdb was told say).
    if older is None or int(older.read_register("rbp")) & MASK == rbp:
        return "no frame of its own here: a leaf procedure, or not native code"
    # The map, a fixnum: the live bits and above them the count of fields;
    # or, for a frame too wide for one, minus its count of fields, every
    # value slot live.
    m = read_u64(rbp + 16)
    m = (m - (1 << 64) if m >= 1 << 63 else m) >> 3
    if m < 0:
        fields = -m
        live = (1 << (fields - 3)) - 1
    else:
        live, fields = m & ((1 << MAP_BITS) - 1), m >> MAP_BITS
    values = fields - 5
    out = []
    for k in range(max(MAP_BITS, fields - 3)):
        if live >> k & 1:
            what = "its code" if k == values else "its closure" if k == values + 1 else "slot %d" % k
            out.append((what, read_u64(rbp + 24 + 8 * k)))
    return out


class FxPrint(gdb.Command):
    """fx-print EXPR: the word EXPR is, as FX-26 writes the value."""

    def __init__(self):
        super().__init__("fx-print", gdb.COMMAND_DATA, gdb.COMPLETE_EXPRESSION)

    def invoke(self, arg, from_tty):
        print(show(int(gdb.parse_and_eval(arg))))


class FxFrame(gdb.Command):
    """fx-frame: the values the selected native frame keeps, by its stack map."""

    def __init__(self):
        super().__init__("fx-frame", gdb.COMMAND_STACK)

    def invoke(self, arg, from_tty):
        got = frame_values(gdb.selected_frame())
        if isinstance(got, str):
            print(got)
            return
        for what, word in got:
            print("  %s: %s" % (what, show(word)))


class FxRegs(gdb.Command):
    """fx-regs: RESULT and REG1-REG3 (rax, rdi, rsi, r8), as values."""

    def __init__(self):
        super().__init__("fx-regs", gdb.COMMAND_DATA)

    def invoke(self, arg, from_tty):
        frame = gdb.selected_frame()
        for name, reg in (("RESULT", "rax"), ("REG1", "rdi"), ("REG2", "rsi"), ("REG3", "r8")):
            print("  %s (%s): %s" % (name, reg, show(int(frame.read_register(reg)))))


FxPrint()
FxFrame()
FxRegs()
