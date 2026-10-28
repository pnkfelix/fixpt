"""FX-26's values in lldb, for the code `fixpt` compiles to the native
convention on x86_64 and arm64, as `fixpt_gdb.py` does for gdb
(docs/research/debugging.md):

    (lldb) command script import scripts/debuggers/fixpt_lldb.py
    (lldb) fx-print $rdi        the word, as FX-26 writes the value it is
    (lldb) fx-frame             the values the selected frame keeps
    (lldb) fx-regs              RESULT and REG1-REG3: rax, rdi, rsi, r8;
                                on arm64, x0 to x3

Importing it also turns on lldb's reading of the code `fixpt` registers
(`plugin.jit-loader.gdb.enable`, off by default on macOS), so import it
before `run`, or before attaching.

Each value is written by the program itself (`fixpt_debug_show`); a word
that is no value the heap holds is said so. A frame's values are those its
stack map says are live (`[rbp + 16]`, on arm64 `[x29 + 16]`), its slots
from 24 bytes above the frame's base; a leaf procedure has no frame of its
own."""

import lldb

MASK = (1 << 64) - 1
MAP_BITS = 48


def show(frame, word):
    """Word `word` as FX-26 writes the value it is."""
    v = frame.EvaluateExpression("(char *)((char *(*)(unsigned long)) fixpt_debug_show)(%dUL)" % (word & MASK))
    if not v.GetError().Success():
        return "(not shown: %s)" % v.GetError().GetCString()
    err = lldb.SBError()
    text = frame.GetThread().GetProcess().ReadCStringFromMemory(v.GetValueAsUnsigned(), 8192, err)
    return text if err.Success() else "(not shown: %s)" % err.GetCString()


def read_u64(frame, addr):
    err = lldb.SBError()
    return frame.GetThread().GetProcess().ReadUnsignedFromMemory(addr, 8, err)


def register(frame, name):
    return frame.FindRegister(name).GetValueAsUnsigned() & MASK


def arm64(frame):
    """Whether the program is arm64's."""
    triple = frame.GetThread().GetProcess().GetTarget().GetTriple() or ""
    return triple.startswith(("arm64", "aarch64"))


def frame_values(frame):
    """The frame's live values, as (what, word), or why none."""
    base = "fp" if arm64(frame) else "rbp"
    rbp = register(frame, base)
    thread = frame.GetThread()
    older = thread.GetFrameAtIndex(frame.GetFrameID() + 1)
    # A procedure with a frame of its own sets its base (rbp, x29) to it,
    # its caller's kept in it; a leaf leaves its caller's.
    if not older.IsValid() or register(older, base) == rbp:
        return "no frame of its own here: a leaf procedure, or not native code"
    # The map, a fixnum: the live bits and above them the count of fields;
    # or, for a frame too wide for one, minus its count of fields.
    m = read_u64(frame, rbp + 16)
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
            out.append((what, read_u64(frame, rbp + 24 + 8 * k)))
    return out


def fx_print(debugger, command, result, internal_dict):
    """fx-print EXPR: the word EXPR is, as FX-26 writes the value."""
    frame = debugger.GetSelectedTarget().GetProcess().GetSelectedThread().GetSelectedFrame()
    v = frame.EvaluateExpression(command)
    result.AppendMessage(show(frame, v.GetValueAsUnsigned()))


def fx_frame(debugger, command, result, internal_dict):
    """fx-frame: the values the selected native frame keeps, by its stack map."""
    frame = debugger.GetSelectedTarget().GetProcess().GetSelectedThread().GetSelectedFrame()
    got = frame_values(frame)
    if isinstance(got, str):
        result.AppendMessage(got)
        return
    for what, word in got:
        result.AppendMessage("  %s: %s" % (what, show(frame, word)))


def fx_regs(debugger, command, result, internal_dict):
    """fx-regs: RESULT and REG1-REG3 (rax, rdi, rsi, r8; x0 to x3), as values."""
    frame = debugger.GetSelectedTarget().GetProcess().GetSelectedThread().GetSelectedFrame()
    regs = ("x0", "x1", "x2", "x3") if arm64(frame) else ("rax", "rdi", "rsi", "r8")
    for name, reg in zip(("RESULT", "REG1", "REG2", "REG3"), regs):
        result.AppendMessage("  %s (%s): %s" % (name, reg, show(frame, register(frame, reg))))


def __lldb_init_module(debugger, internal_dict):
    debugger.HandleCommand("settings set plugin.jit-loader.gdb.enable on")
    for name, fn in (("fx-print", "fx_print"), ("fx-frame", "fx_frame"), ("fx-regs", "fx_regs")):
        debugger.HandleCommand("command script add -f %s.%s %s" % (__name__, fn, name))
