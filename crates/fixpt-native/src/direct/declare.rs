//! The native convention, declared (`TODO.md` §97, `docs/research/
//! declared-conventions.md`): what code in it must keep, as clauses, each a
//! role and where it is, made from this machine's own constants, so that the
//! declaration cannot drift from the code. `fixpt-runtime`'s
//! `native-arm64.conv` and `native-x86_64.conv` are these, one clause to a
//! line, as each checker compares a program's `define-convention` with the
//! one of the machine it runs on; a test says they agree (`FIXPT_BLESS=1`
//! rewrites the files).
//!
//! x86_64's has arm64's clauses, the same roles in the same order, its
//! values, closures, state offsets and barrier word for word. What differs
//! is where things are: its registers by name (`rax` …), and, where arm64
//! has a register and x86_64 none to spare, a place in the state, `(state
//! field)`: REG4…REG8, the fuel, the stack's limit and the code distance
//! (`x64.rs`). The return address is `pushed` by `call`, on the stack's
//! top as a routine is entered, where arm64 has it in `x30`.

use super::*;
use fixpt_heap::layout::{self, HEADER_FIELDS, KINDS, TAGS};

/// A clause's parts: a symbol, an integer, or a list.
#[derive(Clone)]
enum D {
    S(String),
    I(i64),
    L(Vec<D>),
}

fn s(x: &str) -> D {
    D::S(x.to_string())
}

fn i(x: impl TryInto<i64>) -> D {
    D::I(x.try_into().unwrap_or_else(|_| panic!("in range")))
}

fn l(xs: Vec<D>) -> D {
    D::L(xs)
}

/// `(head parts…)`.
fn c(head: &str, mut parts: Vec<D>) -> D {
    parts.insert(0, s(head));
    D::L(parts)
}

fn x(r: Reg) -> D {
    D::S(format!("x{r}"))
}

/// An x86_64 register, by name.
fn r(r: crate::x86_64::Reg) -> D {
    s(crate::x86_64::NAMES[r as usize])
}

/// A word of the state, by its field's name, where x86_64 has no register.
fn in_state(field: &str) -> D {
    c("state", vec![s(field)])
}

/// x86_64's REG1…REG8: three registers, then words of the state.
fn x86_regs(n: usize) -> Vec<D> {
    (1..=n).map(|k| x64::IN_REGS.get(k).map_or_else(|| in_state(&format!("reg{k}")), |&g| r(g))).collect()
}

/// The canonical text, as both checkers print a clause: atoms apart by one
/// space, integers in decimal.
fn text(d: &D) -> String {
    match d {
        D::S(x) => x.clone(),
        D::I(n) => n.to_string(),
        D::L(xs) => format!("({})", xs.iter().map(text).collect::<Vec<_>>().join(" ")),
    }
}

macro_rules! state {
    ($($f:ident),* $(,)?) => {
        vec![$(c(&stringify!($f).replace('_', "-"), vec![i(offset_of!(DState, $f))])),*]
    };
}

/// The clauses both machines share: the values, the closures.
fn values() -> D {
    let tags = TAGS.iter().map(|t| c(t.name, vec![i(t.bits)])).collect();
    let header = HEADER_FIELDS.iter().map(|f| c(f.name, vec![i(f.lo), i(f.width)])).collect();
    let immediates = [
        ("false", Value::FALSE),
        ("true", Value::TRUE),
        ("null", Value::NULL),
        ("unit", Value::UNIT),
        ("eof", Value::EOF),
        ("unspecified", Value::UNSPECIFIED),
        ("default", Value::DEFAULT),
        ("unbound", Value::UNBOUND),
    ]
    .into_iter()
    .map(|(n, v)| c(n, vec![i(v.raw())]))
    .collect();
    let kinds = KINDS.iter().map(|k| c(k.name, vec![i(k.code)])).collect();
    c(
        "values",
        vec![
            c("tags", tags),
            c("fixnum", vec![c("shift", vec![i(3)]), c("bits", vec![i(61)])]),
            c("immediates", immediates),
            c("character", vec![c("subtag", vec![i(8)]), c("payload-shift", vec![i(8)])]),
            c("pair", vec![c("car", vec![i(-1)]), c("cdr", vec![i(7)])]),
            // A bloblet's reference is its suffix's address plus its tag;
            // field `k` (1 the trailer, if any) is `8k` bytes before.
            c("bloblet", vec![c("reference", vec![s("suffix"), i(layout::tag("bloblet"))]), c("field-k-before-suffix", vec![i(8)])]),
            c("header", header),
            c("kinds", kinds),
        ],
    )
}

fn closures() -> D {
    c(
        "closures",
        vec![
            c("kind", vec![i(layout::kind("native-closure"))]),
            c("code-field", vec![i(CLOSURE_WORD)]),
            c("first-free-field", vec![i(CLOSURE_FREE0)]),
            // Whatever the callee, its code runs: native code, or a stub
            // that enters `foreign` (`docs/research/code-stubs.md`).
            c("code-always-runs", vec![]),
        ],
    )
}

/// The `closures` clause before every procedure's code ran
/// (`docs/research/code-stubs.md`): native code when its code is at or past
/// the state's `code-lo`, else called by `foreign`. Code written to it still
/// runs, since a word's code is below `code-lo` and anything else's
/// stub enters `foreign` too: so both checkers accept it still
/// (`fixpt_runtime::NATIVE_CONVENTION_OLDER`; a test says it is this).
pub fn closures_before_stubs() -> String {
    text(&c(
        "closures",
        vec![
            c("kind", vec![i(layout::kind("native-closure"))]),
            c("code-field", vec![i(CLOSURE_WORD)]),
            c("first-free-field", vec![i(CLOSURE_FREE0)]),
            c("native-when-code-at-least", vec![s("code-lo")]),
        ],
    ))
}

/// The state's fields code reads or writes, by offset: the same for both
/// machines, x86_64's REG4…REG8 after them.
fn state(x86: bool) -> D {
    let mut fields = state!(
        fuel, reserve, trap, pc, args, nargs, aux, callout, rust_sp, native_sp, fp, top, words, alloc_limit, code, clo, delta,
        code_lo, trap_stub, foreign, closure, cards, stack_limit, overflow, poll, cons, bloblet,
    );
    if x86 {
        fields.extend((x64::IN_REGS.len()..=8).map(|k| c(&format!("reg{k}"), vec![i(offset_of!(DState, regs) + 8 * k)])));
    }
    c("state", fields)
}

/// A frame's map, from the frame's register `fp`.
fn map(fp: D) -> D {
    // A fixnum: bit `k` below 48 says value slot `k` is live; above, the
    // frame's fields, its link, return and map and its value slots;
    // negative, minus those, every value live.
    c(
        "map",
        vec![
            fp,
            i(R_HEAD as i64 - 8),
            c("live-slots-below", vec![i(MAP_BITS)]),
            c("fields-above", vec![i(MAP_BITS), s("link"), s("return"), s("map"), s("values")]),
            c("all-live", vec![s("negative")]),
        ],
    )
}

/// The routines that take what they take in registers alike: `poll`,
/// `cons` and `bloblet`, the first two arguments' registers given.
fn routines_alike(result: D, a1: D, a2: D) -> Vec<D> {
    vec![
        c("poll", vec![c("entry", vec![s("state"), s("poll")]), c("in", vec![]), c("may-collect", vec![]), c("traps-when-spent", vec![i(OUT_OF_FUEL)])]),
        c(
            "cons",
            vec![
                c("entry", vec![s("state"), s("cons")]),
                c("in", vec![c("car", vec![a1.clone()]), c("cdr", vec![a2.clone()])]),
                c("out", vec![result.clone()]),
                c("may-collect", vec![]),
            ],
        ),
        // A plain bloblet: its trailer field 1, the rest the fixnum 0, its
        // suffix zero; sizes `%make-bloblet-filled` refuses, the trap.
        c(
            "bloblet",
            vec![
                c("entry", vec![s("state"), s("bloblet")]),
                c("in", vec![c("bytes", vec![a1.clone()]), c("fields", vec![a2.clone()])]),
                c("out", vec![result]),
                c("may-collect", vec![]),
                c("makes", vec![c("kind", vec![s("bloblet")]), c("trailer", vec![i(1)]), s("zeroed")]),
                c("traps-when-refused", vec![i(PRIM_FAILED)]),
            ],
        ),
    ]
}

/// The trap's kinds, by number.
fn trap_kinds() -> D {
    c("kinds", TRAPS.iter().enumerate().skip(1).map(|(k, m)| l(vec![i(k), s(&m.replace(' ', "-"))])).collect())
}

fn barrier() -> D {
    c("barrier", vec![c("cards", vec![s("state"), s("cards")]), c("card-shift", vec![i(crate::arm64::CARD_SHIFT)]), c("mark", vec![i(1)])])
}

/// The clauses of fixpt's `native` convention on arm64, in the order
/// written.
fn clauses_arm64() -> Vec<D> {
    let mut routines = vec![
        c(
            "foreign",
            vec![
                c("entry", vec![s("state"), s("foreign")]),
                c("in", vec![c("closure", vec![x(CLO)]), c("count", vec![x(X9)]), c("arguments", (1..=8).map(x).collect())]),
                c("out", vec![x(RESULT)]),
                c("may-collect", vec![]),
            ],
        ),
        // Past the stack's limit, right after the frame is made: the rest
        // flushed, this frame moved; the arguments it holds in X1… (as
        // `info` says) kept, its code bloblet in X16.
        c(
            "overflow",
            vec![
                c("when", vec![s("sp"), s("below"), x(LIMIT), s("after-frame-made")]),
                c("entry", vec![s("state"), s("overflow"), s("by"), x(LINK)]),
                c("in", vec![c("code", vec![x(X16)]), c("info", vec![x(X17), c("arguments-held", vec![i(0), i(8)]), c("closure-read", vec![i(8)]), c("variadic", vec![i(9)])])]),
                c("keeps", (0..=10).map(x).collect()),
            ],
        ),
    ];
    routines.extend(routines_alike(x(RESULT), x(1), x(2)));
    routines.push(c("trap", vec![c("entry", vec![s("state"), s("trap-stub")]), c("in", vec![c("kind", vec![x(X9)])]), trap_kinds()]));
    vec![
        c("target", vec![s("arm64")]),
        c(
            "registers",
            vec![
                c("arguments", (1..=8).map(x).collect()),
                // Past eight, the eighth a list of the rest.
                c("rest-in", vec![x(8)]),
                c("count", vec![x(X9)]),
                c("result", vec![x(RESULT)]),
                c("closure", vec![x(CLO)]),
                c("link", vec![x(LINK)]),
                c("frame", vec![x(FRAME)]),
                c("pinned", vec![c("state", vec![x(ST)]), c("fuel", vec![x(FUEL)]), c("stack-limit", vec![x(LIMIT)]), c("code-distance", vec![x(DELTA)])]),
                c("lost-across-calls", vec![s("all-but-pinned")]),
            ],
        ),
        values(),
        closures(),
        c("code", vec![c("runs-at", vec![s("reference"), s("plus"), x(DELTA)]), c("field-k-before-code", vec![i(8)])]),
        c(
            "frames",
            vec![
                c("align", vec![i(16)]),
                c("header", vec![x(FRAME), i(-8)]),
                c("link", vec![x(FRAME), i(R_LINK as i64 - 8)]),
                c("return", vec![x(FRAME), i(R_SECOND as i64 - 8)]),
                map(x(FRAME)),
                c("values-from", vec![x(FRAME), i(R_HEAD as i64)]),
                c("raw-after-values", vec![]),
                // Its code bloblet among its values, so that the code it
                // runs is alive; stored before anything that may collect.
                c("keeps-its-code", vec![]),
                c("map-stored-before", vec![s("calls"), s("routines-that-collect")]),
                c("made", vec![s("sub"), s("sp"), s("stp"), x(FRAME), x(LINK), s("add"), x(FRAME), s("sp"), i(8)]),
                c("stub", vec![i(STUB_FRAME)]),
            ],
        ),
        state(false),
        c("routines", routines),
        // One less on entry to a procedure that makes a frame, after it
        // keeps what it holds there, and on a loop's back edge; below zero,
        // `poll`.
        c("fuel", vec![c("register", vec![x(FUEL)]), c("subtract", vec![i(1)]), c("on", vec![s("entry"), s("back-edge")]), c("borrow", vec![s("poll")])]),
        barrier(),
    ]
}

/// The clauses of fixpt's `native` convention on x86_64 (`x64.rs`), in
/// the order written: arm64's roles, its places x86_64's.
fn clauses_x86_64() -> Vec<D> {
    use x64::{CLO, FRAME, RESULT, SP, ST, X16, X17, X9};
    let mut routines = vec![
        c(
            "foreign",
            vec![
                c("entry", vec![s("state"), s("foreign")]),
                c("in", vec![c("closure", vec![r(CLO)]), c("count", vec![r(X9)]), c("arguments", x86_regs(8))]),
                c("out", vec![r(RESULT)]),
                c("may-collect", vec![]),
            ],
        ),
        // Called from the procedure's entry once its frame is made, the
        // return address pushed by the `call`; the routine pops it, and
        // pushes it again to return.
        c(
            "overflow",
            vec![
                c("when", vec![r(SP), s("below"), in_state("stack-limit"), s("after-frame-made")]),
                c("entry", vec![s("state"), s("overflow"), s("by"), s("call")]),
                c("in", vec![c("code", vec![r(X16)]), c("info", vec![r(X17), c("arguments-held", vec![i(0), i(8)]), c("closure-read", vec![i(8)]), c("variadic", vec![i(9)])])]),
                c("keeps", [vec![r(RESULT)], x86_regs(8), vec![r(X9), r(CLO)]].concat()),
            ],
        ),
    ];
    routines.extend(routines_alike(r(RESULT), x86_regs(1).remove(0), x86_regs(2).remove(1)));
    routines.push(c("trap", vec![c("entry", vec![s("state"), s("trap-stub")]), c("in", vec![c("kind", vec![r(X9)])]), trap_kinds()]));
    vec![
        c("target", vec![s("x86_64")]),
        c(
            "registers",
            vec![
                c("arguments", x86_regs(8)),
                c("rest-in", vec![x86_regs(8).remove(7)]),
                c("count", vec![r(X9)]),
                c("result", vec![r(RESULT)]),
                c("closure", vec![r(CLO)]),
                // The return address: on the stack's top, as `call` leaves it.
                c("link", vec![s("pushed")]),
                c("frame", vec![r(FRAME)]),
                c(
                    "pinned",
                    vec![
                        c("state", vec![r(ST)]),
                        c("fuel", vec![in_state("fuel")]),
                        c("stack-limit", vec![in_state("stack-limit")]),
                        c("code-distance", vec![in_state("delta")]),
                    ],
                ),
                c("lost-across-calls", vec![s("all-but-pinned")]),
            ],
        ),
        values(),
        closures(),
        c("code", vec![c("runs-at", vec![s("reference"), s("plus"), in_state("delta")]), c("field-k-before-code", vec![i(8)])]),
        c(
            "frames",
            vec![
                c("align", vec![i(16)]),
                c("header", vec![r(FRAME), i(-8)]),
                c("link", vec![r(FRAME), i(R_LINK as i64 - 8)]),
                c("return", vec![r(FRAME), i(R_SECOND as i64 - 8)]),
                map(r(FRAME)),
                c("values-from", vec![r(FRAME), i(R_HEAD as i64)]),
                c("raw-after-values", vec![]),
                c("keeps-its-code", vec![]),
                c("map-stored-before", vec![s("calls"), s("routines-that-collect")]),
                // The return address popped, the frame below where it was,
                // its link and return stored, the frame's register at its
                // link (`push_frame_ret`); undone in reverse, the return
                // pushed again for `ret`.
                c(
                    "made",
                    vec![
                        s("pop"),
                        s("return"),
                        s("sub"),
                        r(SP),
                        s("store"),
                        r(FRAME),
                        r(SP),
                        i(R_LINK),
                        s("store"),
                        s("return"),
                        r(SP),
                        i(R_SECOND),
                        s("lea"),
                        r(FRAME),
                        r(SP),
                        i(8),
                    ],
                ),
                c("stub", vec![i(STUB_FRAME)]),
            ],
        ),
        state(true),
        c("routines", routines),
        c("fuel", vec![in_state("fuel"), c("subtract", vec![i(1)]), c("on", vec![s("entry"), s("back-edge")]), c("borrow", vec![s("poll")])]),
        barrier(),
    ]
}

/// The declaration's clauses for `target` (`arm64` or `x86_64`), one to a
/// line, canonical.
pub fn native_convention_of(target: &str) -> String {
    let clauses = match target {
        "x86_64" => clauses_x86_64(),
        _ => clauses_arm64(),
    };
    clauses.iter().map(|d| text(d) + "\n").collect()
}

/// The declaration of the machine this is: x86_64's there, else arm64's.
pub fn native_convention() -> String {
    native_convention_of(if cfg!(target_arch = "x86_64") { "x86_64" } else { "arm64" })
}
