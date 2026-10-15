//! The native convention, declared (`TODO.md` §97, `docs/research/
//! declared-conventions.md`): what code in it must keep, as clauses, each a
//! role and where it is, made from this machine's own constants, so that the
//! declaration cannot drift from the code. `fixpt-runtime`'s
//! `native-arm64.conv` is this, one clause to a line, as each checker
//! compares a program's `define-convention` with it; a test says the two
//! agree (`FIXPT_BLESS=1` rewrites the file).

use super::*;
use fixpt_heap::layout::{self, HEADER_FIELDS, KINDS, TAGS};

/// A clause's parts: a symbol, an integer, or a list.
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

/// The clauses of fixpt's `native` convention, in the order written.
fn clauses() -> Vec<D> {
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
        ),
        c(
            "closures",
            vec![
                c("kind", vec![i(layout::kind("native-closure"))]),
                c("code-field", vec![i(CLOSURE_WORD)]),
                c("first-free-field", vec![i(CLOSURE_FREE0)]),
                // Native code when its code is at or past the code area's
                // start (the state's `code-lo`), else called by `foreign`.
                c("native-when-code-at-least", vec![s("code-lo")]),
            ],
        ),
        c("code", vec![c("runs-at", vec![s("reference"), s("plus"), x(DELTA)]), c("field-k-before-code", vec![i(8)])]),
        c(
            "frames",
            vec![
                c("align", vec![i(16)]),
                c("header", vec![x(FRAME), i(-8)]),
                c("link", vec![x(FRAME), i(R_LINK as i64 - 8)]),
                c("return", vec![x(FRAME), i(R_SECOND as i64 - 8)]),
                // A fixnum: bit `k` below 48 says value slot `k` is live;
                // above, the frame's fields, its link, return and map and
                // its value slots; negative, minus those, every value live.
                c(
                    "map",
                    vec![
                        x(FRAME),
                        i(R_HEAD as i64 - 8),
                        c("live-slots-below", vec![i(MAP_BITS)]),
                        c("fields-above", vec![i(MAP_BITS), s("link"), s("return"), s("map"), s("values")]),
                        c("all-live", vec![s("negative")]),
                    ],
                ),
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
        c(
            "state",
            state!(
                fuel, reserve, trap, pc, args, nargs, aux, callout, rust_sp, native_sp, fp, top, words, alloc_limit, code, clo,
                delta, code_lo, trap_stub, foreign, closure, cards, stack_limit, overflow, poll, cons,
                bloblet,
            ),
        ),
        c(
            "routines",
            vec![
                c(
                    "foreign",
                    vec![
                        c("entry", vec![s("state"), s("foreign")]),
                        c("in", vec![c("closure", vec![x(CLO)]), c("count", vec![x(X9)]), c("arguments", (1..=8).map(x).collect())]),
                        c("out", vec![x(RESULT)]),
                        c("may-collect", vec![]),
                    ],
                ),
                // Past the stack's limit, right after the frame is made: the
                // rest flushed, this frame moved; the arguments it holds in
                // X1… (as `info` says) kept, its code bloblet in X16.
                c(
                    "overflow",
                    vec![
                        c("when", vec![s("sp"), s("below"), x(LIMIT), s("after-frame-made")]),
                        c("entry", vec![s("state"), s("overflow"), s("by"), x(LINK)]),
                        c("in", vec![c("code", vec![x(X16)]), c("info", vec![x(X17), c("arguments-held", vec![i(0), i(8)]), c("closure-read", vec![i(8)]), c("variadic", vec![i(9)])])]),
                        c("keeps", (0..=10).map(x).collect()),
                    ],
                ),
                c(
                    "poll",
                    vec![
                        c("entry", vec![s("state"), s("poll")]),
                        c("in", vec![]),
                        c("may-collect", vec![]),
                        c("traps-when-spent", vec![i(OUT_OF_FUEL)]),
                    ],
                ),
                c(
                    "cons",
                    vec![
                        c("entry", vec![s("state"), s("cons")]),
                        c("in", vec![c("car", vec![x(1)]), c("cdr", vec![x(2)])]),
                        c("out", vec![x(RESULT)]),
                        c("may-collect", vec![]),
                    ],
                ),
                // A plain bloblet: its trailer field 1, the rest the fixnum
                // 0, its suffix zero; sizes `%make-bloblet-filled` refuses,
                // the trap.
                c(
                    "bloblet",
                    vec![
                        c("entry", vec![s("state"), s("bloblet")]),
                        c("in", vec![c("bytes", vec![x(1)]), c("fields", vec![x(2)])]),
                        c("out", vec![x(RESULT)]),
                        c("may-collect", vec![]),
                        c("makes", vec![c("kind", vec![s("bloblet")]), c("trailer", vec![i(1)]), s("zeroed")]),
                        c("traps-when-refused", vec![i(PRIM_FAILED)]),
                    ],
                ),
                c(
                    "trap",
                    vec![
                        c("entry", vec![s("state"), s("trap-stub")]),
                        c("in", vec![c("kind", vec![x(X9)])]),
                        c("kinds", TRAPS.iter().enumerate().skip(1).map(|(k, m)| l(vec![i(k), s(&m.replace(' ', "-"))])).collect()),
                    ],
                ),
            ],
        ),
        // One less on entry to a procedure that makes a frame, after it
        // keeps what it holds there, and on a loop's back edge; below zero,
        // `poll`.
        c("fuel", vec![c("register", vec![x(FUEL)]), c("subtract", vec![i(1)]), c("on", vec![s("entry"), s("back-edge")]), c("borrow", vec![s("poll")])]),
        c("barrier", vec![c("cards", vec![s("state"), s("cards")]), c("card-shift", vec![i(crate::arm64::CARD_SHIFT)]), c("mark", vec![i(1)])]),
    ]
}

/// The declaration's clauses, one to a line, canonical.
pub fn native_convention() -> String {
    clauses().iter().map(|d| text(d) + "\n").collect()
}
