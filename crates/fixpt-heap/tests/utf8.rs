//! UTF-8 text (`Heap::make_utf8`, `TODO.md` §306): its lengths, read by
//! byte offset, a character where one starts and nowhere else, a piece
//! between boundaries, kept by a collection.

use fixpt_heap::Heap;

const TEXTS: [&str; 7] = ["", "a", "abc", "é", "aé\u{1F600}z", "λx.x", "\u{10FFFF}\u{80}\u{7FF}\u{800}"];

#[test]
fn a_utf8_reads_each_character_where_it_starts() {
    let mut h = Heap::new();
    for t in TEXTS {
        let u = h.make_utf8(t);
        assert!(h.is_utf8(u));
        assert_eq!((h.utf8_chars(u), h.utf8_len(u)), (t.chars().count(), t.len()), "{t:?}");
        assert_eq!(h.utf8_string(u), t);
        // Marked all ASCII where it is made, if it is (`TODO.md` §310).
        assert_eq!(h.utf8_is_ascii(u), t.is_ascii(), "{t:?}");
        // Each character at its offset, the next offset after it; nothing
        // inside one, nor past the end.
        for k in 0..=t.len() + 1 {
            let want = t.get(k..).and_then(|rest| rest.chars().next()).map(|c| (c, k + c.len_utf8()));
            assert_eq!(h.utf8_char_at(u, k), want, "{t:?} at {k}");
            assert_eq!(h.utf8_boundary(u, k), t.is_char_boundary(k) && k <= t.len(), "{t:?} at {k}");
        }
    }
}

#[test]
fn a_utf8_piece_is_between_boundaries() {
    let mut h = Heap::new();
    let t = "aé\u{1F600}z";
    let u = h.make_utf8(t);
    for a in 0..=t.len() {
        for b in 0..=t.len() {
            let want = (a <= b && t.is_char_boundary(a) && t.is_char_boundary(b)).then(|| &t[a..b]);
            let got = h.utf8_substring(u, a, b).map(|p| h.utf8_string(p));
            assert_eq!(got.as_deref(), want, "{a}..{b}");
        }
    }
    let (x, y) = (h.make_utf8("aé"), h.make_utf8("aé"));
    let z = h.make_utf8("ae");
    assert!(h.utf8_eq(x, y) && !h.utf8_eq(x, z));
}

#[test]
fn a_utf8_survives_a_collection() {
    let mut h = Heap::new();
    let mut roots: Vec<_> = TEXTS.iter().map(|t| h.make_utf8(t)).collect();
    let slice: &mut [_] = &mut roots;
    h.collect(&mut [slice]);
    h.verify().expect("sound after collection");
    for (u, t) in roots.iter().zip(TEXTS) {
        assert_eq!((h.utf8_string(*u), h.utf8_chars(*u)), (t.to_string(), t.chars().count()));
    }
}
