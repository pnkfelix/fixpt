//! UTF-8 text (`Heap::make_utf8`, `TODO.md` §306): its lengths, read by
//! byte offset, a character where one starts and nowhere else, a piece
//! between boundaries, kept by a collection.

use fixpt_heap::{Heap, Value, image};

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

/// A slice (`TODO.md` §310): a view of a piece between two characters'
/// starts, read as the piece copied would be, nothing copied; a slice of
/// a slice one of the first's owner; its count known where it is made only
/// if that is free, else kept by the first walk.
#[test]
fn a_utf8_slice_reads_as_its_piece() {
    let mut h = Heap::new();
    for t in TEXTS {
        let u = h.make_utf8(t);
        for a in 0..=t.len() {
            for b in a..=t.len() {
                let (slice, copy) = (h.utf8_slice(u, a, b), h.utf8_substring(u, a, b));
                assert_eq!(slice.is_some(), t.get(a..b).is_some(), "{t:?} {a}..{b}");
                let (Some(s), Some(c)) = (slice, copy) else { continue };
                let piece = &t[a..b];
                assert!(h.is_utf8(s) && h.utf8_is_slice(s) && !h.utf8_is_slice(c));
                // Its count known where it is made only if that is free: of a
                // whole one, its owner all ASCII (a whole one keeps no other).
                let free = t.is_ascii();
                assert_eq!(h.utf8_known_chars(s), free.then(|| piece.chars().count()), "{t:?} {a}..{b}");
                assert_eq!(h.utf8_is_ascii(s), t.is_ascii() || free && piece.is_ascii(), "{t:?} {a}..{b}");
                assert_eq!((h.utf8_string(s), h.utf8_len(s), h.utf8_chars(s)), (piece.to_string(), piece.len(), piece.chars().count()));
                // Counted, kept: the next is no walk, and the piece known all
                // ASCII if it is, whatever its owner.
                assert_eq!(h.utf8_known_chars(s), Some(piece.chars().count()), "{t:?} {a}..{b}");
                assert_eq!(h.utf8_is_ascii(s), piece.is_ascii(), "{t:?} {a}..{b}");
                assert!(h.utf8_eq(s, c) && h.utf8_eq(c, s));
                for k in 0..=piece.len() {
                    let want = piece.get(k..).and_then(|rest| rest.chars().next()).map(|c| (c, k + c.len_utf8()));
                    assert_eq!(h.utf8_char_at(s, k), want, "{t:?} {a}..{b} at {k}");
                }
                // A slice of the slice: of the same owner, the offsets added.
                // Of the whole of the slice, its count, kept, known.
                if let Some(inner) = h.utf8_slice(s, 0, piece.len()) {
                    assert_eq!(h.utf8_string(inner), piece);
                    assert_eq!(h.utf8_known_chars(inner), Some(piece.chars().count()));
                }
            }
        }
    }
}

#[test]
fn a_utf8_slice_keeps_its_owner_through_a_collection() {
    let mut h = Heap::new();
    let mut roots: Vec<_> = TEXTS
        .iter()
        .map(|t| {
            let u = h.make_utf8(t);
            h.utf8_slice(u, 0, t.len()).expect("the whole of it")
        })
        .collect();
    // Half counted before, half after: a count kept is kept.
    for u in roots.iter().step_by(2) {
        h.utf8_chars(*u);
    }
    let slice: &mut [_] = &mut roots;
    h.collect(&mut [slice]);
    h.verify().expect("sound after collection");
    for (i, (u, t)) in roots.iter().zip(TEXTS).enumerate() {
        assert_eq!(h.utf8_string(*u), t.to_string());
        if i % 2 == 0 {
            assert_eq!(h.utf8_known_chars(*u), Some(t.chars().count()), "{t:?}: kept");
        }
        assert_eq!(h.utf8_chars(*u), t.chars().count());
    }
}

/// A slice in an image, its count not known, mapped from its file: its kind
/// settable, it is in the static area's mutable half, not the immutable one
/// mapped read-only, so the walk that counts it keeps the count there.
#[test]
fn a_utf8_slice_in_an_image_keeps_its_count() {
    let text = "a\u{e9}b\u{1F600}";
    let bytes = {
        let mut h = Heap::new();
        let u = h.make_utf8(text);
        let s = h.utf8_slice(u, 1, text.len()).expect("a boundary");
        assert_eq!(h.utf8_known_chars(s), None);
        let l = h.cons(s, Value::NULL);
        h.push_root(l);
        image::dump_static(&h)
    };
    let mut into = Heap::new();
    if into.base_word() != Heap::image_base_word() {
        return;
    }
    let path = std::env::temp_dir().join(format!("fixpt-utf8-slice-map-{}.img", std::process::id()));
    let mut file = vec![0xaa; image::PAGE];
    file.extend(&bytes);
    std::fs::write(&path, &file).unwrap();
    let m = fixpt_heap::Mapped::open(&path).unwrap();
    std::fs::remove_file(&path).unwrap();
    let img = image::parts(&m[image::PAGE..], true).unwrap();
    let roots = into.splice_image_from(&img, &[], Some(&m), true).expect("splices");
    drop(m);
    let s = into.car(roots[0]);
    assert!(into.is_static(s) && into.utf8_is_slice(s));
    assert_eq!(into.utf8_known_chars(s), None);
    assert_eq!(into.utf8_chars(s), 3);
    assert_eq!(into.utf8_known_chars(s), Some(3), "kept, where it is");
    into.verify().unwrap();
}

/// A `utf8` viewing a bytevector's bytes (`TODO.md` §310): validated,
/// nothing copied, read as the text; a piece of a slice of the bytes too;
/// bytes not UTF-8 refused at the offset they are valid up to.
#[test]
fn a_utf8_of_bytes_views_them() {
    let mut h = Heap::new();
    for t in TEXTS {
        let bv = h.make_bytevector(t.as_bytes());
        let u = h.utf8_of_bytes(bv).expect("valid");
        assert_eq!((h.utf8_string(u), h.utf8_chars(u), h.utf8_is_ascii(u)), (t.to_string(), t.chars().count(), t.is_ascii()));
        if let Some(c) = t.chars().next() {
            let n = c.len_utf8();
            let piece = h.bytes_slice(bv, n, t.len());
            let rest = h.utf8_of_bytes(piece).expect("valid from a boundary");
            assert_eq!(h.utf8_string(rest), &t[n..]);
            let inner = h.utf8_slice(rest, 0, t.len() - n).expect("the whole of it");
            assert_eq!(h.utf8_string(inner), &t[n..]);
        }
    }
    let bad = h.make_bytevector(&[b'a', 0xc3]);
    assert_eq!(h.utf8_of_bytes(bad), Err(1));
}
