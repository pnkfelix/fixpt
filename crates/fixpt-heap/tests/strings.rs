//! Strings compared in the heap (`Heap::string_cmp`, `symbol_cmp`), two
//! code points to a word, as their Rust `String`s compare.

use fixpt_heap::{Heap, Value};

#[test]
fn strings_compare_in_place_as_rust_strings_do() {
    let texts = [
        "", "a", "b", "ab", "abc", "abd", "abcd", "abce", "ba", "zz", "z", "é", "éa", "aé",
        "\u{1F600}", "a\u{1F600}", "ab\u{1F600}", "lambda", "lambdas", "let", "let*", "letrec",
    ];
    let mut h = Heap::new();
    let vals: Vec<_> = texts.iter().map(|t| h.make_string(t)).collect();
    let syms: Vec<_> = texts.iter().map(|t| h.intern(t)).collect();
    for (i, a) in texts.iter().enumerate() {
        for (j, b) in texts.iter().enumerate() {
            assert_eq!(h.string_cmp(vals[i], vals[j]), a.cmp(b), "{a:?} against {b:?}");
            assert_eq!(h.symbol_cmp(syms[i], syms[j]), a.cmp(b), "symbols {a:?} against {b:?}");
        }
    }
}

/// Strings made from code points, odd and even lengths, read back whole.
#[test]
fn strings_made_word_at_a_time_read_back() {
    let mut h = Heap::new();
    for t in ["", "a", "ab", "abc", "é\u{1F600}x", "lambda", "(read (globals f g))"] {
        let v = h.make_string(t);
        assert_eq!(h.string_to_rust(v), t);
        assert_eq!(h.string_len(v), t.chars().count());
        let mut ps = Vec::new();
        h.string_points_into(v, &mut ps);
        let w = h.string_from_points(&ps);
        assert_eq!(h.string_to_rust(w), t);
    }
}

/// `string_append`, which copies a part's words, or shifts its points half
/// a word where it starts at an odd point, gives what gathering the points
/// and making one string gives: every way of putting three strings of up
/// to six points together, odd and even, some past one byte.
#[test]
fn appending_matches_points_gathered() {
    let mut heap = Heap::new();
    let text = |n: usize, k: u32| -> Vec<u32> { (0..n as u32).map(|i| if i % 3 == 0 { 0x3bb + i + k } else { 0x61 + i + k }).collect() };
    for a in 0..7 {
        for b in 0..7 {
            for c in 0..7 {
                let ps = [text(a, 0), text(b, 10), text(c, 20)];
                let parts: Vec<Value> = ps.iter().map(|p| heap.string_from_points(p)).collect();
                let all: Vec<u32> = ps.concat();
                let want = heap.string_from_points(&all);
                let got = heap.string_append(&parts);
                let (mut w, mut g) = (Vec::new(), Vec::new());
                heap.string_points_into(want, &mut w);
                heap.string_points_into(got, &mut g);
                assert_eq!(g, w, "lengths {a} {b} {c}");
                assert_eq!(heap.string_len(got), a + b + c);
                assert_eq!(heap.string_fnv(got), heap.string_fnv(want), "lengths {a} {b} {c}: a word's spare half");
            }
        }
    }
}
