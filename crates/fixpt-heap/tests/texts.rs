//! Texts (`Heap::text`, a heap's names, `fixpt_memmgmt::names`) in a heap's
//! image: an image carries the texts its words, roots and globals name, and
//! a load or a splice gives each the number it has among the names of the
//! heap it goes into, writing the words that hold one where that number is
//! another. An image numbers its texts from 0, in the order it holds them,
//! so a heap that holds no name yet numbers them so too, writing nothing;
//! one that holds others finds them elsewhere.

use fixpt_heap::{Heap, Value, image, layout};

const TEXTS: [&str; 3] = ["texts-image:alpha", "texts-image:λ beta", ""];

/// A heap holding `(t0 t1 code . t2)` as its root, `code` a code bloblet
/// whose field is `t0`, a text in the static area too where `statics`, and
/// `t1` in a global; dumped as `dump` does.
fn an_image(dump: fn(&Heap) -> Vec<u8>) -> Vec<u8> {
    let mut h = Heap::new();
    let [t0, t1, t2] = TEXTS.map(|t| h.text(t));
    let code = h.make_code_bloblet(layout::kind("bloblet"), 1, 8, false);
    h.set_bloblet_slot(code, 1, t0);
    let l = h.cons(code, t2);
    let l = h.cons(t1, l);
    let l = h.cons(t0, l);
    h.push_root(l);
    let g = h.intern("texts-image:global");
    let slot = h.symbol_global_slot(g);
    h.set_global(slot, t1);
    dump(&h)
}

/// What [`an_image`] put in, in `h` with its root `l`.
fn check(h: &Heap, l: Value) {
    let t0 = h.car(l);
    assert_eq!(h.text_of(t0), Some(TEXTS[0]));
    assert_eq!(t0, h.text(TEXTS[0]), "the name this heap has");
    assert_eq!(h.text_of(h.car(h.cdr(l))), Some(TEXTS[1]));
    let code = h.car(h.cdr(h.cdr(l)));
    assert!(h.is_code_bloblet(code));
    assert_eq!(h.bloblet_slot(code, 1), h.text(TEXTS[0]), "in the code area too");
    assert_eq!(h.cdr(h.cdr(h.cdr(l))), h.text(TEXTS[2]));
}

fn loaded_and_checked(bytes: &[u8]) {
    let mut h = image::load(bytes).unwrap();
    for _ in 0..2 {
        let l = h.root_at(0);
        check(&h, l);
        let g = h.intern_existing("texts-image:global").expect("its global's symbol");
        assert_eq!(h.global(h.symbol_global_slot(g)), h.text(TEXTS[1]), "a global's text");
        h.collect(&mut []);
        h.verify().unwrap();
    }
}

/// Spliced into a heap of its own (where it was made for, in place, its
/// texts' words alone written), and into one that holds something.
fn spliced_and_checked(bytes: &[u8]) {
    let img = image::parts(bytes, true).unwrap();
    let mut h = Heap::new();
    let roots = h.splice_image(&img, &[]).unwrap();
    h.verify().unwrap();
    let r = h.push_root(roots[0]);
    check(&h, h.root_at(r));
    h.collect(&mut []);
    check(&h, h.root_at(r));
    drop(h);
    let mut h = Heap::new();
    // Something here first, so that the image is not put where it was.
    let t = h.text("texts-image:mine");
    let mine = h.cons(t, Value::NULL);
    let r0 = h.push_root(mine);
    let roots = h.splice_image(&img, &[]).unwrap();
    h.verify().unwrap();
    let r1 = h.push_root(roots[0]);
    for _ in 0..2 {
        check(&h, h.root_at(r1));
        assert_eq!(h.text_of(h.car(h.root_at(r0))), Some("texts-image:mine"));
        h.collect(&mut []);
        h.verify().unwrap();
    }
}

#[test]
fn an_images_texts_come_back() {
    for dump in [image::dump_packed, image::dump_mappable, image::dump_static] {
        let bytes = an_image(dump);
        let img = image::parts(&bytes, true).unwrap();
        // Its three, and its global's symbol's name.
        assert_eq!(img.texts.texts.len(), 4, "each text once");
        assert!(img.texts.texts.iter().any(|&(_, t)| t == "texts-image:global"));
        loaded_and_checked(&bytes);
        spliced_and_checked(&bytes);
    }
}

#[test]
fn a_texts_section_that_is_not_utf8_is_refused() {
    let mut bytes = an_image(image::dump_packed);
    let t = image::sections(&bytes).unwrap().into_iter().find(|t| t.kind == image::TEXTS).unwrap();
    // The section ends with the texts' bytes: `λ`'s two among them.
    let section = &bytes[t.offset..t.offset + t.bytes];
    let at = t.offset + section.windows(TEXTS[1].len()).position(|w| w == TEXTS[1].as_bytes()).unwrap() + "texts-image:".len() + 1;
    assert_eq!(bytes[at], "λ".as_bytes()[1]);
    bytes[at] = 0xff;
    match image::load_trusted(&bytes) {
        Err(image::ImageError::Malformed(m)) => assert!(m.contains("not UTF-8"), "{m}"),
        other => panic!("taken: {:?}", other.err()),
    }
}

/// Into a heap that holds no name yet, an image's texts are numbered as it
/// numbers them: none of its words written. Into one that holds others,
/// they are numbered there, and found so.
#[test]
fn an_images_texts_are_numbered_in_the_heap_it_goes_into() {
    for dump in [image::dump_packed, image::dump_static] {
        let bytes = an_image(dump);
        let img = image::parts(&bytes, true).unwrap();
        assert!(img.texts.numbers(&Heap::new()).is_none(), "a heap of no names: each its number");
        let mut others = Heap::new();
        for i in 0..1000 {
            others.text(&format!("texts-other:{i}"));
        }
        assert!(img.texts.numbers(&others).is_some(), "numbered otherwise there");
        let roots = others.splice_image(&img, &[]).unwrap();
        let r = others.push_root(roots[0]);
        check(&others, others.root_at(r));
        others.collect(&mut []);
        others.verify().unwrap();
        check(&others, others.root_at(r));
    }
}
