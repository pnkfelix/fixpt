//! The image format's sections (`TODO.md` §165): a table of them, each of a
//! space of the heap and where it goes, page-aligned in an image made to be
//! mapped, packed in one made to be read; read back the same either way.

use fixpt_heap::{Heap, Value, image, layout};

/// A heap holding a list, a string, a symbol, and a code bloblet that
/// refers to them.
fn a_heap() -> Heap {
    let mut h = Heap::new();
    let text = h.make_string("text");
    let sym = h.intern("a-symbol");
    let code = h.make_code_bloblet(layout::kind("bloblet"), 2, 24, false);
    h.set_bloblet_slot(code, 1, text);
    h.set_bloblet_slot(code, 2, sym);
    let l = h.cons(code, Value::NULL);
    let l = h.cons(Value::fixnum(7), l);
    h.push_root(l);
    h
}

#[test]
fn a_mappable_image_has_its_spaces_on_pages_and_a_packed_one_not() {
    let h = a_heap();
    let (mapped, packed) = (image::dump_mappable(&h), image::dump_packed(&h));
    for (bytes, on_pages) in [(&mapped, true), (&packed, false)] {
        let table = image::sections(bytes).unwrap();
        assert_eq!(table.iter().filter(|t| t.kind == image::META).count(), 1);
        let spaces: Vec<u32> = table.iter().filter(|t| t.kind == image::WORDS).map(|t| t.space).collect();
        assert_eq!(spaces, [image::OLD, image::STATIC_MUTABLE, image::CODE_STUBBED, image::CODE_NATIVE]);
        for t in table.iter().filter(|t| t.kind == image::WORDS) {
            assert!(t.bytes / 8 <= t.extent, "{t:?}");
            assert_eq!(t.offset.is_multiple_of(image::PAGE), on_pages, "{t:?}");
        }
        let old = table.iter().find(|t| t.space == image::OLD).unwrap();
        assert_eq!(old.what, image::MOVES | image::WRITTEN);
        let code = table.iter().find(|t| t.space == image::CODE_NATIVE).unwrap();
        assert_eq!(code.what & image::MOVES, 0, "code never moves");
    }
    assert!(packed.len() < mapped.len(), "packed has no padding");
    // Read back the same either way.
    for bytes in [&mapped, &packed] {
        let back = image::load(bytes).unwrap();
        let l = back.root_at(0);
        assert_eq!(back.car(l), Value::fixnum(7));
        let code = back.car(back.cdr(l));
        assert!(back.is_code_bloblet(code));
        assert_eq!(back.string_to_rust(back.bloblet_slot(code, 1)), "text");
        assert_eq!(back.symbol_name(back.bloblet_slot(code, 2)), "a-symbol");
    }
}

#[test]
fn a_section_of_a_space_this_heap_has_not_is_refused() {
    let mut bytes = image::dump_packed(&a_heap());
    // The old space's section made one of a space no heap here has: its
    // entry's space field, the second u32 of the second entry.
    let at = 32 + 48 + 4;
    bytes[at..at + 4].copy_from_slice(&99u32.to_le_bytes());
    let body = bytes.len() - 4;
    let crc = image::crc32(&bytes[..body]);
    bytes[body..].copy_from_slice(&crc.to_le_bytes());
    let err = image::load(&bytes).err().expect("refused").to_string();
    assert!(err.contains("space 99"), "{err}");
}
