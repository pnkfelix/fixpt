//! The reader written in FX-26 feeding the checker (`PLAN.md` §11, step 8):
//! what it reads, spans and all, is what the Rust reader reads, and a
//! program read by it checks and runs.

use fixpt_engine::Backend;
use fixpt_fx26::session::Fx26Session;
use fixpt_read::{FileId, Reader, SyntaxProfile};

mod common;

/// Both readers on `text`, into the same heap and interner, so the syntax
/// compares whole: data, and every span. As read, not expanded: an
/// expansion's renamed binders are new symbols each time.
fn same_syntax(s: &mut Fx26Session, text: &str) {
    use fixpt_fx26::heap_syn::{Syn, V};
    fn same(a: Syn, b: Syn) {
        assert_eq!(a.span(), b.span(), "the readers place `{:?}` apart", a.view());
        match (a.view(), b.view()) {
            (V::List { items, tail }, V::List { items: bs, tail: bt }) => {
                assert_eq!(items.len(), bs.len(), "a list's length at {:?}", a.span());
                items.into_iter().zip(bs).for_each(|(a, b)| same(a, b));
                match (tail, bt) {
                    (Some(a), Some(b)) => same(a, b),
                    (None, None) => {}
                    _ => panic!("a tail at {:?}", a.span()),
                }
            }
            (V::Vector(items), V::Vector(bs)) => {
                assert_eq!(items.len(), bs.len());
                items.into_iter().zip(bs).for_each(|(a, b)| same(a, b));
            }
            (x, y) => assert_eq!(x, y, "the readers disagree at {:?}", a.span()),
        }
    }
    s.load_own_reader().expect("loads");
    let ours = fixpt_fx26::syn::read_with_fx26_reader(s.scheme.lowered(), &mut s.checker, FileId(0), text)
        .unwrap_or_else(|e| panic!("the FX-26 reader: {e}"));
    s.checking(|c| {
        let rust = fixpt_fx26::heap_syn::read_syn(text, FileId(0), &mut c.interner).expect("reads");
        assert_eq!(ours.len(), rust.len(), "different numbers of forms");
        for (a, b) in ours.iter().zip(rust) {
            same(a.get(), b);
        }
    });
}

#[test]
fn the_readers_agree_spans_and_all() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    for text in [
        "(f #u #u8(1 2) #t #f Foo \"str\\n\" #\\a #\\space 'q) #| c |# #;(gone) (g . h) #(1 (2))",
        "(λ \"ünïcode\" x) ; a comment\n(after)",
        include_str!("programs/bloblet/expr.fx"),
        include_str!("programs/bidirectional/twice.fx"),
        fixpt_fx26::TABLE,
    ] {
        same_syntax(&mut s, text);
    }
}

#[test]
fn a_program_read_by_fx26_checks_and_runs() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let v = s.run_program_read_by_fx26(include_str!("programs/bloblet/expr.fx")).expect("checks");
    assert_eq!(v, Ok("42".to_string()));
}

#[test]
fn a_reading_error_says_where() {
    let mut s = Fx26Session::with_backend(Backend::Bytecode).expect("starts");
    let err = s.read_with_own_reader("(a b))").expect_err("unbalanced");
    assert!(err.message.contains("unbalanced"), "{}", err.message);
    assert_eq!(err.span.start, 5);
    let err = s.read_with_own_reader("(a (b").expect_err("unfinished");
    assert!(err.message.contains("middle of a form"), "{}", err.message);
}

/// Both front ends' `syn` (`docs/research/heap-syntax.md`): what the Rust
/// reader builds in the heap as it reads (`heap_syn::HeapSyn`) is what the
/// reader written in FX-26 makes of the same text, field for field: each
/// piece's variant, its plain datum, its place, its expansion. For every
/// program the tests read, and every file of the front end: places in
/// characters, both (a text not all ASCII among them).
#[test]
fn the_rust_reader_builds_the_syn_fx26_reads() {
    let mut s = common::front_end_session();
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let mut texts: Vec<(String, String)> = Vec::new();
    let mut todo = vec![dir];
    while let Some(d) = todo.pop() {
        for e in std::fs::read_dir(&d).expect("a directory").flatten() {
            let p = e.path();
            if p.is_dir() {
                todo.push(p);
            } else if p.extension().is_some_and(|x| x == "fx") {
                texts.push((p.display().to_string(), std::fs::read_to_string(&p).expect("readable")));
            }
        }
    }
    texts.extend(fixpt_fx26::FRONT_END_MODULES.iter().chain(&fixpt_fx26::FRONT_END_FILES).map(|(n, t)| (n.to_string(), t.to_string())));
    texts.sort();
    let mut compared = 0;
    for (name, text) in &texts {
        // What FX-26 reads, if it reads it: a text it refuses is the Rust
        // reader's to refuse too, which `same_syntax` holds them to.
        let mark = s.scheme.root_mark();
        let Ok(theirs) = fixpt_fx26::syn::read_to_syns(&mut s.scheme, FileId(0), text) else {
            s.scheme.release_to(mark);
            continue;
        };
        let ours = s.scheme.make(|m| {
            let mut interner = fixpt_read::Interner::new();
            let mut syms = fixpt_fx26::heap_syn::SymTable::default();
            let mut r = Reader::with_builder(text, FileId(0), SyntaxProfile::FX26, &mut interner, fixpt_fx26::heap_syn::HeapSyn::new(m.heap(), &mut syms, 0));
            let forms: Vec<fixpt_heap::Value> = r.read_all_built().expect("reads").into_iter().map(|n| n.0).collect();
            let heap = r.into_builder().heap;
            forms.iter().rev().fold(fixpt_heap::Value::NULL, |l, &f| heap.cons(f, l))
        });
        let mut why = String::new();
        s.scheme.make(|m| {
            let (a, b) = (m.get(ours), m.get(theirs));
            same_syn(m.heap(), a, b, "", &mut why);
            fixpt_heap::Value::NULL
        });
        s.scheme.release_to(mark);
        assert!(why.is_empty(), "{name}: {why}");
        compared += 1;
    }
    assert!(compared > 300, "only {compared} texts compared");
}

/// Whether `a`, Rust's, and `b`, FX-26's, are the same `syn` data; if not,
/// the first difference, at `path`, in `why`.
fn same_syn(h: &fixpt_heap::Heap, a: fixpt_heap::Value, b: fixpt_heap::Value, path: &str, why: &mut String) -> bool {
    let differ = |why: &mut String, what: String| {
        *why = format!("at {path}: {what}");
        false
    };
    if a.is_pair() && b.is_pair() {
        return same_syn(h, h.car(a), h.car(b), &format!("{path}.car"), why) && same_syn(h, h.cdr(a), h.cdr(b), &format!("{path}.cdr"), why);
    }
    if h.is_sum(a) && h.is_sum(b) {
        if h.sum_tag(a) != h.sum_tag(b) {
            return differ(why, format!("{} and {}", fixpt_runtime::write_value(h, h.sum_tag(a)), fixpt_runtime::write_value(h, h.sum_tag(b))));
        }
        let tag = fixpt_runtime::write_value(h, h.sum_tag(a));
        let (pa, pb) = (h.sum_payload(a), h.sum_payload(b));
        let n = h.bloblet_len(pa);
        if n != h.bloblet_len(pb) {
            return differ(why, format!("{n} fields and {}", h.bloblet_len(pb)));
        }
        return (1..=n).all(|i| same_syn(h, h.product_field(pa, i), h.product_field(pb, i), &format!("{path}/{tag}.{i}"), why));
    }
    if h.is_product(a) && h.is_product(b) {
        let (n, m) = (h.bloblet_len(a), h.bloblet_len(b));
        if n != m {
            return differ(why, format!("{n} fields and {m}"));
        }
        return (1..=n).all(|i| same_syn(h, h.product_field(a, i), h.product_field(b, i), &format!("{path}.{i}"), why));
    }
    if fixpt_runtime::equal::equal(h, a, b) {
        return true;
    }
    differ(why, format!("{} and {}", fixpt_runtime::write_value(h, a), fixpt_runtime::write_value(h, b)))
}

/// The heap's `syn`, looked at (`heap_syn::Rd`), is the Rust reader's
/// `Syntax`: each piece's datum and its span, back from its place, the
/// reader's bytes in characters (`fixpt_fx26::chars`). For every program
/// the tests read.
#[test]
fn the_heap_syn_reads_back_as_the_rust_syntax() {
    use fixpt_fx26::heap_syn::{HeapSyn, Rd, Syn, SymTable, V};
    use fixpt_read::{Datum, Syntax};
    fn same(rd: Rd, s: Syn, x: &Syntax, text: &str, name: &str) {
        assert_eq!(rd.span(s), fixpt_fx26::chars::of_bytes(text, x.span), "{name}: a span");
        match (rd.view(s), &x.datum) {
            (V::List { items, tail }, Datum::List { items: xs, tail: xt }) => {
                assert_eq!(items.len(), xs.len(), "{name}: a list's length at {:?}", x.span);
                items.iter().zip(xs).for_each(|(a, b)| same(rd, *a, b, text, name));
                match (tail, xt) {
                    (Some(a), Some(b)) => same(rd, a, b, text, name),
                    (None, None) => {}
                    _ => panic!("{name}: a tail at {:?}", x.span),
                }
            }
            (V::Vector(items), Datum::Vector(xs)) => {
                assert_eq!(items.len(), xs.len());
                items.iter().zip(xs).for_each(|(a, b)| same(rd, *a, b, text, name));
            }
            (V::Nil, Datum::Nil) => {}
            (V::Bool(a), Datum::Bool(b)) => assert_eq!(a, *b),
            (V::Char(a), Datum::Char(b)) => assert_eq!(a, *b),
            (V::Str(a), Datum::Str(b)) => assert_eq!(&a, b),
            (V::Symbol(a), Datum::Symbol(b)) | (V::Keyword(a), Datum::Keyword(b)) => assert_eq!(a, *b, "{name}"),
            (V::Bytevector(a), Datum::Bytevector(b)) => assert_eq!(&a, b),
            (V::Number(a), Datum::Number(b)) => assert_eq!(format!("{a:?}"), format!("{b:?}"), "{name}"),
            (a, b) => panic!("{name}: {a:?} and {b:?} at {:?}", x.span),
        }
    }
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/programs");
    let mut todo = vec![dir];
    let mut heap = fixpt_heap::Heap::new();
    let mut read = 0;
    while let Some(d) = todo.pop() {
        for e in std::fs::read_dir(&d).expect("a directory").flatten() {
            let p = e.path();
            if p.is_dir() {
                todo.push(p);
                continue;
            }
            if p.extension().is_none_or(|x| x != "fx") {
                continue;
            }
            let text = std::fs::read_to_string(&p).expect("readable");
            let name = p.display().to_string();
            let (mut interner, mut syms) = (fixpt_read::Interner::new(), SymTable::default());
            let mut r = Reader::with_builder(&text, FileId(0), SyntaxProfile::FX26, &mut interner, HeapSyn::new(&mut heap, &mut syms, 0));
            let Ok(forms) = r.read_all_built() else { continue };
            drop(r);
            // The same text read as the reader's own trees, to hold them to.
            let trees = Reader::new(&text, FileId(0), SyntaxProfile::FX26, &mut interner).read_all().expect("read once");
            let rd = Rd { heap: &heap, syms: &syms };
            assert_eq!(trees.len(), forms.len(), "{name}");
            for (x, s) in trees.iter().zip(&forms) {
                same(rd, *s, x, &text, &name);
            }
            read += 1;
        }
    }
    assert!(read > 300, "only {read} read");
}

/// A place past characters of more than one byte, as a message says it: the
/// span of what is wrong, in the text's characters, as the place is
/// (`heap_syn::span_of`, `fixpt_fx26::chars`).
#[test]
fn a_place_past_wide_characters_is_said_in_characters() {
    let text = ";; λ → ∀\n(define s string \"é\")\n(+ 1 s)\n";
    let e = match fixpt_fx26::session::compile_program_as(text, "fx:") {
        Err(e) => e,
        Ok(_) => panic!("`(+ 1 s)` adds a string"),
    };
    let (piece, start) = (fixpt_fx26::chars::slice(text, e.span), fixpt_fx26::chars::byte_at(text, e.span.start as usize));
    assert!(piece == "s" && text[..start].ends_with("(+ 1 "), "{piece:?}: {}", e.message);
}
