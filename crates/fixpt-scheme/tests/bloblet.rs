//! Bloblets from Scheme: the `%bloblet` primitives, on both engines.

use fixpt_engine::Backend;
use fixpt_scheme::Session;

fn ev(src: &str) -> Vec<String> {
    [Backend::Ast, Backend::Bytecode]
        .into_iter()
        .map(|b| {
            let mut s = Session::with_backend(b);
            match s.eval_to_string("<test>", src) {
                Ok(v) => v,
                Err(e) => format!("!! {e}"),
            }
        })
        .collect()
}

fn same(src: &str) -> String {
    let [a, b] = <[String; 2]>::try_from(ev(src)).unwrap();
    assert_eq!(a, b, "the engines disagree on {src}");
    a
}

#[test]
fn made_read_and_written() {
    assert_eq!(same("(define b (%make-bloblet 4 'x \"y\" 3)) (list (%bloblet-ref b 2) (%bloblet-ref b 3) (%bloblet-ref b 4))"), "(x \"y\" 3)");
    assert_eq!(same("(define b (%make-bloblet 0 1 2)) (%bloblet-set! b 3 'z) (%bloblet-ref b 3)"), "z");
    assert_eq!(same("(define b (%make-bloblet 3)) (%bloblet-set-byte! b 2 255) (list (%bloblet-byte b 0) (%bloblet-byte b 2) (%bloblet-bytes b))"), "(0 255 3)");
    // Two fields and a trailer: F is 3.
    assert_eq!(same("(%bloblet-fields (%make-bloblet 0 1 2))"), "3");
    assert_eq!(same("(%bloblet-kind (%make-bloblet 0))"), "32");
    assert_eq!(same("(%make-bloblet 8 1 2)"), "#<bloblet 3 fields 8 bytes>");
}

#[test]
fn what_cannot_be_done() {
    // The trailer is not a field; nor is anything past F.
    let got = same("(%bloblet-ref (%make-bloblet 0 1) 1)");
    assert!(got.starts_with("!! error: bloblet field"), "{got}");
    let got = same("(%bloblet-ref (%make-bloblet 0 1) 3)");
    assert!(got.starts_with("!! error: bloblet field"), "{got}");
    let got = same("(%bloblet-byte (%make-bloblet 2) 2)");
    assert!(got.starts_with("!! error: bloblet byte"), "{got}");
    // Frozen fields, and a frozen suffix, refuse writes.
    let got = same("(define b (%make-bloblet 1 1)) (%bloblet-freeze! b #t #f) (%bloblet-set! b 2 0)");
    assert!(got.contains("frozen"), "{got}");
    let got = same("(define b (%make-bloblet 1 1)) (%bloblet-freeze! b #f #t) (%bloblet-set-byte! b 0 1)");
    assert!(got.contains("frozen"), "{got}");
    assert_eq!(same("(define b (%make-bloblet 1 1)) (%bloblet-freeze! b #t #f) (%bloblet-frozen? b)"), "(#t . #f)");
    // Every object but a pair is a bloblet. A closure is readable, but not
    // the program's to change.
    assert_eq!(same("(list (%bloblet? '(1)) (%bloblet? 3) (%bloblet? car) (%bloblet? \"s\"))"), "(#f #f #t #t)");
    assert_eq!(same("(%bloblet? (lambda (x) x))"), "#t");
    let got = same("(%bloblet-set! (lambda (x) x) 2 0)");
    assert!(got.contains("a bloblet the program made"), "{got}");
}
