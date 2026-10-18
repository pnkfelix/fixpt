//! The heap's fast paths of the native convention's compiler to x86_64
//! written in FX-26 (`src/native-direct-x64-flat.fx`) against the Rust
//! ones (`fixpt_native::direct::oracle_x64`), piece by piece: the same
//! bytes, over every register a piece may be given, every layout, and
//! every shape predicate. Any machine compiles for x86_64; none runs the
//! code here.

use fixpt_engine::Backend;
use fixpt_heap::Value;

/// The shape predicates, by the index both sides name them by
/// (`oracle_flat::SHAPES`).
const SHAPES: [&str; 14] = [
    "null?",
    "pair?",
    "char?",
    "%fx26-f32?",
    "boolean?",
    "exact-integer?",
    "symbol?",
    "string?",
    "%fx26-array?",
    "%fx26-box?",
    "%fx26-sum?",
    "%fx26-product?",
    "%fx26-procedure?",
    "%fx26-nothing-in-line?",
];

/// A raw values' module that does only what these pieces need of it,
/// `box_bits` (`direct/x64.rs`'s, as `native-direct-x64-raw.fx` is to do it).
const RAW_STAND_IN: &str = r#"
(define raw
  (module
    (hide (include direct-types))
    (hide (include x86-64) (include dl) (include asm))
    (define dr-box-reg (subr da-assembles (int bool) unit) (lambda (r s) #u))
    (define dr-unbox-reg (subr da-assembles (int) unit) (lambda (r) #u))
    (define dr-unbox-f64 (subr da-assembles (int) unit) (lambda (r) #u))
    (define dr-raw-entry (subr da-assembles (int) unit) (lambda (p) #u))
    (define dr-raw-entry-skip (subr da-assembles (int) int) (lambda (p) 0))
    (define dr-take-raw-f64 (subr da-assembles () unit) (lambda () #u))
    (define dr-raw-return (subr da-assembles () unit) (lambda () #u))
    (define dr-box-f64 (subr da-assembles (int) unit) (lambda (r) #u))
    (define dr-box-bits (subr da-assembles (int) unit)
      (lambda (slow)
        (begin
          (da-ld d-x13 d-st d-st-top)
          (da-ld d-x14 d-x13 0)
          (da-e (x86-lea d-x16 d-x14 2))
          (da-e (x86-alu-rm da-cmp d-x16 d-st d-st-alloc-limit))
          (da-jcc da-c-a slow)
          (da-ld d-x17 d-st d-st-words)
          (da-e (x86-lea-ix d-x11 d-x17 d-x14 8 0))
          (da-imm d-x17 (da-header d-flonum 0 8))
          (da-sto d-x11 0 d-x17)
          (da-sto d-x11 8 d-x9)
          (da-sto d-x13 0 d-x16)
          (da-e (x86-lea d-result d-x11 (+ 8 d-tag-bloblet))))))
    (define dr-unbox-to (subr da-assembles (int int) unit) (lambda (r rep) #u))
    (define dr-convert (subr da-assembles (da-bytes int int) unit) (lambda (cs g r) #u))
    (define dr-f64-of-int (subr da-assembles (int) unit) (lambda (p) #u))
    (define dr-int-of-f64 (subr da-assembles (int) unit) (lambda (p) #u))
    (define dr-float-test (subr da-assembles (bool string) bool) (lambda (d w) #f))
    (define dr-f64-fast (subr da-assembles (string int) unit) (lambda (w y) #u))
    (define dr-f32-fast (subr da-assembles (string int) bool) (lambda (w y) #f))
    (define dr-wrap-small (subr da-assembles (bool int) unit) (lambda (s b) #u))
    (define dr-raw-fast (subr da-assembles (bool string int) unit) (lambda (s w y) #u))
    (define dr-narrow-fast (subr da-assembles (string int int) bool) (lambda (n y s) #f))
    (define dr-int-slow (subr da-assembles (dr-int-slow) unit) (lambda (s) #u))))
"#;

/// Each piece as the oracle runs it: the assembler reset, `slow` and the
/// other label (`done` or `wide`) made, the piece, both bound, an `int3`,
/// the bytes.
const WRAPPERS: &str = r#"
(define tests
  (module
    (hide (include direct-types))
    (hide (include asm) (include flat))
    (define t-run (subr da-assembles ((subr da-assembles (int int) unit)) da-bytes)
      (lambda (f)
        (let* ((ignored (da-reset 0)) (slow (da-label)) (other (da-label)))
          (begin (f slow other) (da-bind slow) (da-bind other) (da-e (cons 204 nil))
                 (da-finish)))))
    (define t-flat-count (subr da-assembles (int int) da-bytes)
      (lambda (arr out) (t-run (lambda (slow other) (df-flat-count arr out)))))
    (define t-flat-element (subr da-assembles (int int) da-bytes)
      (lambda (arr y) (t-run (lambda (slow other) (df-flat-element arr y slow)))))
    (define t-flat-ref (subr da-assembles (int) da-bytes)
      (lambda (y) (t-run (lambda (slow other) (df-flat-ref y slow)))))
    (define t-suffix-owner (subr da-assembles (int) da-bytes)
      (lambda (r) (t-run (lambda (slow other) (df-suffix-owner r slow)))))
    (define t-suffix-writable (subr da-assembles (int) da-bytes)
      (lambda (r) (t-run (lambda (slow other) (df-suffix-writable r slow)))))
    (define t-suffix-store (subr da-assembles (int int int) da-bytes)
      (lambda (code v raw) (t-run (lambda (slow other) (df-suffix-store code v (= raw 1) slow)))))
    (define t-blobref-index (subr da-assembles (int int) da-bytes)
      (lambda (code i) (t-run (lambda (slow other) (df-blobref-index code i slow)))))
    (define t-flat-variant (subr da-assembles (int int) da-bytes)
      (lambda (code l) (t-run (lambda (slow other) (df-flat-variant code l slow)))))
    (define t-blobref-at (subr da-assembles (int) da-bytes)
      (lambda (d) (t-run (lambda (slow other) (df-blobref-at d slow)))))
    (define t-suffix-step (subr da-assembles (int) da-bytes)
      (lambda (d) (t-run (lambda (slow other) (df-suffix-step d slow)))))
    (define t-suffix-fits (subr da-assembles (int) da-bytes)
      (lambda (size) (t-run (lambda (slow other) (df-suffix-fits size slow)))))
    (define t-suffix-length (subr da-assembles (int) da-bytes)
      (lambda (code) (t-run (lambda (slow other) (df-suffix-length code slow)))))
    (define t-suffix-index (subr da-assembles () da-bytes)
      (lambda () (t-run (lambda (slow other) (df-suffix-index slow)))))
    (define t-flat-tag (subr da-assembles (int) da-bytes)
      (lambda (code) (t-run (lambda (slow other) (df-flat-tag code slow)))))
    (define t-suffix-get (subr da-assembles (int int) da-bytes)
      (lambda (code raw) (t-run (lambda (slow other) (df-suffix-get code (= raw 1) slow)))))
    (define t-wide-layout (subr da-assembles (int) da-bytes)
      (lambda (c) (t-run (lambda (slow other) (df-wide-layout c other)))))
    (define t-suffix-set (subr da-assembles () da-bytes)
      (lambda () (t-run (lambda (slow other) (df-suffix-set slow other)))))
    (define t-bytes-set (subr da-assembles () da-bytes)
      (lambda () (t-run (lambda (slow other) (df-bytes-set slow other)))))
    (define t-flat-set (subr da-assembles (int) da-bytes)
      (lambda (raw) (t-run (lambda (slow other) (df-flat-set slow other (= raw 1))))))
    (define t-shape-name (subr pure (int) string)
      (lambda (k)
        (case k
          ((0) "null?") ((1) "pair?") ((2) "char?") ((3) "%fx26-f32?") ((4) "boolean?")
          ((5) "exact-integer?") ((6) "symbol?") ((7) "string?") ((8) "%fx26-array?")
          ((9) "%fx26-box?") ((10) "%fx26-sum?") ((11) "%fx26-product?")
          ((12) "%fx26-procedure?") (else "%fx26-nothing-in-line?"))))
    ;; The bytes, then 1 if the shape was known, else 0.
    (define t-shape-fast (subr da-assembles (int) da-bytes)
      (lambda (k)
        (let ((known (the (ref bool @k) (new #f))))
          (let ((bytes (t-run (lambda (slow other) (set known (df-shape-fast (t-shape-name k) slow))))))
            (append bytes (cons (if (get known) 1 0) nil))))))))
"#;

/// The pieces, `t-` and the oracle's name.
const PIECES: [&str; 20] = [
    "flat-count",
    "flat-element",
    "flat-ref",
    "suffix-owner",
    "suffix-writable",
    "suffix-store",
    "blobref-index",
    "flat-variant",
    "blobref-at",
    "suffix-step",
    "suffix-fits",
    "suffix-length",
    "suffix-index",
    "flat-tag",
    "suffix-get",
    "wide-layout",
    "suffix-set",
    "bytes-set",
    "flat-set",
    "shape-fast",
];

fn session() -> fixpt_scheme::Session {
    let mut program = String::from(
        "(define direct-types (load-module \"fx26:native-direct-x64-types.fx\"))\n\
         (define x86-64 (load-input \"fx26:x86_64.fx\"))\n\
         (define dl (load-module \"fx26:native-direct-x64-layout.fx\"))\n\
         (define asm ((load-input \"fx26:native-direct-x64-asm.fx\") x86-64 dl))\n",
    );
    program.push_str(RAW_STAND_IN);
    program.push_str("(define flat ((load-input \"fx26:native-direct-x64-flat.fx\") x86-64 dl asm raw))\n");
    program.push_str(WRAPPERS);
    for p in PIECES {
        program.push_str(&format!("(define t-{p} (with tests t-{p}))\n"));
    }
    let compiled = fixpt_fx26::session::compile_program(&program).unwrap_or_else(|e| panic!("checks: {e}"));
    let mut s = fixpt_scheme::Session::with_backend(Backend::Bytecode);
    compiled.load_into(&mut s).expect("loads");
    s
}

/// What FX-26's piece makes of integer `args`.
fn ints_of(s: &mut fixpt_scheme::Session, name: &str, args: &[i64]) -> Vec<i64> {
    s.scope(|sc| {
        let args: Vec<_> = args.iter().map(|x| sc.make(|_| Value::fixnum(*x))).collect();
        let r = sc.call_global(&format!("fx:t-{name}"), &args).unwrap_or_else(|e| panic!("{name} runs: {e}"));
        sc.view(|v| v.get(r).list().expect("a list").iter().map(|b| b.fixnum().expect("an int")).collect())
    })
}

/// The flat layouts, the scalars' codes.
const LAYOUTS: [i64; 6] = [0, 1, 2, 3, 4, 5];

/// Array operands (`layout::array_operand`): lengths, the last running to
/// the end, by element sizes, powers of two and not.
fn array_operands() -> Vec<i64> {
    let mut out = Vec::new();
    for n in [0i64, 1, 3, 1000, fixpt_heap::layout::FLAT_TO_THE_END] {
        for size in [1i64, 2, 4, 8, 12, 24, 3] {
            out.push((n << fixpt_heap::layout::ARRAY_OPERAND_LENGTH_SHIFT) | size);
        }
    }
    out
}

/// Flat sums' codes: a tag's width (1, 2 or 4 bytes), numeric or not, and
/// where the payload is.
fn sum_codes() -> Vec<i64> {
    let mut out = Vec::new();
    for w in [1i64, 2, 4] {
        for numeric in [0i64, 8] {
            for p in [0i64, 3, 200, 4096] {
                out.push(w | numeric | p << 8);
            }
        }
    }
    out
}

#[test]
fn every_heap_piece_as_the_rust_compiler_makes_it() {
    let mut s = session();
    let regs: Vec<i64> = (0..16).collect();
    let mut cases: Vec<(&str, Vec<i64>)> = Vec::new();
    for &x in &regs {
        for &y in &regs {
            cases.push(("flat-count", vec![x, y]));
            cases.push(("flat-element", vec![x, y]));
        }
        cases.push(("flat-ref", vec![x]));
        cases.push(("suffix-owner", vec![x]));
        cases.push(("suffix-writable", vec![x]));
        cases.push(("wide-layout", vec![x]));
        for code in LAYOUTS {
            for raw in [0, 1] {
                cases.push(("suffix-store", vec![code, x, raw]));
            }
        }
        for code in array_operands() {
            cases.push(("blobref-index", vec![code, x]));
        }
        for code in sum_codes() {
            cases.push(("flat-variant", vec![code, x]));
        }
    }
    for d in [0i64, 1, 8, 1000, (1 << 24) - 1, (1 << 26) - 1] {
        cases.push(("blobref-at", vec![d]));
        cases.push(("suffix-step", vec![d]));
        cases.push(("suffix-fits", vec![d]));
    }
    for code in array_operands() {
        cases.push(("suffix-length", vec![code]));
    }
    for code in sum_codes() {
        cases.push(("flat-tag", vec![code]));
    }
    for code in LAYOUTS {
        for raw in [0, 1] {
            cases.push(("suffix-get", vec![code, raw]));
        }
    }
    cases.push(("suffix-index", vec![]));
    cases.push(("suffix-set", vec![]));
    cases.push(("bytes-set", vec![]));
    for raw in [0, 1] {
        cases.push(("flat-set", vec![raw]));
    }
    for k in 0..SHAPES.len() as i64 {
        cases.push(("shape-fast", vec![k]));
    }
    let mut wrong = Vec::new();
    let mut bytes = 0;
    for (name, args) in &cases {
        let (code, known) = fixpt_native::direct::oracle_x64(name, args).unwrap_or_else(|| panic!("no Rust piece {name}"));
        let mut want: Vec<i64> = code.iter().map(|&b| b as i64).collect();
        if *name == "shape-fast" {
            want.extend(known);
        }
        let got = ints_of(&mut s, name, args);
        bytes += want.len();
        if got != want {
            wrong.push(format!("{name} {args:?}: FX-26 {got:02x?}, Rust {want:02x?}"));
        }
    }
    eprintln!("{} heap pieces, {bytes} bytes; {} differ", cases.len(), wrong.len());
    assert!(wrong.is_empty(), "{}", wrong.iter().take(20).cloned().collect::<Vec<_>>().join("\n"));
}
