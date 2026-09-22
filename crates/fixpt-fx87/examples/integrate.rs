//! What the metadata buys, end to end.
use fixpt_engine::compile::disassemble;
use fixpt_engine::Backend;
use fixpt_heap::ObjType;
use fixpt_scheme::Session;

fn disasm(src: &str) -> String {
    let mut s = Session::with_backend(Backend::Bytecode);
    s.eval_str("<x>", &format!("(define (f a b) {src})")).expect("compiles");
    let sym = s.rt.heap.intern_existing("f").expect("defined");
    let v = s.rt.heap.global(s.rt.heap.symbol_global_slot(sym));
    let code = s.rt.heap.obj_ref(v, 0);
    assert!(s.rt.heap.is_a(code, ObjType::Code));
    disassemble(&s.rt.heap, code)
}

fn main() {
    let mut fx = fixpt_fx87::Fx87Session::new().expect("loads");
    let src = "(+ 1 2)";
    let mut sources = fixpt_read::SourceMap::new();
    let file = sources.add("<t>", src);
    let mut i = std::mem::take(&mut fx.checker.p.interner);
    let forms = fixpt_read::Reader::new(src, file, fixpt_read::SyntaxProfile::FX87, &mut i)
        .read_all()
        .expect("reads");
    fx.checker.p.interner = i;
    let out = fx.run(&forms[0]).expect("checks");
    println!("FX-87 source : {src}");
    println!("erased to    : {}\n", out.code);

    // The erased form is itself a top-level `begin`, which R7RS splices — so
    // the annotation has to be recognised before that happens, or the metadata
    // is destroyed exactly where FX delivers it.
    println!("=== the erased form, compiled as FX-87 emits it ===");
    {
        let mut s = Session::with_backend(Backend::Bytecode);
        s.eval_str("<x>", &format!("(define (fx) {})", out.code)).expect("compiles");
        let sym = s.rt.heap.intern_existing("fx").expect("defined");
        let v = s.rt.heap.global(s.rt.heap.symbol_global_slot(sym));
        print!("{}", disassemble(&s.rt.heap, s.rt.heap.obj_ref(v, 0)));
    }

    println!("=== compiled WITHOUT the annotation (what Scheme gets) ===");
    print!("{}", disasm("(+ a b)"));
    println!("=== compiled WITH it (what FX-87 now emits) ===");
    print!(
        "{}",
        disasm("(begin '(%fx-note (integrable +) (basis checked) (because \"immutable region\")) (+ a b))")
    );
}
