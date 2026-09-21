fn main() {
    let mut s = fixpt_fx87::Fx87Session::new().expect("loads");
    for src in ["(+ 1 2)", "(let ((+ 3)) +)", "((lambda ((+ int)) +) 7)", "(set! + 3)", "(let ((x 1)) (set! x 2))", "(let ((x 1 @!)) (set! x 2))"] {
        let mut sources = fixpt_read::SourceMap::new();
        let file = sources.add("<t>", src);
        let mut i = std::mem::take(&mut s.checker.p.interner);
        let forms = fixpt_read::Reader::new(src, file, fixpt_read::SyntaxProfile::FX87, &mut i)
            .read_all().expect("reads");
        s.checker.p.interner = i;
        match s.run(&forms[0]) {
            Ok(o) => println!("  {src:<28} => {} ! {}   value {:?}", o.ty, o.effect, o.value),
            Err(e) => println!("  {src:<28} => error: {e}"),
        }
    }
}
