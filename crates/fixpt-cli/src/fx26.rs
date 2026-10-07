//! FX-26 at the command line.
//!
//! A form is checked, lowered to Scheme that carries what the checker proved
//! (`fixpt_fx26::lower`), and run. The REPL prints what FX-87's did — the
//! value, then ` : <type> ! <effect>` — and `,code` shows the lowered Scheme
//! (under `--fx26-run cellular`, the words each form makes).
//!
//! Definitions persist between inputs: `(define name type expression)`,
//! `(define name expression)` and `(define-type name type)`.

use crate::lineedit::{Line, LineReader, Note};
use fixpt_engine::Backend;
use fixpt_fx26::session::{Fx26Session, Outcome, Strategy};
use fixpt_fx26::{Checker, Top};
use fixpt_read::{Datum, FileId, Syntax, SyntaxProfile};

/// Line and column (both from 1) of byte `at` in `text`.
fn line_col(text: &str, at: usize) -> (usize, usize) {
    let before = &text[..at.min(text.len())];
    let line = before.matches('\n').count() + 1;
    let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
    (line, col)
}

/// `FILE LINE COL`, as `,at` takes it: the file's name may hold spaces;
/// the line and column are its last two words, each 1 or more.
fn parse_origin(arg: &str) -> Option<(String, usize, usize)> {
    let mut words = arg.trim().rsplitn(3, char::is_whitespace);
    let col = words.next()?.parse::<usize>().ok().filter(|c| *c >= 1)?;
    let line = words.next()?.parse::<usize>().ok().filter(|l| *l >= 1)?;
    let file = words.next()?.trim().trim_matches('"');
    (!file.is_empty()).then(|| (file.to_string(), line, col))
}

fn located(name: &str, text: &str, e: &fixpt_fx26::FxError) -> String {
    let (line, col) = line_col(text, e.span.start as usize);
    format!("{name}:{line}:{col}: {}", e.message)
}

/// What checking found, as the REPL prints it after the value.
fn report(c: &Checker, top: &Top) -> String {
    match top {
        Top::Exp(k) => format!(" : {} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect)),
        Top::Define { name, ty, effect, .. } => {
            format!("{} : {} ! {}", c.interner.name(*name), c.show_ty(*ty), c.show_effect(effect))
        }
        Top::DefineRec { bindings, .. } => {
            let lines: Vec<String> =
                bindings.iter().map(|(n, t, _)| format!("{} : {} ! pure", c.interner.name(*n), c.show_ty(*t))).collect();
            lines.join("\n")
        }
        Top::DefineType { name, ty } => format!("{} = {}", c.interner.name(*name), c.show_definition(*ty)),
        Top::DefineTypeFamily { name } => format!("{}: a type with parameters", c.interner.name(*name)),
        Top::DefineGenerative { name } => format!("{}: a new type", c.interner.name(*name)),
        Top::DefineEffect { name, effect } => format!("{} = {}", c.interner.name(*name), c.show_effect(effect)),
        Top::PrivateRegions { regions } => {
            let names: Vec<String> = regions.iter().map(|r| c.show_region(*r)).collect();
            format!("; private: {}", names.join(" "))
        }
    }
}

/// One result: what it printed, its value and what checking found — or why
/// running it failed.
fn show(session: &Fx26Session, out: &Outcome, show_code: bool) {
    if show_code && !out.code.is_empty() {
        for line in out.code.lines() {
            println!("; {line}");
        }
    }
    print!("{}", out.printed);
    let found = report(&session.checker, &out.top);
    match &out.value {
        Ok(Some(v)) => println!("{v}{found}"),
        Ok(None) => println!("{found}"),
        Err(e) => {
            println!("{found}");
            eprintln!("! evaluation failed: {e}");
        }
    }
}

fn start(backend: Backend) -> Result<Fx26Session, i32> {
    let mut s = Fx26Session::with_backend(backend).map_err(|e| {
        eprintln!("fixpt: {e}");
        1
    })?;
    s.strategy = crate::FX26_RUN.get().copied().unwrap_or_default();
    if let Some(m) = crate::CELLULAR_MACHINE.get() {
        s.scheme.runtime_unrooted().run_word = Some(*m);
    }
    s.scheme.runtime_unrooted().machine_code = crate::CELLULAR_MACHINE_CODE.get().copied().flatten();
    s.scheme.runtime_unrooted().place_code = crate::CELLULAR_PLACE_CODE.get().copied().flatten();
    s.register_code = crate::CELLULAR_MACHINE_NAME.get().is_some_and(|n| n.contains("register code"));
    s.redefine = Some(ask_redefine);
    if crate::NATIVE_CONVENTION.get().copied().unwrap_or(false) {
        s.set_native_convention(true);
        s.native_runner = Some(run_native);
        s.native_compiler = Some(fixpt_native::direct::compile_closure);
        // What the native convention's compiler starts from.
        s.register_code = true;
        s.scheme.runtime_unrooted().native_code = Some(fixpt_native::direct::code_text);
    }
    // Cellular code calls native code (what the native compiler did not
    // decline, or an adapter), and a conversion makes adapters.
    s.scheme.runtime_unrooted().call_native = Some(fixpt_native::direct::call_native);
    s.scheme.runtime_unrooted().adapt = Some(fixpt_native::direct::adapt);
    crate::apply_gc_policy(&mut s.scheme);
    if let Some(l) = crate::STEP_LIMIT.get() {
        s.set_step_limit(*l);
    }
    // The front end's checker and compilers as register code, on the hand
    // register machine, whatever machine runs the program.
    s.scheme.runtime_unrooted().front_end_run_word = Some(fixpt_native::cellular::run_word_registers);
    s.front_end_compiled = std::env::var_os("FIXPT_FRONT_END_LOWERED").is_none();
    if let Some(l) = crate::SPECULATION_STEP_LIMIT.get() {
        s.speculation_limit = *l;
    }
    Ok(s)
}

pub fn repl(backend: Backend) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    let engine = match backend {
        Backend::Ast => "AST engine",
        Backend::Bytecode => "bytecode engine",
    };
    println!("fixpt {} — FX-26, {engine}", env!("CARGO_PKG_VERSION"));
    // Say what runs each form: `--fx26-run` chooses.
    let machine = crate::CELLULAR_MACHINE_NAME.get().copied().unwrap_or("the cellular machine written in Rust");
    let how = match session.strategy {
        Strategy::Lower => format!("lowered to Scheme and run on the {engine}"),
        Strategy::Evaluate => "run by the evaluator written in FX-26".to_string(),
        Strategy::Cellular if session.native_runner.is_some() => format!(
            "compiled by the compiler written in FX-26, then in the native convention, and run as machine code (where it cannot be yet, on {machine}, saying why)"
        ),
        Strategy::Cellular => format!("compiled to cellular words by the compiler written in FX-26, and run on {machine}"),
    };
    println!("(each form is checked, {how}.");
    match session.strategy {
        Strategy::Lower => println!(" `,help` for commands, `,code` to show the lowered Scheme. ^D leaves.)"),
        Strategy::Cellular => println!(" `,help` for commands, `,code` to show the words each form makes. ^D leaves.)"),
        _ => println!(" `,help` for commands, `,code` to show the lowering to Scheme, which is not what runs. ^D leaves.)"),
    }

    // FX-26 code reads FX-26 input: the eager reader written in FX-26, once
    // its licence is checked. Without it, the Rust reader.
    let mut eager = match fixpt_fx26::session::load_eager_reader(&mut session.scheme).and_then(|()| {
        fixpt_scheme::eager::EagerReader::attach_starting(
            &mut session.scheme,
            fixpt_fx26::session::READER_PREFIX,
            "eager-start-fx26",
        )
        .map_err(|e| e.to_string())
    }) {
        Ok(r) => {
            println!("(read as you type by the eager reader written in FX-26; its licence checked)");
            Some(r)
        }
        Err(why) => {
            println!("(the FX-26 eager reader is not used: {why})");
            None
        }
    };
    let mut reader = LineReader::new(".fixpt_fx26_history", SyntaxProfile::FX26);
    let mut show_code = false;
    let mut disassembling;
    let mut n = 0usize;
    // `--emacs`: where the next form was sent from (`,at`), as a file's name
    // and its line and column, so that its errors are said there.
    let emacs = crate::EMACS.get().copied().unwrap_or(false);
    let mut origin: Option<(String, usize, usize)> = None;
    // A redefinition at another type leaves the definitions that use the
    // name out of date, keeping the old global, until `,rerun-outdated`:
    // so that a load does not run again what it will define again.
    session.set_defer_reruns(true);
    let mut outdated_said = Vec::new();
    loop {
        // Said when what is out of date changes.
        let outdated = session.outdated();
        if outdated != outdated_said && !outdated.is_empty() {
            println!("{}", outdated_line(&outdated));
        }
        outdated_said = outdated;
        reader.set_completions(known_names(&session.checker));
        let line = {
            let mut oracle = Oracle { session: &mut session, reader: eager.as_mut() };
            reader.read_with("fx26> ", if emacs { "" } else { "     | " }, &mut oracle, "")
        };
        let text = match line {
            Line::Eof => {
                reader.save();
                return 0;
            }
            Line::Interrupted | Line::Ask { .. } => continue,
            Line::Form(text) => text,
        };
        // `,at FILE LINE COL` (with `--emacs`): the next form is from FILE,
        // starting at LINE and COL.
        if emacs && let Some(arg) = text.trim().strip_prefix(",at ") {
            match parse_origin(arg) {
                Some(o) => origin = Some(o),
                None => println!("; `,at FILE LINE COL`: where the next form was sent from"),
            }
            continue;
        }
        if let Some(ask) = crate::help::parse(&text) {
            crate::help::answer(&mut session.checker, &ask);
            continue;
        }
        // `,redefine b|r`: what the next redefinition that would break
        // definitions does, said ahead of it (for input no one is asked).
        if let Some(arg) = text.trim().strip_prefix(",redefine") {
            use fixpt_fx26::session::Redefine;
            session.next_redefine = match arg.trim() {
                "b" | "break" => Some(Redefine::Break),
                "r" | "refuse" => Some(Redefine::Refuse),
                _ => {
                    println!("; `,redefine b|r`: the next redefinition that would break definitions breaks them, or is refused");
                    continue;
                }
            };
            continue;
        }
        // `,list-outdated`: the definitions out of date, and why each is.
        if text.trim() == ",list-outdated" {
            let outdated = session.outdated();
            if outdated.is_empty() {
                println!("; nothing is out of date");
            }
            for (names, since) in outdated {
                println!("; {} uses {}, defined again since at another type", quoted(&names), quoted(&since));
            }
            continue;
        }
        // `,rerun-outdated`: each definition out of date run again.
        if text.trim() == ",rerun-outdated" {
            for (names, out) in session.rerun_outdated() {
                match out {
                    Ok(out) => {
                        print!("{}", out.printed);
                        if let Err(e) = &out.value {
                            println!("; {} failed as it ran again: {e}", quoted(&names));
                        }
                    }
                    Err(e) => println!("; {} stays out of date: {}", quoted(&names), e.message.lines().next().unwrap_or("")),
                }
            }
            outdated_said = Vec::new();
            if session.outdated().is_empty() {
                println!("; nothing is out of date");
            }
            continue;
        }
        // `,inliners NAME`: the globals whose code inlines NAME's calls.
        if let Some(rest) = text.trim().strip_prefix(",inliners") {
            let name = rest.trim();
            match session.inliners(name) {
                Ok(Ok(ns)) if ns.is_empty() => println!("; no global's code inlines `{name}`"),
                Ok(Ok(ns)) => {
                    let ns: Vec<String> = ns.iter().map(|n| format!("`{n}`")).collect();
                    println!("; inlining `{name}`: {}", ns.join(", "));
                    println!(";   (redefined, `{name}` is called by them instead: nothing is compiled again)");
                }
                Ok(Err(why)) => println!("; {why}"),
                Err(e) => eprintln!("; {}", e.message),
            }
            continue;
        }
        // `,time E`: E run as any form is, then how long its code ran, and
        // what the heap did meanwhile.
        let (timing, text) = match text.trim().strip_prefix(",time") {
            Some(e) if e.starts_with(char::is_whitespace) && !e.trim().is_empty() => (true, e.trim().to_string()),
            Some(e) if e.trim().is_empty() => {
                println!("; `,time E`: run E, then say how long it took to check, generate code for and run, and its collections");
                continue;
            }
            _ => (false, text),
        };
        // `,load FILE`: the file's forms run as a file's are (its types
        // declared ahead), each shown as an entry's is; a `load-module` in
        // it is from the file's directory.
        if let Some(arg) = text.trim().strip_prefix(",load")
            && (arg.is_empty() || arg.starts_with(char::is_whitespace))
        {
            let path = arg.trim().trim_matches('"');
            if path.is_empty() {
                println!("; `,load FILE`: run the file's forms here, as `fixpt eval` runs a file");
                continue;
            }
            match std::fs::read_to_string(path) {
                Ok(t) => {
                    let dir = std::path::Path::new(path).parent().map(|d| d.to_path_buf());
                    let outer = std::mem::replace(&mut session.checker.base_dir, dir);
                    eval_program_in(&mut session, path, &t);
                    session.checker.base_dir = outer;
                }
                Err(e) => println!("; cannot read `{path}`: {e}"),
            }
            continue;
        }
        // `,pending [clear]`: the entries waiting on types not defined yet.
        if let Some(arg) = text.trim().strip_prefix(",pending") {
            match arg.trim() {
                "" if session.pending.is_empty() => println!("; nothing is pending"),
                "" => println!("{}", pending_line(&mut session)),
                "clear" => {
                    session.pending.clear();
                    println!("; nothing is pending");
                }
                _ => println!("; `,pending` shows the entries waiting on types not defined yet; `,pending clear` drops them"),
            }
            continue;
        }
        // `,native NAME [ARG…]`: NAME's procedure in the native convention.
        if let Some(rest) = text.trim().strip_prefix(",native") {
            native(&mut session, rest);
            continue;
        }
        // `,disassemble-asm E`: the same, with each word's machine code as
        // the machine that runs it has it: native code, decoded, or, for
        // the stencil machine, its stencils' Rust source.
        let (asm, text) = match text.trim().strip_prefix(",disassemble-asm") {
            Some(e) => (true, format!(",disassemble {e}")),
            None => (false, text),
        };
        session.scheme.runtime_unrooted().show_machine_code = asm;
        // (In the native convention the procedures are machine code, which
        // it shows, whatever the cellular machine is.)
        if asm && session.strategy != Strategy::Lower && session.native_runner.is_none() {
            let name = crate::CELLULAR_MACHINE_NAME.get().copied().unwrap_or("");
            if crate::CELLULAR_MACHINE_CODE.get().copied().flatten().is_none() {
                println!("; {name} interprets the cells: it has no machine code for a word to show.");
                if name.contains("hand-encoded") {
                    println!(";   `--cellular-machine native-compiled`, `fx-compiled` or `registers` compiles each word.");
                }
            }
        }
        // `,disassemble E`: E's cellular code, shown, as `disassemble` gives
        // it (under `--fx26-run cellular`; lowered, there is none).
        let text = match text.trim().strip_prefix(",disassemble") {
            Some(e) if !e.trim().is_empty() && session.strategy == Strategy::Lower => {
                println!("; lowered to Scheme, `{}` is a Scheme procedure, with no cellular code:", e.trim());
                println!(";   `,code` shows a form's lowering; run with `--fx26-run cellular` to disassemble.");
                continue;
            }
            Some(e) if !e.trim().is_empty() => {
                disassembling = true;
                // A polymorphic value projected first, any description
                // standing in for each binder: `proj` compiles to nothing,
                // so the code shown is the same, and it is checked as
                // written. (Its type not known, the error is the form's.)
                match session.checker.stand_ins(e.trim()) {
                    Ok((levels, places)) if !levels.is_empty() => {
                        let projected = levels.iter().fold(e.trim().to_string(), |x, ins| format!("(proj {x} {})", ins.join(" ")));
                        println!("; as {projected}: `proj` compiles to nothing");
                        // A place stood in for is made around it.
                        places.iter().rev().fold(format!("(disassemble {projected})"), |x, p| format!("(letrena {p} {x})"))
                    }
                    _ => format!("(disassemble {e})"),
                }
            }
            _ => {
                disassembling = false;
                text
            }
        };
        // `,step-limit [N|none]`: the limit on a form's steps, shown or set.
        if let Some(arg) = text.trim().strip_prefix(",step-limit") {
            let show = |l: Option<u64>| l.map_or("none".to_string(), |n| n.to_string());
            match arg.trim() {
                "" => println!("; step limit: {}", show(session.step_limit())),
                v => match crate::parse_limit(v) {
                    Some(l) => {
                        session.set_step_limit(l);
                        println!("; step limit: {}", show(l));
                    }
                    None => eprintln!("; `,step-limit` takes a count of steps, or none"),
                },
            }
            continue;
        }
        match text.trim() {
            "" => continue,
            ",code" => {
                show_code = !show_code;
                let what = if session.strategy == Strategy::Cellular { "cellular words" } else { "lowered Scheme" };
                session.show_words = show_code && session.strategy == Strategy::Cellular;
                println!("; {what}: {}", if show_code { "on" } else { "off" });
                continue;
            }
            ",quit" => {
                reader.save();
                return 0;
            }
            _ => {}
        }
        n += 1;
        // Sent from a file (`,at`): read where it stands there, so that
        // each position in it is the file's.
        let (name, text) = match origin.take() {
            Some((file, line, col)) => (file, format!("{}{}{text}", "\n".repeat(line - 1), " ".repeat(col - 1))),
            None => (format!("<fx26:{n}>"), text),
        };
        let forms = match session.checker.read_in(FileId(0), &text) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("read error: {}", located(&name, &text, &e));
                continue;
            }
        };
        // An entry of types naming types not defined yet waits for them; the
        // one that supplies the last runs with every entry waiting.
        use fixpt_fx26::session::Consider;
        match session.consider(&forms) {
            Consider::Pends(_) => {
                session.hold(&forms);
                println!("{}", pending_line(&mut session));
                continue;
            }
            Consider::Completes(names) => {
                complete_pending(&mut session, &forms, &names, &name, &text, show_code);
                continue;
            }
            Consider::Run => {}
        }
        for form in &forms {
            if let Some(lines) = answer_hole(&mut session.checker, form) {
                for l in lines {
                    println!("{l}");
                }
                continue;
            }
            let before = timing.then(|| GcStats::start_form(&mut session));
            let ran = session.run(form);
            if let Some(b) = before {
                GcStats::of(&mut session).form_since(&b);
                GcStats::end_form(&mut session, &b);
            }
            match ran {
                Ok(out) if disassembling => match &out.value {
                    Ok(Some(v)) => print!("{}", unwrite_string(v)),
                    _ => show(&session, &out, show_code),
                },
                Ok(out) => show(&session, &out, show_code),
                Err(e) => {
                    eprintln!("{}", located(&name, &text, &e));
                    if let Some(note) = pending_note(&mut session, &e.message) {
                        eprintln!("{note}");
                    }
                }
            }
        }
        // What this entry defined may be what the entries waiting lacked.
        if !session.pending.is_empty() && session.awaiting().is_empty() {
            let names: Vec<String> = session.pending.iter().flat_map(|p| p.defines.clone()).collect();
            complete_pending(&mut session, &[], &names, &name, &text, show_code);
        }
    }
}

/// The entries waiting, and what for, as a line.
fn pending_line(session: &mut Fx26Session) -> String {
    let quote = |ns: &[String]| ns.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ");
    let defines: Vec<String> = session.pending.iter().flat_map(|p| p.defines.clone()).collect();
    format!("; pending: {}, awaiting definitions of: {}", quote(&defines), quote(&session.awaiting()))
}

/// For a refusal that names something an entry waiting defines: that it
/// is waiting, and for what.
fn pending_note(session: &mut Fx26Session, message: &str) -> Option<String> {
    let first = message.lines().next().unwrap_or("");
    let waiting = session.pending.iter().flat_map(|p| p.defines.clone()).find(|d| first.contains(&format!("`{d}`")))?;
    let awaiting: Vec<String> = session.awaiting().iter().map(|n| format!("`{n}`")).collect();
    Some(format!("  `{waiting}` is pending, awaiting definitions of: {}", awaiting.join(", ")))
}

/// The entries waiting, with `forms`, run now that nothing is missing.
fn complete_pending(session: &mut Fx26Session, forms: &[Syntax], names: &[String], name: &str, text: &str, show_code: bool) {
    match session.complete(forms) {
        Ok(outs) => {
            for o in outs {
                match o {
                    Ok(out) => show(session, &out, show_code),
                    Err(e) => eprintln!("{}", located(name, text, &e)),
                }
            }
            let names: Vec<String> = names.iter().map(|n| format!("`{n}`")).collect();
            println!("; no longer pending: {}", names.join(", "));
        }
        Err(e) => eprintln!("{}", located(name, text, &e)),
    }
}

/// Names as messages show them: `a`, `b`.
fn quoted(names: &[String]) -> String {
    names.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ")
}

/// What is out of date, said in one line.
fn outdated_line(outdated: &[(Vec<String>, Vec<String>)]) -> String {
    let names: Vec<String> = outdated.iter().flat_map(|(ns, _)| ns.clone()).collect();
    let n = names.len();
    let shown = if n <= 6 { quoted(&names) } else { format!("{}, …", quoted(&names[..5])) };
    format!("; out of date ({n}), using what was defined again: {shown}; `,rerun-outdated` runs them again")
}

/// A redefinition that would break definitions, asked about at a terminal
/// (`Fx26Session::redefine`); anywhere else, `b`, as the session does with
/// no one to ask.
fn ask_redefine(q: &fixpt_fx26::session::Redefinition) -> fixpt_fx26::session::Redefine {
    use fixpt_fx26::session::Redefine;
    use std::io::{BufRead, IsTerminal, Write};
    if !std::io::stdin().is_terminal() {
        return Redefine::Break;
    }
    let names: Vec<String> = q.names.iter().map(|n| format!("`{n}`")).collect();
    println!("; redefining {} breaks what uses it as it was:", names.join(", "));
    for (n, why) in &q.breaking {
        println!(";   {n}: {why}");
    }
    if !q.rerun.is_empty() {
        println!("; and runs again, as they still check: {}", q.rerun.join(", "));
    }
    println!("; [b]reak them: unusable until you define them again (the default)");
    println!("; [r]efuse this redefinition: nothing changes");
    println!(";   (to keep an old value, bind it: `(define d (let ((g g)) …))`)");
    print!("; which? [b] ");
    let _ = std::io::stdout().flush();
    let mut line = String::new();
    let _ = std::io::stdin().lock().read_line(&mut line);
    match line.trim() {
        "r" | "refuse" => Redefine::Refuse,
        _ => Redefine::Break,
    }
}

/// A string as it was written, `"…"` with escapes, back to its text.
fn unwrite_string(w: &str) -> String {
    let Some(inner) = w.strip_prefix('"').and_then(|x| x.strip_suffix('"')) else { return format!("{w}\n") };
    let mut out = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('t') => out.push('\t'),
            Some(x) => out.push(x),
            None => {}
        }
    }
    out
}

/// Run every form of `files` in one session, printing only what the program
/// prints. The first error, static or dynamic, stops it.
pub fn run_files(backend: Backend, files: &[String]) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    for f in files {
        let text = match std::fs::read_to_string(f) {
            Ok(t) => t,
            Err(e) => {
                eprintln!("fixpt: cannot read {f}: {e}");
                return 1;
            }
        };
        let forms = match session.checker.read_in(FileId(0), &text) {
            Ok(forms) => forms,
            Err(e) => {
                eprintln!("fixpt: read error: {}", located(f, &text, &e));
                return 1;
            }
        };
        // A file is a whole program: its definitions may come in any order.
        let outs = match session.run_forms(&forms) {
            Ok(outs) => outs,
            Err(e) => {
                eprintln!("fixpt: {}", located(f, &text, &e));
                return 1;
            }
        };
        for out in outs {
            match out {
                Ok(out) => {
                    print!("{}", out.printed);
                    if let Err(e) = out.value {
                        eprintln!("fixpt: {e}");
                        return 1;
                    }
                }
                Err(e) => {
                    eprintln!("fixpt: {}", located(f, &text, &e));
                    return 1;
                }
            }
        }
    }
    0
}

/// A command's INPUT, its arguments: a file, if there is one at the one
/// argument's path; the standard input, if that is `-`; or else the text
/// of the arguments, joined. Its name for messages, and its text.
pub fn input(args: &[String]) -> Result<(String, String), String> {
    match args {
        [a] if a == "-" => {
            let mut text = String::new();
            std::io::Read::read_to_string(&mut std::io::stdin(), &mut text).map_err(|e| format!("cannot read the standard input: {e}"))?;
            Ok(("<stdin>".to_string(), text))
        }
        [a] if std::path::Path::new(a).is_file() => {
            std::fs::read_to_string(a).map(|t| (a.clone(), t)).map_err(|e| format!("cannot read {a}: {e}"))
        }
        _ => Ok(("<argument>".to_string(), args.join(" "))),
    }
}

/// `fixpt check`: both checkers on a program, each form's type and effect;
/// said once where they agree, both where they do not (and then 1).
pub fn check(backend: Backend, name: &str, text: &str) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    // A `load-module`'s path is from the file's directory, as `eval`'s is.
    session.checker.base_dir = std::path::Path::new(name).parent().map(|d| d.to_path_buf());
    let (fx26, rust) = match fixpt_fx26::compare::both_checkers(&mut session, text) {
        Ok(both) => both,
        Err(e) => {
            eprintln!("fixpt: the FX-26 front end: {}", located(name, text, &e));
            return 1;
        }
    };
    let say = |r: &fixpt_fx26::syn::Checked26, who: &str| match r {
        Ok(lines) => lines.iter().for_each(|l| println!("{who}{l}")),
        Err(e) => println!("{who}! {}", located(name, text, e)),
    };
    let same = match (&fx26, &rust) {
        (Ok(a), Ok(b)) => a == b,
        (Err(a), Err(b)) => a.message == b.message && a.span == b.span,
        _ => false,
    };
    if same {
        say(&fx26, "");
        println!("; both checkers agree");
        i32::from(fx26.is_err())
    } else {
        say(&fx26, "FX-26: ");
        say(&rust, "Rust:  ");
        println!("; the checkers disagree");
        1
    }
}

/// `fixpt compile`: both compilers on a program, with register code; the
/// code the FX-26 one made, and whether the Rust one made the same (both,
/// if not, and then 1).
pub fn compile(backend: Backend, name: &str, text: &str) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    session.checker.base_dir = std::path::Path::new(name).parent().map(|d| d.to_path_buf());
    let (fx26, rust, declined) = match fixpt_fx26::compare::both_compilers_declining(&mut session, text) {
        Ok(both) => both,
        Err(e) => {
            eprintln!("fixpt: {}", located(name, text, &e));
            return 1;
        }
    };
    print!("{declined}");
    match (&fx26, &rust) {
        (Ok(a), Ok(b)) if a == b => {
            print!("{a}");
            println!("; both compilers made this");
            0
        }
        (Err(a), Err(b)) if a == b => {
            println!("! {a}");
            println!("; both compilers refuse it");
            1
        }
        _ => {
            for (who, r) in [("FX-26", &fx26), ("Rust", &rust)] {
                println!("; the {who} compiler:");
                match r {
                    Ok(code) => print!("{code}"),
                    Err(e) => println!("! {e}"),
                }
            }
            println!("; the compilers disagree");
            1
        }
    }
}

/// `fixpt eval` of a file: the whole program (definitions in any order),
/// each form's value and type.
pub fn eval_program(backend: Backend, name: &str, text: &str) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    // `FIXPT_GC_SUMMARY` (or its older name, `FIXPT_GC_REPORT`): what the
    // heap did while the program ran, at its end.
    let report = std::env::var_os("FIXPT_GC_SUMMARY").is_some() || std::env::var_os("FIXPT_GC_REPORT").is_some();
    // A `load-module`'s relative path is from the program's directory.
    session.checker.base_dir = std::path::Path::new(name).parent().map(|d| d.to_path_buf());
    let before = GcStats::of(&mut session);
    let code = eval_program_in(&mut session, name, text);
    if report {
        GcStats::of(&mut session).since(&before);
    }
    code
}

/// What the heap has done, for `FIXPT_GC_REPORT` and `,time`.
struct GcStats {
    time: std::time::Instant,
    run: u64,
    compile: u64,
    major: u64,
    minor: u64,
    nanos: u64,
    minor_nanos: u64,
    allocated: u64,
    copied: u64,
    minor_copied: u64,
    peak: u64,
    max_major: u64,
    max_minor: u64,
}

impl GcStats {
    fn of(s: &mut Fx26Session) -> GcStats {
        let rt = s.scheme.runtime_unrooted();
        let (run, compile) = (rt.run_nanos, rt.compile_nanos);
        let h = &rt.heap;
        GcStats {
            time: std::time::Instant::now(),
            run,
            compile,
            major: h.gc_count,
            minor: h.minor_count,
            nanos: h.gc_nanos,
            minor_nanos: h.minor_nanos,
            allocated: h.allocated(),
            copied: h.words_copied,
            minor_copied: h.minor_words_copied,
            peak: h.peak_words,
            max_major: h.max_major_nanos,
            max_minor: h.max_minor_nanos,
        }
    }

    /// Before a form `,time` runs: the longest pauses and the peak, kept
    /// for the session, start again from nothing, so that they are the
    /// form's own; `b.max_*` and `b.peak` keep the session's.
    fn start_form(s: &mut Fx26Session) -> GcStats {
        let b = GcStats::of(s);
        let h = &mut s.scheme.runtime_unrooted().heap;
        (h.max_major_nanos, h.max_minor_nanos, h.peak_words) = (0, 0, 0);
        b
    }

    /// After it: the session's longest pauses and peak again, counting the
    /// form's.
    fn end_form(s: &mut Fx26Session, b: &GcStats) {
        let h = &mut s.scheme.runtime_unrooted().heap;
        h.max_major_nanos = h.max_major_nanos.max(b.max_major);
        h.max_minor_nanos = h.max_minor_nanos.max(b.max_minor);
        h.peak_words = h.peak_words.max(b.peak);
    }

    /// What `,time` says of one form, run since `b`.
    fn form_since(&self, b: &GcStats) {
        println!("{}", self.form_line(b));
    }

    /// One line, the form's phases in the order they happen: checking
    /// (reading, both checkers, lowering: what is neither of the others),
    /// code generation, and the run; then the heap's part in it.
    fn form_line(&self, b: &GcStats) -> String {
        let ms = |n: u64| n as f64 / 1e6;
        let all = self.time.duration_since(b.time).as_nanos() as u64;
        let (run, codegen) = (self.run - b.run, self.compile - b.compile);
        let check = all.saturating_sub(run + codegen);
        let mut line = format!("; check {:.3} ms, codegen {:.3} ms, run {:.3} ms", ms(check), ms(codegen), ms(run));
        line.push_str(&format!("; {:.3} M words allocated", (self.allocated - b.allocated) as f64 / 1e6));
        let (major, minor) = (self.major - b.major, self.minor - b.minor);
        let major_ns = (self.nanos - b.nanos) - (self.minor_nanos - b.minor_nanos);
        let mut gcs = Vec::new();
        if major > 0 {
            gcs.push(format!("{major} major, {:.2} ms (longest {:.2})", ms(major_ns), ms(self.max_major)));
        }
        if minor > 0 {
            gcs.push(format!("{minor} minor, {:.2} ms (longest {:.2})", ms(self.minor_nanos - b.minor_nanos), ms(self.max_minor)));
        }
        line.push_str(&if gcs.is_empty() { "; no collections".to_string() } else { format!("; {}", gcs.join("; ")) });
        line
    }

    /// On stderr: what the heap did since `b`, the front end's loading
    /// left out.
    fn since(&self, b: &GcStats) {
        let ms = |n: u64| n as f64 / 1e6;
        let mw = |n: u64| n as f64 / 1e6;
        eprintln!(
            "; the program: {:.3} s; {} major collection(s), {:.1} ms; {} minor, {:.1} ms; {:.1} M words allocated; copied {:.1} M by major, {:.1} M by minor",
            self.time.duration_since(b.time).as_secs_f64(),
            self.major - b.major,
            ms((self.nanos - b.nanos) - (self.minor_nanos - b.minor_nanos)),
            self.minor - b.minor,
            ms(self.minor_nanos - b.minor_nanos),
            mw(self.allocated - b.allocated),
            mw((self.copied - b.copied) - (self.minor_copied - b.minor_copied)),
            mw(self.minor_copied - b.minor_copied),
        );
        // Since the session began: the front end's loading included.
        eprintln!(
            "; longest pause {:.2} ms major, {:.2} ms minor; at most {:.1} M words in use",
            ms(self.max_major),
            ms(self.max_minor),
            mw(self.peak)
        );
    }
}

fn eval_program_in(session: &mut Fx26Session, name: &str, text: &str) -> i32 {
    let forms = match session.checker.read_in(FileId(0), text) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("fixpt: read error: {}", located(name, text, &e));
            return 1;
        }
    };
    let outs = match session.run_forms(&forms) {
        Ok(outs) => outs,
        Err(e) => {
            eprintln!("fixpt: {}", located(name, text, &e));
            return 1;
        }
    };
    for out in outs {
        match out {
            Ok(out) => {
                show(session, &out, false);
                if out.value.is_err() {
                    return 1;
                }
            }
            Err(e) => {
                eprintln!("fixpt: {}", located(name, text, &e));
                return 1;
            }
        }
    }
    0
}

/// Run the forms of `text` and print what each is.
pub fn eval(backend: Backend, text: &str) -> i32 {
    let mut session = match start(backend) {
        Ok(s) => s,
        Err(code) => return code,
    };
    let forms = match session.checker.read_in(FileId(0), text) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("fixpt: read error: {}", located("<argument>", text, &e));
            return 1;
        }
    };
    for form in &forms {
        match session.run(form) {
            Ok(out) => {
                show(&session, &out, false);
                if out.value.is_err() {
                    return 1;
                }
            }
            Err(e) => {
                eprintln!("fixpt: {}", located("<argument>", text, &e));
                return 1;
            }
        }
    }
    0
}

/// Names for completion and for not colouring as unbound: what the
/// environment binds, the type names, and the reserved words.
fn known_names(c: &Checker) -> Vec<String> {
    let mut names: Vec<String> = c
        .value_names()
        .into_iter()
        .chain(c.type_names())
        .chain(c.base_names())
        .map(|s| c.interner.name(s).to_string())
        .chain(fixpt_fx26::top::KEYWORDS.iter().map(|k| k.to_string()))
        .collect();
    names.sort();
    names.dedup();
    names
}

// ------------------------------------------------------------------- help

impl crate::help::Helpful for Checker {
    fn dialect(&self) -> &'static str {
        "FX-26"
    }

    fn typed(&self) -> bool {
        true
    }

    fn holes(&self) -> bool {
        true
    }

    fn describe(&mut self, name: &str) -> Vec<String> {
        let Some(sym) = self.interner.get(name) else { return Vec::new() };
        let mut out = Vec::new();
        if let Some(t) = self.type_of_name(sym) {
            out.push(format!("{name} : {}", self.show_ty(t)));
        }
        for (s, kind, shown) in self.description_entries() {
            if s == sym {
                out.push(format!("{shown}  ({})", a_kind(kind)));
            }
        }
        out
    }

    /// Names containing `pattern`, in every namespace: values, and each
    /// kind of description. `KIND TEXT` (`value`, `type`, `family`,
    /// `generative`, `effect`, `region` or `base`) looks in that one only.
    fn apropos(&mut self, pattern: &str) -> Vec<String> {
        const KINDS: [&str; 7] = ["value", "type", "family", "generative", "effect", "region", "base"];
        let (only, text) = match pattern.split_once(char::is_whitespace) {
            Some((k, rest)) if KINDS.contains(&k) && !rest.trim().is_empty() => (Some(k), rest.trim()),
            _ => (None, pattern),
        };
        let wants = |k: &str| only.is_none_or(|o| o == k || (o == "base" && k == "base type"));
        let mut out: Vec<String> = Vec::new();
        if wants("value") {
            out.extend(self.value_names().into_iter().filter(|s| self.interner.name(*s).contains(text)).filter_map(|s| {
                let t = self.type_of_name(s)?;
                Some(format!("{} : {}", self.interner.name(s), self.show_ty(t)))
            }));
        }
        for (s, kind, shown) in self.description_entries() {
            if wants(kind) && self.interner.name(s).contains(text) {
                out.push(format!("{shown}  ({})", a_kind(kind)));
            }
        }
        out.sort();
        out.dedup();
        out
    }

    fn fits(&mut self, type_text: &str) -> Option<Vec<String>> {
        let want = self.type_of_str(type_text).ok()?;
        Some(self.search(|c, params, _| params.first().is_some_and(|p| c.subtype(want, *p))))
    }

    fn returns(&mut self, type_text: &str) -> Option<Vec<String>> {
        let want = self.type_of_str(type_text).ok()?;
        Some(self.search(|c, _, result| c.subtype(result, want)))
    }
}

/// A search over the subroutines in the environment. Polymorphic ones are
/// not instantiated — FX-26 has no inference yet (plan step 4) — so they are
/// found only by name.
trait Search {
    fn search(
        &mut self,
        keep: impl FnMut(&mut Checker, &[fixpt_fx26::ast::TyId], fixpt_fx26::ast::TyId) -> bool,
    ) -> Vec<String>;
}

impl Search for Checker {
    fn search(
        &mut self,
        mut keep: impl FnMut(&mut Checker, &[fixpt_fx26::ast::TyId], fixpt_fx26::ast::TyId) -> bool,
    ) -> Vec<String> {
        let mut out = Vec::new();
        for s in self.value_names() {
            let Some(t) = self.type_of_name(s) else { continue };
            let fixpt_fx26::ast::Ty::Subr { params, result, .. } = self.arena.get(t).clone() else {
                continue;
            };
            if keep(self, &params, result) {
                out.push(format!("{} : {}", self.interner.name(s), self.show_ty(t)));
            }
        }
        out.sort();
        out
    }
}

// ----------------------------------------------- help inside an expression

/// Where a `,help` hole is in `form`, if `form` is an application with one.
fn hole_position(c: &Checker, form: &Syntax) -> Option<(Vec<Syntax>, usize)> {
    let Datum::List { items, tail: None } = &form.datum else { return None };
    let is_hole = |s: &Syntax| match &s.datum {
        Datum::List { items, tail: None } if items.len() == 2 => matches!(
            (&items[0].datum, &items[1].datum),
            (Datum::Symbol(u), Datum::Symbol(h))
                if c.interner.name(*u) == "unquote" && matches!(c.interner.name(*h), "help" | "?")
        ),
        _ => false,
    };
    let at = items.iter().position(is_hole)?;
    Some((items.clone(), at))
}

/// The static answer to a hole: what the argument there must be.
fn answer_hole(c: &mut Checker, form: &Syntax) -> Option<Vec<String>> {
    let (items, at) = hole_position(c, form)?;
    if at == 0 {
        return Some(vec!["; FX-26 answers a hole in argument position, not as the operator".into()]);
    }
    let op = fixpt_read::write_syntax(&items[0], &c.interner);
    Some(match c.describe_argument(&items, at) {
        Some(t) => vec![format!("; the hole wants: {t}  (argument {at} of {op})")],
        None => vec![format!("; `{op}` is not a subroutine whose argument {at} can be known here")],
    })
}

// ------------------------------------------------ checking while typing

/// Reads with the Rust reader, and checks the form as it is typed — see
/// [`crate::speculate`]. A finished expression is also *run* as it is typed,
/// when its effect is licensed (`fixpt_fx26::licence`): its value is shown
/// before `Enter`, and nothing it could do is visible to the program.
struct Oracle<'a> {
    session: &'a mut Fx26Session,
    /// The eager reader written in FX-26, deciding what `Enter` does.
    reader: Option<&'a mut fixpt_scheme::eager::EagerReader>,
}

impl crate::lineedit::Oracle for Oracle<'_> {
    fn status(&mut self, text: &str, at_enter: bool) -> crate::lineedit::Status {
        match self.reader.as_deref_mut() {
            // A `,help` hole in FX-26 is answered once the form is entered,
            // so a hole mid-form is just an unfinished form.
            Some(r) => crate::eager_status(r, &mut self.session.scheme, text, at_enter, SyntaxProfile::FX26, false),
            None => crate::lineedit::Reread(SyntaxProfile::FX26).status(text, at_enter),
        }
    }

    fn notes(&mut self, text: &str) -> Vec<Note> {
        let Some(p) = crate::speculate::partial(text, SyntaxProfile::FX26) else {
            return Vec::new();
        };
        // Leave no trace: symbols read here are forgotten afterwards, so a
        // typo never turns up as a completion.
        let mark = self.session.checker.interner.len();
        let notes = speculative_notes(self.session, text, &p);
        self.session.checker.interner.truncate(mark);
        notes
    }
}

fn speculative_notes(session: &mut Fx26Session, text: &str, p: &crate::speculate::Partial) -> Vec<Note> {
    let notes = speculative_notes_now(session, text, p);
    if !notes.is_empty() || session.pending.is_empty() {
        return notes;
    }
    // Nothing else to say: what is waiting, and for what.
    let line = pending_line(session);
    vec![Note { span: None, message: line.trim_start_matches("; ").to_string(), error: false }]
}

fn speculative_notes_now(session: &mut Fx26Session, text: &str, p: &crate::speculate::Partial) -> Vec<Note> {
    let c = &mut session.checker;
    let Ok(forms) = c.read_in(FileId(0), &p.closed) else { return Vec::new() };
    // A finished entry of types that names types not defined yet would wait,
    // or complete what is waiting: said before what checking it alone finds.
    if p.finished(text) {
        use fixpt_fx26::session::Consider;
        let quote = |ns: Vec<String>| ns.iter().map(|n| format!("`{n}`")).collect::<Vec<_>>().join(", ");
        let message = match session.consider(&forms) {
            Consider::Pends(m) => Some(format!("pending when entered, awaiting definitions of: {}", quote(m))),
            Consider::Completes(n) => Some(format!("completes what is pending: {}", quote(n))),
            Consider::Run => None,
        };
        if let Some(message) = message {
            return vec![Note { span: None, message, error: false }];
        }
    }
    let c = &mut session.checker;
    // Each form is tried in the environment the ones before it would make,
    // and all of it is forgotten afterwards.
    let error = try_all(c, &forms, &mut |e| {
        let (start, end) = (e.span.start as usize, e.span.end as usize);
        (p.finished(text) || p.believe(start, end)).then(|| Note {
            span: char_span(text, start, end),
            message: e.message.clone(),
            error: true,
        })
    });
    if let Some(note) = error {
        return vec![note];
    }
    // One finished expression: run it early, if the licence allows.
    if p.finished(text)
        && let [form] = &forms[..]
    {
        use fixpt_fx26::session::Speculation;
        let message = match session.speculate(form) {
            Speculation::Value(v) => Some(format!("= {v}")),
            Speculation::Failed(e) => Some(format!("running it fails: {e}")),
            Speculation::NotLicensed(atom) => Some(format!("not run early: it may {atom}")),
            Speculation::Rejected(_) | Speculation::NotAnExpression => None,
        };
        return message.map(|message| vec![Note { span: None, message, error: false }]).unwrap_or_default();
    }
    let c = &mut session.checker;
    let hint = p.hole_form.as_ref().and_then(|h| {
        let form = c.read_in(FileId(0), h).ok()?.into_iter().next()?;
        let (items, at) = hole_position(c, &form)?;
        let want = c.describe_argument(&items, at)?;
        let op = fixpt_read::write_syntax(&items[0], &c.interner);
        Some(format!("argument {at} of {op} wants {want}"))
    });
    // Else what the grammar and the types around the hole say goes there.
    let hint = hint.or_else(|| {
        let forms: Vec<Syntax> =
            [&p.with_hole, &p.with_fill].into_iter().flatten().filter_map(|t| c.read_in(FileId(0), t).ok()?.into_iter().next()).collect();
        let next = c.describe_hole(&forms)?;
        // An operator could be anything; saying so says nothing.
        (!(p.hole_first && next == "an expression")).then(|| format!("next: {next}"))
    });
    hint.map(|message| vec![Note { span: None, message, error: false }]).unwrap_or_default()
}

/// Try `forms` in order, each in the scope of the ones before, keeping
/// nothing; the first error `judge` accepts is the answer.
fn try_all(
    c: &mut Checker,
    forms: &[Syntax],
    judge: &mut dyn FnMut(&fixpt_fx26::FxError) -> Option<Note>,
) -> Option<Note> {
    let (first, rest) = forms.split_first()?;
    c.try_top(first, |c, r| match r {
        Err(e) => judge(&e),
        Ok(_) => try_all(c, rest, judge),
    })
}

/// A byte span of `text` as characters, if it is a real one.
fn char_span(text: &str, start: usize, end: usize) -> Option<(usize, usize)> {
    if start >= end || end > text.len() {
        return None;
    }
    Some((text[..start].chars().count(), text[..end].chars().count()))
}

#[cfg(test)]
mod speculative {
    use super::*;
    use crate::lineedit::Oracle as _;

    fn notes_in(s: &mut Fx26Session, text: &str) -> Vec<Note> {
        let before = s.checker.interner.len();
        let notes = Oracle { session: s, reader: None }.notes(text);
        assert_eq!(s.checker.interner.len(), before, "checking left symbols behind");
        notes
    }

    fn session() -> Fx26Session {
        Fx26Session::with_backend(Backend::Ast).expect("starts")
    }

    fn notes(text: &str) -> Vec<Note> {
        notes_in(&mut session(), text)
    }

    #[test]
    fn an_error_in_a_finished_subform_is_reported_while_typing() {
        let n = notes("(+ 1 (car 5) ");
        assert_eq!(n.len(), 1, "{n:?}");
        assert!(n[0].error);
        // The argument itself, and the pair `+` needs one element of.
        assert_eq!(n[0].span, Some((10, 11)), "{n:?}");
        assert_eq!(n[0].message, "argument 1 is a int, where a (union nil (pairof int ? r)) is expected");
    }

    #[test]
    fn what_closing_off_would_break_is_not_reported() {
        for text in ["(if", "(if #t", "(+ 1", "(lambda ((x int))"] {
            assert!(notes(text).iter().all(|n| !n.error), "{text:?}: {:?}", notes(text));
        }
    }

    #[test]
    fn a_finished_form_is_judged_whole() {
        assert!(notes("(+ 1 #t)").first().is_some_and(|n| n.error));
    }

    /// A finished expression whose effect is licensed runs as it is typed,
    /// and its value is the hint.
    #[test]
    fn a_licensed_expression_shows_its_value_before_enter() {
        assert_eq!(notes("(+ 1 2)")[0].message, "= 3");
        assert_eq!(notes("(car (cons 1 #t))")[0].message, "= 1");
    }

    /// One that is not licensed says why, and does not run.
    #[test]
    fn an_unlicensed_expression_says_why_it_was_not_run() {
        let mut s = session();
        let forms = s.checker.read_in(FileId(0), "(define c (ref int @c) (new 1))").expect("reads");
        s.run(&forms[0]).expect("runs");
        assert_eq!(notes_in(&mut s, "(set c 5)")[0].message, "not run early: it may (write @c)");
        let forms = s.checker.read_in(FileId(0), "(define* peek (subr (read @c) () int) (lambda () (get c)))").expect("reads");
        s.run(&forms[0]).expect("runs");
        let forms = s.checker.read_in(FileId(0), "(peek)").expect("reads");
        assert_eq!(s.run(&forms[0]).expect("runs").value, Ok(Some("1".into())));
    }

    #[test]
    fn the_argument_at_the_cursor_is_described() {
        let n = notes("(+ 1 ");
        assert_eq!(n.len(), 1, "{n:?}");
        assert!(!n[0].error);
        assert_eq!(n[0].message, "argument 2 of + wants int");
    }

    /// The hint infers from the arguments already written: once `cons` has
    /// an int, its pair's first element is known, and the second is not.
    #[test]
    fn the_hint_solves_what_the_arguments_so_far_determine() {
        assert_eq!(notes("(car ")[0].message, "argument 1 of car wants (union nil (pairof t1 t2 r))");
        assert_eq!(notes("(set-car! (cons 1 #t) ")[0].message.split(" wants ").nth(1), Some("int"));
    }

    /// The hint under a form being typed, in a session where `t` is a sum
    /// of `x` and `y` and `v` one of them.
    fn next_after(text: &str) -> String {
        let mut s = session();
        let defs = "(define-type t (sumof (x int) (y int))) (define v (the t (sum x 3)))";
        for f in s.checker.read_in(FileId(0), defs).expect("reads") {
            s.checker.top(&f).expect("checks");
        }
        notes_in(&mut s, text).first().map(|n| n.message.clone()).unwrap_or_default()
    }

    /// What goes next, from the grammar and the types around the hole.
    #[test]
    fn the_hint_says_what_goes_next() {
        let cases = [
            // The tags an arm may still take, and none once all have one.
            ("(tagcase v ", "an arm `(tag name body …)` for `x` (int), `y` (int), or `(else name body …)`"),
            ("(tagcase v (x n n) ", "an arm `(tag name body …)` for `y` (int), or `(else name body …)`"),
            ("(tagcase v (x n n) (y m m) ", "nothing: every tag has an arm"),
            ("(lambda ((w t)) (tagcase w (y k k) ", "an arm `(tag name body …)` for `x` (int), or `(else name body …)`"),
            // The tags of the sum expected, then the payload's type.
            ("(the t (sum ", "a tag, then its value: `x` (int), `y` (int)"),
            ("(the t (sum x ", "an expression of type int"),
            ("(the int (if #t 1 ", "an expression of type int"),
            ("(the int (tagcase v (x n n) (y m ", "an expression of type int"),
            // The shape of the form the hole is in, innermost first.
            ("(if ", "`(if test then else)`"),
            ("(lambda (", "a parameter is `name` or `(name type)`"),
            ("(the (subr ", "`(subr effect (param …) result)`"),
            ("(define-type u ", "a type"),
        ];
        for (text, want) in cases {
            assert_eq!(next_after(text), format!("next: {want}"), "{text}");
        }
        // An operator could be anything: nothing is said.
        assert_eq!(next_after("(f ("), "");
    }

    /// A type naming one not defined yet would wait: said as it is typed,
    /// and then, while it waits, what it awaits; and what completes it.
    #[test]
    fn what_is_pending_is_said_while_typing() {
        let mut s = session();
        let tree = "(define-datatype tree (leaf int) (node forest))";
        assert_eq!(notes_in(&mut s, tree)[0].message, "pending when entered, awaiting definitions of: `forest`");
        let forms = s.checker.read_in(FileId(0), tree).expect("reads");
        s.hold(&forms);
        assert_eq!(notes_in(&mut s, "(+ 1 ")[0].message.split(" wants ").next(), Some("argument 2 of +"), "other notes first");
        assert_eq!(notes_in(&mut s, "(")[0].message, "pending: `tree`, `leaf`, `node`, awaiting definitions of: `forest`");
        let forest = "(define-datatype forest (fnil) (fcons tree forest))";
        assert_eq!(notes_in(&mut s, forest)[0].message, "completes what is pending: `tree`, `leaf`, `node`");
    }

    #[test]
    fn a_definition_being_typed_is_not_kept() {
        let mut s = session();
        assert!(notes_in(&mut s, "(define z 4) (+ z 1)").is_empty());
        let x = s.checker.read_in(FileId(0), "z").expect("reads");
        assert!(s.checker.top(&x[0]).is_err(), "a definition typed but not entered was kept");
    }
}

#[cfg(test)]
mod commands {
    use super::*;
    use crate::help::Helpful;

    #[test]
    fn known_names_include_definitions_types_and_keywords() {
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), "(define seven 7) (define-type cell (ref int @c))").expect("reads");
        for f in &forms {
            c.top(f).expect("checks");
        }
        let names = known_names(&c);
        for want in ["seven", "cell", "int", "cwcc", "lambda", "define-type"] {
            assert!(names.iter().any(|n| n == want), "missing {want:?}");
        }
    }

    #[test]
    fn describe_and_search() {
        let mut c = Checker::new();
        assert_eq!(c.describe("+"), ["+ : (subr pure (int int) int)"]);
        let returns = c.returns("bool").expect("typed");
        assert!(returns.iter().any(|l| l.starts_with("= :")), "{returns:?}");
        let fits = c.fits("int").expect("typed");
        assert!(fits.iter().any(|l| l.starts_with("+ :")), "{fits:?}");
    }

    #[test]
    fn a_hole_is_answered_from_the_operators_type() {
        let mut c = Checker::new();
        let forms = c.read_in(FileId(0), "(= 1 ,help)").expect("reads");
        let lines = answer_hole(&mut c, &forms[0]).expect("a hole");
        assert_eq!(lines, ["; the hole wants: int  (argument 2 of =)"]);
    }
}

/// "a type", "an effect": a kind of description, with its article.
fn a_kind(kind: &str) -> String {
    let article = if kind.starts_with(['a', 'e', 'i', 'o', 'u']) { "an" } else { "a" };
    let name = if kind == "family" { "type family" } else if kind == "generative" { "generative type" } else if kind == "region" { "private region" } else { kind };
    format!("{article} {name}")
}

/// `,native NAME [ARG…]`: the procedure the global NAME holds, compiled in
/// the native convention (`fixpt_native::direct`), with every procedure it
/// calls: its machine code shown, and, given integer ARGs, called on them.
/// What the compiler cannot do yet it says.
fn native(session: &mut Fx26Session, rest: &str) {
    if session.strategy != Strategy::Cellular {
        println!("; `,native` compiles what the compiler written in FX-26 makes: run with `--fx26-run cellular`.");
        return;
    }
    // `,native (E)`: E, as a procedure of no arguments, compiled and run.
    if rest.trim().starts_with('(') {
        let limit = session.step_limit().unwrap_or(u64::MAX >> 1);
        let shown = session.with_thunk(rest.trim(), |rt, closure| {
            let mut out = String::new();
            let r = fixpt_native::direct::with_machine(|m| {
                let procs = m.compile(&mut rt.heap, closure)?;
                out.push_str(&listing(m, &rt.heap, &procs, "E"));
                Ok::<_, String>(m.call(rt, procs[0].1, &[], limit).map(|v| fixpt_runtime::write_value(&rt.heap, v)))
            })??;
            match r {
                Ok(v) => out.push_str(&format!("{v}\n")),
                Err(t) => out.push_str(&format!("! {}\n", t.what)),
            }
            Ok::<String, String>(out)
        });
        match shown {
            Ok(Ok(Ok(out))) => print!("{out}"),
            Ok(Ok(Err(why))) => println!("; not compiled in the native convention yet: {why}"),
            Ok(Err(why)) => println!("! {why}"),
            Err(e) => println!("! {e}"),
        }
        return;
    }
    let mut words = rest.split_whitespace();
    let Some(name) = words.next() else {
        println!("; `,native NAME [ARG…]` or `,native (E)`: compiled in the native convention");
        return;
    };
    let args: Option<Vec<i64>> = words.map(|a| a.parse().ok()).collect();
    let Some(args) = args else {
        println!("; `,native` takes integer arguments only, for now");
        return;
    };
    let limit = session.step_limit().unwrap_or(u64::MAX >> 1);
    let shown = session.with_global_value(name, |rt, closure| {
        let mut m = fixpt_native::direct::DirectMachine::new()?;
        // Already native code (defined in the native convention): as it is.
        let (procs, mut out) = match fixpt_native::direct::DirectMachine::compiled_of(&rt.heap, closure) {
            Some(p) => (vec![(name.to_string(), p)], fixpt_native::direct::code_text(&rt.heap, closure).unwrap_or_default()),
            None => {
                let procs = m.compile(&mut rt.heap, closure)?;
                let out = listing(&m, &rt.heap, &procs, name);
                (procs, out)
            }
        };
        let p = procs[0].1;
        if !args.is_empty() || p.arity == 0 {
            if p.arity != usize::MAX && args.len() != p.arity {
                return Err(format!("`{name}` takes {} argument(s)", p.arity));
            }
            let vals: Vec<fixpt_heap::Value> = args.iter().map(|a| fixpt_heap::Value::fixnum(*a)).collect();
            let start = std::time::Instant::now();
            let r = m.call(rt, p, &vals, limit);
            let ms = 1e3 * start.elapsed().as_secs_f64();
            match r {
                Ok(v) => out.push_str(&format!("{}\n; ({ms:.3} ms)\n", fixpt_runtime::write_value(&rt.heap, v))),
                Err(t) => out.push_str(&format!("! {} ({ms:.3} ms)\n", t.what)),
            }
        }
        Ok::<String, String>(out)
    });
    match shown {
        Ok(Ok(Ok(out))) => print!("{out}"),
        Ok(Ok(Err(why))) => println!("; `{name}` is not compiled in the native convention yet: {why}"),
        Ok(Err(why)) => println!("! {why}"),
        Err(e) => println!("! {e}"),
    }
}

/// Each procedure compiled, its instructions one to a line; the first
/// named `name`.
fn listing(m: &fixpt_native::direct::DirectMachine, heap: &fixpt_heap::Heap, procs: &[(String, fixpt_native::direct::Compiled)], name: &str) -> String {
    let mut out = String::new();
    for (i, (n, p)) in procs.iter().enumerate() {
        let n = if i == 0 { format!("{name} ({n})") } else { n.clone() };
        out.push_str(&format!("; {n}, {} instructions:\n", p.len));
        for (i, w) in m.instructions(heap, *p).iter().enumerate() {
            out.push_str(&format!(";   {i:>4}  {}\n", fixpt_native::arm64::disasm::disassemble(*w, i as i64)));
        }
    }
    out
}

/// The session's runner for the native convention (`--calling-convention
/// native`): the expression's procedure compiled (`fixpt_native::direct`)
/// and called.
fn run_native(rt: &mut fixpt_runtime::Runtime, closure: fixpt_heap::Value, fuel: u64) -> fixpt_fx26::session::NativeRun {
    use fixpt_fx26::session::NativeRun;
    fixpt_native::direct::with_machine(|m| {
        let start = std::time::Instant::now();
        let compiled = m.compile(&mut rt.heap, closure);
        rt.compile_nanos += start.elapsed().as_nanos() as u64;
        let procs = match compiled {
            Ok(p) => p,
            Err(why) => return NativeRun::Declined(why),
        };
        NativeRun::Ran(m.call(rt, procs[0].1, &[], fuel).map_err(|t| t.what))
    })
    .unwrap_or_else(|e| NativeRun::Ran(Err(e)))
}

