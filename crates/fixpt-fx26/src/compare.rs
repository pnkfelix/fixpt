//! Both checkers and both compilers on one program, side by side: what the
//! agreement tests compare, and what `fixpt check` and `fixpt compile` show.

use crate::check::Checker;
use crate::error::R;
use crate::session::Fx26Session;
use crate::syn::Checked26;
use crate::top::Top;
use fixpt_heap::Value;
use fixpt_read::FileId;

/// What the Rust checker makes of `text`, as the FX-26 one says it (see
/// [`Checked26`]); under redefinition, each form with what it runs again.
pub fn check_with_rust_checker(c: &mut Checker, text: &str) -> Checked26 {
    let forms = c.read_in(FileId(0), text)?;
    let done = c.declare_ahead(&forms)?;
    let mut out = Vec::new();
    for (f, done) in forms.iter().zip(done) {
        if done {
            continue;
        }
        let done = c.top_defining(f)?;
        for (top, _) in done.hoisted.into_iter().chain(done.run) {
            match top {
                Top::Define { name, ty, effect, .. } => {
                    out.push(format!("define {} : {} ! {}", c.interner.name(name), c.show_ty(ty), c.show_effect(&effect)))
                }
                Top::DefineRec { bindings, .. } => {
                    for (name, ty, _) in bindings {
                        out.push(format!("define {} : {} ! pure", c.interner.name(name), c.show_ty(ty)))
                    }
                }
                Top::Exp(k) => out.push(format!("{} ! {}", c.show_ty(k.ty), c.show_effect(&k.effect))),
                _ => {}
            }
        }
    }
    Ok(out)
}

/// `s` with each `(maxeff …)`'s atoms sorted, as the two checkers may list
/// them in different orders.
pub fn canonical(s: &str) -> String {
    let mut out = String::new();
    let mut rest = s;
    while let Some(i) = rest.find("(maxeff ") {
        out.push_str(&rest[..i]);
        let inner = &rest[i + "(maxeff ".len()..];
        let (mut depth, mut end, mut items, mut start) = (0, inner.len(), Vec::new(), 0);
        for (j, c) in inner.char_indices() {
            match c {
                '(' => depth += 1,
                ')' if depth == 0 => {
                    end = j;
                    break;
                }
                ')' => depth -= 1,
                ' ' if depth == 0 => {
                    items.push(&inner[start..j]);
                    start = j + 1;
                }
                _ => {}
            }
        }
        items.push(&inner[start..end]);
        items.sort();
        out.push_str(&format!("(maxeff {})", items.join(" ")));
        rest = &inner[(end + 1).min(inner.len())..];
    }
    out.push_str(rest);
    out
}

/// [`canonical`] on each line, and on the error's message.
pub fn canonical_checked(r: Checked26) -> Checked26 {
    r.map(|ls| ls.iter().map(|l| canonical(l)).collect()).map_err(|mut e| {
        e.message = canonical(&e.message);
        e
    })
}

/// Both checkers on `text`, canonical: the FX-26 one's, then the Rust
/// one's, with `s`'s convention. The outer error is the FX-26 front end
/// failing to read or parse.
pub fn both_checkers(s: &mut Fx26Session, text: &str) -> R<(Checked26, Checked26)> {
    // With `FIXPT_TIME_PHASES` set, how long each checker took.
    let timing = std::env::var_os("FIXPT_TIME_PHASES").is_some();
    let started = std::time::Instant::now();
    let fx26 = canonical_checked(s.check_with_own_checker(text)?);
    let between = std::time::Instant::now();
    let mut c = s.fresh_checker();
    let rust = canonical_checked(check_with_rust_checker(&mut c, text));
    if timing {
        eprintln!("; the FX-26 checker {:.3} s, the Rust checker {:.3} s", (between - started).as_secs_f64(), between.elapsed().as_secs_f64());
    }
    Ok((fx26, rust))
}

/// Both compilers' code for `text`, disassembled, with register code: the
/// FX-26 one's, given what the Rust checker found, then the Rust one's; or
/// why either made none. The outer error is the program not checking.
pub fn both_compilers(s: &mut Fx26Session, text: &str) -> R<(Result<String, String>, Result<String, String>)> {
    both_compilers_declining(s, text).map(|(fx26, rust, _)| (fx26, rust))
}

/// `both_compilers`, and a line for each procedure the Rust compiler made
/// no register code for, and why: such a procedure runs as cellular code,
/// however it is called.
pub fn both_compilers_declining(s: &mut Fx26Session, text: &str) -> R<(Result<String, String>, Result<String, String>, String)> {
    let mut c = s.fresh_checker();
    let forms = c.read_in(FileId(0), text)?;
    let done = c.declare_ahead(&forms)?;
    let mut tops = Vec::new();
    for (f, done) in forms.iter().zip(done) {
        if !done {
            tops.extend(c.top_all(f)?);
        }
    }
    s.load_own_pieces()?;
    let limit = s.step_limit();
    s.scheme.engine.set_step_limit(None);
    let out = s.scheme.scope(|sc| {
        let facts = crate::syn::rust_facts(sc, FileId(0), text)?;
        let fx26 = crate::syn::compile_to_word_with_registers(sc, FileId(0), text, facts)?;
        let fx26 = fx26.map(|w| {
            let mut shown = String::new();
            sc.make(|m| {
                let w = m.get(w);
                shown = fixpt_runtime::disasm::disassemble(m.heap(), w);
                w
            });
            shown
        });
        let mut rust = Err(String::new());
        let mut declined = String::new();
        sc.make(|m| {
            let mut comp = crate::cellular::Compiler::new(m.heap(), &c, text);
            comp.registers = true;
            let word = comp.program(&tops);
            declined =
                comp.register_report.iter().filter_map(|(n, why)| why.as_ref().map(|w| format!("; `{n}`: no register code: {w}\n"))).collect();
            drop(comp);
            rust = word.map(|w| fixpt_runtime::disasm::disassemble(m.heap(), w));
            Value::NULL
        });
        Ok((fx26, rust, declined))
    });
    s.scheme.engine.set_step_limit(limit);
    out
}
