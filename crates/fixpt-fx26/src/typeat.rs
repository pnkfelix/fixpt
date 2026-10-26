//! `type-at` (Heist's, `FIXPT-CHANGES.md` F3): what the checker says of a
//! program text at a place, for an editor written in FX-26 to show. The text
//! is checked by the checker written in Rust, keeping each expression's type
//! (`Checker::record_types`, as the verifier does), and the innermost
//! expression of the text itself (not of a file it loads) whose span holds
//! the place is given, with its type, as `%fx26-type-at` says it: `START END
//! TYPE`, or `error START END MESSAGE` for the first refusal, up to the
//! form the place is in (what follows it is not checked). Places are in
//! characters, as FX-26's strings count them; spans are bytes.

use crate::check::Checker;
use crate::top::Top;
use fixpt_read::FileId;

/// The byte offset of character `c` of `text` (its end, past the last).
fn byte_of(text: &str, c: i64) -> usize {
    if c <= 0 {
        return 0;
    }
    text.char_indices().nth(c as usize).map(|(b, _)| b).unwrap_or(text.len())
}

/// The character offset of byte `b` of `text`.
fn char_of(text: &str, b: usize) -> usize {
    text[..b.min(text.len())].chars().count()
}

pub fn type_at(text: &str, pos: i64) -> String {
    let mut c = Checker::new();
    c.record_types = true;
    let at = byte_of(text, pos);
    // Checked up to the form the place is in: a definition sees only those
    // before it, so what comes after cannot change the type there, and a
    // mistake further down should not hide it.
    let checked = (|| {
        let forms = c.read_in(FileId(0), text)?;
        let done = c.declare_ahead(&forms)?;
        for (f, done) in forms.iter().zip(done) {
            if !done {
                let _: Top = c.top(f)?;
            }
            if f.span.file == FileId(0) && f.span.end as usize >= at {
                break;
            }
        }
        Ok::<(), crate::FxError>(())
    })();
    if let Err(e) = checked {
        let (a, b) = if e.span.file == FileId(0) { (e.span.start as usize, e.span.end as usize) } else { (0, 0) };
        let message = e.message.lines().next().unwrap_or("").to_string();
        return format!("error {} {} {}", char_of(text, a), char_of(text, b), message);
    }
    let mut best: Option<(usize, usize, crate::ast::TyId)> = None;
    for (&e, &t) in c.facts.types.iter() {
        let span = c.arena.span_of(e);
        let (start, end) = (span.start as usize, span.end as usize);
        if span.file != FileId(0) || start > at || at > end {
            continue;
        }
        if best.is_none_or(|(a, b, _)| end - start < b - a) {
            best = Some((start, end, t));
        }
    }
    match best {
        Some((a, b, t)) => format!("{} {} {}", char_of(text, a), char_of(text, b), named(&mut c, t)),
        None => format!("error {pos} {pos} no expression here"),
    }
}

/// Type `t` printed with each compound type a `define-type` names shown
/// by its name. The checker keeps a name only for data that mentions no
/// variable (`closed_named`): a copy of any other type, a `subr`'s or a
/// product's holding one, prints expanded, and an editor's types run to
/// hundreds of characters. So `t` and each named type are printed with no
/// names at all, and each named type's text in `t`'s is put back as its
/// name, longest first, so that a name inside another's expansion goes
/// back first. Names of a single word (an alias of `int`) are left.
fn named(c: &mut Checker, t: crate::ast::TyId) -> String {
    // Each named type as checking sees it: a module's types and effects
    // selected (`(select core turn-eff)` read before `core` was known)
    // replaced by what they are, as a copy made in checking has them.
    let named: Vec<(fixpt_read::Sym, crate::ast::TyId)> =
        c.type_names().into_iter().filter_map(|n| c.type_named(n).map(|d| (n, d))).collect();
    // A module's effect read as `(select m e)` is an effect variable; each
    // replaced by the effect `m` defines.
    let mut map = std::collections::HashMap::new();
    for ((m, e), v) in c.effect_selects.clone() {
        if let Ok(x) = c.selected_effect(m, e, fixpt_read::Span::new(FileId(0), 0, 0)) {
            map.insert(v, crate::ast::D::Effect(x));
        }
    }
    // A type read as `(select m t)`, a module's, as what `m`'s type says it
    // is, before anything else.
    let selected = |c: &Checker, d: crate::ast::TyId| -> crate::ast::TyId {
        if let crate::ast::Ty::Select(m, n) = c.arena.get(c.arena.resolve(d)).clone()
            && let Some(mt) = c.type_of_name(m)
            && let crate::ast::Ty::Module { descs, .. } = c.arena.get(c.arena.resolve(mt)).clone()
            && let Some((_, x)) = descs.iter().find(|(k, _)| *k == n)
        {
            return *x;
        }
        d
    };
    // And everywhere inside types: each module a name selects from, all its
    // descriptions known to substitution (`select_map`), which then also
    // applies a family it finds applied (`(actor buffer)` in `frame`).
    for &(_, d) in &named {
        if let crate::ast::Ty::Select(m, _) = c.arena.get(c.arena.resolve(d)).clone()
            && let Some(mt) = c.type_of_name(m)
            && let crate::ast::Ty::Module { descs, .. } = c.arena.get(c.arena.resolve(mt)).clone()
        {
            for (k, x) in descs {
                c.select_map.insert((m, k), x);
            }
        }
    }
    let named: Vec<(fixpt_read::Sym, crate::ast::TyId)> = named.into_iter().map(|(n, d)| (n, selected(c, d))).collect();
    let defs: Vec<(fixpt_read::Sym, crate::ast::TyId)> = named.into_iter().map(|(n, d)| (n, c.subst(d, &map))).collect();
    // The families of one type parameter (`(actor s)`, a module's), each
    // applied to each named type and the base types: `(actor frame)`.
    let mut families = Vec::new();
    let mut plain = Vec::new();
    for &(n, d) in &defs {
        match c.arena.get(c.arena.resolve(d)).clone() {
            crate::ast::Ty::Lam { params, body: crate::ast::D::Type(b) } if params.len() == 1 && params[0].1 == crate::ast::Kind::Type => {
                families.push((n, params[0].0, b))
            }
            crate::ast::Ty::Lam { .. } => {}
            _ => plain.push((c.interner.name(n).to_string(), d)),
        }
    }
    c.print_expanded.set(true);
    let mut out = c.show_ty(t);
    // Each named type with what it prints as, written out.
    let printed: Vec<(String, crate::ast::TyId, String)> =
        plain.iter().map(|(name, d)| (name.clone(), *d, c.show_ty(*d))).collect();
    let mut names: Vec<(String, String)> =
        printed.iter().filter(|(_, _, e)| e.starts_with('(')).map(|(n, _, e)| (e.clone(), n.clone())).collect();
    // A family is applied only to what is in the type printed: if
    // `(actor frame)` is there written out, so is `frame`. (Each family
    // applied to every named type cost 0.4 s a query on the editor.)
    let mut args: Vec<(String, crate::ast::TyId)> =
        printed.iter().filter(|(_, _, e)| e.starts_with('(') && out.contains(e.as_str())).map(|(n, d, _)| (n.clone(), *d)).collect();
    c.print_expanded.set(false);
    for b in ["int", "string", "bool", "char", "unit"] {
        if let Some(&t) = c.base.get(&c.interner.intern(b)) {
            args.push((b.to_string(), t));
        }
    }
    let mut instances = Vec::new();
    for &(f, p, b) in &families {
        for (an, at) in &args {
            let mut m = map.clone();
            m.insert(p, crate::ast::D::Type(*at));
            instances.push((format!("({} {})", c.interner.name(f), an), c.subst(b, &m)));
        }
    }
    c.print_expanded.set(true);
    for (name, d) in instances {
        let expanded = c.show_ty(d);
        if expanded.starts_with('(') {
            names.push((expanded, name));
        }
    }
    c.print_expanded.set(false);
    names.sort_by(|a, b| b.0.len().cmp(&a.0.len()).then(a.1.cmp(&b.1)));
    names.dedup_by(|a, b| a.0 == b.0);
    for (expanded, name) in &names {
        if out.contains(expanded.as_str()) {
            out = out.replace(expanded.as_str(), name);
        }
    }
    out
}
