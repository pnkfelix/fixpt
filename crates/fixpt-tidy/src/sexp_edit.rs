//! Structural edits of S-expression source (`sexp-edit`, `src/bin`).
//!
//! Editing FX-26 and Scheme source as text is fragile: an edit found by
//! exact text fails when the text has drifted, an inserted form with one
//! closing parenthesis too many breaks the file, and a helper defined after
//! its first use is found only by a slow load. So these edits address
//! definitions by name, through the reader's own spans, carry a
//! definition's comment block with it, and re-read the file before writing
//! it: an edit that would not parse is refused, and says where.

use fixpt_read::{Datum, FileId, Interner, Reader, Sym, Syntax, SyntaxProfile, TokenKind, tokens};

/// The reader's profile for a file, by extension.
pub fn profile_for(path: &str) -> SyntaxProfile {
    if path.ends_with(".fx") { SyntaxProfile::FX26 } else { SyntaxProfile::SCHEME }
}

/// A definition found in a file.
#[derive(Clone, Debug, PartialEq)]
pub struct Found {
    pub name: String,
    /// What defines it: `define`, `define-type`, `define-rec` (a member), …
    pub kind: String,
    /// The form's bytes.
    pub start: usize,
    pub end: usize,
    /// Where its leading comment block starts (`start` if it has none).
    pub lead: usize,
}

/// 1-based line and column of byte `at`.
pub fn line_col(text: &str, at: usize) -> (usize, usize) {
    let before = &text[..at.min(text.len())];
    let line = before.matches('\n').count() + 1;
    let col = before.len() - before.rfind('\n').map_or(0, |i| i + 1) + 1;
    (line, col)
}

fn read(text: &str, profile: SyntaxProfile) -> Result<(Vec<Syntax>, Interner), String> {
    let mut interner = Interner::new();
    let forms = Reader::new(text, FileId(0), profile, &mut interner).read_all();
    match forms {
        Ok(f) => Ok((f, interner)),
        Err(e) => {
            let (l, c) = line_col(text, e.span.start as usize);
            Err(format!("{l}:{c}: {}", e.message))
        }
    }
}

/// Whether `text` reads, and if not where it stops.
pub fn check(text: &str, profile: SyntaxProfile) -> Result<usize, String> {
    read(text, profile).map(|(f, _)| f.len())
}

fn items(s: &Syntax) -> &[Syntax] {
    match &s.datum {
        Datum::List { items, .. } => items,
        _ => &[],
    }
}

fn sym<'a>(s: &Syntax, i: &'a Interner) -> Option<&'a str> {
    s.as_symbol().map(|x: Sym| i.name(x))
}

/// Where the comment block directly above byte `start` begins: lines of
/// only a comment, with no blank line between them and the form.
fn lead_of(text: &str, start: usize) -> usize {
    let line_start = text[..start].rfind('\n').map_or(0, |i| i + 1);
    if !text[line_start..start].trim().is_empty() {
        return start;
    }
    let mut lead = line_start;
    while lead > 0 {
        let prev_end = lead - 1;
        let prev_start = text[..prev_end].rfind('\n').map_or(0, |i| i + 1);
        if text[prev_start..prev_end].trim_start().starts_with(';') {
            lead = prev_start;
        } else {
            break;
        }
    }
    if lead == line_start { start } else { lead }
}

/// Every definition in `text`: top-level ones, and the members of a
/// `define-rec` (`(define-rec (name type lambda) …)`).
pub fn definitions(text: &str, profile: SyntaxProfile) -> Result<Vec<Found>, String> {
    let (forms, i) = read(text, profile)?;
    let mut out = Vec::new();
    for f in &forms {
        let its = items(f);
        let Some(head) = its.first().and_then(|h| sym(h, &i)) else { continue };
        let mut push = |name: &str, s: &Syntax, kind: &str| {
            let (start, end) = (s.span.start as usize, s.span.end as usize);
            out.push(Found { name: name.to_string(), kind: kind.to_string(), start, end, lead: lead_of(text, start) });
        };
        match head {
            "define-rec" => {
                for m in &its[1..] {
                    if let Some(n) = items(m).first().and_then(|h| sym(h, &i)) {
                        push(n, m, "define-rec");
                    }
                }
            }
            h if h.starts_with("define") => {
                let Some(target) = its.get(1) else { continue };
                let name = sym(target, &i).or_else(|| items(target).first().and_then(|n| sym(n, &i)));
                if let Some(n) = name {
                    push(n, f, h);
                }
            }
            _ => {}
        }
    }
    Ok(out)
}

/// The definition `name` in `text`.
pub fn find(text: &str, profile: SyntaxProfile, name: &str) -> Result<Found, String> {
    let all = definitions(text, profile)?;
    let mut hits: Vec<Found> = all.into_iter().filter(|d| d.name == name).collect();
    match hits.len() {
        0 => Err(format!("no definition of `{name}`")),
        1 => Ok(hits.remove(0)),
        n => Err(format!("`{name}` is defined {n} times")),
    }
}

/// `text` with `[start, end)` replaced by `by`, refused unless it reads.
fn splice(text: &str, profile: SyntaxProfile, start: usize, end: usize, by: &str) -> Result<String, String> {
    let out = format!("{}{}{}", &text[..start], by, &text[end..]);
    check(&out, profile).map_err(|e| format!("the edit would not read: {e}"))?;
    Ok(out)
}

/// `new` must be whole forms, `n` of them if given.
fn whole(new: &str, profile: SyntaxProfile, n: Option<usize>) -> Result<(), String> {
    let got = check(new, profile).map_err(|e| format!("the new text does not read: {e}"))?;
    match n {
        Some(n) if n != got => Err(format!("the new text is {got} form(s), and {n} is expected")),
        _ => Ok(()),
    }
}

/// `new` indented, every line but the first, to column `col` (0-based) more
/// than it is.
fn indent(new: &str, col: usize) -> String {
    let pad = " ".repeat(col);
    let mut out = String::new();
    for (k, line) in new.trim_end_matches('\n').split('\n').enumerate() {
        if k > 0 {
            out.push('\n');
            if !line.is_empty() {
                out.push_str(&pad);
            }
        }
        out.push_str(line);
    }
    out
}

fn column_of(text: &str, at: usize) -> usize {
    line_col(text, at).1 - 1
}

/// Replace the definition `name` with `new`, one form: its form, and, if
/// `new` begins with a comment, its comment block too, which `new`'s
/// replaces.
pub fn replace(text: &str, profile: SyntaxProfile, name: &str, new: &str) -> Result<String, String> {
    whole(new, profile, Some(1))?;
    let d = find(text, profile, name)?;
    let from = if new.trim_start().starts_with(';') { d.lead } else { d.start };
    splice(text, profile, from, d.end, &indent(new, column_of(text, from)))
}

/// Insert `new`, whole forms (and comments), before the definition `name`
/// and its comments, at its indentation.
pub fn insert_before(text: &str, profile: SyntaxProfile, name: &str, new: &str) -> Result<String, String> {
    whole(new, profile, None)?;
    let d = find(text, profile, name)?;
    let col = column_of(text, d.lead);
    let by = format!("{}\n{}", indent(new, col), " ".repeat(col));
    splice(text, profile, d.lead, d.lead, &by)
}

/// Insert `new` after the definition `name`, on the next line, at its
/// indentation.
pub fn insert_after(text: &str, profile: SyntaxProfile, name: &str, new: &str) -> Result<String, String> {
    whole(new, profile, None)?;
    let d = find(text, profile, name)?;
    let col = column_of(text, d.lead);
    let by = format!("\n{}{}", " ".repeat(col), indent(new, col));
    splice(text, profile, d.end, d.end, &by)
}

/// Remove the definition `name`, with its comments: its lines, whole.
pub fn delete(text: &str, profile: SyntaxProfile, name: &str) -> Result<String, String> {
    let d = find(text, profile, name)?;
    let from = text[..d.lead].rfind('\n').map_or(0, |i| i + 1);
    let to = text[d.end..].find('\n').map_or(text.len(), |i| d.end + i + 1);
    if !text[from..d.lead].trim().is_empty() || !text[d.end..to].trim().is_empty() {
        return Err(format!("`{name}` shares a line with other text"));
    }
    let out = format!("{}{}", &text[..from], &text[to..]);
    check(&out, profile).map_err(|e| format!("the deletion would not read: {e}"))?;
    Ok(out)
}

/// Move the definition `name`, with its comments, to just before `other`.
pub fn move_before(text: &str, profile: SyntaxProfile, name: &str, other: &str) -> Result<String, String> {
    let d = find(text, profile, name)?;
    let o = find(text, profile, other)?;
    if o.lead >= d.lead && o.lead < d.end {
        return Err(format!("`{other}` is inside `{name}`"));
    }
    // The definition's lines, whole, from its comments to the end of its
    // last line.
    let from = text[..d.lead].rfind('\n').map_or(0, |i| i + 1);
    let to = text[d.end..].find('\n').map_or(text.len(), |i| d.end + i + 1);
    let block = &text[from..to];
    let without = format!("{}{}", &text[..from], &text[to..]);
    let at = if o.lead > from { o.lead - (to - from) } else { o.lead };
    let line = without[..at].rfind('\n').map_or(0, |i| i + 1);
    let out = format!("{}{}{}", &without[..line], block, &without[line..]);
    check(&out, profile).map_err(|e| format!("the move would not read: {e}"))?;
    Ok(out)
}

/// The lists `frag` opens less those it closes (strings, characters and
/// comments aside): a fragment of a form need not be one, but must keep the
/// balance of what it replaces.
fn depth(frag: &str, profile: SyntaxProfile) -> i64 {
    tokens(frag, profile)
        .iter()
        .map(|t| match t.kind {
            TokenKind::Open => 1,
            TokenKind::Close => -1,
            // `#(` and its kin open a list too.
            TokenKind::Hash if frag[t.start..t.end].ends_with('(') => 1,
            _ => 0,
        })
        .sum()
}

/// Replace the text `old`, found once within the definition `name`, by
/// `new`: an edit inside a definition. `old` and `new` need not be whole
/// forms, but must open and close as many lists as each other, and the
/// file must still read.
pub fn edit(text: &str, profile: SyntaxProfile, name: &str, old: &str, new: &str) -> Result<String, String> {
    let d = find(text, profile, name)?;
    let within = &text[d.lead..d.end];
    let at = match within.match_indices(old).map(|(i, _)| i).collect::<Vec<_>>()[..] {
        [] => return Err(format!("the old text is not in `{name}`")),
        [i] => d.lead + i,
        ref many => return Err(format!("the old text is in `{name}` {} times", many.len())),
    };
    let (was, is) = (depth(old, profile), depth(new, profile));
    if was != is {
        let how = if is > was { format!("leaves {} more list(s) open", is - was) } else { format!("closes {} more list(s)", was - is) };
        return Err(format!("the new text {how} than the old: it would unbalance `{name}`"));
    }
    splice(text, profile, at, at + old.len(), new)
}

/// Several edits in the definition `name` at once, each old text once in it
/// (as it was before any), balanced taken together: for a change that opens
/// a list in one place and closes it in another. Checked to read after.
pub fn edit_many(text: &str, profile: SyntaxProfile, name: &str, pairs: &[(&str, &str)]) -> Result<String, String> {
    let d = find(text, profile, name)?;
    let within = &text[d.lead..d.end];
    let mut at = Vec::new();
    for (k, (old, _)) in pairs.iter().enumerate() {
        match within.match_indices(old).map(|(i, _)| i).collect::<Vec<_>>()[..] {
            [] => return Err(format!("old text {} is not in `{name}`", k + 1)),
            [i] => at.push((d.lead + i, k)),
            ref many => return Err(format!("old text {} is in `{name}` {} times", k + 1, many.len())),
        }
    }
    at.sort();
    if at.windows(2).any(|w| w[0].0 + pairs[w[0].1].0.len() > w[1].0) {
        return Err(format!("two old texts overlap in `{name}`"));
    }
    let (was, is): (i64, i64) = pairs.iter().fold((0, 0), |(w, i), (o, n)| (w + depth(o, profile), i + depth(n, profile)));
    if was != is {
        let how = if is > was { format!("leave {} more list(s) open", is - was) } else { format!("close {} more list(s)", was - is) };
        return Err(format!("the new texts {how} than the old: they would unbalance `{name}`"));
    }
    let mut out = text.to_string();
    for &(i, k) in at.iter().rev() {
        out.replace_range(i..i + pairs[k].0.len(), pairs[k].1);
    }
    check(&out, profile).map_err(|e| format!("the edits would not read: {e}"))?;
    Ok(out)
}

/// Rename the symbol `old` to `new` (never in strings or comments), within
/// the definition `within` if given.
pub fn rename(text: &str, profile: SyntaxProfile, old: &str, new: &str, within: Option<&str>) -> Result<(String, usize), String> {
    let (lo, hi) = match within {
        Some(n) => {
            let d = find(text, profile, n)?;
            (d.start, d.end)
        }
        None => (0, text.len()),
    };
    let mut out = String::new();
    let (mut last, mut n) = (0, 0);
    for t in tokens(text, profile) {
        if t.kind == TokenKind::Symbol && t.start >= lo && t.end <= hi && &text[t.start..t.end] == old {
            out.push_str(&text[last..t.start]);
            out.push_str(new);
            last = t.end;
            n += 1;
        }
    }
    out.push_str(&text[last..]);
    check(&out, profile).map_err(|e| format!("the rename would not read: {e}"))?;
    Ok((out, n))
}

/// A use before its definition: the name, where it is used, and where it is
/// defined (byte offsets into the concatenation of `texts`, in order, and
/// the index of the text each is in).
#[derive(Debug, PartialEq)]
pub struct Early {
    pub name: String,
    pub used: (usize, usize),
    pub defined: (usize, usize),
}

/// Names used before their top-level definitions, across `texts` loaded in
/// order. Types and effects are declared ahead, so only values count; a
/// `define-rec`'s members may use each other; a definition may use itself.
/// A local binding of the same name shows up here too: this is a report to
/// read, not a proof.
pub fn order(texts: &[(String, SyntaxProfile)]) -> Result<Vec<Early>, String> {
    // Where each value is defined: (text, start, and the top-level form
    // around it, whose members may use each other).
    let mut defined: std::collections::HashMap<String, (usize, usize, usize, usize)> = std::collections::HashMap::new();
    for (k, (text, profile)) in texts.iter().enumerate() {
        let (forms, _) = read(text, *profile)?;
        for d in definitions(text, *profile)? {
            if matches!(d.kind.as_str(), "define" | "define-rec") {
                let group = forms
                    .iter()
                    .find(|f| (f.span.start as usize) <= d.start && d.start < f.span.end as usize)
                    .map_or((d.start, d.end), |f| (f.span.start as usize, f.span.end as usize));
                defined.entry(d.name).or_insert((k, d.start, group.0, group.1));
            }
        }
    }
    let mut out = Vec::new();
    for (k, (text, profile)) in texts.iter().enumerate() {
        let (forms, i) = read(text, *profile)?;
        let mut uses = Vec::new();
        for f in &forms {
            value_uses(f, &i, &mut Vec::new(), &mut uses);
        }
        for (name, at) in uses {
            let Some(&(dk, ds, gs, ge)) = defined.get(&name) else { continue };
            let in_group = k == dk && at >= gs && at < ge;
            if (k < dk || (k == dk && at < ds)) && !in_group {
                out.push(Early { name, used: (k, at), defined: (dk, ds) });
            }
        }
    }
    Ok(out)
}

/// The symbols in `s` that name a value not bound locally, with where: a
/// light walk of FX-26's binding forms (`lambda`, `plambda`, `let`, `let*`,
/// `letrec`, `tagcase` arms), skipping type positions (a definition's
/// signature, `the`'s type, types and effects defined).
fn value_uses(s: &Syntax, i: &Interner, bound: &mut Vec<String>, out: &mut Vec<(String, usize)>) {
    match &s.datum {
        Datum::Symbol(x) => {
            let n = i.name(*x);
            if !bound.iter().any(|b| b == n) {
                out.push((n.to_string(), s.span.start as usize));
            }
        }
        Datum::List { items: its, .. } => {
            let head = its.first().and_then(|h| sym(h, i)).unwrap_or("");
            let name_of = |b: &Syntax| sym(b, i).or_else(|| items(b).first().and_then(|n| sym(n, i))).map(str::to_string);
            let depth = bound.len();
            match head {
                "define-type" | "define-datatype" | "define-effect" | "define-generative" | "private-regions" | "quote" => {}
                // `(define name type expression)`: the type is skipped.
                "define" => {
                    if let Some(e) = its.last().filter(|_| its.len() >= 3) {
                        value_uses(e, i, bound, out);
                    }
                }
                "the" => {
                    if let Some(e) = its.get(2) {
                        value_uses(e, i, bound, out);
                    }
                }
                "lambda" | "plambda" => {
                    if let Some(ps) = its.get(1) {
                        bound.extend(items(ps).iter().filter_map(name_of));
                    }
                    for b in its.iter().skip(2) {
                        value_uses(b, i, bound, out);
                    }
                }
                "let" | "letrec" | "let*" => {
                    let bs = its.get(1).map(items).unwrap_or(&[]);
                    for b in bs {
                        let parts = items(b);
                        if head == "let*" || head == "let" {
                            if let Some(e) = parts.last().filter(|_| parts.len() >= 2) {
                                value_uses(e, i, bound, out);
                            }
                        }
                        if head != "let" {
                            bound.extend(parts.first().and_then(|n| sym(n, i)).map(str::to_string));
                        }
                    }
                    if head == "letrec" {
                        for b in bs {
                            if let Some(e) = items(b).last() {
                                value_uses(e, i, bound, out);
                            }
                        }
                    }
                    if head == "let" {
                        bound.extend(bs.iter().filter_map(|b| items(b).first().and_then(|n| sym(n, i)).map(str::to_string)));
                    }
                    for b in its.iter().skip(2) {
                        value_uses(b, i, bound, out);
                    }
                }
                "tagcase" => {
                    if let Some(e) = its.get(1) {
                        value_uses(e, i, bound, out);
                    }
                    for arm in its.iter().skip(2) {
                        let parts = items(arm);
                        let d = bound.len();
                        if let Some(x) = parts.get(1) {
                            match &x.datum {
                                Datum::Symbol(_) => bound.extend(sym(x, i).map(str::to_string)),
                                _ => bound.extend(items(x).iter().filter_map(|n| sym(n, i).map(str::to_string))),
                            }
                        }
                        for b in parts.iter().skip(2) {
                            value_uses(b, i, bound, out);
                        }
                        bound.truncate(d);
                    }
                }
                _ => {
                    for x in its {
                        value_uses(x, i, bound, out);
                    }
                }
            }
            bound.truncate(depth);
        }
        _ => {}
    }
}
