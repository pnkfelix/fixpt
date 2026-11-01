//! Types as reps (`docs/research/heap-types.md`, step 1): every type the
//! test programs define, exported by the Rust checker, imported, and
//! exported again, is the same rep, and prints as it did; and each rep reads
//! back as itself from its binary form and its readable one.

use fixpt_fx26::{Checker, Top};
use fixpt_read::FileId;

mod common;

const DIRS: &[&str] = &[
    "bidirectional", "bloblet", "control", "run", "pldi89", "regions", "datum", "recursive", "terminate", "generative", "lemmas", "sizes",
    "conventions", "redefine", "modules", "higher-kinds", "unions", "io", "processes", "arrows", "specs", "globals",
];

#[test]
fn every_defined_type_is_its_rep_and_back() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let (mut wrong, mut types, mut declined) = (Vec::new(), 0, Vec::new());
    for sub in DIRS {
        let mut paths: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
        paths.sort();
        for path in paths {
            let name = format!("{sub}/{}", path.file_name().unwrap().to_string_lossy());
            let program = std::fs::read_to_string(&path).unwrap();
            let mut c = Checker::new();
            c.base_dir = path.parent().map(|d| d.to_path_buf());
            let Ok(forms) = c.read_in(FileId(0), &program) else { continue };
            for f in &forms {
                let tys = match c.top(f) {
                    Ok(Top::Define { name: n, ty, .. }) => vec![(n, ty)],
                    Ok(Top::DefineRec { bindings, .. }) => bindings.iter().map(|(n, t, _)| (*n, *t)).collect(),
                    Ok(_) => continue,
                    Err(_) => break,
                };
                for (n, t) in tys {
                    let what = format!("{name}: `{}`", c.interner.name(n));
                    match round_trip(&mut c, t) {
                        Ok(true) => types += 1,
                        Ok(false) => declined.push(what),
                        Err(e) => wrong.push(format!("{what}: {e}")),
                    }
                }
            }
        }
    }
    println!("{types} types through their reps and back; {} declined: {declined:?}", declined.len());
    assert!(wrong.is_empty(), "{} of {} types wrong:\n{}", wrong.len(), types + wrong.len(), wrong.join("\n"));
    assert!(types >= 1000, "only {types} types exported");
    // None declined: every type the programs define is taken (an
    // unresolved `select`, the one it declines, is never a definition's).
    assert!(declined.is_empty(), "{} declined:\n{}", declined.len(), declined.join("\n"));
}

/// Type `t` through its rep and back: `Ok(true)` if all agrees, `Ok(false)`
/// if export declines it (what it does not take yet), else what differs.
fn round_trip(c: &mut Checker, t: fixpt_fx26::ast::TyId) -> Result<bool, String> {
    let Ok(ex) = c.export_ty(t) else { return Ok(false) };
    let back = c.import_rep(&ex.rep, &ex.holes)?;
    let again = c.export_ty(back)?;
    if again.rep != ex.rep || again.holes != ex.holes {
        return Err(format!("exported again, another rep:\n  {}\n  {}", fixpt_reps::text::write(&ex.rep), fixpt_reps::text::write(&again.rep)));
    }
    let (was, now) = (c.show_ty_expanded(t), c.show_ty_expanded(back));
    if was != now {
        return Err(format!("prints otherwise: `{was}`, now `{now}`"));
    }
    let bytes = fixpt_reps::binary::encode(&ex.rep);
    if fixpt_reps::binary::decode(&bytes, true)? != ex.rep {
        return Err("its binary form reads back otherwise".into());
    }
    let text = fixpt_reps::text::write(&ex.rep);
    if fixpt_reps::text::read(&text)? != ex.rep {
        return Err(format!("its readable form reads back otherwise: {text}"));
    }
    Ok(true)
}

/// The two checkers' reps of each type a test program defines are one rep
/// (`docs/research/heap-types.md`, step 2): the agreement, by reps, not by
/// printed lines. Each program both checkers take.
#[test]
fn both_checkers_export_each_type_as_one_rep() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let (mut wrong, mut agreed) = (Vec::new(), 0);
    common::with_own(|s| {
        for sub in DIRS {
            let mut paths: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
            paths.sort();
            for path in paths {
                let name = format!("{sub}/{}", path.file_name().unwrap().to_string_lossy());
                let program = std::fs::read_to_string(&path).unwrap();
                let base = path.parent().map(|d| d.to_path_buf());
                // The FX-26 checker's, if it takes the whole program.
                let outer = std::mem::replace(&mut s.checker.base_dir, base.clone());
                let ours = s.check_with_own_checker(&program).ok().and_then(|r| r.ok()).and_then(|_| s.own_checked_reps().ok());
                s.checker.base_dir = outer;
                let Some(ours) = ours else { continue };
                // The Rust checker's, of each form it takes.
                let mut c = Checker::new();
                c.base_dir = base;
                let Ok(forms) = c.read_in(FileId(0), &program) else { continue };
                let mut rust: Vec<(String, Vec<u8>)> = Vec::new();
                for f in &forms {
                    let tys = match c.top(f) {
                        Ok(Top::Define { name: n, ty, .. }) => vec![(n, ty)],
                        Ok(Top::DefineRec { bindings, .. }) => bindings.iter().map(|(n, t, _)| (*n, *t)).collect(),
                        Ok(_) => continue,
                        Err(_) => break,
                    };
                    for (n, t) in tys {
                        if let Ok(ex) = c.export_ty(t) {
                            rust.push((c.interner.name(n).to_string(), fixpt_reps::binary::encode(&ex.rep)));
                        }
                    }
                }
                for (n, bytes) in &ours {
                    // The latest of the name's, as a redefinition leaves it.
                    let Some((_, theirs)) = rust.iter().rev().find(|(m, _)| m == n) else { continue };
                    if theirs == bytes {
                        agreed += 1;
                    } else {
                        let show = |b: &[u8]| fixpt_reps::binary::decode(b, true).map(|r| fixpt_reps::text::write(&r)).unwrap_or_else(|e| e);
                        wrong.push(format!("{name}: `{n}`:\n  FX-26 {}\n  Rust  {}", show(bytes), show(theirs)));
                    }
                }
            }
        }
    });
    println!("{agreed} types one rep in both checkers; {} not", wrong.len());
    assert!(wrong.is_empty(), "{} of {} differ:\n{}", wrong.len(), agreed + wrong.len(), wrong.iter().take(40).cloned().collect::<Vec<_>>().join("\n"));
    assert!(agreed >= 850, "only {agreed} compared");
}

/// The FX-26 checker's import gives back the rep it took: each type a test
/// program defines, exported, imported and exported again, the same rep.
#[test]
fn the_fx26_checker_imports_each_rep_as_its_type() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/programs");
    let (mut wrong, mut same) = (Vec::new(), 0);
    common::with_own(|s| {
        for sub in DIRS {
            let mut paths: Vec<_> = std::fs::read_dir(format!("{dir}/{sub}")).unwrap().map(|e| e.unwrap().path()).collect();
            paths.sort();
            for path in paths {
                let name = format!("{sub}/{}", path.file_name().unwrap().to_string_lossy());
                let program = std::fs::read_to_string(&path).unwrap();
                let outer = std::mem::replace(&mut s.checker.base_dir, path.parent().map(|d| d.to_path_buf()));
                let ok = s.check_with_own_checker(&program).ok().and_then(|r| r.ok()).is_some();
                let again = if ok { s.own_checked_reps_again() } else { Ok(Vec::new()) };
                s.checker.base_dir = outer;
                match again {
                    Ok(reps) => {
                        for (n, r, back) in reps {
                            if r == back {
                                same += 1;
                            } else {
                                let show = |b: &[u8]| fixpt_reps::binary::decode(b, true).map(|r| fixpt_reps::text::write(&r)).unwrap_or_else(|e| e);
                                wrong.push(format!("{name}: `{n}`:\n  was   {}\n  again {}", show(&r), show(&back)));
                            }
                        }
                    }
                    Err(e) => wrong.push(format!("{name}: {}", e.message)),
                }
            }
        }
    });
    println!("{same} types through the FX-26 checker's reps and back; {} not", wrong.len());
    assert!(wrong.is_empty(), "{} wrong:\n{}", wrong.len(), wrong.iter().take(30).cloned().collect::<Vec<_>>().join("\n"));
    assert!(same >= 850, "only {same}");
}
