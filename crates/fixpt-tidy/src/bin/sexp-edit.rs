//! `sexp-edit`: structural edits of FX-26 and Scheme source, by definition
//! name (`fixpt_tidy::sexp_edit`). Every edit is re-read before it is
//! written; one that would not read is refused.
//!
//!     sexp-edit list FILE                      the definitions, where
//!     sexp-edit find FILE NAME                 one definition, printed
//!     sexp-edit check FILE…                    whether each reads
//!     sexp-edit replace FILE NAME NEW          NEW: a file, or - for stdin
//!     sexp-edit insert-before FILE NAME NEW
//!     sexp-edit insert-after FILE NAME NEW
//!     sexp-edit move FILE NAME OTHER           NAME, with its comments, before OTHER
//!     sexp-edit delete FILE NAME               NAME, with its comments
//!     sexp-edit rename FILE OLD NEW [WITHIN]   symbols only; within one definition
//!     sexp-edit edit FILE NAME OLD NEW …       text OLD, once in NAME, to NEW (files, or
//!                                              - for one); as many lists opened as closed,
//!                                              over all the pairs, applied at once
//!     sexp-edit order FILE…                    values used before defined, in load order

use std::io::Read;
use std::process::ExitCode;

use fixpt_tidy::sexp_edit as se;

fn slurp(path: &str) -> Result<String, String> {
    if path == "-" {
        let mut s = String::new();
        std::io::stdin().read_to_string(&mut s).map_err(|e| e.to_string())?;
        Ok(s)
    } else {
        std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))
    }
}

fn write(path: &str, text: &str) -> Result<(), String> {
    std::fs::write(path, text).map_err(|e| format!("{path}: {e}"))
}

fn run(args: &[String]) -> Result<(), String> {
    let usage = "usage: sexp-edit list|find|check|replace|insert-before|insert-after|move|move-to|delete|rename|edit|order …";
    let (cmd, rest) = args.split_first().ok_or(usage)?;
    let at = |text: &str, i: usize| {
        let (l, c) = se::line_col(text, i);
        format!("{l}:{c}")
    };
    match (cmd.as_str(), rest) {
        ("list", [file]) => {
            let text = slurp(file)?;
            for d in se::definitions(&text, se::profile_for(file))? {
                println!("{file}:{} {} {}", at(&text, d.start), d.kind, d.name);
            }
            Ok(())
        }
        ("find", [file, name]) => {
            let text = slurp(file)?;
            let d = se::find(&text, se::profile_for(file), name)?;
            println!("{file}:{}-{} {}", at(&text, d.start), at(&text, d.end), d.kind);
            println!("{}", &text[d.lead..d.end]);
            Ok(())
        }
        ("check", files) if !files.is_empty() => {
            let mut bad = false;
            for f in files {
                match se::check(&slurp(f)?, se::profile_for(f)) {
                    Ok(n) => println!("{f}: {n} forms"),
                    Err(e) => {
                        println!("{f}:{e}");
                        bad = true;
                    }
                }
            }
            if bad { Err("some files do not read".into()) } else { Ok(()) }
        }
        (op @ ("replace" | "insert-before" | "insert-after"), [file, name, new]) => {
            let (text, new) = (slurp(file)?, slurp(new)?);
            let p = se::profile_for(file);
            let out = match op {
                "replace" => se::replace(&text, p, name, &new),
                "insert-before" => se::insert_before(&text, p, name, &new),
                _ => se::insert_after(&text, p, name, &new),
            }
            .map_err(|e| format!("{file}: {e}"))?;
            write(file, &out)?;
            println!("{file}: {op} `{name}`");
            Ok(())
        }
        ("move", [file, name, other]) => {
            let text = slurp(file)?;
            let out = se::move_before(&text, se::profile_for(file), name, other).map_err(|e| format!("{file}: {e}"))?;
            write(file, &out)?;
            println!("{file}: moved `{name}` before `{other}`");
            Ok(())
        }
        // The whole top-level form holding `name` (its `define-rec` group,
        // if it is a member), with its comments, into another file.
        ("move-to", [file, name, other, anchor]) => {
            let (from, to) = (slurp(file)?, slurp(other)?);
            let (from2, to2) = se::move_to(&from, &to, se::profile_for(file), name, anchor).map_err(|e| format!("{file} → {other}: {e}"))?;
            write(file, &from2)?;
            write(other, &to2)?;
            println!("{file}: moved `{name}`'s form to {other}, before `{anchor}`'s");
            Ok(())
        }
        ("delete", [file, name]) => {
            let text = slurp(file)?;
            let out = se::delete(&text, se::profile_for(file), name).map_err(|e| format!("{file}: {e}"))?;
            write(file, &out)?;
            println!("{file}: deleted `{name}`");
            Ok(())
        }
        ("rename", [file, old, new, within @ ..]) if within.len() <= 1 => {
            let text = slurp(file)?;
            let (out, n) = se::rename(&text, se::profile_for(file), old, new, within.first().map(|s| s.as_str()))
                .map_err(|e| format!("{file}: {e}"))?;
            write(file, &out)?;
            println!("{file}: renamed {n} `{old}` to `{new}`");
            Ok(())
        }
        ("edit", [file, name, rest @ ..]) if rest.len() > 2 && rest.len() % 2 == 0 => {
            let text = slurp(file)?;
            let texts: Vec<String> = rest.iter().map(|p| slurp(p).map(|t| t.strip_suffix('\n').map(str::to_string).unwrap_or(t))).collect::<Result<_, _>>()?;
            let pairs: Vec<(&str, &str)> = texts.chunks(2).map(|c| (c[0].as_str(), c[1].as_str())).collect();
            let out = se::edit_many(&text, se::profile_for(file), name, &pairs).map_err(|e| format!("{file}: {e}"))?;
            write(file, &out)?;
            println!("{file}: edited `{name}` in {} places", pairs.len());
            Ok(())
        }
        ("edit", [file, name, old, new]) => {
            let (text, old, new) = (slurp(file)?, slurp(old)?, slurp(new)?);
            // A fragment in a file ends where its last line does.
            let (old, new) = (old.strip_suffix('\n').unwrap_or(&old), new.strip_suffix('\n').unwrap_or(&new));
            let out = se::edit(&text, se::profile_for(file), name, old, new).map_err(|e| format!("{file}: {e}"))?;
            write(file, &out)?;
            println!("{file}: edited `{name}`");
            Ok(())
        }
        ("order", files) if !files.is_empty() => {
            let texts: Vec<(String, fixpt_read::SyntaxProfile)> =
                files.iter().map(|f| slurp(f).map(|t| (t, se::profile_for(f)))).collect::<Result<_, _>>()?;
            let early = se::order(&texts)?;
            for e in &early {
                let (uk, ua) = e.used;
                let (dk, da) = e.defined;
                println!(
                    "{}:{}: `{}` is used before it is defined, at {}:{}",
                    files[uk],
                    at(&texts[uk].0, ua),
                    e.name,
                    files[dk],
                    at(&texts[dk].0, da)
                );
            }
            if early.is_empty() { Ok(()) } else { Err(format!("{} use(s) before definition", early.len())) }
        }
        _ => Err(usage.into()),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("sexp-edit: {e}");
            ExitCode::FAILURE
        }
    }
}
