//! The limits of macro expansion (`TODO.md` §231), as `FIXPT_MACRO_DEPTH`
//! and `FIXPT_MACRO_USES` set them: how deep uses may be, each in the
//! expansion of the one before, 1000 unless said; and how many one form's
//! expansion may expand, 10000 unless said. Each front end's, the Rust
//! one's (`run`) and FX-26's (`check`, which runs both).

use std::process::Command;

const FIXPT: &str = env!("CARGO_BIN_EXE_fixpt");

/// `fixpt <how> <program>`, the variables `env` set: what it printed and
/// said, and whether it succeeded.
fn fixpt(how: &str, program: &str, env: &[(&str, &str)]) -> (String, bool) {
    let mut cmd = Command::new(FIXPT);
    cmd.args([how, program]).env_remove("FIXPT_MACRO_DEPTH").env_remove("FIXPT_MACRO_USES");
    for (k, v) in env {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("runs");
    let said = String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr);
    (said, out.status.success())
}

/// A use of `count` `n` deep, each in the expansion of the one before.
fn deep(n: usize) -> String {
    format!(
        "(define-syntax count (syntax-rules ((_ n) n) ((_ n x . xs) (count (+ n 1) . xs))))\n(count 0 {})\n",
        vec!["x"; n].join(" ")
    )
}

fn file(name: &str, text: &str) -> String {
    let dir = std::env::temp_dir().join(format!("fixpt-macro-limits-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a directory");
    let path = dir.join(name);
    std::fs::write(&path, text).expect("written");
    path.to_string_lossy().into_owned()
}

/// A depth said, lower or higher than one a use needs (the default, 1000,
/// is `tests/programs/macros/loop-deep.fx`'s; one set empty is unsaid).
#[test]
fn a_depth_said_bounds_a_use_that_ends() {
    let p = file("deep150.fx", &deep(150));
    for how in ["run", "check"] {
        let (said, ok) = fixpt(how, &p, &[("FIXPT_MACRO_DEPTH", "100")]);
        assert!(!ok && said.contains("its uses are 100 deep"), "{how}: {said}");
        for value in ["200", ""] {
            let (said, ok) = fixpt(how, &p, &[("FIXPT_MACRO_DEPTH", value)]);
            assert!(ok, "{how}, {value:?}: {said}");
        }
    }
    let (said, _) = fixpt("check", &p, &[("FIXPT_MACRO_DEPTH", "200")]);
    assert!(said.contains("(nat 150)") && said.contains("both checkers agree"), "{said}");
}

#[test]
fn a_depth_said_is_the_limit() {
    let p = file("loop.fx", "(define-syntax m (macro (_ expr) expr) (syntax-rules ((_ e) (m (+ e 1)))))\n(m 1)\n");
    for how in ["run", "check"] {
        let (said, ok) = fixpt(how, &p, &[("FIXPT_MACRO_DEPTH", "50")]);
        assert!(!ok && said.contains("its uses are 50 deep, each in the expansion of the one before"), "{how}: {said}");
    }
}

#[test]
fn the_uses_said_are_the_limit() {
    let p = file("wide.fx", "(define-syntax two (syntax-rules ((_) (+ 1 1))))\n(list (two) (two) (two) (two) (two) (two))\n");
    for how in ["run", "check"] {
        let (said, ok) = fixpt(how, &p, &[("FIXPT_MACRO_USES", "5")]);
        assert!(!ok && said.contains("5 uses expanded in one form, the last of `two`"), "{how}: {said}");
        let (said, ok) = fixpt(how, &p, &[("FIXPT_MACRO_USES", "6")]);
        assert!(ok, "{how}: {said}");
    }
}

#[test]
fn a_limit_that_is_no_number_is_refused() {
    let p = file("one.fx", "(define-syntax two (syntax-rules ((_) (+ 1 1))))\n(two)\n");
    for (var, value) in [("FIXPT_MACRO_DEPTH", "abc"), ("FIXPT_MACRO_DEPTH", "0"), ("FIXPT_MACRO_USES", "-3"), ("FIXPT_MACRO_USES", "2000000000")] {
        for how in ["run", "check"] {
            let (said, ok) = fixpt(how, &p, &[(var, value)]);
            let want = format!("`{var}` is `{value}`: a limit of macro expansion is a whole number from 1 to 1000000000");
            assert!(!ok && said.contains(&want), "{how}, {var}={value}: {said}");
        }
    }
}
