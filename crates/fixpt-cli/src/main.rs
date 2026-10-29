//! `fixpt` — the command-line driver.
//!
//! Argument parsing is hand-rolled rather than pulled from a crate: the command
//! surface is small and fixed, and a runtime whose whole point is a
//! self-contained, dumpable image is better off with a dependency list this
//! short. The same reasoning produced [`lineedit`], which is why this binary
//! has no external dependencies at all.

mod bench;
mod survey;
mod help;
mod fx26;
mod fx87;
mod fx91;
mod image_run;
mod lineedit;
mod speculate;

use crate::lineedit::{Line, LineReader};
use fixpt_engine::Backend;
use fixpt_heap::image;
use fixpt_scheme::Session;

const USAGE: &str = "\
fixpt — FX-26, and Scheme, FX-87 and FX-91

usage:
  fixpt                          the FX-26 REPL, on the fastest machine here
  fixpt FILE [ARG...]            run a program: `fixpt run FILE -- ARG...`
  fixpt run FILE... [-- ARG...]  run each file in one session; FX-26: then
                                 `main`, if defined, its integer result the
                                 exit status (70 if the run fails); `args`
                                 gives the ARGs
  fixpt eval EXPR                evaluate one expression and print it; EXPR
                                 may be a file (a whole program) or `-` for
                                 the standard input
  fixpt eval --raw INPUT         FX-26: print only the last form's value, a
                                 string, as its characters (no quotes,
                                 escapes, type or effect); exit 1 if it is
                                 no string, or the program fails
  fixpt check INPUT              FX-26: both checkers (Rust and FX-26) on a
                                 file, `-` or program text; each form's type
                                 and effect, and where the checkers disagree
  fixpt query FILE QUERY…        FX-26: the program's definitions that answer
  fixpt query FILE… -- QUERY…    QUERY, each with its type and place (the
                                 files run in order, as `fixpt run` does):
                                 `effect E`, `uses T`, `returns T`,
                                 `constructs T`, `transforms T`,
                                 `consumes T`, `mutates T`; each may
                                 end `around CONTEXT` (a FILE:LINE:COL, a
                                 definition or a file) for the locals in
                                 scope there too (`,query` at the REPL)
  fixpt test INPUT [RUNS]        FX-26: run the program, then each procedure
                                 with a specification, and each harness (a
                                 procedure of `unit` result), on RUNS inputs
                                 drawn from its parameters' types (100);
                                 the first counterexample of each; exit 1 if
                                 one is found
  fixpt verify INPUT [NAME…]     FX-26: compile the program with certificates
                                 and verify each word (or each NAME) against
                                 its own: what fails or is left open, and
                                 why, each open obligation given to z3 if
                                 there is one (`FIXPT_SMT`) and sorted:
                                 proved, false (an input), not inductive
                                 or beyond it; exit 1 if a word is not
                                 verified
  fixpt compile INPUT            FX-26: both compilers, with register code;
                                 the code, and where the compilers disagree
                                 (`--eval`, `--check` and `--compile` too)
  fixpt compile --full-literals INPUT
                                 the same, every literal in full, in a form
                                 read back exactly (docs/fx26.md)
  fixpt compile-file [--program] [--cellular] FILE...
                                 each FX-26 file's `.fasl` made beside it, which a
                                 load of the file (a program's: `fixpt run`,
                                 `,load`) reads while it is fresh; its native
                                 code kept, or with --cellular its cellular
                                 words alone, compiled natively at load
  fixpt machines                 the machines FX-26 runs on, and which run here
  fixpt prewarm                  make this executable's caches of the FX-26
                                 front end, both kinds, before they are wanted
  fixpt bench [FILE...]          time FX-26 programs on each machine (`fixpt bench --help`)
  fixpt repl                     the REPL of the language (`fixpt fx26` too)
  fixpt scheme                   the Scheme REPL: `fixpt --dialect scheme repl`
  fixpt dump-heap -o OUT FILE... Scheme: run FILE... and write the resulting
                                 heap image
  fixpt build -o PROG FILE...    the same, as a standalone executable
  fixpt run-image FILE [ARG...]  run a heap image's entry point
  fixpt image info FILE          describe a heap image
  fixpt image verify FILE        load a heap image and check its invariants
  fixpt front-end-files          the FX-26 front end's files: its module files
                                 built in, then the rest in the order it joins
                                 them: lines (of the text built in) and path
  fixpt help                     show this

options (before or after the command; after `--`, the program's):
  --machine NAME                 how FX-26 runs (default: fast, the fastest
                                 here); `fixpt machines` lists them. Also
                                 spelled --fx26-machine
  --dialect fx26|scheme|fx87|fx91
                                 the language (default: fx26; Scheme for a
                                 `.scm` or `.ss` file, and for dump-heap and
                                 build)
  --step-limit N|none            how many evaluation steps a form may take before
                                 it is stopped, or no limit (default: 20000000
                                 for FX-87, FX-91 and FX-26; none for Scheme)
  --syscalls                     FX-26: the program is a runtime's, which may
                                 declare syscalls (`define-syscall`,
                                 `docs/research/syscalls.md`)
  --emacs                        the FX-26 REPL as Emacs drives it over a pipe
                                 (`editors/emacs/fx26-mode.el`): no continuation
                                 prompt, and `,at FILE LINE COL` before a form to
                                 have its errors said at FILE:LINE:COL
  --speculation-step-limit N|none
                                 the same for the FX-26 REPL's run of a form as it
                                 is typed (default: 200000); with none, typing a
                                 loop can hang the editor
  --engine bytecode|ast          the Scheme engine (default: bytecode)
  --reader scheme|fx26           the Scheme REPL's eager reader (default: scheme)
  --main NAME                    an image's entry point (default: main)
  --gc-every N                   also collect at every Nth safepoint, moving every
                                 object each time, to shake out rooting bugs
                                 (default: 0, only when the heap is full)

`--dialect fx87` and `--dialect fx91` select a *language*, not merely its
reader: a form is type- and effect-checked, erased to Scheme and run on the same
engine. Each REPL reports in its own reference's layout — FX-91 puts the type
and effect above the value, FX-87 after it. FX-26 reports as FX-87 does.

`--reader fx26` reads the Scheme REPL's input with the eager reader written in
FX-26 rather than the one written in Scheme. It runs on every keystroke, so it
is loaded only after its licence is checked: every entry point's effect must
stay within the reader's own regions.

An image built with `build` is a program in its own right: it carries its own
heap, needs no `fixpt` on the target, and runs its entry point when invoked.
`run-image` accepts either kind of file, and picks the engine the image was
made with rather than being told.
";

/// The commands, as the first word: a word that is none of them but names
/// a file runs it (`fixpt FILE`).
const COMMANDS: [&str; 22] = [
    "repl", "fx26", "scheme", "run", "eval", "check", "query", "test", "verify", "compile", "compile-file", "machines", "prewarm", "bench", "dump-heap", "build", "run-image", "image",
    "front-end-files", "help", "regcode-survey", "--help",
];

/// Rust's allocations, counted, and sampled with `FIXPT_ALLOC_PROFILE`.
#[global_allocator]
static ALLOCATOR: fixpt_memmgmt::alloc_profile::Counting = fixpt_memmgmt::alloc_profile::Counting;

fn main() {
    fixpt_memmgmt::alloc_profile::start();
    // A binary that carries an image *is* that program: it owns its whole
    // command line, and never looks like the driver that built it.
    if let Some(heap) = image_run::embedded_in_self() {
        let argv: Vec<String> = std::env::args().skip(1).collect();
        let code = image_run::run_entry(heap, "main", &argv);
        let _ = fixpt_runtime::tty::restore();
        std::process::exit(code);
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    // The reader, the expander and the IR passes recurse on the Rust stack —
    // one level per nested form, and per nested macro use — so the work runs
    // on a thread with room for it. The size is only reserved address space;
    // pages are committed as they are touched. At about 3.5 KB a level in a
    // debug build, the expander's own limit of 2 000 nested macro uses needs
    // ~7 MB, more than the main thread is given.
    let code = std::thread::Builder::new()
        .name("fixpt".into())
        .stack_size(STACK)
        .spawn(move || run(&args))
        .expect("the main thread can be spawned")
        .join();
    // A program that put the terminal in raw mode leaves it as it found
    // it, however it ended (`TODO.md` §95).
    let _ = fixpt_runtime::tty::restore();
    let code = code.unwrap_or_else(|e| std::panic::resume_unwind(e));
    fixpt_memmgmt::alloc_profile::report();
    std::process::exit(code);
}

/// The stack the whole command runs on.
const STACK: usize = 256 << 20;

fn run(args: &[String]) -> i32 {
    // `fixpt bench` takes options of its own.
    if args.first().is_some_and(|a| a == "bench") {
        return bench::command(&args[1..]);
    }
    // `fixpt regcode-survey`: what register code leaves to a simplifier.
    if args.first().is_some_and(|a| a == "regcode-survey") {
        return survey::command(&args[1..]);
    }
    let (mut flags, mut rest) = match split_flags(args) {
        Ok(split) => split,
        Err(e) => {
            eprintln!("fixpt: {e}\n(`fixpt help` lists the commands and options)");
            return 2;
        }
    };
    // `--eval INPUT` and its kin are the commands `eval INPUT`, and so on.
    if let Some(cmd) = rest.first().and_then(|a| a.strip_prefix("--")).filter(|c| ["eval", "check", "compile"].contains(c)) {
        rest[0] = cmd.to_string();
    }
    // `fixpt fx26` and `fixpt scheme`: that language's REPL.
    for (cmd, dialect) in [("fx26", "fx26"), ("scheme", "scheme")] {
        if rest.first().is_some_and(|a| a == cmd) && flags.dialect.as_deref().is_none_or(|d| d == dialect) {
            flags.dialect = Some(dialect.into());
            rest[0] = "repl".into();
        }
    }
    // `fixpt FILE [ARG...]`: `fixpt run FILE -- ARG...` (`split_flags`
    // put the `--` in).
    if rest.first().is_some_and(|f| !COMMANDS.contains(&f.as_str()) && std::path::Path::new(f).is_file()) {
        rest.insert(0, "run".into());
    }
    // A machine by its name, the fastest unless another is named
    // (`TODO.md` §78), and the parts it stands for.
    let m = flags.fx26_machine.clone().unwrap_or_else(|| "fast".into());
    let Some((run, machine, convention)) = FX26_MACHINES.iter().find(|(n, ..)| *n == m || (m == "fast" && *n == FASTEST)).map(|(_, r, c, v, _)| (*r, *c, *v))
    else {
        eprintln!("fixpt: unknown machine `{m}`; `fixpt machines` lists them{}", did_you_mean(&m, FX26_MACHINES.iter().map(|(n, ..)| *n)));
        return 2;
    };
    flags.fx26_run = Some(run.into());
    flags.cellular_machine = machine.map(Into::into);
    flags.calling_convention = convention.map(Into::into);
    // FX-26 unless said otherwise, or the files are Scheme's (`.scm`,
    // `.ss`), or the command is Scheme's alone.
    let scheme_file = |f: &String| f.ends_with(".scm") || f.ends_with(".ss");
    let scheme_implied = match rest.first().map(String::as_str) {
        Some("dump-heap" | "build") => true,
        Some("run") => rest[1..].iter().take_while(|a| *a != "--").all(scheme_file) && rest.len() > 1,
        Some("eval") => rest.len() == 2 && scheme_file(&rest[1]) && std::path::Path::new(&rest[1]).is_file(),
        _ => false,
    };
    // The dialect picks a *language*, which is a front end, not just a set of
    // lexical rules: FX-91 forms go through the checker and the code generator
    // before any of this runs them.
    let dialect = match flags.dialect.as_deref() {
        None if scheme_implied => Dialect::Scheme,
        None => Dialect::Fx26,
        Some("scheme") => Dialect::Scheme,
        Some("fx91") => Dialect::Fx91,
        Some("fx87") => Dialect::Fx87,
        Some("fx26") => Dialect::Fx26,
        Some(name) => {
            eprintln!("fixpt: unknown dialect `{name}` (want scheme, fx87, fx91 or fx26)");
            return 2;
        }
    };
    let profile = fixpt_read::SyntaxProfile::SCHEME;

    let backend = match flags.engine.as_deref() {
        None | Some("bytecode") | Some("vm") | Some("compiled") => Backend::Bytecode,
        Some("ast") | Some("interp") | Some("interpreted") => Backend::Ast,
        Some(name) => {
            eprintln!("fixpt: unknown engine `{name}` (want bytecode or ast)");
            return 2;
        }
    };
    let entry = flags.main.as_deref().unwrap_or("main");
    let strategy = match flags.fx26_run.as_deref() {
        None | Some("lower") => fixpt_fx26::session::Strategy::Lower,
        Some("evaluate") => fixpt_fx26::session::Strategy::Evaluate,
        Some("cellular") => fixpt_fx26::session::Strategy::Cellular,
        Some(name) => unreachable!("a machine's parts: {name}"),
    };
    let _ = FX26_RUN.set(strategy);
    let _ = FX26_MACHINE_NAME.set(if m == "fast" { FASTEST.to_string() } else { m });
    if let Some(why) = unavailable(flags.cellular_machine.as_deref(), flags.calling_convention.as_deref()) {
        eprintln!("fixpt: machine `{}`: {why}", FX26_MACHINE_NAME.get().map(String::as_str).unwrap_or(""));
        return 2;
    }
    let machine: fixpt_runtime::RunWord = match flags.cellular_machine.as_deref() {
        None | Some("rust") => fixpt_engine::cellular::run_word,
        Some("native") => fixpt_native::cellular::run_word,
        Some("native-compiled") => fixpt_native::cellular::run_word_compiled,
        // Compiled before the run, by `native.fx` (`CELLULAR_PLACE_CODE`).
        Some("fx-compiled") => fixpt_native::cellular::run_word_as_is,
        // Register code compiled before the run, by `native-x64-regs.fx`:
        // only for x86_64 so far (`TODO.md` §81 for arm64).
        Some("fx-registers") => fixpt_native::cellular::run_word_as_is,
        Some("stencils") => fixpt_native::stencil::run_word,
        Some("registers") => fixpt_native::cellular::run_word_registers,
        Some(name) => unreachable!("a machine's parts: {name}"),
    };
    let _ = CELLULAR_MACHINE.set(machine);
    let _ = CELLULAR_PLACE_CODE.set(match flags.cellular_machine.as_deref() {
        Some("fx-compiled" | "fx-registers") => Some(fixpt_native::cellular::place_word as fixpt_runtime::PlaceCode),
        _ => None,
    });
    let _ = EMACS.set(flags.emacs);
    let _ = SYSCALLS.set(flags.syscalls);
    let _ = NATIVE_BY_FX26.set(flags.calling_convention.as_deref() == Some("fx-native"));
    let _ = NATIVE_CONVENTION.set(match flags.calling_convention.as_deref() {
        None | Some("cellular") => false,
        Some("native" | "fx-native") => true,
        Some(name) => unreachable!("a machine's parts: {name}"),
    });
    let _ = CELLULAR_MACHINE_CODE.set(match flags.cellular_machine.as_deref() {
        Some("native-compiled" | "fx-compiled" | "registers" | "fx-registers") => Some(fixpt_native::cellular::machine_code_text as fixpt_runtime::MachineCode),
        Some("stencils") => Some(fixpt_native::stencil::stencil_source_text as fixpt_runtime::MachineCode),
        _ => None,
    });
    let _ = CELLULAR_MACHINE_NAME.set(match flags.cellular_machine.as_deref() {
        Some("native") => "the hand-encoded native machine",
        Some("native-compiled") => "the hand-encoded native machine, its words compiled to machine code",
        Some("fx-compiled") => "the hand-encoded native machine, its words compiled to machine code by native.fx",
        Some("fx-registers") => "the native machine, as register code compiled by native-x64-regs.fx",
        Some("stencils") => "the stencil machine",
        Some("registers") => "the native machine, as register code",
        _ => "the cellular machine written in Rust",
    });
    for (flag, value, cell) in [
        ("--step-limit", &flags.step_limit, &STEP_LIMIT),
        ("--speculation-step-limit", &flags.speculation_step_limit, &SPECULATION_STEP_LIMIT),
    ] {
        if let Some(v) = value.as_deref() {
            match parse_limit(v) {
                Some(l) => {
                    let _ = cell.set(l);
                }
                None => {
                    eprintln!("fixpt: {flag} takes a count of steps, or none");
                    return 2;
                }
            }
        }
    }
    if let Some(n) = flags.gc_every.as_deref() {
        match n.parse::<u64>() {
            Ok(n) => {
                let _ = GC_EVERY.set(n);
            }
            Err(_) => {
                eprintln!("fixpt: --gc-every takes a count, 0 or more");
                return 2;
            }
        }
    }

    match rest.first().map(String::as_str) {
        Some("help") | Some("-h") | Some("--help") => {
            print!("{USAGE}");
            0
        }
        Some("machines") => {
            print!("{}", machines_listing());
            0
        }
        Some("prewarm") => prewarm(),
        // The FX-26 front end's files, in order, as `wc -l` prints them:
        // what this build of fixpt was made of, for scripts.
        Some("front-end-files") => {
            use std::io::Write;
            let dir = fixpt_fx26::SOURCE_DIR;
            let mut out = std::io::stdout().lock();
            // A reader that stops early (`| head`) ends the listing. First
            // the module files built in, each loaded by the next, the last
            // by `reader.fx`.
            let modules = fixpt_fx26::FRONT_END_MODULES.iter().try_for_each(|(name, text)| {
                writeln!(out, "{:>6} {dir}/{name} (a module file, built in)", text.lines().count())
            });
            let listed = modules.and_then(|()| {
                fixpt_fx26::FRONT_END_FILES.iter().try_for_each(|(name, text)| writeln!(out, "{:>6} {dir}/{name}", text.lines().count()))
            });
            let _ = listed.and_then(|()| writeln!(out, "{:>6} {dir}/bootstrap.fx (the bootstrap's driver, after them)", fixpt_fx26::BOOTSTRAP.lines().count()));
            0
        }
        None | Some("repl") => match dialect {
            Dialect::Scheme => repl(profile, backend, flags.reader.as_deref() == Some("fx26")),
            Dialect::Fx87 => fx87::repl(backend),
            Dialect::Fx91 => fx91::repl(backend),
            Dialect::Fx26 => fx26::repl(backend),
        },
        Some("run") => {
            if rest.len() < 2 {
                eprintln!("fixpt run: needs at least one file");
                return 2;
            }
            // Only FX-26 gives a program its arguments: the others take the
            // files before a `--`.
            let files: Vec<String> = rest[1..].iter().take_while(|a| *a != "--").cloned().collect();
            match dialect {
                Dialect::Fx87 => fx87::run_files(backend, &files),
                Dialect::Fx91 => fx91::run_files(backend, &files),
                Dialect::Fx26 => fx26::run_files(backend, &rest[1..]),
                Dialect::Scheme => match run_files(profile, backend, &files) {
                    Ok(_) => 0,
                    Err(e) => {
                        eprintln!("fixpt: {e}");
                        1
                    }
                },
            }
        }
        Some("compile-file") => {
            if dialect != Dialect::Fx26 {
                eprintln!("fixpt compile-file: FX-26 only");
                return 2;
            }
            if rest.len() < 2 {
                eprintln!("fixpt compile-file: needs at least one module file");
                return 2;
            }
            fx26::compile_files(backend, &rest[1..])
        }
        Some(cmd @ ("check" | "compile")) => {
            if dialect != Dialect::Fx26 {
                eprintln!("fixpt {cmd}: FX-26 only");
                return 2;
            }
            if rest.len() < 2 {
                eprintln!("fixpt {cmd}: needs a file, `-` or a program");
                return 2;
            }
            // `compile --full-literals`: every literal in full, read back exactly.
            let full = cmd == "compile" && rest[1] == "--full-literals";
            match fx26::input(&rest[1 + full as usize..]) {
                Ok((name, text)) if cmd == "check" => fx26::check(backend, &name, &text),
                Ok((name, text)) => fx26::compile(backend, &name, &text, full),
                Err(e) => {
                    eprintln!("fixpt: {e}");
                    1
                }
            }
        }
        Some("query") => {
            if dialect != Dialect::Fx26 {
                eprintln!("fixpt query: FX-26 only");
                return 2;
            }
            // `FILE… -- QUERY…`, or one file and the query after it.
            let (files, query) = match rest.iter().position(|a| a == "--") {
                Some(i) => (&rest[1..i], &rest[i + 1..]),
                None => (rest.get(1..2).unwrap_or(&[]), rest.get(2..).unwrap_or(&[])),
            };
            if files.is_empty() || query.is_empty() {
                eprintln!("fixpt query: needs files and a query, as `fixpt query prog.fx constructs buffer` or `fixpt query a.fx b.fx -- uses buffer`");
                return 2;
            }
            fx26::query_files(backend, files, &query.join(" "))
        }
        Some("test") => {
            if dialect != Dialect::Fx26 {
                eprintln!("fixpt test: FX-26 only");
                return 2;
            }
            let runs = match rest.get(2).map(|r| r.parse::<usize>()) {
                None => 100,
                Some(Ok(n)) => n,
                Some(Err(_)) => {
                    eprintln!("fixpt test: RUNS is a number");
                    return 2;
                }
            };
            match rest.get(1).map(|f| fx26::input(std::slice::from_ref(f))) {
                Some(Ok((name, text))) => fx26::test(backend, &name, &text, runs),
                Some(Err(e)) => {
                    eprintln!("fixpt: {e}");
                    1
                }
                None => {
                    eprintln!("fixpt test: needs a file, `-` or a program");
                    2
                }
            }
        }
        Some("verify") => {
            if dialect != Dialect::Fx26 {
                eprintln!("fixpt verify: FX-26 only");
                return 2;
            }
            match rest.get(1).map(|f| fx26::input(std::slice::from_ref(f))) {
                Some(Ok((name, text))) => fx26::verify(backend, &name, &text, &rest[2..]),
                Some(Err(e)) => {
                    eprintln!("fixpt: {e}");
                    1
                }
                None => {
                    eprintln!("fixpt verify: needs a file, `-` or a program");
                    2
                }
            }
        }
        Some("eval") => {
            if rest.len() < 2 {
                eprintln!("fixpt eval: needs an expression");
                return 2;
            }
            match dialect {
                Dialect::Fx87 => return fx87::eval(backend, &rest[1..].join(" ")),
                Dialect::Fx91 => return fx91::eval(backend, &rest[1..].join(" ")),
                Dialect::Fx26 => {
                    // `--raw`: the last form's string as it is, nothing else.
                    let raw = rest[1] == "--raw";
                    let args = &rest[1 + raw as usize..];
                    if args.is_empty() {
                        eprintln!("fixpt eval: needs an expression");
                        return 2;
                    }
                    return match fx26::input(args) {
                        Ok((name, text)) if name == "<argument>" && !raw => fx26::eval(backend, &text),
                        Ok((name, text)) => fx26::eval_program(backend, &name, &text, raw),
                        Err(e) => {
                            eprintln!("fixpt: {e}");
                            1
                        }
                    };
                }
                Dialect::Scheme => {}
            }
            let mut session = Session::with_backend(backend);
    apply_gc_policy(&mut session);
            session.profile = profile;
            match session.eval_to_string("<argument>", &rest[1..].join(" ")) {
                Ok(v) => {
                    println!("{v}");
                    0
                }
                Err(e) => {
                    eprintln!("fixpt: {e}");
                    1
                }
            }
        }
        Some("dump-heap") | Some("build") => {
            if dialect != Dialect::Scheme {
                eprintln!("fixpt: {} is Scheme-only for now", rest[0]);
                return 2;
            }
            let standalone = rest[0] == "build";
            let Some(out) = flags.out.clone() else {
                eprintln!("fixpt {}: needs -o OUT", rest[0]);
                return 2;
            };
            dump_command(profile, backend, &rest[1..], &out, standalone)
        }
        Some("run-image") => {
            if rest.len() < 2 {
                eprintln!("fixpt run-image: needs an image file");
                return 2;
            }
            match image_run::read_image(&rest[1]) {
                Ok(heap) => image_run::run_entry(heap, entry, &rest[2..]),
                Err(e) => {
                    eprintln!("fixpt: {e}");
                    1
                }
            }
        }
        Some("image") => image_command(&rest[1..]),
        Some(other) => {
            eprintln!("fixpt: unknown command `{other}`, and no such file{}\n(`fixpt help` lists the commands)", did_you_mean(other, COMMANDS.into_iter()));
            2
        }
    }
}

/// Which language the source is in.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
enum Dialect {
    Scheme,
    Fx87,
    Fx91,
    Fx26,
}

struct Flags {
    dialect: Option<String>,
    engine: Option<String>,
    out: Option<String>,
    main: Option<String>,
    reader: Option<String>,
    fx26_run: Option<String>,
    gc_every: Option<String>,
    cellular_machine: Option<String>,
    calling_convention: Option<String>,
    fx26_machine: Option<String>,
    step_limit: Option<String>,
    speculation_step_limit: Option<String>,
    emacs: bool,
    syscalls: bool,
}

/// The FX-26 machines by name (`--machine`, `TODO.md` §78): who
/// generates the code (`rs` Rust, `fx` FX-26), what code (Scheme, the
/// checked tree, cellular words, register code), what runs it, and, where
/// it is machine code, the calling convention (`cellcc`, inside the
/// cellular machine; `nativecc`, native procedures); then the parts they
/// stand for, and what each is, for `fixpt machines` and the REPL. `fast`
/// is `FASTEST`.
pub(crate) const FX26_MACHINES: [(&str, &str, Option<&str>, Option<&str>, &str); 12] = [
    ("rs-scheme-vm", "lower", None, None, "lowered to Scheme by Rust, run on the bytecode VM"),
    ("fx-ast-eval", "evaluate", None, None, "run by the evaluator written in FX-26"),
    ("fx-cells-rsinterp", "cellular", Some("rust"), None, "cellular words by the FX-26 compiler, interpreted by Rust"),
    (
        "fx-cells-rsinterp-nativecc",
        "cellular",
        Some("rust"),
        Some("native"),
        "the same, its procedures compiled by Rust to native ones where it can",
    ),
    ("fx-cells-asminterp", "cellular", Some("native"), None, "cellular words, interpreted by hand-written machine code"),
    ("fx-cells-rsjit-cellcc", "cellular", Some("native-compiled"), None, "cellular words, compiled to machine code by Rust"),
    (
        "fx-cells-fxjit-cellcc",
        "cellular",
        Some("fx-compiled"),
        None,
        "cellular words, compiled to machine code by FX-26 (native.fx; native-x64.fx on x86_64)",
    ),
    ("fx-cells-stencils-cellcc", "cellular", Some("stencils"), None, "cellular words, by copy-and-patch stencils (built with nightly)"),
    ("fx-regs-rsjit-cellcc", "cellular", Some("registers"), None, "register code, compiled to machine code by Rust"),
    ("fx-regs-fxjit-cellcc", "cellular", Some("fx-registers"), None, "register code, compiled to x86_64 by native-x64-regs.fx (FX-26)"),
    (
        "fx-regs-fxjit-nativecc",
        "cellular",
        Some("registers"),
        Some("fx-native"),
        "register code, compiled to x86_64 by native-direct-x64.fx (FX-26), native calls",
    ),
    (
        "fx-regs-rsjit-nativecc",
        "cellular",
        Some("registers"),
        Some("native"),
        "register code, compiled to machine code by Rust's direct.rs, native calls",
    ),
];

/// `fixpt prewarm`: this executable's two caches of the FX-26 front end
/// made now (`front_end_cache`): the one for its register code, which every
/// machine but one native in its convention by Rust's compiler reads, and the
/// one for its native code, which those read. Each made by a run of this
/// executable on a machine of that kind, since a process runs one machine.
/// So that processes started together after a build (a test suite's) find
/// them, rather than each making them at once.
fn prewarm() -> i32 {
    if std::env::var_os("FIXPT_NO_CACHE").is_some() {
        eprintln!("fixpt: prewarm: `FIXPT_NO_CACHE` keeps no cache");
        return 1;
    }
    let Ok(exe) = std::env::current_exe() else {
        eprintln!("fixpt: prewarm: this executable cannot be found");
        return 1;
    };
    let first = |native: bool| {
        FX26_MACHINES.iter().find(|(_, run, m, c, _)| *run == "cellular" && (*c == Some("native")) == native && (native || c.is_none()) && unavailable(*m, *c).is_none()).map(|(n, ..)| *n)
    };
    let mut status = 0;
    for (what, native) in [("register code", false), ("native code", true)] {
        let Some(machine) = first(native) else {
            println!("; the front end's {what}: no machine here runs it");
            continue;
        };
        let started = std::time::Instant::now();
        match std::process::Command::new(&exe).args(["--fx26-machine", machine, "eval", "0"]).output() {
            Ok(out) if out.status.success() => println!("; the front end's {what} cached ({machine}), {:.1} s", started.elapsed().as_secs_f64()),
            Ok(out) => {
                eprintln!("fixpt: prewarm: {machine} failed: {}", String::from_utf8_lossy(&out.stderr).trim());
                status = 1;
            }
            Err(e) => {
                eprintln!("fixpt: prewarm: cannot run {}: {e}", exe.display());
                status = 1;
            }
        }
    }
    status
}

/// Why a machine of these parts cannot run here, or `None`.
fn unavailable(machine: Option<&str>, convention: Option<&str>) -> Option<String> {
    // Where neither arm64 nor x86_64 code runs, only the machine written in
    // Rust, with neither native convention.
    let native_machine = machine.is_some_and(|m| m != "rust");
    if !fixpt_native::AVAILABLE
        && ((native_machine && !fixpt_native::CELLULAR_AVAILABLE)
            || (matches!(convention, Some("native" | "fx-native")) && !fixpt_native::NATIVE_CONVENTION_AVAILABLE))
    {
        return Some(fixpt_native::UNAVAILABLE.to_string());
    }
    // FX-26 compiles register code and the native convention for x86_64
    // only (`TODO.md` §81 for arm64).
    if (machine == Some("fx-registers") || convention == Some("fx-native")) && !cfg!(target_arch = "x86_64") {
        return Some("FX-26 compiles it for x86_64 only (TODO.md §81)".into());
    }
    if machine == Some("stencils") && fixpt_native::stencil::opt_levels().is_empty() {
        return Some("this build has no stencils (it found no nightly compiler)".into());
    }
    None
}

/// `fixpt machines`: each machine, which is the default, and which cannot
/// run here, and why.
fn machines_listing() -> String {
    let mut out = String::from("FX-26's machines (`--machine NAME`; the default, `fast`, marked *):\n");
    for (name, _, machine, convention, what) in FX26_MACHINES {
        let mark = if name == FASTEST { "*" } else { " " };
        out.push_str(&format!("{mark} {name:<27} {what}\n"));
        if let Some(why) = unavailable(machine, convention) {
            out.push_str(&format!("  {:<27} (not here: {why})\n", ""));
        }
    }
    out.push_str(
        "\nA name says who generates the code (rs Rust, fx FX-26), what code (scheme,\n\
         the checked ast, cellular words or register code), what runs it, and,\n\
         for machine code, the calling convention (cellcc: inside the cellular\n\
         machine; nativecc: native procedures). All but the default are\n\
         references the tests compare against.\n",
    );
    out
}

/// `, did you mean NAME?` for the name of `names` nearest `word`, if near.
fn did_you_mean<'a>(word: &str, names: impl Iterator<Item = &'a str>) -> String {
    // Edit distance, by one row at a time.
    let distance = |a: &str, b: &str| {
        let b: Vec<char> = b.chars().collect();
        let mut row: Vec<usize> = (0..=b.len()).collect();
        for (i, ca) in a.chars().enumerate() {
            let mut prev = row[0];
            row[0] = i + 1;
            for (j, cb) in b.iter().enumerate() {
                let next = (prev + (ca != *cb) as usize).min(row[j] + 1).min(row[j + 1] + 1);
                prev = row[j + 1];
                row[j + 1] = next;
            }
        }
        row[b.len()]
    };
    match names.map(|n| (distance(word, n), n)).min() {
        // Near: 2 edits, more in a longer word, and fewer than half its letters.
        Some((d, n)) if d <= 2.max(word.len() / 5) && 2 * d < word.chars().count() => format!("; did you mean `{n}`?"),
        _ => String::new(),
    }
}
/// The machine `fast` names: `fx-regs-rsjit-nativecc`, on arm64 and on
/// x86_64 (there since 2026-10-22: the 46 ports in 91 s against 206 s on
/// `fx-regs-rsjit-cellcc`, CLAUDES_CHOICES.md "`fast` on x86_64 is
/// native"); where only the hand-encoded cellular machine runs,
/// `fx-regs-rsjit-cellcc`; and elsewhere `fx-cells-rsinterp`, faster than
/// `rs-scheme-vm` on each of `fixpt bench`'s programs.
pub(crate) const FASTEST: &str = if fixpt_native::NATIVE_CONVENTION_AVAILABLE {
    "fx-regs-rsjit-nativecc"
} else if fixpt_native::CELLULAR_AVAILABLE {
    "fx-regs-rsjit-cellcc"
} else {
    "fx-cells-rsinterp"
};
/// The FX-26 machine this process runs, by name (`FX26_MACHINES`), or the
/// parts given one by one where they name none.
pub(crate) static FX26_MACHINE_NAME: std::sync::OnceLock<String> = std::sync::OnceLock::new();

/// How the machine runs FX-26, for every FX-26 session this process starts.
pub(crate) static FX26_RUN: std::sync::OnceLock<fixpt_fx26::session::Strategy> = std::sync::OnceLock::new();
/// The machine's cellular machine, for every FX-26 session this process
/// starts.
pub(crate) static CELLULAR_MACHINE: std::sync::OnceLock<fixpt_runtime::RunWord> = std::sync::OnceLock::new();
/// How words' machine code made by `native.fx` (or `native-x64.fx` and
/// `native-x64-regs.fx`) is placed: `fx-compiled` and `fx-registers` only.
pub(crate) static CELLULAR_PLACE_CODE: std::sync::OnceLock<Option<fixpt_runtime::PlaceCode>> = std::sync::OnceLock::new();
/// How that machine shows a word's machine code (`,disassemble-asm`): none
/// for the one written in Rust, which interprets cells.
pub(crate) static CELLULAR_MACHINE_CODE: std::sync::OnceLock<Option<fixpt_runtime::MachineCode>> = std::sync::OnceLock::new();
/// Which machine that is, for the REPL to say.
pub(crate) static CELLULAR_MACHINE_NAME: std::sync::OnceLock<&'static str> = std::sync::OnceLock::new();
/// The machine for register code, where the front end runs: the hand
/// register machine (arm64 or x86_64); where that cannot run, the cellular
/// machine written in Rust.
pub(crate) fn register_machine() -> fixpt_runtime::RunWord {
    if fixpt_native::CELLULAR_AVAILABLE {
        fixpt_native::cellular::run_word_registers
    } else {
        fixpt_engine::cellular::run_word
    }
}

/// Whether the machine's convention is native (`nativecc`), for every FX-26
/// session this process starts.
pub(crate) static NATIVE_CONVENTION: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
/// `fx-regs-fxjit-nativecc`: the native convention, each
/// procedure's code made by the compiler written in FX-26
/// (`fx26::compile_by_fx26`).
pub(crate) static NATIVE_BY_FX26: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
/// `--emacs`: the REPL as Emacs drives it (`editors/emacs/fx26-mode.el`).
pub(crate) static EMACS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
/// `--syscalls`: the FX-26 program is a runtime's, which may declare
/// syscalls (`docs/research/syscalls.md`, "Containment").
pub(crate) static SYSCALLS: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
/// `--gc-every`, for every heap this process starts.
pub(crate) static GC_EVERY: std::sync::OnceLock<u64> = std::sync::OnceLock::new();

/// `--step-limit` and `--speculation-step-limit`: `Some(limit)` when given,
/// `limit` being `None` for no limit.
pub(crate) static STEP_LIMIT: std::sync::OnceLock<Option<u64>> = std::sync::OnceLock::new();
pub(crate) static SPECULATION_STEP_LIMIT: std::sync::OnceLock<Option<u64>> = std::sync::OnceLock::new();

/// A step limit as written: a count, or `none` (also `off`).
pub(crate) fn parse_limit(v: &str) -> Option<Option<u64>> {
    match v {
        "none" | "off" => Some(None),
        n => n.parse::<u64>().ok().map(Some),
    }
}

/// Apply `--gc-every` to a session's heap, and `--step-limit` to its engine.
pub(crate) fn apply_gc_policy(session: &mut Session) {
    if let Some(n) = GC_EVERY.get() {
        session.set_gc_every(*n);
    }
    if let Some(l) = STEP_LIMIT.get() {
        session.engine.set_step_limit(*l);
    }
    // A line on stderr for each collection (`docs/research/telemetry.md`).
    session.runtime_unrooted().heap.trace = std::env::var_os("FIXPT_GC_TRACE").is_some();
}

/// The options a command takes after it, left for it to read.
const COMMAND_OPTIONS: [&str; 9] = ["--raw", "--full-literals", "--program", "--cellular", "--eval", "--check", "--compile", "--help", "-h"];

/// The options, read from anywhere before a `--`; the rest of the words,
/// in order, with the `--` and all after it. Or why not: an unknown option.
fn split_flags(args: &[String]) -> Result<(Flags, Vec<String>), String> {
    let mut flags = Flags {
        dialect: None,
        engine: None,
        out: None,
        main: None,
        reader: None,
        fx26_run: None,
        gc_every: None,
        cellular_machine: None,
        calling_convention: None,
        fx26_machine: None,
        step_limit: None,
        speculation_step_limit: None,
        emacs: false,
        syscalls: false,
    };
    let mut rest = Vec::new();
    let mut i = 0;
    // Each flag takes a value, spelled either `--flag v` or `--flag=v`.
    type Setter = fn(&mut Flags, String);
    let named: [(&str, Setter); 10] = [
        ("--machine", |f, v| f.fx26_machine = Some(v)),
        ("--fx26-machine", |f, v| f.fx26_machine = Some(v)),
        ("--speculation-step-limit", |f, v| f.speculation_step_limit = Some(v)),
        ("--step-limit", |f, v| f.step_limit = Some(v)),
        ("--gc-every", |f, v| f.gc_every = Some(v)),
        ("--dialect", |f, v| f.dialect = Some(v)),
        ("--reader", |f, v| f.reader = Some(v)),
        ("--engine", |f, v| f.engine = Some(v)),
        ("--main", |f, v| f.main = Some(v)),
        ("-o", |f, v| f.out = Some(v)),
    ];
    'outer: while i < args.len() {
        // After `--`, the program's arguments; after a first word that
        // names a file (`fixpt FILE ARG...`), too.
        if args[i] == "--" {
            rest.extend(args[i..].iter().cloned());
            break;
        }
        if rest.is_empty() && !args[i].starts_with('-') && !COMMANDS.contains(&args[i].as_str()) && std::path::Path::new(&args[i]).is_file() {
            rest.push(args[i].clone());
            rest.push("--".into());
            rest.extend(args[i + 1..].iter().cloned());
            break;
        }
        // Flags that take no value.
        if args[i] == "--emacs" {
            flags.emacs = true;
            i += 1;
            continue;
        }
        if args[i] == "--syscalls" {
            flags.syscalls = true;
            i += 1;
            continue;
        }
        for (name, set) in named {
            if args[i] == name {
                let Some(v) = args.get(i + 1) else { return Err(format!("`{name}` needs a value")) };
                set(&mut flags, v.clone());
                i += 2;
                continue 'outer;
            }
            let prefix = format!("{name}=");
            if let Some(v) = args[i].strip_prefix(&prefix) {
                set(&mut flags, v.to_string());
                i += 1;
                continue 'outer;
            }
        }
        let word = args[i].split('=').next().unwrap_or("");
        if ["--fx26-run", "--cellular-machine", "--calling-convention"].contains(&word) {
            return Err(format!("`{word}` is gone: a machine is chosen by its name, `--machine NAME` (`fixpt machines` lists them)"));
        }
        if word.starts_with("--") && !COMMAND_OPTIONS.contains(&word) {
            let known = named.iter().map(|(n, _)| *n).chain(["--emacs", "--syscalls"]).chain(COMMAND_OPTIONS);
            return Err(format!("unknown option `{word}`{}", did_you_mean(word, known)));
        }
        rest.push(args[i].clone());
        i += 1;
    }
    Ok((flags, rest))
}

fn run_files(
    profile: fixpt_read::SyntaxProfile,
    backend: Backend,
    files: &[String],
) -> Result<Session, String> {
    let mut session = Session::with_backend(backend);
    apply_gc_policy(&mut session);
    session.profile = profile;
    for f in files {
        let text = std::fs::read_to_string(f).map_err(|e| format!("cannot read {f}: {e}"))?;
        session.eval_str(f, &text).map_err(|e| e.to_string())?;
    }
    Ok(session)
}

/// `dump-heap` and `build`: run the files, then write out what they left behind.
///
/// Collecting first is not just tidiness. The collector compacts, so the image
/// holds only reachable objects laid out contiguously — which is what makes
/// loading a `memcpy` and a root fixup rather than a graph walk.
fn dump_command(
    profile: fixpt_read::SyntaxProfile,
    backend: Backend,
    files: &[String],
    out: &str,
    standalone: bool,
) -> i32 {
    let mut session = match run_files(profile, backend, files) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("fixpt: {e}");
            return 1;
        }
    };
    session.collect();
    if let Err(e) = session.verify() {
        eprintln!("fixpt: refusing to write an unsound heap: {e}");
        return 1;
    }
    let bytes = session.image();
    let result = if standalone {
        image_run::embed(&bytes, out)
    } else {
        std::fs::write(out, &bytes).map_err(|e| format!("cannot write {out}: {e}"))
    };
    match result {
        Ok(()) => {
            let kind = if standalone {
                "executable"
            } else {
                "heap image"
            };
            let size = std::fs::metadata(out)
                .map(|m| m.len())
                .unwrap_or(bytes.len() as u64);
            println!(
                "wrote {out}: {kind}, {size} bytes ({} live words)",
                session.heap_used()
            );
            0
        }
        Err(e) => {
            eprintln!("fixpt: {e}");
            1
        }
    }
}

fn repl(profile: fixpt_read::SyntaxProfile, backend: Backend, fx26_reader: bool) -> i32 {
    let mut session = Session::with_backend(backend);
    apply_gc_policy(&mut session);
    session.profile = profile;
    let engine = match backend {
        Backend::Ast => "AST engine",
        Backend::Bytecode => "bytecode engine",
    };
    println!("fixpt {} — {} reader, {engine}", env!("CARGO_PKG_VERSION"), profile.name);
    println!("(an expression, `,help` for commands, or ^D to leave)");

    let mut reader = LineReader::new(".fixpt_history", profile);
    // The eager reader reads the Scheme profile; if it cannot be loaded, the
    // REPL still works, re-reading with the Rust reader.
    let mut eager = if profile.name != "scheme" {
        None
    } else if fx26_reader {
        match load_fx26_reader(&mut session) {
            Ok(r) => {
                println!("(reading with the eager reader written in FX-26; its licence checked)");
                Some(r)
            }
            Err(why) => {
                println!("(the FX-26 reader is not used: {why}; reading with the Scheme one)");
                fixpt_scheme::eager::EagerReader::new(&mut session).ok()
            }
        }
    } else {
        fixpt_scheme::eager::EagerReader::new(&mut session).ok()
    };
    // What to give back for further editing after a mid-form hole.
    let mut initial = String::new();
    loop {
        reader.set_completions(bound_names(&session));
        let line = match eager.as_mut() {
            Some(r) => {
                let mut oracle = EagerOracle { session: &mut session, reader: r };
                reader.read_with("> ", "| ", &mut oracle, &initial)
            }
            None => {
                let mut oracle = lineedit::Reread(profile);
                reader.read_with("> ", "| ", &mut oracle, &initial)
            }
        };
        initial.clear();
        match line {
            Line::Eof => {
                reader.save();
                return 0;
            }
            Line::Interrupted => continue,
            // `,help` written before the form is finished: answer it as though
            // the form had been closed right after the hole, then hand the
            // form back — minus the hole — to carry on typing.
            Line::Ask { closed, keep } => {
                match run_line(&mut session, &closed) {
                    // `,resume` would continue the form as it was closed off to
                    // answer the hole — not the one being typed — so it is not
                    // offered here.
                    Ok(v) => {
                        let report: Vec<&str> = v.lines().filter(|l| !l.contains("`,resume EXPR`")).collect();
                        println!("{}", report.join("\n"));
                        println!("; the form is given back without the hole: carry on typing");
                    }
                    Err(e) => eprintln!("{e}"),
                }
                initial = keep;
            }
            Line::Form(text) if hole_command(&text).is_some() => {
                match hole_command(&text).expect("just checked") {
                    HoleCommand::Where => match session.held_hole_report() {
                        Some(r) => println!("{}", hole_report(&r)),
                        None => println!("; no hole is held — write `,help` inside a form to make one"),
                    },
                    HoleCommand::Resume(expr) => match resume_line(&mut session, expr) {
                        Ok(v) => println!("{v}"),
                        Err(fixpt_scheme::SessionError::Hole(r)) => println!("{}", hole_report(&r)),
                        Err(e) => eprintln!("{e}"),
                    },
                }
            }
            Line::Form(text) if help::parse(&text).is_some() => {
                let ask = help::parse(&text).expect("just checked");
                help::answer(&mut SchemeHelp(&session), &ask);
            }
            Line::Form(text) => match run_line(&mut session, &text) {
                Ok(v) => println!("{v}"),
                Err(e) => eprintln!("{e}"),
            },
        }
    }
}

/// Run one REPL line, answering a `,help` hole rather than evaluating past it.
///
/// Scheme is where the dynamic half of `,help` earns its keep. The FX dialects
/// can answer a hole statically, from the operator's type; Scheme has no types
/// to consult, so the only way to say anything about a position is to *get
/// there* — run the program as written, with the hole replaced by a primitive
/// that reports the machine's pending work instead of computing a value. The
/// answer is then made of things that actually happened: this operator, these
/// arguments, these values.
fn run_line(session: &mut Session, text: &str) -> Result<String, String> {
    // Each line's handles are released when it is done.
    session.scope(|session| run_line_in(session, text))
}

fn run_line_in(session: &mut Session, text: &str) -> Result<String, String> {
    let forms = session.read_forms("<repl>", text).map_err(|e| e.to_string())?;
    let has_hole = {
        let names = |s: fixpt_read::Sym| session.interner_ref().name(s).to_string();
        forms.iter().any(|f| help::mentions_hole(f, &names))
    };
    if has_hole {
        let with = session.interner().intern("%hole");
        let names = |s: fixpt_read::Sym| session.interner_ref().name(s).to_string();
        let plugged: Vec<_> =
            forms.iter().map(|f| help::plug_hole(f, &names, with)).collect();
        return match session.eval_forms(&plugged) {
            // Reaching the hole raises, so a value means the hole was never
            // reached: the program took a branch around it, which is itself
            // the answer.
            Ok(v) => Ok(format!("; the hole was never reached — the form evaluated to {}", session.write(v))),
            Err(e @ fixpt_scheme::SessionError::Hole(_)) => Ok(format!(
                "{}\n; `,resume EXPR` continues from the hole with EXPR's value; `,where` repeats this",
                hole_report(&e.to_string())
            )),
            Err(e) => Ok(hole_report(&e.to_string())),
        };
    }
    session
        .eval_forms(&forms)
        .map(|v| session.write(v))
        .map_err(|e| e.to_string())
}

/// `,resume EXPR`. The expression may itself contain a hole — continuing
/// with a value that is still being worked out — so it is plugged exactly as
/// an ordinary line is.
fn resume_line(session: &mut Session, text: &str) -> Result<String, fixpt_scheme::SessionError> {
    session.scope(|session| {
        let forms = session.read_forms("<resume>", text)?;
        let with = session.interner().intern("%hole");
        let names = |s: fixpt_read::Sym| session.interner_ref().name(s).to_string();
        let plugged: Vec<_> = forms.iter().map(|f| help::plug_hole(f, &names, with)).collect();
        let v = session.resume_forms(&plugged)?;
        Ok(session.write(v))
    })
}

enum HoleCommand<'a> {
    /// `,where` — describe the held hole again.
    Where,
    /// `,resume EXPR` — continue the held hole with a value.
    Resume(&'a str),
}

fn hole_command(line: &str) -> Option<HoleCommand<'_>> {
    let line = line.trim();
    if line == ",where" {
        return Some(HoleCommand::Where);
    }
    let rest = line.strip_prefix(",resume")?;
    if !rest.is_empty() && !rest.starts_with(char::is_whitespace) {
        return None;
    }
    Some(HoleCommand::Resume(rest.trim()))
}

/// Print the engine's report as help rather than as a failure.
fn hole_report(raised: &str) -> String {
    let body = raised
        .split_once("evaluation reached a hole")
        .map(|(_, rest)| rest.trim_start_matches([':', ' ']))
        .unwrap_or(raised);
    let mut out = String::from("; at the hole:");
    for line in body.lines() {
        let line = line.trim();
        if !line.is_empty() {
            out.push_str("\n  ");
            out.push_str(line);
        }
    }
    out
}

/// The eager reader written in FX-26, checked, licensed and loaded into this
/// session. Nothing of it runs until the licence is checked: it runs on every
/// keystroke, so every entry point's effect must stay within the regions the
/// reader owns — allocation, and its own state, prompt and marks.
fn load_fx26_reader(session: &mut Session) -> Result<fixpt_scheme::eager::EagerReader, String> {
    fixpt_fx26::session::load_reader_alone(session)?;
    fixpt_scheme::eager::EagerReader::attach(session, fixpt_fx26::session::READER_PREFIX).map_err(|e| e.to_string())
}

/// The eager reader as the line editor's oracle: one checkpoint per character,
/// so each keystroke is one character's worth of parsing, and a mistake is
/// reported where it is made.
struct EagerOracle<'a> {
    session: &'a mut Session,
    reader: &'a mut fixpt_scheme::eager::EagerReader,
}

impl lineedit::Oracle for EagerOracle<'_> {
    fn status(&mut self, text: &str, at_enter: bool) -> lineedit::Status {
        eager_status(self.reader, self.session, text, at_enter, fixpt_read::SyntaxProfile::SCHEME, true)
    }
}

/// What an eager reader says of `text`, as the line editor wants it. With
/// `holes`, a `,help` hole at `Enter` asks for the form to be answered while
/// still unfinished; without, it is simply unfinished.
pub(crate) fn eager_status(
    reader: &mut fixpt_scheme::eager::EagerReader,
    session: &mut Session,
    text: &str,
    at_enter: bool,
    profile: fixpt_read::SyntaxProfile,
    holes: bool,
) -> lineedit::Status {
    use fixpt_scheme::eager::EagerStatus;
    use lineedit::Status;
    match reader.status(session, text, at_enter) {
        Ok(EagerStatus::Complete) => Status::Complete,
        Ok(EagerStatus::Incomplete) => Status::Incomplete,
        Ok(EagerStatus::Invalid { at, message }) => Status::Invalid { at, message },
        Ok(EagerStatus::Hole { closers }) if at_enter && holes => Status::Ask {
            closed: format!("{text}{closers}"),
            keep: without_trailing_hole(text),
        },
        Ok(EagerStatus::Hole { .. }) => Status::Incomplete,
        // The eager reader failing is a bug in it, not the user's problem:
        // fall back to the Rust reader for this answer.
        Err(_) => lineedit::Oracle::status(&mut lineedit::Reread(profile), text, at_enter),
    }
}

/// The text with the `,help` it ends with taken off.
fn without_trailing_hole(text: &str) -> String {
    let trimmed = text.trim_end();
    for hole in [",help", ",?"] {
        if let Some(rest) = trimmed.strip_suffix(hole) {
            return rest.to_string();
        }
    }
    text.to_string()
}

/// Scheme's answer to the same questions.
///
/// Less than FX can say, and the difference is the point: without types there
/// is no way to ask what accepts a value, so `,fits` reports that it needs a
/// typed dialect rather than returning nothing. What Scheme *does* know is the
/// primitive table — every name with its arity — and which globals are bound.
struct SchemeHelp<'a>(&'a Session);

impl help::Helpful for SchemeHelp<'_> {
    fn dialect(&self) -> &'static str {
        "Scheme"
    }

    fn holes(&self) -> bool {
        true
    }

    fn resumable(&self) -> bool {
        true
    }

    fn describe(&mut self, name: &str) -> Vec<String> {
        let mut out = Vec::new();
        if let Some(i) = fixpt_runtime::prim::lookup(name) {
            let d = fixpt_runtime::prim::def(i);
            out.push(format!("{name} — a primitive, {}", arity(d.min, d.max)));
        }
        let heap = &self.0.runtime_unrooted_ref().heap;
        if let Some(sym) = heap.intern_existing(name) {
            let v = heap.global(heap.symbol_global_slot(sym));
            if !v.is_unbound() && out.is_empty() {
                out.push(match arity_of_closure(self.0, v) {
                    Some(text) => format!("{name} — a procedure, {text}"),
                    None => format!("{name} = {}", fixpt_runtime::write_value(heap, v)),
                });
            }
        }
        out
    }

    fn apropos(&mut self, pattern: &str) -> Vec<String> {
        let mut out: Vec<String> = bound_names(self.0)
            .into_iter()
            .filter(|n| n.contains(pattern))
            .map(|n| match fixpt_runtime::prim::lookup(&n) {
                Some(i) => {
                    let d = fixpt_runtime::prim::def(i);
                    format!("{n} — a primitive, {}", arity(d.min, d.max))
                }
                None => n,
            })
            .collect();
        out.sort();
        out.dedup();
        out
    }
}

fn arity(min: usize, max: Option<usize>) -> String {
    match max {
        Some(m) if m == min => format!("{min} argument(s)"),
        Some(m) => format!("{min} to {m} arguments"),
        None => format!("{min} or more arguments"),
    }
}

/// A compiled or interpreted closure's arity, read off its code object.
fn arity_of_closure(session: &Session, v: fixpt_heap::Value) -> Option<String> {
    let heap = &session.runtime_unrooted_ref().heap;
    if !heap.is_a(v, fixpt_heap::ObjType::Closure) {
        return None;
    }
    let code = heap.closure_code(v);
    if !heap.is_a(code, fixpt_heap::ObjType::Code) {
        return None;
    }
    let n = heap.bloblet_slot(code, fixpt_core::lower::CODE_ARITY).as_fixnum() as usize;
    let rest = heap.bloblet_slot(code, fixpt_core::lower::CODE_HAS_REST).is_true();
    Some(arity(n, if rest { None } else { Some(n) }))
}

/// Every name the session has actually bound, for completion.
///
/// Read out of the heap's symbol table rather than kept alongside it, so a
/// procedure defined a moment ago can be completed immediately and one that was
/// never defined never appears.
pub fn bound_names(session: &Session) -> Vec<String> {
    let heap = &session.runtime_unrooted_ref().heap;
    let symbols: Vec<fixpt_heap::Value> = heap.symbols_slice().to_vec();
    symbols
        .into_iter()
        .filter(|s| !heap.global(heap.symbol_global_slot(*s)).is_unbound())
        .map(|s| heap.symbol_name(s))
        .filter(|n| !n.starts_with('%'))
        .collect()
}

fn image_command(args: &[String]) -> i32 {
    match args.first().map(String::as_str) {
        Some("info") | Some("verify") if args.len() == 2 => {
            let path = &args[1];
            let bytes = match std::fs::read(path) {
                Ok(b) => b,
                Err(e) => {
                    eprintln!("fixpt: cannot read {path}: {e}");
                    return 1;
                }
            };
            // An image may be appended to an executable rather than standing
            // alone; look for the trailer first.
            let img = image::extract_embedded(&bytes).unwrap_or(&bytes);
            match image::load(img) {
                Ok(heap) => {
                    println!("{path}: valid fixpt heap image");
                    println!("  live words:  {}", heap.used());
                    println!("  globals:     {}", heap.global_count());
                    println!("  symbols:     {}", heap.symbol_count());
                    if img.len() != bytes.len() {
                        println!(
                            "  embedded in an executable of {} bytes",
                            bytes.len() - img.len()
                        );
                    }
                    match heap.verify() {
                        Ok(()) => {
                            println!("  structure:   ok");
                            0
                        }
                        Err(e) => {
                            eprintln!("  structure:   FAILED: {e}");
                            1
                        }
                    }
                }
                Err(e) => {
                    eprintln!("fixpt: {path}: {e}");
                    1
                }
            }
        }
        _ => {
            eprintln!("usage: fixpt image info|verify FILE");
            2
        }
    }
}
