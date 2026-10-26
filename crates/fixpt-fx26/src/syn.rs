//! Reading FX-26 with the reader written in FX-26 (`eager-reader.fx`), and
//! turning what it read into the Rust checker's syntax.
//!
//! The reader builds `syn` values, a `define-datatype`: each piece of what
//! it read with where it starts and ends. At run time they are frozen
//! bloblets, a sum's tag and its product, so they can be walked here without
//! running anything. Positions are in characters there and in bytes in
//! [`Span`], and are converted with the text.

use crate::error::{FxError, R};
use crate::session::READER_PREFIX;
use fixpt_heap::Value;
use fixpt_read::{Datum, FileId, Interner, Num, Span, Syntax};
use fixpt_scheme::{Handle, Local, Session};
use fixpt_scheme::eager::EagerReader;
use std::collections::HashMap;
use crate::ast::ExpId;

/// Read `text` with the FX-26 reader, already loaded into `scheme` (see
/// [`crate::session::load_eager_reader`]), interning names in `interner`.
pub fn read_with_fx26_reader(scheme: &mut Session, interner: &mut Interner, file: FileId, text: &str) -> R<Vec<Syntax>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let mut reader =
        EagerReader::attach_starting(scheme, READER_PREFIX, "eager-start-fx26").map_err(|e| fail(e.to_string()))?;
    scheme.scope(|s| {
        // As though Enter were pressed: a newline ends a trailing atom.
        let st = reader.state_after(s, text, true).map_err(|e| fail(e.to_string()))?;
        let call = |s: &mut Session, name: &str| {
            s.call_global(&format!("{READER_PREFIX}{name}"), &[st]).map_err(|e| fail(e.to_string()))
        };
        let offsets = byte_offsets(text);
        let at = |c: i64| offsets.get(c as usize).copied().unwrap_or(text.len()) as u32;
        let status = call(s, "eager-status")?;
        match s.view(|v| v.get(status).symbol_name()).as_deref() {
            Some("complete") => {}
            Some("error") => {
                let pos = call(s, "eager-state-position")?;
                let msg = call(s, "eager-state-message")?;
                return Err(s.view(|v| {
                    let pos = v.get(pos).fixnum().unwrap_or(0);
                    FxError::at(Span::new(file, at(pos), at(pos)), v.get(msg).string().unwrap_or_default())
                }));
            }
            _ => {
                return Err(FxError::at(Span::new(file, text.len() as u32, text.len() as u32), "the text ends in the middle of a form"));
            }
        }
        let syns = call(s, "eager-state-syntax")?;
        s.view(|v| {
            let items = v.get(syns).list().expect("a list");
            items.into_iter().map(|x| to_syntax(interner, file, &at, x)).collect()
        })
    })
}

/// Parse `text` with the reader and the parser written in FX-26: each
/// top-level form's tree, as [`crate::sexp::show_value`] prints it.
pub fn parse_with_fx26_parser(scheme: &mut Session, file: FileId, text: &str) -> R<Vec<String>> {
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        Ok(s.view(|v| v.get(tops).list().expect("a list").into_iter().map(crate::sexp::show_value).collect()))
    })
}

/// Read, parse, check (in the initial environment `standard`) and run
/// `text` with the pieces written in FX-26, the evaluator running what the
/// checker says the program runs (`checked-tops`, under redefinition): its
/// value as Scheme would write it, or `!! ` and its error.
pub fn eval_with_fx26_evaluator(scheme: &mut Session, standard: Handle, file: FileId, text: &str) -> R<String> {
    eval_more_with_fx26_evaluator(scheme, Some(standard), file, text, 0)
}

/// [`eval_with_fx26_evaluator`], or, `standard` none, `text` as more of the
/// program the evaluator ran before: checked after the forms before, and
/// run with the globals they made (`run-checked-more`). Its positions are
/// counted from `base`, past every text given before, so that what the
/// checker says of a place is said of no other form's.
pub fn eval_more_with_fx26_evaluator(scheme: &mut Session, standard: Option<Handle>, file: FileId, text: &str, base: i64) -> R<String> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let entry = if standard.is_some() { "run-checked" } else { "run-checked-more" };
    scheme.scope(|s| {
        let tops = parse_to_trees_at(s, file, text, base)?;
        let checked = check_in(s, standard, tops).map_err(|e| fail(e.to_string()))?;
        if let Some(m) = s.view(|v| {
            let r = v.get(checked);
            (r.field(2).and_then(|t| t.symbol_name()).as_deref() == Some("k-err"))
                .then(|| r.field(3).and_then(|p| p.field(2)).and_then(|m| m.string()).unwrap_or_default())
        }) {
            return Ok(format!("!! check: {m}"));
        }
        let runs = s.call_global(&format!("{READER_PREFIX}checked-tops"), &[]).map_err(|e| fail(e.to_string()))?;
        // A primitive the evaluator calls may fail, as the program's own
        // failure (`DONE.md` §85).
        s.bare_failures = true;
        let out = s.call_global(&format!("{READER_PREFIX}{entry}"), &[runs]);
        s.bare_failures = false;
        match out {
            Ok(out) => Ok(s.view(|v| v.get(out).string().unwrap_or_default())),
            Err(e) => Ok(format!("!! {}", run_failure(&e.to_string()))),
        }
    })
}

/// Read, parse and compile `text` with the reader, the parser and the
/// compiler written in FX-26, and run the word it makes on the cellular
/// machine: the value, as Scheme writes it; or `!! ` and why it failed.
pub fn compile_with_fx26_compiler(scheme: &mut Session, standard: Handle, file: FileId, text: &str) -> R<String> {
    compile_with_fx26_compiler_showing(scheme, Some(standard), file, text, false, None).map(|(out, _)| out)
}

/// The same, and, if `show`, the word made, and every word it reaches,
/// disassembled before it runs; the run limited to `steps`, if given.
/// `standard` begins the checker's state; without it, `text` is checked
/// after the forms checked before (`check-more`), as the REPL gives them.
pub fn compile_with_fx26_compiler_showing(
    scheme: &mut Session,
    standard: Option<Handle>,
    file: FileId,
    text: &str,
    show: bool,
    steps: Option<u64>,
) -> R<(String, Option<String>)> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        // Checked first, by the checker written in FX-26, which says where
        // each `extract`'s field is.
        let checked = check_in(s, standard, tops).map_err(|e| fail(e.to_string()))?;
        if let Some(m) = s.view(|v| {
            let r = v.get(checked);
            (r.field(2).and_then(|t| t.symbol_name()).as_deref() == Some("k-err"))
                .then(|| r.field(3).and_then(|p| p.field(2)).and_then(|m| m.string()).unwrap_or_default())
        }) {
            return Ok((format!("!! check: {m}"), None));
        }
        let facts = s.call_global(&format!("{READER_PREFIX}checked-extracts"), &[]).map_err(|e| fail(e.to_string()))?;
        let runs = s.call_global(&format!("{READER_PREFIX}checked-tops"), &[]).map_err(|e| fail(e.to_string()))?;
        let start = std::time::Instant::now();
        let result = s.call_global(&format!("{READER_PREFIX}compile-checked"), &[runs, facts]).map_err(|e| fail(e.to_string()))?;
        s.runtime_unrooted().compile_nanos += start.elapsed().as_nanos() as u64;
        let (tag, word) = s.view(|v| {
            let r = v.get(result);
            let tag = r.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
            let payload = r.field(3).expect("a sum");
            (tag, payload.field(2).map(|x| x.string()))
        });
        if tag == "c-err" {
            return Ok((format!("!! compile: {}", word.flatten().unwrap_or_default()), None));
        }
        let word = s.make(|m| {
            let r = m.get(result);
            let payload = m.heap().bloblet_slot(r, 3);
            m.heap().bloblet_slot(payload, 2)
        });
        let mut words = None;
        if show {
            let _ = s.make(|m| {
                let w = m.get(word);
                words = Some(fixpt_runtime::disasm::disassemble(m.heap(), w));
                w
            });
        }
        let no_args = s.make(|_| Value::NULL);
        s.runtime_unrooted().word_fuel = steps.unwrap_or(u64::MAX);
        if let Err(why) = assemble_by_fx26(s, word) {
            return Ok((format!("!! native.fx: {why}"), words));
        }
        let start = std::time::Instant::now();
        let run = s.call_global("%run-word", &[word, no_args]);
        s.runtime_unrooted().run_nanos += start.elapsed().as_nanos() as u64;
        s.runtime_unrooted().word_fuel = u64::MAX;
        match run {
            Ok(v) => Ok((s.write(v), words)),
            Err(e) => Ok((format!("!! {}", run_failure(&e.to_string())), words)),
        }
    })
}

/// A run's failure, `why`, as the program's own (`DONE.md` §85): not the
/// word's that ran it, and a step limit as the lowered form says it,
/// whichever machine ran out.
fn run_failure(why: &str) -> &str {
    let why = why.trim_start_matches("error: ").trim_start_matches("cellular word: ");
    if why.contains("step limit") { "evaluation step limit exceeded" } else { why }
}

/// When the runtime places code made elsewhere (its `place_code`): every
/// word made of cells that `word` reaches, compiled to machine code by the
/// compiler written in FX-26 and placed ([`assemble_reachable_by_fx26`]).
/// The time is compiling's.
fn assemble_by_fx26(s: &mut Session, word: Handle) -> Result<(), String> {
    let Some(place) = s.runtime_unrooted().place_code else { return Ok(()) };
    let start = std::time::Instant::now();
    let r = assemble_reachable_by_fx26(s, word, &mut |heap, w, code, starts| place(heap, w, code, starts));
    s.runtime_unrooted().compile_nanos += start.elapsed().as_nanos() as u64;
    r
}

/// The words made of cells (not yet compiled) that `word` reaches through
/// its cells and operands, `word` too if it is one: what `fixpt_native`'s
/// `compile_reachable` compiles.
pub fn cell_words_reachable(heap: &fixpt_heap::Heap, word: Value) -> Vec<Value> {
    use fixpt_heap::layout::cellular::{CLOSURE_WORD, PRIMITIVES, ROUTINE_DOCOL, WORD_CELL0, WORD_ENTRY};
    let closure = const { fixpt_heap::layout::kind("cellular-closure") };
    let (mut todo, mut seen, mut found) = (vec![word], std::collections::HashSet::new(), Vec::new());
    while let Some(w) = todo.pop() {
        if !seen.insert(w.raw()) {
            continue;
        }
        let entry = heap.bloblet_slot(w, WORD_ENTRY).as_fixnum() as u64;
        if entry != ROUTINE_DOCOL && entry < PRIMITIVES as u64 {
            continue;
        }
        for k in WORD_CELL0..=heap.bloblet_head(w).fields {
            let v = heap.bloblet_slot(w, k);
            if heap.is_cellular_word(v) {
                todo.push(v);
            } else if v.is_bloblet() && heap.bloblet_kind(v) == closure {
                todo.push(heap.bloblet_slot(v, CLOSURE_WORD));
            }
        }
        if entry == ROUTINE_DOCOL {
            found.push(w);
        }
    }
    found
}

/// Every word made of cells that `word` reaches
/// ([`cell_words_reachable`]), compiled to machine code for the machine
/// this runs on by the compiler written in FX-26 (`native.fx`'s
/// `native-assemble` for arm64, `native-x64.fx`'s `native-assemble-x64`
/// for x86_64) and given to `place` with the heap: its bytes, and where
/// each cell's code starts in them. On x86_64, a word with register code
/// (its twin, `layout::regcode`) has that compiled instead
/// (`native-x64-regs.fx`), and its entry is the adapter into it, as
/// `fixpt_native`'s `compile_register_word` does them.
pub fn assemble_reachable_by_fx26(
    s: &mut Session,
    word: Handle,
    place: &mut dyn FnMut(&mut fixpt_heap::Heap, Value, &[u8], &[i64]) -> Result<(), String>,
) -> Result<(), String> {
    // Found where nothing can collect, then rooted: running the compiler
    // may collect.
    let mut found = Vec::new();
    s.make(|m| {
        let first = m.get(word);
        found = cell_words_reachable(m.heap(), first);
        Value::NULL
    });
    let words: Vec<Handle> = found.into_iter().map(|w| s.make(|_| w)).collect();
    // The code reaches the machine's common trap and exit through the
    // state, so where it goes does not change it.
    let far = s.make(|_| Value::fixnum(0));
    let x64 = cfg!(target_arch = "x86_64");
    for w in words {
        if x64 && assemble_twin_by_fx26(s, w, place)? {
            continue;
        }
        let assembled = if x64 {
            s.call_global(&format!("{READER_PREFIX}native-assemble-x64"), &[w])
        } else {
            s.call_global(&format!("{READER_PREFIX}native-assemble"), &[w, far, far])
        };
        let assembled = assembled.map_err(|e| e.to_string())?;
        let (code, starts) = s.view(|v| {
            let r = v.get(assembled);
            (ints_of(r.field(2)), ints_of(r.field(3)))
        });
        // arm64's instructions are words of 4 bytes, little-endian.
        let (code, starts): (Vec<u8>, Vec<i64>) = if x64 {
            (code.into_iter().map(|x| x as u8).collect(), starts)
        } else {
            (code.into_iter().flat_map(|x| (x as u32).to_le_bytes()).collect(), starts.into_iter().map(|s| if s < 0 { s } else { 4 * s }).collect())
        };
        place_in(s, w, &code, &starts, place)?;
    }
    Ok(())
}

/// A list of ints, or none.
fn ints_of(l: Option<Local>) -> Vec<i64> {
    l.and_then(|l| l.list()).unwrap_or_default().iter().filter_map(|x| x.fixnum()).collect()
}

/// `code` given to `place` as word `w`'s, with where its cells start.
fn place_in(
    s: &mut Session,
    w: Handle,
    code: &[u8],
    starts: &[i64],
    place: &mut dyn FnMut(&mut fixpt_heap::Heap, Value, &[u8], &[i64]) -> Result<(), String>,
) -> Result<(), String> {
    let mut placed = Ok(());
    s.make(|m| {
        let w = m.get(w);
        placed = place(m.heap(), w, code, starts);
        Value::NULL
    });
    placed
}

/// Word `w`'s register code, if it has some not yet compiled, compiled
/// to x86_64 by `native-x64-regs.fx` and placed, and the adapter into it
/// as `w`'s entry: whether it was. Not a variadic procedure's, which is
/// for native code, nor, past `REGS` arguments, the adapter, which would
/// have to make a list of the rest: `w` stays stack code then.
fn assemble_twin_by_fx26(
    s: &mut Session,
    w: Handle,
    place: &mut dyn FnMut(&mut fixpt_heap::Heap, Value, &[u8], &[i64]) -> Result<(), String>,
) -> Result<bool, String> {
    use fixpt_heap::layout::cellular::{WORD_CELL0, WORD_ENTRY, WORD_TWIN};
    let mut twin = None;
    s.make(|m| {
        let w = m.get(w);
        let heap = m.heap();
        let rw = heap.bloblet_slot(w, WORD_TWIN);
        if heap.is_register_word(rw)
            && heap.bloblet_slot(rw, WORD_ENTRY).as_fixnum() == 0
            && heap.bloblet_slot(rw, WORD_CELL0).as_fixnum() as usize != const { fixpt_heap::layout::regcode::op("vargs") }
        {
            twin = Some(rw);
        }
        Value::NULL
    });
    let Some(rw) = twin else { return Ok(false) };
    let rw = s.make(|_| rw);
    let assembled = s.call_global(&format!("{READER_PREFIX}native-assemble-x64-regs"), &[rw]).map_err(|e| e.to_string())?;
    let (code, resume, err) = s.view(|v| {
        let r = v.get(assembled);
        (ints_of(r.field(2)), ints_of(r.field(3)), r.field(4).and_then(|e| e.string()).unwrap_or_default())
    });
    if !err.is_empty() {
        return Err(format!("register code: {err}"));
    }
    let code: Vec<u8> = code.into_iter().map(|x| x as u8).collect();
    place_in(s, rw, &code, &resume, place)?;
    let (mut slot, mut n, mut cells) = (0, 0, 0);
    s.make(|m| {
        let (rw, w) = (m.get(rw), m.get(w));
        let heap = m.heap();
        slot = heap.bloblet_slot(rw, WORD_ENTRY).as_fixnum();
        n = heap.bloblet_slot(rw, WORD_CELL0 + 1).as_fixnum();
        cells = heap.bloblet_head(w).fields + 1 - WORD_CELL0;
        Value::NULL
    });
    if n as usize > fixpt_heap::layout::regcode::REGS {
        return Ok(false);
    }
    let (n, slot) = (s.make(|_| Value::fixnum(n)), s.make(|_| Value::fixnum(slot)));
    let adapter = s.call_global(&format!("{READER_PREFIX}native-adapter-x64"), &[n, slot]).map_err(|e| e.to_string())?;
    let adapter: Vec<u8> = s.view(|v| ints_of(Some(v.get(adapter)))).into_iter().map(|x| x as u8).collect();
    let mut starts = vec![-1i64; cells];
    starts[0] = 0;
    place_in(s, w, &adapter, &starts, place)?;
    Ok(true)
}

/// Check, compile and run `text`, a program whose last form names a global,
/// with the pieces written in FX-26: that global's value, given to `f` with
/// the runtime, which only `f` changes while it runs (the value is not
/// rooted: it moves if `f` collects); or why there is none.
pub fn with_last_value<T>(
    scheme: &mut Session,
    standard: Option<Handle>,
    file: FileId,
    text: &str,
    native: Option<crate::session::NativeFx>,
    f: impl FnOnce(&mut fixpt_runtime::Runtime, Value) -> T,
) -> R<Result<T, String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        let checked = check_in(s, standard, tops).map_err(|e| fail(e.to_string()))?;
        if let Some(m) = s.view(|v| {
            let r = v.get(checked);
            (r.field(2).and_then(|t| t.symbol_name()).as_deref() == Some("k-err"))
                .then(|| r.field(3).and_then(|p| p.field(2)).and_then(|m| m.string()).unwrap_or_default())
        }) {
            return Ok(Err(format!("check: {m}")));
        }
        let facts = s.call_global(&format!("{READER_PREFIX}checked-extracts"), &[]).map_err(|e| fail(e.to_string()))?;
        let word = match compile_checked_to_word(s, file, facts)? {
            Ok(w) => w,
            Err(m) => return Ok(Err(format!("compile: {m}"))),
        };
        assemble_by_fx26(s, word).map_err(|why| fail(format!("native.fx: {why}")))?;
        let no_args = s.make(|_| Value::NULL);
        let v = match s.call_global("%run-word", &[word, no_args]) {
            Ok(v) => v,
            Err(e) => return Ok(Err(e.to_string())),
        };
        // Compiled to native code by the compiler written in FX-26, if it
        // is to be (`Fx26Session::native_fx`): what declines is given as it
        // is, the compiler having kept why for the runner.
        let v = match native {
            Some(compile) => compile(s, v).unwrap_or(v),
            None => v,
        };
        let mut value = Value::NULL;
        s.make(|m| {
            value = m.get(v);
            value
        });
        Ok(Ok(f(s.runtime_unrooted(), value)))
    })
}

/// `text` checked by the checker written in FX-26 (after the forms before,
/// without `standard`), and nothing more: what it found wrong, if anything.
pub fn check_only(scheme: &mut Session, standard: Option<Handle>, file: FileId, text: &str) -> R<Result<(), String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        let checked = check_in(s, standard, tops).map_err(|e| fail(e.to_string()))?;
        Ok(match s.view(|v| {
            let r = v.get(checked);
            (r.field(2).and_then(|t| t.symbol_name()).as_deref() == Some("k-err"))
                .then(|| r.field(3).and_then(|p| p.field(2)).and_then(|m| m.string()).unwrap_or_default())
        }) {
            Some(m) => Err(m),
            None => Ok(()),
        })
    })
}

/// The checker written in FX-26 on `tops`: a program, in the initial
/// environment `standard`; or, without it, more forms after those checked
/// before.
fn check_in(s: &mut Session, standard: Option<Handle>, tops: Handle) -> Result<Handle, fixpt_scheme::SessionError> {
    // What these callers keep is the facts, not the lines (`check-lines!`).
    lines(s, false)?;
    match standard {
        Some(std) => s.call_global(&format!("{READER_PREFIX}check-program"), &[std, tops]),
        None => s.call_global(&format!("{READER_PREFIX}check-more"), &[tops]),
    }
}

/// Whether the checker written in FX-26 makes each form's line, `define
/// name : type ! effect`: only for a caller that reads them.
pub fn lines(s: &mut Session, on: bool) -> Result<(), fixpt_scheme::SessionError> {
    let v = s.make(|_| Value::boolean(on));
    s.call_global(&format!("{READER_PREFIX}check-lines!"), &[v]).map(|_| ())
}

/// What the checker written in FX-26 made of a program: for each definition
/// and expression, in order, `define name : type ! effect` or `type !
/// effect`; or its first error.
pub type Checked26 = Result<Vec<String>, FxError>;

/// Read, parse and check `text` with the reader, the parser and the checker
/// written in FX-26, in the initial environment of [`crate::standard`].
/// The outer error is the front end failing to read or parse.
pub fn check_with_fx26_checker(scheme: &mut Session, standard: Handle, file: FileId, text: &str) -> R<Checked26> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    // With `FIXPT_TIME_PHASES` set, how long each phase took.
    let timing = std::env::var_os("FIXPT_TIME_PHASES").is_some();
    let started = std::time::Instant::now();
    let phase = |name: &str| {
        if timing {
            eprintln!("check-program: {name} at {:.3} s", started.elapsed().as_secs_f64());
        }
    };
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        phase("program parsed");
        lines(s, true).map_err(|e| fail(e.to_string()))?;
        let result = s.call_global(&format!("{READER_PREFIX}check-program"), &[standard, tops]).map_err(|e| fail(e.to_string()))?;
        phase("checked");
        let offsets = byte_offsets(text);
        let at = |c: i64| offsets.get(c as usize).copied().unwrap_or(text.len()) as u32;
        Ok(s.view(|v| {
            let r = v.get(result);
            let tag = r.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
            let p = r.field(3).expect("a sum");
            if tag == "k-ok" {
                let lines = p.field(2).and_then(|l| l.list()).unwrap_or_default();
                Ok(lines.into_iter().map(|l| l.string().unwrap_or_default()).collect())
            } else {
                let message = p.field(2).and_then(|m| m.string()).unwrap_or_default();
                let (a, b) = (p.field(3).and_then(|x| x.fixnum()).unwrap_or(0), p.field(4).and_then(|x| x.fixnum()).unwrap_or(0));
                Err(FxError::at(Span::new(file, at(a), at(b)), message))
            }
        }))
    })
}

/// The initial environment of [`crate::standard`], read by the FX-26
/// reader, as `(name type)` for each binding: what `check-program` takes.
pub fn read_standard(scheme: &mut Session) -> R<Handle> {
    let text = crate::standard::standard_text();
    read_to_syns(scheme, FileId(0), &text)
}

/// What the FX-26 reader reads from `text`: a list of `syn`s, as a handle
/// in the caller's scope.
pub fn read_to_syns(scheme: &mut Session, file: FileId, text: &str) -> R<Handle> {
    read_to_syns_at(scheme, file, text, 0)
}

/// [`read_to_syns`], its positions counted from `at`: a loaded file's
/// base, so that the parser takes its syntax as read, not moved there.
pub fn read_to_syns_at(scheme: &mut Session, file: FileId, text: &str, at: i64) -> R<Handle> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    // The whole text read inside FX-26 (`read-text`), not fed from here a
    // character at a time: so that with the front end run as register code
    // (`FRONT_ENTRIES`) the reader is too, not lowered Scheme.
    // With no step limit: it is licensed code, and a text ends (as
    // `Fx26Session::read_with_own_reader`). Fed a character at a time,
    // each call was a few steps; the whole text is many.
    let s = scheme.make(|m| m.heap().make_string(text));
    let limit = scheme.engine.step_limit();
    scheme.engine.set_step_limit(None);
    let at = scheme.make(|_| fixpt_heap::Value::fixnum(at));
    let read = scheme.call_global(&format!("{READER_PREFIX}read-text-at"), &[s, at]);
    scheme.engine.set_step_limit(limit);
    let read = read.map_err(|e| fail(e.to_string()))?;
    // Its forms, the list's one element, or `#f` for none.
    let mut read_all = false;
    let forms = scheme.make(|m| {
        let l = m.get(read);
        read_all = !l.is_null();
        if read_all { m.heap().car(l) } else { fixpt_heap::Value::FALSE }
    });
    if !read_all {
        // Where and why, as the Rust reader says: the two agree on what
        // reads (`tests/syn.rs`), and it places its errors, where an
        // unfinished read here has no one place to blame.
        let mut interner = fixpt_read::Interner::new();
        if let Err(e) = fixpt_read::Reader::new(text, file, fixpt_read::SyntaxProfile::FX26, &mut interner).read_all() {
            return Err(FxError::at(e.span, e.message));
        }
        return Err(fail("the FX-26 reader did not read the whole text".into()));
    }
    Ok(forms)
}

/// What the Rust checker finds about `text` that the compiler written in
/// FX-26 needs, as `checked-extracts` would give it: each `extract`'s
/// field, keyed by where it is, in characters. A handle in the caller's
/// scope; or the check's error. In the cellular convention.
pub fn rust_facts(scheme: &mut Session, file: FileId, text: &str) -> R<Handle> {
    rust_facts_in(scheme, file, text, crate::ast::Conv::Cellular, false)
}

/// [`rust_facts`] of a program of convention `conv`, as its own checker
/// (`Fx26Session::fresh_checker`) checks it: what each call is compiled in
/// follows. With `syscalls`, a runtime's program (`Checker::syscalls`).
pub fn rust_facts_in(scheme: &mut Session, file: FileId, text: &str, conv: crate::ast::Conv, syscalls: bool) -> R<Handle> {
    let mut c = crate::Checker::with_convention(conv);
    c.syscalls = syscalls;
    c.base_dir = LOAD_BASE.with(|b| b.borrow().clone());
    let forms = c.read_in(file, text)?;
    let done = c.declare_ahead(&forms)?;
    // Which of the expressions at its span each is, as the FX-26 parser
    // numbers them (`crate::ids`): the forms in order, each after the
    // hidden globals of the files it loads first.
    let mut kth = crate::ids::Kth::new();
    for (f, done) in forms.iter().zip(done) {
        if !done {
            let defining = c.top_defining(f)?;
            for (t, _) in defining.hoisted.iter().chain(&defining.run[..1]) {
                kth.top(&c, t);
            }
        }
    }
    // Where a span is, as the pieces written in FX-26 have it: in
    // characters; in a module's file (`load-module`), past that file's base.
    let offsets = byte_offsets(text);
    let files: HashMap<FileId, Vec<usize>> = c.loaded.values().map(|(_, t, f)| (*f, byte_offsets(t))).collect();
    let at = |f: FileId, byte: u32| -> i64 {
        match files.get(&f) {
            Some(o) if f != file => LOAD_BASE_STEP * (f.0 as i64 - 1000) + o.partition_point(|&x| x < byte as usize) as i64,
            _ => offsets.partition_point(|&o| o < byte as usize) as i64,
        }
    };
    // An expression's identity (`k-at`): where it starts and ends, and which
    // of the expressions there it is.
    let place = |e: ExpId| {
        let span = c.arena.span_of(e);
        (at(span.file, span.start), at(span.file, span.end), kth.of(e) as i64)
    };
    type At = (i64, i64, i64);
    // What each is noted to be, as `k-noted` says it: its constructor, and
    // its value: none, an integer, or a `k-datum`.
    enum Noted {
        None,
        Int(i64),
        Datum(crate::check::Datum),
        // A sum of no fields, by its constructor's name.
        Tag(&'static str),
    }
    let facts: Vec<(At, &str, Noted)> = c.facts.datum.iter().map(|(e, d)| (place(*e), "n-datum", Noted::Datum(*d))).collect();
    // And each expression's effect summary: the greatest of its effects'.
    let mut summaries: HashMap<At, i64> = HashMap::new();
    for (e, s) in c.effect_summaries_by_exp() {
        let k = summaries.entry(place(e)).or_insert(s as i64);
        *k = (*k).max(s as i64);
    }
    let facts: Vec<(At, &str, Noted)> = facts
        .into_iter()
        .chain(summaries.into_iter().map(|(at, s)| (at, "n-summary", Noted::Int(s))))
        // And each conversion, its code (`k-convert-at`).
        .chain(c.facts.converted.keys().filter_map(|e| c.facts.conversion_code(*e).map(|k| (place(*e), "n-conversion", Noted::Int(k)))))
        // And each `apply` of a list at `acyclic` (`k-note-apply-shares`).
        .chain(c.facts.apply_shares.iter().map(|e| (place(*e), "n-apply-shares", Noted::None)))
        // And each definition's value that is a list nothing writes
        // (`k-note-frozen-define`).
        .chain(c.facts.frozen_defines.iter().map(|e| (place(*e), "n-frozen-define", Noted::None)))
        // And each `(with #%fx n)` that is the plain `n` (`k-synth-fx`).
        .chain(c.facts.fx_plain.keys().map(|e| (place(*e), "n-plain-fx", Noted::None)))
        // And each call's convention, a `k-conv` (`k-note-call`).
        .chain(c.facts.call_convs.keys().map(|e| {
            let cv = match c.facts.call_conv(*e) {
                crate::ast::Conv::Cellular => "cv-cellular",
                crate::ast::Conv::Native => "cv-native",
                _ => "cv-fx",
            };
            (place(*e), "n-call", Noted::Tag(cv))
        }))
        .collect();
    // A datatype's value: a sum of its constructor's name and the product
    // of its fields.
    let sum = |scheme: &mut Session, name: &str, fields: &[Handle]| -> R<Handle> {
        let mut parts = vec![scheme.make(|_| Value::fixnum(37))];
        parts.extend_from_slice(fields);
        let fields = scheme.call_global("%make-frozen", &parts).map_err(|e| FxError::at(Span::new(file, 0, 0), e.to_string()))?;
        let (tag, name) = (scheme.make(|_| Value::fixnum(36)), scheme.make(|m| m.heap().intern(name)));
        scheme.call_global("%make-frozen", &[tag, name, fields]).map_err(|e| FxError::at(Span::new(file, 0, 0), e.to_string()))
    };
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    // An identity, as the product `k-at` is.
    let identity = |scheme: &mut Session, (a, b, k): At| -> R<Handle> {
        let args = [37, a, b, k].map(|n| scheme.make(|_| Value::fixnum(n)));
        scheme.call_global("%make-frozen", &args).map_err(|e| fail(e.to_string()))
    };
    // And each `with`'s module's values it names, and their positions, by
    // expression (`checked-withs!`): the checker's record, which the
    // compiler reads.
    let mut withs = scheme.make(|_| Value::NULL);
    for (e, names) in &c.facts.with_vals {
        let (mut ns, mut is) = (scheme.make(|_| Value::NULL), scheme.make(|_| Value::NULL));
        for (n, i) in names.iter().rev() {
            let sym = scheme.make(|m| m.heap().intern(c.interner.name(*n)));
            ns = scheme.call_global("cons", &[sym, ns]).map_err(|e| fail(e.to_string()))?;
            let at = scheme.make(|_| Value::fixnum(*i as i64));
            is = scheme.call_global("cons", &[at, is]).map_err(|e| fail(e.to_string()))?;
        }
        let at = identity(scheme, place(*e))?;
        let tag = scheme.make(|_| Value::fixnum(37));
        let one = scheme.call_global("%make-frozen", &[tag, at, ns, is]).map_err(|e| fail(e.to_string()))?;
        withs = scheme.call_global("cons", &[one, withs]).map_err(|e| fail(e.to_string()))?;
    }
    scheme.call_global(&format!("{READER_PREFIX}checked-withs!"), &[withs]).map_err(|e| fail(e.to_string()))?;
    // And each module reshaped, with the positions it keeps (`checked-reshapes!`).
    let mut reshapes = scheme.make(|_| Value::NULL);
    for (e, keep) in &c.facts.reshaped {
        let mut ks = scheme.make(|_| Value::NULL);
        // Each a `k-pick`, `check-env-types.fx`'s.
        for k in keep.iter().rev() {
            let ns: Vec<Handle> = match k.steps() {
                (k, None) => vec![scheme.make(|_| Value::fixnum(k as i64))],
                (k, Some(j)) => vec![scheme.make(|_| Value::fixnum(k as i64)), scheme.make(|_| Value::fixnum(j as i64))],
            };
            let k = sum(scheme, if ns.len() == 1 { "pick-value" } else { "pick-path" }, &ns)?;
            ks = scheme.call_global("cons", &[k, ks]).map_err(|e| fail(e.to_string()))?;
        }
        let at = identity(scheme, place(*e))?;
        let tag = scheme.make(|_| Value::fixnum(37));
        let one = scheme.call_global("%make-frozen", &[tag, at, ks]).map_err(|e| fail(e.to_string()))?;
        reshapes = scheme.call_global("cons", &[one, reshapes]).map_err(|e| fail(e.to_string()))?;
    }
    scheme.call_global(&format!("{READER_PREFIX}checked-reshapes!"), &[reshapes]).map_err(|e| fail(e.to_string()))?;
    let mut list = scheme.make(|_| Value::NULL);
    for (at, noted, value) in facts {
        use crate::check::Datum;
        let at = identity(scheme, at)?;
        let int = |scheme: &mut Session, n: i64| scheme.make(|_| Value::fixnum(n));
        let fields = match value {
            Noted::None => Vec::new(),
            Noted::Int(n) => vec![int(scheme, n)],
            Noted::Tag(name) => vec![sum(scheme, name, &[])?],
            // A `k-datum`, `parser-types.fx`'s.
            Noted::Datum(d) => {
                let (name, ns) = match d {
                    Datum::Field(i) => ("datum-field", vec![i as i64]),
                    Datum::BlobrefField(o) => ("datum-blobref-field", vec![o as i64]),
                    Datum::Layout(code) => ("datum-layout", vec![code as i64]),
                    Datum::Array { n, size } => ("datum-array", vec![n, size as i64]),
                    Datum::Fits(size) => ("datum-fits", vec![size as i64]),
                };
                let ns: Vec<Handle> = ns.into_iter().map(|n| int(scheme, n)).collect();
                vec![sum(scheme, name, &ns)?]
            }
        };
        let noted = sum(scheme, noted, &fields)?;
        let tag = scheme.make(|_| Value::fixnum(37));
        let fact = scheme.call_global("%make-frozen", &[tag, at, noted]).map_err(|e| fail(e.to_string()))?;
        list = scheme.call_global("cons", &[fact, list]).map_err(|e| fail(e.to_string()))?;
    }
    Ok(list)
}

/// Compile `text` with the compiler written in FX-26, given what checking
/// it found (`facts`, from `checked-extracts` or [`rust_facts`]): the word
/// that runs the program, as a handle in the caller's scope, or why the
/// compiler would not make one.
/// The same, with each lambda's register code as its word's twin, made by the
/// register compiler written in FX-26 (`regcode.fx`).
pub fn compile_to_word_with_registers(scheme: &mut Session, file: FileId, text: &str, facts: Handle) -> R<Result<Handle, String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let on = scheme.make(|_| Value::TRUE);
    scheme.call_global(&format!("{READER_PREFIX}compile-registers!"), &[on]).map_err(|e| fail(e.to_string()))?;
    let out = compile_to_word(scheme, file, text, facts);
    let off = scheme.make(|_| Value::FALSE);
    scheme.call_global(&format!("{READER_PREFIX}compile-registers!"), &[off]).map_err(|e| fail(e.to_string()))?;
    out
}

/// Compile what the checker written in FX-26 just checked, as it runs it
/// (`checked-tops`, under redefinition), given what it found (`facts`):
/// the word, as a handle in the caller's scope, or why the compiler would
/// not make one.
pub fn compile_checked_to_word(scheme: &mut Session, file: FileId, facts: Handle) -> R<Result<Handle, String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let runs = scheme.call_global(&format!("{READER_PREFIX}checked-tops"), &[]).map_err(|e| fail(e.to_string()))?;
    let start = std::time::Instant::now();
    let result = scheme.call_global(&format!("{READER_PREFIX}compile-checked"), &[runs, facts]).map_err(|e| fail(e.to_string()))?;
    scheme.runtime_unrooted().compile_nanos += start.elapsed().as_nanos() as u64;
    word_of(scheme, result)
}

pub fn compile_to_word(scheme: &mut Session, file: FileId, text: &str, facts: Handle) -> R<Result<Handle, String>> {
    let tops = parse_to_trees(scheme, file, text)?;
    compile_trees_to_word(scheme, file, tops, facts)
}

/// The same, from the program's trees ([`parse_syns`]).
pub fn compile_trees_to_word(scheme: &mut Session, file: FileId, tops: Handle, facts: Handle) -> R<Result<Handle, String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let result = scheme.call_global(&format!("{READER_PREFIX}compile-program"), &[tops, facts]).map_err(|e| fail(e.to_string()))?;
    word_of(scheme, result)
}

/// A `cresult`'s word, or its error.
fn word_of(scheme: &mut Session, result: Handle) -> R<Result<Handle, String>> {
    let err = scheme.view(|v| {
        let r = v.get(result);
        (r.field(2).and_then(|t| t.symbol_name()).as_deref() == Some("c-err"))
            .then(|| r.field(3).and_then(|p| p.field(2)).and_then(|m| m.string()).unwrap_or_default())
    });
    Ok(match err {
        Some(m) => Err(m),
        None => Ok(scheme.make(|m| {
            let r = m.get(result);
            let payload = m.heap().bloblet_slot(r, 3);
            m.heap().bloblet_slot(payload, 2)
        })),
    })
}

/// The parser's trees for `text`: a list of `top`s, as a handle in the
/// caller's scope.
fn parse_to_trees(scheme: &mut Session, file: FileId, text: &str) -> R<Handle> {
    parse_to_trees_at(scheme, file, text, 0)
}

/// [`parse_to_trees`], its positions counted from `base`.
fn parse_to_trees_at(scheme: &mut Session, file: FileId, text: &str, base: i64) -> R<Handle> {
    supply_loaded_at(scheme, file, text, base)?;
    let syns = read_to_syns_at(scheme, file, text, base)?;
    parse_syns_at(scheme, file, text, syns, base)
}

/// What the parser written in FX-26 makes of `syns`, read from `text`
/// ([`read_to_syns`]): the program's trees, or where it is wrong.
pub fn parse_syns(scheme: &mut Session, file: FileId, text: &str, syns: Handle) -> R<Handle> {
    parse_syns_at(scheme, file, text, syns, 0)
}

/// [`parse_syns`], the positions read counted from `base`.
fn parse_syns_at(scheme: &mut Session, file: FileId, text: &str, syns: Handle, base: i64) -> R<Handle> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let result = scheme.call_global(&format!("{READER_PREFIX}parse-program"), &[syns]).map_err(|e| fail(e.to_string()))?;
    let (tag, err) = scheme.view(|v| {
        let r = v.get(result);
        let tag = r.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
        let p = r.field(3).expect("a sum");
        let err = (tag == "p-err").then(|| {
            (p.field(2).and_then(|m| m.string()).unwrap_or_default(), p.field(3).and_then(|x| x.fixnum()).unwrap_or(0), p.field(4).and_then(|x| x.fixnum()).unwrap_or(0))
        });
        (tag, err)
    });
    if let Some((msg, a, b)) = err {
        let offsets = byte_offsets(text);
        let at = |c: i64| offsets.get((c - base).max(0) as usize).copied().unwrap_or(text.len()) as u32;
        return Err(FxError::at(Span::new(file, at(a), at(b)), msg));
    }
    debug_assert_eq!(tag, "p-ok");
    Ok(scheme.make(|m| {
        let r = m.get(result);
        let payload = m.heap().bloblet_slot(r, 3);
        m.heap().bloblet_slot(payload, 2)
    }))
}

thread_local! {
    /// Where a `load-module`'s relative path is from, for the pieces written
    /// in FX-26: the program's directory, or none for the current one.
    static LOAD_BASE: std::cell::RefCell<Option<std::path::PathBuf>> = const { std::cell::RefCell::new(None) };
}

/// Set where `load-module`'s relative paths are from (`Checker::base_dir`).
pub fn set_load_base(dir: Option<std::path::PathBuf>) {
    LOAD_BASE.with(|b| *b.borrow_mut() = dir);
}

thread_local! {
    /// The loads whose hidden globals the session has made already, by
    /// key: the parser written in FX-26 is told so (a file at base -1), and
    /// makes none of them again, so that a form compiled alone, as the
    /// native convention compiles each, uses the one made in the program's
    /// convention (`Fx26Session::shared_made`).
    static SHARED_MADE: std::cell::RefCell<std::collections::HashSet<String>> = std::cell::RefCell::new(Default::default());
}

/// Set the loads the session has made (`SHARED_MADE`).
pub fn set_shared_made(made: std::collections::HashSet<String>) {
    SHARED_MADE.with(|m| *m.borrow_mut() = made);
}

/// The positions of one module file and the next apart, in the parser
/// written in FX-26 (`parser-exps.fx`'s `load-base`).
const LOAD_BASE_STEP: i64 = 1_000_000_000;

/// A load found in a text: where it starts, its path as written, whether
/// it is a `load-input`, and, a `(%loaded "key" "path")`'s, the file its key
/// names, the path resolved.
type Load = (u32, String, bool, Option<String>);

/// Each `(load-module "path")` in `forms`, in order: where it starts, and
/// the path; and each form of processes or `par`, which loads the scheduler
/// (`parser-forms.fx`). Only where an expression is, as the parsers read
/// them: a name bound, a parameter, a type, a `tagcase`'s arm's tag, which
/// may be a list headed by a form's name (a binding `(self x)`), is none
/// (`TODO.md` §92). A load found where the parsers find none would be a
/// file read the Rust checker does not read, the numbering of the files
/// after it moved.
fn load_modules_in(forms: &[Syntax], interner: &Interner, out: &mut Vec<Load>) {
    for f in forms {
        load_modules_at(f, interner, out);
    }
}

/// `load_modules_in` of one expression, or definition.
fn load_modules_at(f: &Syntax, interner: &Interner, out: &mut Vec<Load>) {
    let Some(items) = f.as_proper_list() else { return };
    let exps = |xs: &[Syntax], out: &mut Vec<Load>| load_modules_in(xs, interner, out);
    // The last item of each list in `xs`: a binding's expression.
    let inits = |xs: Option<&[Syntax]>, out: &mut Vec<Load>| {
        for b in xs.unwrap_or_default() {
            if let Some([_, .., init]) = b.as_proper_list() {
                load_modules_at(init, interner, out);
            }
        }
    };
    // Each clause of `xs` from item `k` on: an arm's body.
    let arms = |xs: &[Syntax], k: usize, out: &mut Vec<Load>| {
        for c in xs {
            if let Some(parts) = c.as_proper_list() {
                load_modules_in(parts.get(k..).unwrap_or_default(), interner, out);
            }
        }
    };
    if let [head, path] = items
        && let Some(h) = head.as_symbol()
        && matches!(interner.name(h), "load-module" | "load-input")
        && let Datum::Str(p) = &path.datum
    {
        out.push((f.span.start, p.to_string(), interner.name(h) == "load-input", None));
    }
    if let [head, key, path] = items
        && head.as_symbol().is_some_and(|h| interner.name(h) == "%loaded")
        && let (Datum::Str(k), Datum::Str(p)) = (&key.datum, &path.datum)
    {
        let (input, file) = match k.strip_prefix("input:") {
            Some(f) => (true, f),
            None => (false, k.as_str()),
        };
        out.push((f.span.start, p.to_string(), input, Some(file.to_string())));
    }
    let head = items.first().and_then(|h| h.as_symbol()).map(|h| interner.name(h));
    if matches!(head, Some("spawn" | "spawn-monitored" | "send" | "receive" | "self" | "par" | "race" | "pselect" | "icell-get" | "icell-put!")) {
        out.push((f.span.start, crate::check::PROCESSES.to_string(), false, None));
    }
    let rest = items.get(1..).unwrap_or_default();
    let from = |k: usize| items.get(k..).unwrap_or_default();
    match head {
        // Data, not forms: a quotation, and a `case`'s clauses' data.
        Some("quote" | "quasiquote") => {}
        Some("case") => {
            exps(&items[..items.len().min(2)], out);
            arms(from(2), 1, out);
        }
        // Types and effects, and the regions a module takes.
        Some("define-type" | "define-effect" | "define-convention" | "module-parameters") => {}
        // Parameters, or a region's name, then a body.
        Some("lambda" | "plambda" | "letregion" | "letfreeze" | "letrena" | "letreap") => exps(from(2), out),
        Some("let" | "let*" | "letrec" | "letrec*" | "par") => {
            inits(items.get(1).and_then(|b| b.as_proper_list()), out);
            exps(from(2), out);
        }
        // `(define name expression)`, `(define name type expression)`.
        Some("define" | "define*" | "the") => exps(&items[items.len().max(1) - 1..], out),
        Some("define-rec") => inits(Some(rest), out),
        Some("tagcase" | "typecase") => {
            exps(&items[..items.len().min(2)], out);
            arms(from(2), 2, out);
        }
        Some("cond") => arms(rest, 0, out),
        Some("sum") => exps(from(2), out),
        // `(spawn (box M r) body …)`; `spawn-monitored`'s watcher and
        // `on-failure` first.
        Some("spawn") => exps(from(2), out),
        Some("spawn-monitored") => {
            exps(&items[..items.len().min(3)], out);
            exps(from(4), out);
        }
        _ => exps(items, out),
    }
}

/// What FX-26 code cannot do itself, done for it, as a system call would:
/// each file `text`'s `load-module`s name read, and read by the reader
/// written in FX-26, then handed to the parser written in FX-26
/// (`loaded-files!`): by where the form starts, the file's base (0 if it
/// was not read), its path, why not, its forms and its text. A file read is
/// a module's in order, as the Rust checker numbers them.
pub fn supply_loaded(scheme: &mut Session, file: FileId, text: &str) -> R<()> {
    supply_loaded_at(scheme, file, text, 0)
}

/// [`supply_loaded`], `text`'s positions counted from `base`.
fn supply_loaded_at(scheme: &mut Session, file: FileId, text: &str, base: i64) -> R<()> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let list = loaded_files_at(scheme, file, text, base)?;
    scheme.call_global(&format!("{READER_PREFIX}loaded-files!"), &[list]).map_err(|e| fail(e.to_string()))?;
    Ok(())
}

/// What `text`'s `load-module`s read, as [`supply_loaded`] hands it to the
/// parser written in FX-26: for a driver that hands it to a front end of
/// its own (`tests/bootstrap.rs`, whose front end reads the front end's
/// built-in module files).
pub fn loaded_files(scheme: &mut Session, file: FileId, text: &str) -> R<fixpt_scheme::Handle> {
    loaded_files_at(scheme, file, text, 0)
}

fn loaded_files_at(scheme: &mut Session, file: FileId, text: &str, base: i64) -> R<fixpt_scheme::Handle> {
    let base_dir = LOAD_BASE.with(|b| b.borrow().clone());
    let mut list = scheme.make(|_| Value::NULL);
    let mut read = 0;
    let mut seen = HashMap::new();
    supply_loaded_in(scheme, file, text, base, base_dir, &mut read, &mut seen, &mut list)?;
    Ok(list)
}

/// [`supply_loaded`] for the `load-module`s of `text`, a program or a file
/// read at `base` (its positions moved past the program's by it), whose
/// relative paths are from `dir`: each file read, then those it loads, in
/// the order the Rust checker begins them (`Checker::files_read`).
fn supply_loaded_in(
    scheme: &mut Session,
    file: FileId,
    text: &str,
    base: i64,
    dir: Option<std::path::PathBuf>,
    read: &mut u32,
    seen: &mut HashMap<String, Read>,
    list: &mut fixpt_scheme::Handle,
) -> R<()> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let mut interner = Interner::new();
    let Ok(forms) = fixpt_read::Reader::new(text, file, fixpt_read::SyntaxProfile::FX26, &mut interner).read_all() else {
        return Ok(());
    };
    let mut loads = Vec::new();
    load_modules_in(&forms, &interner, &mut loads);
    let offsets = byte_offsets(text);
    let char_at = |byte: u32| offsets.partition_point(|&o| o < byte as usize) as i64;
    for (start, path, input, resolved) in loads {
        let at = match (&resolved, &dir) {
            (Some(file), _) => std::path::PathBuf::from(file),
            (None, Some(d)) if std::path::Path::new(&path).is_relative() && crate::built_in_module(&path).is_none() => d.join(&path),
            _ => std::path::PathBuf::from(&path),
        };
        // Every load of a path is one (`TODO.md` §68): the file read once,
        // as the Rust checker reads it, and named by `key` for the parser.
        let key = at.display().to_string();
        let string = |sc: &mut Session, t: &str| sc.make(|m| m.heap().string_from_chars(&t.chars().collect::<Vec<_>>()));
        let entry = |sc: &mut Session, list: &mut fixpt_scheme::Handle, r: &Read| -> R<()> {
            let fields = [
                sc.make(|_| Value::fixnum(37)),
                sc.make(|_| Value::fixnum(base + char_at(start))),
                sc.make(|_| Value::fixnum(r.base)),
                string(sc, &r.why),
                string(sc, &path),
                r.syns,
                string(sc, &r.text),
                string(sc, &key),
            ];
            let one = sc.call_global("%make-frozen", &fields).map_err(|e| fail(e.to_string()))?;
            *list = sc.call_global("cons", &[one, *list]).map_err(|e| fail(e.to_string()))?;
            Ok(())
        };
        let shared = if input { format!("input:{key}") } else { key.clone() };
        if let Some(r) = seen.get(&shared) {
            entry(scheme, list, r)?;
            continue;
        }
        // Made by a form before, and loaded here, not defined (a
        // `%loaded` is its definition).
        if resolved.is_none() && SHARED_MADE.with(|m| m.borrow().contains(&shared)) {
            let nil = scheme.make(|_| Value::NULL);
            entry(scheme, list, &Read { base: -1, why: String::new(), syns: nil, text: String::new() })?;
            continue;
        }
        // A module file built in (`fx26:…`) is its text, not a file's.
        let contents = |at: &std::path::Path| match crate::built_in_module(&path) {
            Some(t) => Ok(t.to_string()),
            None => std::fs::read_to_string(at),
        };
        let (file_base, why, syns, ftext) = match contents(&at) {
            Err(e) => (0, format!("cannot read `{path}`: {e}"), scheme.make(|_| Value::NULL), String::new()),
            Ok(ftext) => match read_to_syns_at(scheme, FileId(1001 + *read), &ftext, LOAD_BASE_STEP * (*read as i64 + 1)) {
                Err(e) => {
                    let before = &ftext[..(e.span.start as usize).min(ftext.len())];
                    let line = before.matches('\n').count() + 1;
                    let col = before.chars().rev().take_while(|c| *c != '\n').count() + 1;
                    (0, format!("in `{path}`, {line}:{col}: {}", e.message), scheme.make(|_| Value::NULL), ftext)
                }
                Ok(syns) => {
                    *read += 1;
                    (LOAD_BASE_STEP * *read as i64, String::new(), syns, ftext)
                }
            },
        };
        let r = Read { base: file_base, why, syns, text: ftext };
        entry(scheme, list, &r)?;
        let ftext = r.text.clone();
        seen.insert(shared, r);
        // The files it loads, from its directory, at its positions.
        if file_base > 0 {
            supply_loaded_in(scheme, FileId(1000 + *read), &ftext, file_base, at.parent().map(|d| d.to_path_buf()), read, seen, list)?;
        }
    }
    Ok(())
}

/// A file read for a load: its base, why not (if its base is 0), its forms
/// and its text.
struct Read {
    base: i64,
    why: String,
    syns: fixpt_scheme::Handle,
    text: String,
}

/// The byte offset of each character, and of the end.
fn byte_offsets(text: &str) -> Vec<usize> {
    let mut v: Vec<usize> = text.char_indices().map(|(i, _)| i).collect();
    v.push(text.len());
    v
}

/// Field `i` (from 0) of a product: the object model's field `i + 2`.
fn part(product: Local<'_>, i: usize) -> Local<'_> {
    product.field(i + 2).expect("a product's field")
}

fn to_syntax(interner: &mut Interner, file: FileId, at: &dyn Fn(i64) -> u32, s: Local<'_>) -> R<Syntax> {
    let tag = s.field(2).and_then(|t| t.symbol_name()).unwrap_or_default();
    let p = s.field(3).expect("a sum");
    let span = |a: Local<'_>, b: Local<'_>| Span::new(file, at(a.fixnum().unwrap_or(0)), at(b.fixnum().unwrap_or(0)));
    let many = |interner: &mut Interner, list: Local<'_>| -> R<Vec<Syntax>> {
        let items = list.list().expect("a list");
        items.into_iter().map(|x| to_syntax(interner, file, at, x)).collect()
    };
    match tag.as_str() {
        "atom" => {
            let sp = span(part(p, 1), part(p, 2));
            let d = atom(interner, part(p, 0)).ok_or_else(|| FxError::at(sp, "a datum FX-26 does not read"))?;
            Ok(Syntax::new(sp, d))
        }
        "lst" => {
            let sp = span(part(p, 2), part(p, 3));
            let items = many(interner, part(p, 0))?;
            Ok(if items.is_empty() { Syntax::new(sp, Datum::Nil) } else { Syntax::new(sp, Datum::List { items, tail: None }) })
        }
        "dotted" => {
            let sp = span(part(p, 3), part(p, 4));
            let items = many(interner, part(p, 0))?;
            let tail = to_syntax(interner, file, at, part(p, 1))?;
            Ok(Syntax::new(sp, Datum::List { items, tail: Some(Box::new(tail)) }))
        }
        "vec" => {
            let sp = span(part(p, 2), part(p, 3));
            Ok(Syntax::new(sp, Datum::Vector(many(interner, part(p, 0))?)))
        }
        other => unreachable!("the reader makes no `{other}`"),
    }
}

/// A datum that is not a list, as the Rust reader would have it.
fn atom(interner: &mut Interner, v: Local<'_>) -> Option<Datum> {
    if let Some(n) = v.fixnum() {
        return Some(Datum::Number(Num::Int(n)));
    }
    // A bignum: as the Rust reader has an integer, a word's if it fits one.
    if v.obj_type() == Some(fixpt_heap::ObjType::Bignum) {
        let written = v.write();
        let (negative, digits) = match written.strip_prefix('-') {
            Some(d) => (true, d.to_string()),
            None => (false, written.clone()),
        };
        return Some(Datum::Number(match written.parse::<i64>() {
            Ok(n) => Num::Int(n),
            Err(_) => Num::Big { negative, digits, radix: 10 },
        }));
    }
    if v.is_true() || v.is_false() {
        return Some(Datum::Bool(v.is_true()));
    }
    if let Some(c) = v.char() {
        return Some(Datum::Char(c));
    }
    if let Some(n) = v.symbol_name() {
        return Some(Datum::Symbol(interner.intern(&n)));
    }
    if let Some(s) = v.string() {
        return Some(Datum::Str(s));
    }
    if let Some(b) = v.bytevector() {
        return Some(Datum::Bytevector(b));
    }
    v.flonum().map(|f| Datum::Number(Num::Real(f)))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Where the loads' scan finds the scheduler loaded (`load_modules_in`).
    fn scheduler_loads(text: &str) -> Vec<u32> {
        let mut interner = Interner::new();
        let forms = fixpt_read::Reader::new(text, FileId(0), fixpt_read::SyntaxProfile::FX26, &mut interner).read_all().expect("reads");
        let mut out = Vec::new();
        load_modules_in(&forms, &interner, &mut out);
        out.into_iter().filter(|(_, p, _, _)| p == crate::check::PROCESSES).map(|(at, ..)| at).collect()
    }

    /// A form's name bound, as a parameter, a variant, a type's effect or a
    /// `tagcase`'s arm, is no form (`TODO.md` §92); a form is, where an
    /// expression is, and a `pselect`'s events are.
    #[test]
    fn the_scheduler_is_loaded_by_forms_only() {
        let names = [
            "(let ((self 1) (send 2)) (+ self send))",
            "(let* ((par 1)) par)",
            "(lambda ((self int) (race int)) self)",
            "(define-type m (sumof (send int) (receive int)))",
            "(define f (subr (maxeff (send @w)) (int) int) (lambda ((x int)) x))",
            "(tagcase v (send x x) (receive y y))",
            "(cond (self 1) (else 2))",
            "(the (sumof (self int)) (sum self 1))",
        ];
        for text in names {
            assert_eq!(scheduler_loads(text), Vec::<u32>::new(), "{text}");
        }
        let forms = [
            ("(send p 1)", vec![0]),
            ("(let ((x (receive b))) x)", vec![9]),
            ("(define x (icell-get c))", vec![10]),
            ("(pselect ((receive b) x x))", vec![0, 10]),
            ("(lambda ((self int)) (self box))", vec![21]),
        ];
        for (text, at) in forms {
            assert_eq!(scheduler_loads(text), at, "{text}");
        }
    }
}
