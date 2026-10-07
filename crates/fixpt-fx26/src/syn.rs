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
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        let checked = check_in(s, Some(standard), tops).map_err(|e| fail(e.to_string()))?;
        if let Some(m) = s.view(|v| {
            let r = v.get(checked);
            (r.field(2).and_then(|t| t.symbol_name()).as_deref() == Some("k-err"))
                .then(|| r.field(3).and_then(|p| p.field(2)).and_then(|m| m.string()).unwrap_or_default())
        }) {
            return Ok(format!("!! check: {m}"));
        }
        let runs = s.call_global(&format!("{READER_PREFIX}checked-tops"), &[]).map_err(|e| fail(e.to_string()))?;
        let out = s.call_global(&format!("{READER_PREFIX}run-checked"), &[runs]).map_err(|e| fail(e.to_string()))?;
        Ok(s.view(|v| v.get(out).string().unwrap_or_default()))
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
            Err(e) => {
                let why = e.to_string();
                let why = why.trim_start_matches("error: cellular word: ");
                // As the lowered form says it, whichever machine ran out.
                let why = if why.contains("OutOfFuel") { "evaluation step limit exceeded" } else { why };
                Ok((format!("!! {why}"), words))
            }
        }
    })
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
    let closure = fixpt_heap::layout::kind("cellular-closure");
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
/// ([`cell_words_reachable`]), compiled to machine code by the compiler
/// written in FX-26 (`native.fx`'s `native-assemble`) and given to `place`
/// with the heap: its instructions, and where each cell's start.
pub fn assemble_reachable_by_fx26(
    s: &mut Session,
    word: Handle,
    place: &mut dyn FnMut(&mut fixpt_heap::Heap, Value, &[u32], &[i64]) -> Result<(), String>,
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
    for w in words {
        let assembled = s.call_global(&format!("{READER_PREFIX}native-assemble"), &[w, far, far]);
        let assembled = assembled.map_err(|e| e.to_string())?;
        let (code, starts) = s.view(|v| {
            let r = v.get(assembled);
            let ints = |l: Option<Local>| -> Vec<i64> {
                let l = l.and_then(|l| l.list()).unwrap_or_default();
                l.iter().filter_map(|x| x.fixnum()).collect()
            };
            (ints(r.field(2)), ints(r.field(3)))
        });
        let code: Vec<u32> = code.into_iter().map(|x| x as u32).collect();
        let mut placed = Ok(());
        s.make(|m| {
            let w = m.get(w);
            placed = place(m.heap(), w, &code, &starts);
            Value::NULL
        });
        placed?;
    }
    Ok(())
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
    match standard {
        Some(std) => s.call_global(&format!("{READER_PREFIX}check-program"), &[std, tops]),
        None => s.call_global(&format!("{READER_PREFIX}check-more"), &[tops]),
    }
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
    let read = scheme.call_global(&format!("{READER_PREFIX}read-text"), &[s]);
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
/// scope; or the check's error.
pub fn rust_facts(scheme: &mut Session, file: FileId, text: &str) -> R<Handle> {
    let mut c = crate::Checker::new();
    c.base_dir = LOAD_BASE.with(|b| b.borrow().clone());
    let forms = c.read_in(file, text)?;
    let done = c.declare_ahead(&forms)?;
    for (f, done) in forms.iter().zip(done) {
        if !done {
            c.top_defining(f)?;
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
    let place = |e: ExpId| {
        let span = c.arena.span_of(e);
        (at(span.file, span.start), at(span.file, span.end))
    };
    let facts: Vec<(i64, i64, i64)> = c
        .facts
        .field_index
        .iter()
        .map(|(e, i)| {
            let (a, b) = place(*e);
            (a, b, *i as i64)
        })
        .collect();
    // And each expression's effect summary, as -1 - s (`checked-extracts`):
    // `Checker::effect_summaries`, by span in its file.
    let mut summaries: HashMap<(i64, i64), i64> = HashMap::new();
    for (e, eff) in &c.facts.effects {
        use crate::ast::{Atom, Region};
        let s = if eff.is_pure() {
            0
        } else if eff.0.iter().all(|a| matches!(a, Atom::Read(_))) {
            1
        } else if eff.0.iter().any(|a| matches!(a, Atom::Comefrom(_) | Atom::Var(_) | Atom::App(_) | Atom::Write(Region::Global(_) | Region::Globals))) {
            3
        } else {
            2
        };
        let k = summaries.entry(place(*e)).or_insert(s);
        *k = (*k).max(s);
    }
    let facts: Vec<(i64, i64, i64)> = facts
        .into_iter()
        .chain(summaries.into_iter().map(|((a, b), s)| (a, b, -1 - s)))
        // And each conversion, as -1000 - its code (`k-convert-at`).
        .chain(c.facts.converted.keys().filter_map(|e| {
            let (a, b) = place(*e);
            c.facts.conversion_code(*e).map(|k| (a, b, -1000 - k))
        }))
        // And each `apply` of a list at `acyclic`, as -500
        // (`k-note-apply-shares`).
        .chain(c.facts.apply_shares.iter().map(|e| {
            let (a, b) = place(*e);
            (a, b, -500)
        }))
        // And each definition's value that is a list nothing writes, as
        // -501 (`k-note-frozen-define`).
        .chain(c.facts.frozen_defines.iter().map(|e| {
            let (a, b) = place(*e);
            (a, b, -501)
        }))
        .collect();
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    // And each `with`'s module's values it names, and their positions, by
    // where it is (`checked-withs!`): the checker's record, which the
    // compiler reads.
    let mut withs = scheme.make(|_| Value::NULL);
    for (e, names) in &c.facts.with_vals {
        let (wa, wb) = place(*e);
        let (mut ns, mut is) = (scheme.make(|_| Value::NULL), scheme.make(|_| Value::NULL));
        for (n, i) in names.iter().rev() {
            let sym = scheme.make(|m| m.heap().intern(c.interner.name(*n)));
            ns = scheme.call_global("cons", &[sym, ns]).map_err(|e| fail(e.to_string()))?;
            let at = scheme.make(|_| Value::fixnum(*i as i64));
            is = scheme.call_global("cons", &[at, is]).map_err(|e| fail(e.to_string()))?;
        }
        let (a, b) = (scheme.make(|_| Value::fixnum(wa)), scheme.make(|_| Value::fixnum(wb)));
        let tag = scheme.make(|_| Value::fixnum(37));
        let one = scheme.call_global("%make-frozen", &[tag, a, b, ns, is]).map_err(|e| fail(e.to_string()))?;
        withs = scheme.call_global("cons", &[one, withs]).map_err(|e| fail(e.to_string()))?;
    }
    scheme.call_global(&format!("{READER_PREFIX}checked-withs!"), &[withs]).map_err(|e| fail(e.to_string()))?;
    // And each module reshaped, with the positions it keeps (`checked-reshapes!`).
    let mut reshapes = scheme.make(|_| Value::NULL);
    for (e, keep) in &c.facts.reshaped {
        let (ra, rb) = place(*e);
        let mut ks = scheme.make(|_| Value::NULL);
        for k in keep.iter().rev() {
            let k = scheme.make(|_| Value::fixnum(*k as i64));
            ks = scheme.call_global("cons", &[k, ks]).map_err(|e| fail(e.to_string()))?;
        }
        let (a, b) = (scheme.make(|_| Value::fixnum(ra)), scheme.make(|_| Value::fixnum(rb)));
        let tag = scheme.make(|_| Value::fixnum(37));
        let one = scheme.call_global("%make-frozen", &[tag, a, b, ks]).map_err(|e| fail(e.to_string()))?;
        reshapes = scheme.call_global("cons", &[one, reshapes]).map_err(|e| fail(e.to_string()))?;
    }
    scheme.call_global(&format!("{READER_PREFIX}checked-reshapes!"), &[reshapes]).map_err(|e| fail(e.to_string()))?;
    let mut list = scheme.make(|_| Value::NULL);
    for (a, b, i) in facts {
        let args = [37, a, b, i].map(|n| scheme.make(|_| Value::fixnum(n)));
        let fact = scheme.call_global("%make-frozen", &args).map_err(|e| fail(e.to_string()))?;
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
    supply_loaded(scheme, file, text)?;
    let syns = read_to_syns(scheme, file, text)?;
    parse_syns(scheme, file, text, syns)
}

/// What the parser written in FX-26 makes of `syns`, read from `text`
/// ([`read_to_syns`]): the program's trees, or where it is wrong.
pub fn parse_syns(scheme: &mut Session, file: FileId, text: &str, syns: Handle) -> R<Handle> {
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
        let at = |c: i64| offsets.get(c as usize).copied().unwrap_or(text.len()) as u32;
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

/// The positions of one module file and the next apart, in the parser
/// written in FX-26 (`parser-exps.fx`'s `load-base`).
const LOAD_BASE_STEP: i64 = 1_000_000_000;

/// Each `(load-module "path")` in `forms`, in order: where it starts, and
/// the path.
fn load_modules_in(forms: &[Syntax], interner: &Interner, out: &mut Vec<(u32, String)>) {
    for f in forms {
        let Some(items) = f.as_proper_list() else { continue };
        if let [head, path] = items
            && head.as_symbol().is_some_and(|h| interner.name(h) == "load-module")
            && let Datum::Str(p) = &path.datum
        {
            out.push((f.span.start, p.to_string()));
        }
        load_modules_in(items, interner, out);
    }
}

/// What FX-26 code cannot do itself, done for it, as a system call would:
/// each file `text`'s `load-module`s name read, and read by the reader
/// written in FX-26, then handed to the parser written in FX-26
/// (`loaded-files!`): by where the form starts, the file's base (0 if it
/// was not read), its path, why not, its forms and its text. A file read is
/// a module's in order, as the Rust checker numbers them.
fn supply_loaded(scheme: &mut Session, file: FileId, text: &str) -> R<()> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let base_dir = LOAD_BASE.with(|b| b.borrow().clone());
    let mut list = scheme.make(|_| Value::NULL);
    let mut read = 0;
    supply_loaded_in(scheme, file, text, 0, base_dir, &mut read, &mut list)?;
    scheme.call_global(&format!("{READER_PREFIX}loaded-files!"), &[list]).map_err(|e| fail(e.to_string()))?;
    Ok(())
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
    for (start, path) in loads {
        let at = match &dir {
            Some(d) if std::path::Path::new(&path).is_relative() => d.join(&path),
            _ => std::path::PathBuf::from(&path),
        };
        let (file_base, why, syns, ftext) = match std::fs::read_to_string(&at) {
            Err(e) => (0, format!("cannot read `{path}`: {e}"), scheme.make(|_| Value::NULL), String::new()),
            Ok(ftext) => match read_to_syns(scheme, FileId(1001 + *read), &ftext) {
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
        let string = |sc: &mut Session, t: &str| sc.make(|m| m.heap().string_from_chars(&t.chars().collect::<Vec<_>>()));
        let fields = [
            scheme.make(|_| Value::fixnum(37)),
            scheme.make(|_| Value::fixnum(base + char_at(start))),
            scheme.make(|_| Value::fixnum(file_base)),
            string(scheme, &why),
            string(scheme, &path),
            syns,
            string(scheme, &ftext),
        ];
        let one = scheme.call_global("%make-frozen", &fields).map_err(|e| fail(e.to_string()))?;
        *list = scheme.call_global("cons", &[one, *list]).map_err(|e| fail(e.to_string()))?;
        // The files it loads, from its directory, at its positions.
        if file_base > 0 {
            supply_loaded_in(scheme, FileId(1000 + *read), &ftext, file_base, at.parent().map(|d| d.to_path_buf()), read, list)?;
        }
    }
    Ok(())
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
