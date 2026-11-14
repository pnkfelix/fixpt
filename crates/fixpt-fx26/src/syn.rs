//! Reading FX-26 with the reader written in FX-26 (`eager-reader.fx`), and
//! turning what it read into the Rust checker's syntax.
//!
//! The reader builds `syn` values, a `define-datatype`: each piece of what
//! it read with where it starts and ends. At run time they are frozen
//! bloblets, a sum's tag and its product, so they can be walked here without
//! running anything. Positions are in characters there and in bytes in
//! [`Span`], and are converted with the text.

use crate::error::{FxError, R};
use crate::ids::State;
use crate::session::READER_PREFIX;
use fixpt_heap::Value;
use crate::heap_syn::Syn;
use fixpt_read::{FileId, Interner, Span};
use crate::front::Front;
use fixpt_scheme::{Handle, Local, Session};
use fixpt_scheme::eager::EagerReader;
use fixpt_hash::HashMap;

/// Read `text` with the FX-26 reader, already loaded into `scheme` (see
/// [`crate::session::load_eager_reader`]): the `syn` it makes, as it is,
/// the checker's forms, `checker` a session's of `scheme`'s heap
/// (`Checker::in_session_heap`), its names noted
/// ([`crate::heap_syn::adopted`]). Not expanded.
pub fn read_with_fx26_reader(scheme: &mut Session, checker: &mut crate::Checker, file: FileId, text: &str) -> R<Vec<crate::heap_syn::Form>> {
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
        crate::heap_syn::note_text(file, std::sync::Arc::from(text));
        let mut forms = Ok(Vec::new());
        s.make(|m| {
            let mut l = m.get(syns);
            let heap = m.heap();
            let mut items = Vec::new();
            while l.is_pair() {
                items.push(heap.car(l));
                l = heap.cdr(l);
            }
            forms = checker.with_heap(heap, |c| {
                let held = items.iter().map(|&v| crate::heap_syn::adopted(v, &mut c.interner).map(crate::heap_syn::Form::new));
                held.collect::<Result<Vec<_>, _>>().map_err(|e| FxError::at(Span::new(file, 0, 0), e))
            });
            fixpt_heap::Value::NULL
        });
        forms
    })
}

/// Parse `text` with the reader and the parser written in FX-26: each
/// top-level form's tree, as [`crate::sexp::show_value`] prints it.
pub fn parse_with_fx26_parser(scheme: &mut Front, file: FileId, text: &str) -> R<Vec<String>> {
    parse_with_fx26_parser_from(scheme, file, text).map(|(trees, _)| trees)
}

/// The same, and how many expressions the parser had walked before it:
/// where `path`'s numbers of these begin.
pub fn parse_with_fx26_parser_from(scheme: &mut Front, file: FileId, text: &str) -> R<(Vec<String>, i64)> {
    scheme.scope(|s| {
        let tops = parse_to_trees(s, file, text)?;
        Ok((s.view(|v| v.get(tops.tops).list().expect("a list").into_iter().map(crate::sexp::show_value).collect()), tops.base))
    })
}

/// Read, parse, check (in the initial environment `standard`) and run
/// `text` with the pieces written in FX-26, the evaluator running what the
/// checker says the program runs (`checked-tops`, under redefinition): its
/// value as Scheme would write it, or `!! ` and its error.
pub fn eval_with_fx26_evaluator(scheme: &mut Front, standard: Handle, file: FileId, text: &str) -> R<String> {
    eval_more_with_fx26_evaluator(scheme, Some(standard), file, Given::Text(text, 0), &mut State::begun())
}

/// [`eval_with_fx26_evaluator`], or, `standard` none, `text` as more of the
/// program the evaluator ran before: checked after the forms before, and
/// run with the globals they made (`run-checked-more`). Its positions are
/// counted from `base`, past every text given before, so that what the
/// checker says of a place is said of no other form's. Read in `state`,
/// which it leaves the state after, if the checker keeps `text`
/// ([`State`]).
pub fn eval_more_with_fx26_evaluator(scheme: &mut Front, standard: Option<Handle>, file: FileId, given: Given<'_>, state: &mut State) -> R<String> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let entry = if standard.is_some() { "run-checked" } else { "run-checked-more" };
    scheme.scope(|s| {
        let parsed = parse_to_trees_at(s, file, given, state, standard.is_none())?;
        let (tops, after) = (parsed.tops, parsed.after);
        let checked = check_in(s, standard, tops).map_err(|e| fail(e.to_string()))?;
        if let Some(m) = refusal(s, checked) {
            return Ok(format!("!! check: {m}"));
        }
        state.at = after.at;
        let runs = crate::entries::call(&mut *s, "checked-tops", &[]).map_err(|e| fail(e.to_string()))?;
        // A primitive the evaluator calls may fail, as the program's own
        // failure (`DONE.md` §85).
        s.set_bare_failures(true);
        let out = crate::entries::call(s, entry, &[runs]);
        s.set_bare_failures(false);
        match out {
            Ok(out) => Ok(s.view(|v| v.get(out).string().unwrap_or_default())),
            Err(e) => Ok(format!("!! {}", run_failure(&e.to_string()))),
        }
    })
}

/// Read, parse and compile `text` with the reader, the parser and the
/// compiler written in FX-26, and run the word it makes on the cellular
/// machine: the value, as Scheme writes it; or `!! ` and why it failed.
pub fn compile_with_fx26_compiler(scheme: &mut Front, standard: Handle, file: FileId, text: &str) -> R<String> {
    compile_with_fx26_compiler_showing(scheme, Some(standard), &mut State::begun(), file, Given::Text(text, 0), false, None).map(|(out, _)| out)
}

/// The same, and, if `show`, the word made, and every word it reaches,
/// disassembled before it runs; the run limited to `steps`, if given.
/// `standard` begins the checker's state; without it, `text` is checked
/// after the forms checked before (`check-more`), as the REPL gives them,
/// read in `state`, which it leaves the state after, if the checker keeps
/// `text` ([`State`]).
pub fn compile_with_fx26_compiler_showing(
    scheme: &mut Front,
    standard: Option<Handle>,
    state: &mut State,
    file: FileId,
    given: Given<'_>,
    show: bool,
    steps: Option<u64>,
) -> R<(String, Option<String>)> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let parsed = parse_to_trees_at(s, file, given, state, standard.is_none())?;
        let (tops, after) = (parsed.tops, parsed.after);
        // Checked first, by the checker written in FX-26, which says where
        // each `extract`'s field is.
        let checked = check_in(s, standard, tops).map_err(|e| fail(e.to_string()))?;
        if let Some(m) = refusal(s, checked) {
            return Ok((format!("!! check: {m}"), None));
        }
        state.at = after.at;
        let facts = crate::entries::call(&mut *s, "checked-extracts", &[]).map_err(|e| fail(e.to_string()))?;
        let runs = crate::entries::call(&mut *s, "checked-tops", &[]).map_err(|e| fail(e.to_string()))?;
        let start = std::time::Instant::now();
        let own = own_numbering(s).map_err(fail)?;
        let result = crate::entries::call(&mut *s, "compile-checked", &[runs, facts, own]).map_err(|e| fail(e.to_string()))?;
        s.runtime_unrooted().compile_nanos += start.elapsed().as_nanos() as u64;
        let (tag, word) = s.view(|v| {
            let r = v.get(result);
            let tag = r.sum_tag().and_then(|t| t.symbol_name()).unwrap_or_default();
            let payload = r.sum_payload().expect("a sum");
            (tag, payload.product_field(1).map(|x| x.string()))
        });
        if tag == "c-err" {
            return Ok((format!("!! compile: {}", word.flatten().unwrap_or_default()), None));
        }
        let word = s.make(|m| {
            let r = m.get(result);
            let payload = m.heap().sum_payload(r);
            m.heap().product_field(payload, 1)
        });
        let mut words = None;
        if show {
            let _ = s.make(|m| {
                let w = m.get(word);
                words = Some(fixpt_runtime::disasm::disassemble(m.heap(), w));
                w
            });
        }
        s.runtime_unrooted().word_fuel = steps.unwrap_or(u64::MAX);
        if let Err(why) = assemble_by_fx26(s, word) {
            return Ok((format!("!! native.fx: {why}"), words));
        }
        let start = std::time::Instant::now();
        let run = s.run_word(word, &[]);
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
fn assemble_by_fx26(s: &mut Front, word: Handle) -> Result<(), String> {
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
    use fixpt_heap::layout::cellular::{CLOSURE_WORD, WORD_CELL0};
    let closure = const { fixpt_heap::layout::kind("cellular-closure") };
    let (mut todo, mut seen, mut found) = (vec![word], fixpt_hash::HashSet::default(), Vec::new());
    while let Some(w) = todo.pop() {
        if !seen.insert(w.raw()) {
            continue;
        }
        if !heap.word_runs_cells(w) {
            continue;
        }
        for v in heap.bloblet_fields_from(w, WORD_CELL0) {
            if heap.is_cellular_word(v) {
                todo.push(v);
            } else if v.is_bloblet() && heap.bloblet_kind(v) == closure {
                todo.push(heap.bloblet_slot(v, CLOSURE_WORD));
            }
        }
        if heap.word_code(w).is_none() {
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
/// each cell's code starts in them. A word with register code (its twin,
/// `layout::regcode`) has that compiled instead (`native-arm64-regs.fx`,
/// `native-x64-regs.fx`), and its entry is the adapter into it, as
/// `fixpt_native`'s `compile_register_word` does them.
pub fn assemble_reachable_by_fx26(
    s: &mut Front,
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
        if assemble_twin_by_fx26(s, w, place)? {
            continue;
        }
        let assembled = if x64 {
            crate::entries::call(&mut *s, "native-assemble-x64", &[w])
        } else {
            crate::entries::call(&mut *s, "native-assemble", &[w, far, far])
        };
        let assembled = assembled.map_err(|e| e.to_string())?;
        let (code, starts) = s.view(|v| {
            let r = v.get(assembled);
            (ints_of(r.product_field(1)), ints_of(r.product_field(2)))
        });
        let (code, starts) = machine_bytes(code, starts);
        place_in(s, w, &code, &starts, place)?;
    }
    Ok(())
}

/// Code as the compiler written in FX-26 gives it, ints, as bytes, and
/// where its cells start in them: x86_64's are bytes already; arm64's
/// instructions are words of 4 bytes, little-endian, and the starts count
/// instructions.
fn machine_bytes(code: Vec<i64>, starts: Vec<i64>) -> (Vec<u8>, Vec<i64>) {
    if cfg!(target_arch = "x86_64") {
        (code.into_iter().map(|x| x as u8).collect(), starts)
    } else {
        (code.into_iter().flat_map(|x| (x as u32).to_le_bytes()).collect(), starts.into_iter().map(|s| if s < 0 { s } else { 4 * s }).collect())
    }
}

/// A list of ints, or none.
fn ints_of(l: Option<Local>) -> Vec<i64> {
    l.and_then(|l| l.list()).unwrap_or_default().iter().filter_map(|x| x.fixnum()).collect()
}

/// `code` given to `place` as word `w`'s, with where its cells start.
fn place_in(
    s: &mut Front,
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
/// for the machine this runs on by `native-arm64-regs.fx` or
/// `native-x64-regs.fx` and placed, and the adapter into it as `w`'s
/// entry: whether it was. Not a variadic procedure's, which is
/// for native code, nor, past `REGS` arguments, the adapter, which would
/// have to make a list of the rest: `w` stays stack code then.
fn assemble_twin_by_fx26(
    s: &mut Front,
    w: Handle,
    place: &mut dyn FnMut(&mut fixpt_heap::Heap, Value, &[u8], &[i64]) -> Result<(), String>,
) -> Result<bool, String> {
    use fixpt_heap::layout::cellular::{WORD_CELL0, WORD_TWIN};
    let x64 = cfg!(target_arch = "x86_64");
    let mut twin = None;
    s.make(|m| {
        let w = m.get(w);
        let heap = m.heap();
        let rw = heap.bloblet_slot(w, WORD_TWIN);
        if heap.is_register_word(rw)
            && heap.word_code(rw).is_none()
            && heap.bloblet_slot(rw, WORD_CELL0).as_fixnum() as usize != const { fixpt_heap::layout::regcode::op("vargs") }
        {
            twin = Some(rw);
        }
        Value::NULL
    });
    let Some(rw) = twin else { return Ok(false) };
    let rw = s.make(|_| rw);
    let assembled = if x64 {
        crate::entries::call(&mut *s, "native-assemble-x64-regs", &[rw])
    } else {
        // As `native-assemble`, of a place it need not know; and the time
        // slice, which arm64's register code has as a constant.
        let far = s.make(|_| Value::fixnum(0));
        let slice = s.make(|_| Value::fixnum(fixpt_runtime::sched::slice() as i64));
        crate::entries::call(&mut *s, "native-assemble-arm64-regs", &[rw, far, far, slice])
    };
    let assembled = assembled.map_err(|e| e.to_string())?;
    let (code, resume, err) = s.view(|v| {
        let r = v.get(assembled);
        (ints_of(r.product_field(1)), ints_of(r.product_field(2)), r.product_field(3).and_then(|e| e.string()).unwrap_or_default())
    });
    if !err.is_empty() {
        return Err(format!("register code: {err}"));
    }
    let (code, resume) = machine_bytes(code, resume);
    place_in(s, rw, &code, &resume, place)?;
    let (mut n, mut cells) = (0, 0);
    s.make(|m| {
        let (rw, w) = (m.get(rw), m.get(w));
        let heap = m.heap();
        n = heap.bloblet_slot(rw, WORD_CELL0 + 1).as_fixnum();
        cells = heap.bloblet_count_from(w, WORD_CELL0);
        Value::NULL
    });
    if n as usize > fixpt_heap::layout::regcode::REGS {
        return Ok(false);
    }
    let n = s.make(|_| Value::fixnum(n));
    let adapter = crate::entries::call(s, if x64 { "native-adapter-x64" } else { "native-adapter-arm64" }, &[n]).map_err(|e| e.to_string())?;
    let (adapter, _) = machine_bytes(s.view(|v| ints_of(Some(v.get(adapter)))), Vec::new());
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
    scheme: &mut Front,
    standard: Option<Handle>,
    state: &mut State,
    file: FileId,
    given: Given<'_>,
    native: Option<crate::session::NativeFx>,
    f: impl FnOnce(&mut fixpt_runtime::Runtime, Value) -> T,
) -> R<Result<T, String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let parsed = parse_to_trees_at(s, file, given, state, standard.is_none())?;
        let (tops, after) = (parsed.tops, parsed.after);
        let checked = check_in(s, standard, tops).map_err(|e| fail(e.to_string()))?;
        if let Some(m) = refusal(s, checked) {
            return Ok(Err(format!("check: {m}")));
        }
        state.at = after.at;
        let facts = crate::entries::call(&mut *s, "checked-extracts", &[]).map_err(|e| fail(e.to_string()))?;
        let word = match compile_checked_to_word(s, file, facts)? {
            Ok(w) => w,
            Err(m) => return Ok(Err(format!("compile: {m}"))),
        };
        assemble_by_fx26(s, word).map_err(|why| fail(format!("native.fx: {why}")))?;
        let v = match s.run_word(word, &[]) {
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
/// Read in `state`, which it leaves the state after, if the checker keeps
/// `text` ([`State`]).
pub fn check_only(scheme: &mut Front, standard: Option<Handle>, state: &mut State, file: FileId, given: Given<'_>) -> R<Result<(), String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let parsed = parse_to_trees_at(s, file, given, state, standard.is_none())?;
        let (tops, after) = (parsed.tops, parsed.after);
        let checked = check_in(s, standard, tops).map_err(|e| fail(e.to_string()))?;
        Ok(match refusal(s, checked) {
            Some(m) => Err(m),
            None => {
                state.at = after.at;
                Ok(())
            }
        })
    })
}

/// Why the checker refused, if its result `checked` is a `k-err`.
fn refusal(s: &mut Front, checked: Handle) -> Option<String> {
    s.view(|v| {
        let r = v.get(checked);
        (r.sum_tag().and_then(|t| t.symbol_name()).as_deref() == Some("k-err"))
            .then(|| r.sum_payload().and_then(|p| p.product_field(1)).and_then(|m| m.string()).unwrap_or_default())
    })
}

/// The types of rep `bytes` (a rep of several, `reps.rs`'s `export_tys`)
/// in the checker written in FX-26, by id, in order (`import-types`); none
/// if it could not import them.
pub fn import_types(scheme: &mut Front, bytes: &[u8]) -> Result<Vec<i64>, String> {
    let b = scheme.make(|m| m.heap().make_bytevector(bytes));
    let ids = crate::entries::call(&mut *scheme, "import-types", &[b]).map_err(|e| e.to_string())?;
    Ok(scheme.view(|v| v.get(ids).list().unwrap_or_default().iter().filter_map(|x| x.fixnum()).collect()))
}

/// `check_only` of a definition that loads nothing, given more forms (no
/// `standard`), each of `typed` a name the text gives a type by, bound to
/// that type, by its id (`import_types`): read, parsed and checked in one
/// call (`check-text-typed`); a `.fasl`'s definitions,
/// `docs/research/heap-types.md`, step 5. Read in `state` (the checker
/// written in FX-26 folds its own switches, `check-text-typed`), which it
/// leaves the state after if the checker keeps `text` ([`State`]).
pub fn check_only_typed(scheme: &mut Front, state: &mut State, file: FileId, text: &str, typed: &[(String, i64)]) -> R<Result<(), String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    scheme.scope(|s| {
        let whole = s.make(|m| m.heap().make_string(text));
        let list = s.make(|m| {
            let mut l = fixpt_heap::Value::NULL;
            for (n, id) in typed.iter().rev() {
                let h = m.heap();
                let base = h.push_root(l);
                let sym = h.intern(n);
                let p = h.make_frozen(fixpt_heap::layout::kind("product"), &[sym, fixpt_heap::Value::fixnum(*id)]);
                h.push_root(p);
                let (l0, p) = (h.root_at(base), h.root_at(base + 1));
                l = h.cons(p, l0);
                h.pop_roots_to(base);
            }
            l
        });
        let int = |s: &mut Front, n: i64| s.make(|_| Value::fixnum(n));
        let args = [int(s, crate::ids::mode() as i64), int(s, state.at), whole, list];
        let said = crate::entries::call(&mut *s, "check-text-typed", &args).map_err(|e| fail(e.to_string()))?;
        let (said, at) = s.view(|v| {
            let r = v.get(said);
            (r.product_field(1).and_then(|m| m.string()).unwrap_or_default(), r.product_field(2).and_then(|x| x.fixnum()).unwrap_or(0))
        });
        if !said.is_empty() {
            return Ok(Err(said));
        }
        state.at = at;
        Ok(Ok(()))
    })
}

/// The checker written in FX-26 on `tops`: a program, in the initial
/// environment `standard`; or, without it, more forms after those checked
/// before.
fn check_in(s: &mut Front, standard: Option<Handle>, tops: Handle) -> Result<Handle, fixpt_scheme::SessionError> {
    // What these callers keep is the facts, not the lines (`check-lines!`).
    lines(s, false)?;
    match standard {
        Some(std) => crate::entries::call(&mut *s, "check-program", &[std, tops]),
        None => crate::entries::call(&mut *s, "check-more", &[tops]),
    }
}

/// Whether the checker written in FX-26 makes each form's line, `define
/// name : type ! effect`: only for a caller that reads them.
pub fn lines(s: &mut Front, on: bool) -> Result<(), fixpt_scheme::SessionError> {
    let v = s.make(|_| Value::boolean(on));
    crate::entries::call(&mut *s, "check-lines!", &[v]).map(|_| ())
}

/// What the checker written in FX-26 made of a program: for each definition
/// and expression, in order, `define name : type ! effect` or `type !
/// effect`; or its first error.
pub type Checked26 = Result<Vec<String>, FxError>;

/// Read, parse and check `text` with the reader, the parser and the checker
/// written in FX-26, in the initial environment of [`crate::standard`].
/// The outer error is the front end failing to read or parse.
pub fn check_with_fx26_checker(scheme: &mut Front, standard: Handle, file: FileId, text: &str) -> R<Checked26> {
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
        let result = crate::entries::call(&mut *s, "check-program", &[standard, tops.tops]).map_err(|e| fail(e.to_string()))?;
        phase("checked");
        let offsets = byte_offsets(text);
        let at = |c: i64| offsets.get(c as usize).copied().unwrap_or(text.len()) as u32;
        let checked = s.view(|v| {
            let r = v.get(result);
            let tag = r.sum_tag().and_then(|t| t.symbol_name()).unwrap_or_default();
            let p = r.sum_payload().expect("a sum");
            if tag == "k-ok" {
                // Not the lines of what shows none (`k-define-line`).
                let lines = p.product_field(1).and_then(|l| l.list()).unwrap_or_default();
                Ok(lines.into_iter().map(|l| l.string().unwrap_or_default()).filter(|l| !l.is_empty()).collect())
            } else {
                let message = p.product_field(1).and_then(|m| m.string()).unwrap_or_default();
                Err((message, p.product_field(2).and_then(|x| x.fixnum()).unwrap_or(0), p.product_field(3).and_then(|x| x.fixnum()).unwrap_or(0)))
            }
        });
        Ok(checked.map_err(|(message, a, b)| FxError::at(fx26_span(s, file, &at, a, b), message)))
    })
}

/// The initial environment of [`crate::standard`], read by the FX-26
/// reader, as `(name type)` for each binding: what `check-program` takes.
pub fn read_standard(scheme: &mut Front) -> R<Handle> {
    let text = crate::standard::standard_text();
    read_to_syns(scheme, FileId(0), &text)
}

/// What the FX-26 reader reads from `text`: a list of `syn`s, as a handle
/// in the caller's scope.
pub fn read_to_syns(scheme: &mut Front, file: FileId, text: &str) -> R<Handle> {
    read_to_syns_at(scheme, file, text, 0)
}

/// [`read_to_syns`], its positions counted from `at`: a loaded file's
/// base, so that the parser takes its syntax as read, not moved there.
pub fn read_to_syns_at(scheme: &mut Front, file: FileId, text: &str, at: i64) -> R<Handle> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    // The whole text read inside FX-26 (`read-text`), not fed from here a
    // character at a time: so that with the front end run as register code
    // (`FRONT_ENTRIES`) the reader is too, not lowered Scheme.
    // With no step limit: it is licensed code, and a text ends (as
    // `Fx26Session::read_with_own_reader`). Fed a character at a time,
    // each call was a few steps; the whole text is many.
    let s = scheme.make(|m| m.heap().make_string(text));
    let limit = scheme.step_limit();
    scheme.set_step_limit(None);
    let at = scheme.make(|_| fixpt_heap::Value::fixnum(at));
    let read = crate::entries::call(&mut *scheme, "read-text-at", &[s, at]);
    scheme.set_step_limit(limit);
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
pub fn rust_facts(scheme: &mut Front, file: FileId, text: &str) -> R<Handle> {
    rust_facts_in(scheme, file, text, crate::ast::Conv::Cellular, false)
}

/// [`rust_facts`] of a program of convention `conv`, as its own checker
/// (`Fx26Session::fresh_checker`) checks it: what each call is compiled in
/// follows. With `syscalls`, a runtime's program (`Checker::syscalls`).
/// What it found kept, and read back where it was (`facts_cache`): the
/// same text checks alike.
pub fn rust_facts_in(scheme: &mut Front, file: FileId, text: &str, conv: crate::ast::Conv, syscalls: bool) -> R<Handle> {
    let found = form_facts(file, text, conv, syscalls)?;
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    // And each `with`'s module's values it names, and their positions, by
    // expression (`checked-withs!`), and each module reshaped
    // (`checked-reshapes!`): the checker's record, which the compiler reads.
    let withs = scheme.make(|m| found.withs(m.heap()));
    crate::entries::call(&mut *scheme, "checked-withs!", &[withs]).map_err(|e| fail(e.to_string()))?;
    let reshapes = scheme.make(|m| found.reshapes(m.heap()));
    crate::entries::call(&mut *scheme, "checked-reshapes!", &[reshapes]).map_err(|e| fail(e.to_string()))?;
    let list = scheme.make(|m| found.facts(m.heap()));
    Ok(list)
}

/// The front end's facts, as the tests compile it ([`rust_facts`], of file
/// 0), found now and kept (`fixpt prewarm`): so that a suite's tests,
/// started together, find them rather than each checking the front end.
/// How long it took, or why it failed.
pub fn prewarm_front_end_facts() -> Result<f64, String> {
    prewarm_facts(&crate::front_end())
}

/// The bootstrap program's facts, as its compile by the compiler written in
/// FX-26 wants them (`bootstrap_cache`), found now and kept likewise: half
/// of that compile's time, where its cache is cold.
pub fn prewarm_bootstrap_facts() -> Result<f64, String> {
    prewarm_facts(&crate::bootstrap_program())
}

fn prewarm_facts(text: &str) -> Result<f64, String> {
    let started = std::time::Instant::now();
    form_facts(FileId(0), text, crate::ast::Conv::Cellular, false).map_err(|e| e.message)?;
    Ok(started.elapsed().as_secs_f64())
}

/// What the Rust checker finds of `text` for [`rust_facts_in`], as plain
/// data: kept, and read back where it was (`facts_cache`).
fn form_facts(file: FileId, text: &str, conv: crate::ast::Conv, syscalls: bool) -> R<crate::rust_facts::FormFacts> {
    crate::facts_cache::found(text, conv, syscalls, || {
        let mut c = crate::Checker::with_convention(conv);
        c.syscalls = syscalls;
        c.base_dir = LOAD_BASE.with(|b| b.borrow().clone());
        let forms = c.read_in(file, text)?;
        let done = c.declare_ahead(&forms)?;
        // Which of the expressions at its span each is, as the FX-26 parser
        // numbers them (`crate::ids`): the forms in order, each after the
        // hidden globals of the files it loads first.
        let mut tops = Vec::new();
        for (f, done) in forms.iter().zip(done) {
            if !done {
                let defining = c.top_defining(f)?;
                tops.extend(defining.hoisted.iter().chain(&defining.run[..1]).map(|(t, _)| t.clone()));
            }
        }
        Ok(crate::rust_facts::FormFacts::of(&c, &tops.iter().collect::<Vec<_>>(), file, text, false))
    })
}

/// Compile `text` with the compiler written in FX-26, given what checking
/// it found (`facts`, from `checked-extracts` or [`rust_facts`]): the word
/// that runs the program, as a handle in the caller's scope, or why the
/// compiler would not make one.
/// The same, with each lambda's register code as its word's twin, made by the
/// register compiler written in FX-26 (`regcode.fx`).
pub fn compile_to_word_with_registers(scheme: &mut Front, file: FileId, text: &str, facts: Handle) -> R<Result<Handle, String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let on = scheme.make(|_| Value::TRUE);
    crate::entries::call(&mut *scheme, "compile-registers!", &[on]).map_err(|e| fail(e.to_string()))?;
    let out = compile_to_word(scheme, file, text, facts);
    let off = scheme.make(|_| Value::FALSE);
    crate::entries::call(&mut *scheme, "compile-registers!", &[off]).map_err(|e| fail(e.to_string()))?;
    out
}

/// Compile what the checker written in FX-26 just checked, as it runs it
/// (`checked-tops`, under redefinition), given what it found (`facts`):
/// the word, as a handle in the caller's scope, or why the compiler would
/// not make one.
pub fn compile_checked_to_word(scheme: &mut Front, file: FileId, facts: Handle) -> R<Result<Handle, String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let runs = crate::entries::call(&mut *scheme, "checked-tops", &[]).map_err(|e| fail(e.to_string()))?;
    let start = std::time::Instant::now();
    let own = own_numbering(scheme).map_err(fail)?;
    let result = crate::entries::call(&mut *scheme, "compile-checked", &[runs, facts, own]).map_err(|e| fail(e.to_string()))?;
    scheme.runtime_unrooted().compile_nanos += start.elapsed().as_nanos() as u64;
    word_of(scheme, result)
}

/// The numbering the compiler is given with the facts of the checker written
/// in FX-26, which are the trees' own keys (`compile-checked`): the mode's,
/// for `validate`, none to place.
fn own_numbering(scheme: &mut Front) -> Result<Handle, String> {
    let mode = crate::ids::mode() as i64;
    let fields = [37, mode, 0].map(|n| scheme.make(|_| Value::fixnum(n)));
    let nil = scheme.make(|_| Value::NULL);
    make_frozen(scheme, &[fields[0], fields[1], fields[2], nil]).map_err(|e| e.to_string())
}

pub fn compile_to_word(scheme: &mut Front, file: FileId, text: &str, facts: Handle) -> R<Result<Handle, String>> {
    let parsed = parse_to_trees(scheme, file, text)?;
    compile_trees_to_word(scheme, file, &parsed, facts)
}

/// The same, from the program's trees ([`parse_syns`]).
pub fn compile_trees_to_word(scheme: &mut Front, file: FileId, parsed: &Parsed, facts: Handle) -> R<Result<Handle, String>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let result = crate::entries::call(&mut *scheme, "compile-program", &[parsed.tops, facts, parsed.numbering]).map_err(|e| fail(e.to_string()))?;
    word_of(scheme, result)
}

/// A `cresult`'s word, or its error.
fn word_of(scheme: &mut Front, result: Handle) -> R<Result<Handle, String>> {
    let err = scheme.view(|v| {
        let r = v.get(result);
        (r.sum_tag().and_then(|t| t.symbol_name()).as_deref() == Some("c-err"))
            .then(|| r.sum_payload().and_then(|p| p.product_field(1)).and_then(|m| m.string()).unwrap_or_default())
    });
    Ok(match err {
        Some(m) => Err(m),
        None => Ok(scheme.make(|m| {
            let r = m.get(result);
            let payload = m.heap().sum_payload(r);
            m.heap().product_field(payload, 1)
        })),
    })
}

/// The parser's trees for `text`: a list of `top`s, as a handle in the
/// caller's scope.
fn parse_to_trees(scheme: &mut Front, file: FileId, text: &str) -> R<Parsed> {
    parse_to_trees_at(scheme, file, Given::Text(text, 0), &State::begun(), false)
}

/// What the parser written in FX-26 made of a text: its trees, and how it
/// numbered them (`numbering`, as the compiler takes it with facts numbered
/// by their place in the walk: `c-set-facts!`), after how many expressions
/// the parser walked before (`base`); and the session's state after it, if
/// it is kept (`after`).
pub struct Parsed {
    pub tops: Handle,
    pub numbering: Handle,
    pub base: i64,
    pub after: State,
}

/// [`parse_to_trees`], its positions counted from `base`, read in `state`.
/// `globals`: whether the checker goes on from its state (checked by
/// `check-more`, not `check-program`), its globals' shapes told the
/// expander (`check-global-shapes!`).
fn parse_to_trees_at(scheme: &mut Front, file: FileId, given: Given<'_>, state: &State, globals: bool) -> R<Parsed> {
    match given {
        Given::Text(text, base) => {
            supply_loaded_at(scheme, file, text, base)?;
            let syns = read_to_syns_at(scheme, file, text, base)?;
            parse_syns_at(scheme, file, Some((text, base)), syns, state, globals)
        }
        Given::Syn(handed) => {
            supply_loaded_from(scheme, file, Loads::Forms(&handed.loads))?;
            parse_syns_at(scheme, file, None, handed.syns, state, globals)
        }
    }
}

/// What the front end written in FX-26 is given to parse: a text, which
/// its reader reads, its places counted from a base; or the `syn` the
/// Rust reader and expander made, handed as it is ([`Handed`]).
#[derive(Clone, Copy)]
pub enum Given<'a> {
    Text(&'a str, i64),
    Syn(&'a Handed),
}

/// Forms the Rust reader read and its expander expanded, as the front end
/// written in FX-26 is handed them (`docs/research/heap-syntax.md`,
/// `heap_syn::Syn::handed`): their `syn`, a list held by a handle, in the
/// heap that runs that front end; and the files they load, where.
pub struct Handed {
    pub syns: Handle,
    /// What the forms load ([`load_modules_in`]).
    pub(crate) loads: Vec<Load>,
}

/// What the parser written in FX-26 makes of `syns`, read from `text`
/// ([`read_to_syns`]): the program's trees, or where it is wrong; read in
/// the standard environment's state, by the default switches.
pub fn parse_syns(scheme: &mut Front, file: FileId, text: &str, syns: Handle) -> R<Parsed> {
    parse_syns_at(scheme, file, Some((text, 0)), syns, &State::begun(), false)
}

/// [`parse_syns`], read in `state` by the process's mode
/// (`parser-types.fx`'s `keys`): of `text`, its positions counted from a
/// base; or, none, of `syn` handed over, placed where it is.
fn parse_syns_at(scheme: &mut Front, file: FileId, text: Option<(&str, i64)>, syns: Handle, state: &State, globals: bool) -> R<Parsed> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let mode = crate::ids::mode() as i64;
    let settings = state.settings.text();
    let product = |sc: &mut Front, fields: &[Handle]| {
        let mut all = vec![sc.make(|_| Value::fixnum(fixpt_heap::layout::kind("product") as i64))];
        all.extend_from_slice(fields);
        make_frozen(sc, &all).map_err(|e| fail(e.to_string()))
    };
    let int = |sc: &mut Front, n: i64| sc.make(|_| Value::fixnum(n));
    let fields = [int(scheme, mode), int(scheme, state.at), scheme.make(|m| m.heap().make_string(&settings))];
    let keys = product(scheme, &fields)?;
    // The expander told, first, the shapes of the globals the forms name, as
    // the checker has their types (`check-global-shapes!`): none if it is not
    // to go on from them (`globals`), whatever it last held.
    if crate::entries::bound(scheme, "check-global-shapes!") {
        let fresh = scheme.make(|_| Value::boolean(!globals));
        crate::entries::call(scheme, "check-global-shapes!", &[syns, fresh]).map_err(|e| fail(e.to_string()))?;
    }
    let keyed = crate::entries::call(&mut *scheme, "parse-program", &[keys, syns]).map_err(|e| fail(e.to_string()))?;
    // The checker told of this parse, if there is one: the macros each
    // `with`'s body used (`check-macro-uses!`).
    if crate::entries::bound(scheme, "check-macro-uses!") {
        crate::entries::call(&mut *scheme, "check-macro-uses!", &[]).map_err(|e| fail(e.to_string()))?;
    }
    // And the register compiler told of the keys the expander made
    // (`keys-mirrored!`), where a part a template made is placed.
    if crate::entries::bound(scheme, "keys-mirrored!") {
        crate::entries::call(&mut *scheme, "keys-mirrored!", &[]).map_err(|e| fail(e.to_string()))?;
    }
    let (tag, err, at, walked) = scheme.view(|v| {
        let k = v.get(keyed);
        let r = k.product_field(1).expect("a parse");
        let tag = r.sum_tag().and_then(|t| t.symbol_name()).unwrap_or_default();
        let p = r.sum_payload().expect("a sum");
        let err = (tag == "p-err").then(|| {
            (p.product_field(1).and_then(|m| m.string()).unwrap_or_default(), p.product_field(2).and_then(|x| x.fixnum()).unwrap_or(0), p.product_field(3).and_then(|x| x.fixnum()).unwrap_or(0))
        });
        (tag, err, k.product_field(2).and_then(|x| x.fixnum()).unwrap_or(0), k.product_field(3).and_then(|x| x.fixnum()).unwrap_or(0))
    });
    if let Some((msg, a, b)) = err {
        let span = match text {
            Some((text, base)) => {
                let offsets = byte_offsets(text);
                let at = |c: i64| offsets.get((c - base).max(0) as usize).copied().unwrap_or(text.len()) as u32;
                fx26_span(scheme, file, &at, a, b)
            }
            None => handed_span(scheme, file, a, b),
        };
        return Err(FxError::at(span, msg));
    }
    debug_assert_eq!(tag, "p-ok");
    let tops = scheme.make(|m| {
        let k = m.get(keyed);
        let r = m.heap().product_field(k, 1);
        let payload = m.heap().sum_payload(r);
        m.heap().product_field(payload, 1)
    });
    let given = scheme.make(|m| {
        let k = m.get(keyed);
        m.heap().product_field(k, 4)
    });
    let fields = [int(scheme, mode), int(scheme, walked), given];
    let numbering = product(scheme, &fields)?;
    Ok(Parsed { tops, numbering, base: walked, after: State { at, settings: state.settings } })
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
    static SHARED_MADE: std::cell::RefCell<fixpt_hash::HashSet<String>> = std::cell::RefCell::new(Default::default());
}

/// Set the loads the session has made (`SHARED_MADE`).
pub fn set_shared_made(made: fixpt_hash::HashSet<String>) {
    SHARED_MADE.with(|m| *m.borrow_mut() = made);
}

thread_local! {
    /// The loads the Rust checker read from their `.fasl`s, by key: each
    /// the expression it was checked as (`Checker::fasl_load`), which the
    /// parser written in FX-26 is given for it in place of the file's
    /// forms.
    static FASL_USED: std::cell::RefCell<HashMap<String, String>> = std::cell::RefCell::new(HashMap::default());
}

/// Set the loads read from `.fasl`s (`FASL_USED`).
pub fn set_fasl_used(used: HashMap<String, String>) {
    FASL_USED.with(|f| *f.borrow_mut() = used);
}

/// The positions of one module file and the next apart, in the parser
/// written in FX-26 (`parser-exps.fx`'s `load-base`).
const LOAD_BASE_STEP: i64 = 1_000_000_000;

/// A load found in a text: where it starts, its path as written, whether
/// it is a `load-input`, and, a `(%loaded "key" "path")`'s, the file its key
/// names, the path resolved.
pub(crate) type Load = (Span, String, bool, Option<String>);

/// Each `(load-module "path")` in `forms`, in order: where it starts, and
/// the path; and each form of processes or `par`, which loads the scheduler
/// (`parser-forms.fx`). Only where an expression is, as the parsers read
/// them: a name bound, a parameter, a type, a `tagcase`'s arm's tag, which
/// may be a list headed by a form's name (a binding `(self x)`), is none
/// (`TODO.md` §92). A load found where the parsers find none would be a
/// file read the Rust checker does not read, the numbering of the files
/// after it moved.
pub(crate) fn load_modules_in(forms: &[Syn], interner: &Interner, out: &mut Vec<Load>) {
    for f in forms {
        // The files its types name first, as the parsers load them
        // (`Checker::type_loads`, `type-loaded`).
        type_loads_at(f, interner, out);
        load_modules_at(f, interner, out);
    }
}

/// Each `(load-moduleof "file" …)` and `(load-input-moduleof "file" …)` in
/// `f`, outside quotations, in order.
fn type_loads_at(f: &Syn, interner: &Interner, out: &mut Vec<Load>) {
    let Some(items) = f.list() else { return };
    match items.first().and_then(|h| h.sym()).map(|h| interner.name(h)) {
        Some("quote" | "quasiquote") => {}
        Some(loader @ ("load-moduleof" | "load-input-moduleof")) => {
            if let Some(p) = items.get(1).and_then(|p| string_of(*p)) {
                out.push((f.span(), p.to_string(), loader == "load-input-moduleof", None));
            }
        }
        _ => items.iter().for_each(|x| type_loads_at(x, interner, out)),
    }
}

/// `load_modules_in` of one expression, or definition.
fn load_modules_at(f: &Syn, interner: &Interner, out: &mut Vec<Load>) {
    let Some(items) = f.list() else { return };
    let exps = |xs: &[Syn], out: &mut Vec<Load>| xs.iter().for_each(|x| load_modules_at(x, interner, out));
    // The last item of each list in `xs`: a binding's expression.
    let inits = |xs: Option<&[Syn]>, out: &mut Vec<Load>| {
        for b in xs.unwrap_or_default() {
            if let Some([_, .., init]) = b.list().as_deref() {
                load_modules_at(init, interner, out);
            }
        }
    };
    // Each clause of `xs` from item `k` on: an arm's body.
    let arms = |xs: &[Syn], k: usize, out: &mut Vec<Load>| {
        for c in xs {
            if let Some(parts) = c.list() {
                parts.get(k..).unwrap_or_default().iter().for_each(|x| load_modules_at(x, interner, out));
            }
        }
    };
    if let [head, path] = &items[..]
        && let Some(h) = head.sym()
        && matches!(interner.name(h), "load-module" | "load-input")
        && let Some(p) = string_of(*path)
    {
        out.push((f.span(), p.to_string(), interner.name(h) == "load-input", None));
    }
    if let [head, key, path] = &items[..]
        && head.sym().is_some_and(|h| interner.name(h) == "%loaded")
        && let (Some(k), Some(p)) = (string_of(*key), string_of(*path))
    {
        let (input, file) = match k.strip_prefix("input:") {
            Some(f) => (true, f),
            None => (false, k.as_str()),
        };
        out.push((f.span(), p.to_string(), input, Some(file.to_string())));
    }
    let head = items.first().and_then(|h| h.sym()).map(|h| interner.name(h));
    if matches!(head, Some("spawn" | "spawn-monitored" | "send" | "receive" | "self" | "par" | "race" | "attempt" | "attempt-within" | "pselect" | "icell-get" | "icell-put!")) {
        out.push((f.span(), crate::check::PROCESSES.to_string(), false, None));
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
            inits(items.get(1).and_then(|b| b.list()).as_deref(), out);
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
        _ => exps(&items, out),
    }
}

/// The string `s` is, if it is one.
fn string_of(s: Syn) -> Option<String> {
    match s.shape() {
        crate::heap_syn::Shape::Atom => match s.view() {
            crate::heap_syn::V::Str(t) => Some(t),
            _ => None,
        },
        _ => None,
    }
}

/// What FX-26 code cannot do itself, done for it, as a system call would:
/// each file `text`'s `load-module`s name read, and read by the reader
/// written in FX-26, then handed to the parser written in FX-26
/// (`loaded-files!`): by where the form starts, the file's base (0 if it
/// was not read), its path, why not, its forms and its text. A file read is
/// a module's in order, as the Rust checker numbers them.
pub fn supply_loaded(scheme: &mut Front, file: FileId, text: &str) -> R<()> {
    supply_loaded_at(scheme, file, text, 0).map(|_| ())
}

/// [`supply_loaded`], `text`'s positions counted from `base`. And what
/// each top-level `include` of it gives (`includes-given!`), as
/// [`set_includes`] said, then forgotten. Each file read, by its key, and
/// its text (or why it could not be read), in the order read: what a
/// reading folds of them ([`crate::ids::read_in`]).
fn supply_loaded_at(scheme: &mut Front, file: FileId, text: &str, base: i64) -> R<Vec<(String, String)>> {
    supply_loaded_from(scheme, file, Loads::Text(text, base))
}

/// [`supply_loaded_at`], of the loads `from` has.
fn supply_loaded_from(scheme: &mut Front, file: FileId, from: Loads<'_>) -> R<Vec<(String, String)>> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let (list, loads) = loaded_files_at(scheme, file, from)?;
    crate::entries::call(&mut *scheme, "loaded-files!", &[list]).map_err(|e| fail(e.to_string()))?;
    let mut list = scheme.make(|_| Value::NULL);
    let char_at: Box<dyn Fn(u32) -> i64> = match from {
        Loads::Text(text, base) => {
            let offsets = byte_offsets(text);
            Box::new(move |byte| base + offsets.partition_point(|&o| o < byte as usize) as i64)
        }
        Loads::Forms(..) => Box::new(move |byte| crate::heap_syn::at_of(Span::new(file, byte, byte)).start),
    };
    for given in INCLUDES.with(|i| std::mem::take(&mut *i.borrow_mut())).into_iter().rev() {
        let mut fields = vec![scheme.make(|_| Value::fixnum(37))];
        fields.push(scheme.make(|_| Value::fixnum(char_at(given.at))));
        for names in &given.names {
            let mut l = scheme.make(|_| Value::NULL);
            for n in names.iter().rev() {
                let sym = scheme.make(|m| m.heap().intern(n));
                l = cons(scheme, sym, l).map_err(|e| fail(e.to_string()))?;
            }
            fields.push(l);
        }
        fields.push(scheme.make(|m| m.heap().string_from_chars(&given.why.chars().collect::<Vec<_>>())));
        fields.push(scheme.make(|_| Value::fixnum(char_at(given.why_at))));
        fields.push(scheme.make(|_| Value::fixnum(char_at(given.why_end))));
        let one = make_frozen(scheme, &fields).map_err(|e| fail(e.to_string()))?;
        list = cons(scheme, one, list).map_err(|e| fail(e.to_string()))?;
    }
    crate::entries::call(&mut *scheme, "includes-given!", &[list]).map_err(|e| fail(e.to_string()))?;
    let mut names = scheme.make(|_| Value::NULL);
    for n in STANDARD_NAMES.with(|n| std::mem::take(&mut *n.borrow_mut())).into_iter().rev() {
        let sym = scheme.make(|m| m.heap().intern(&n));
        names = cons(scheme, sym, names).map_err(|e| fail(e.to_string()))?;
    }
    crate::entries::call(&mut *scheme, "standard-names!", &[names]).map_err(|e| fail(e.to_string()))?;
    Ok(loads)
}

thread_local! {
    /// What the next text the front end written in FX-26 parses has of
    /// top-level `include`s: each's start (a byte), and the names of its
    /// module's values, types and effects (`Checker::include_names`).
    static INCLUDES: std::cell::RefCell<Vec<IncludeGiven>> = const { std::cell::RefCell::new(Vec::new()) };
    /// The standard bindings' names, for the next text ([`set_standard_names`]).
    static STANDARD_NAMES: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Where the FX-26 expander's keys begin: a part a template made is at a
/// key of its own, past every text's place (`source-base`, `macros.fx`).
const SOURCE_BASE: i64 = 1 << 50;

/// The span of FX-26 places `a`..`b`, characters' places in the text
/// (`at` takes one to a byte): a part a template made, by its keys, where
/// the template wrote it, of the expansion that made it, recorded with each
/// use that made it as the Rust expander records its own, so that what is
/// said there is said at each use (`located`).
fn fx26_span(scheme: &mut Front, file: FileId, at: &dyn Fn(i64) -> u32, a: i64, b: i64) -> Span {
    if a < SOURCE_BASE && b < SOURCE_BASE {
        return Span::new(file, at(a), at(b));
    }
    let made = expansions_made(scheme);
    Sources { file, at, made, done: HashMap::default() }.span(scheme, a, b)
}

/// The span of places `a`..`b` of `syn` handed over
/// ([`Given::Syn`]): a part a template made, at its provenance's use
/// site, the outermost, as the Rust checker says what a macro made is
/// wrong at its use; a part the FX-26 expander made, by its keys
/// ([`fx26_span`]); another, where it is (`heap_syn::span_of`).
fn handed_span(scheme: &mut Front, file: FileId, a: i64, b: i64) -> Span {
    let at = |p: i64| crate::heap_syn::span_of(crate::heap_syn::At { start: p, end: p, expansion: 0 });
    if fixpt_heap::provenance::is_provenance(a) {
        let used = scheme.runtime_unrooted().heap.provenance.chain(a).and_then(|c| c.last().copied());
        return used.map_or(Span::new(file, 0, 0), at);
    }
    if a >= SOURCE_BASE || b >= SOURCE_BASE {
        let to_byte = |c: i64| at(c).start;
        return fx26_span(scheme, file, &to_byte, a, b);
    }
    crate::heap_syn::span_of(crate::heap_syn::At { start: a, end: b, expansion: 0 })
}

/// The FX-26 expander's expansions, and those recorded as Rust's so far.
struct Sources<'a> {
    file: FileId,
    at: &'a dyn Fn(i64) -> u32,
    made: HashMap<i64, (String, i64, i64)>,
    done: HashMap<i64, u32>,
}

impl Sources<'_> {
    fn span(&mut self, scheme: &mut Front, a: i64, b: i64) -> Span {
        let (ra, x) = source_of(scheme, a);
        let (rb, _) = source_of(scheme, b);
        let mut span = Span::new(self.file, (self.at)(ra), (self.at)(rb));
        span.expansion = self.expansion(scheme, x);
        span
    }

    /// FX-26 expansion `x` as a Rust one, its use's own first; 0 if none.
    fn expansion(&mut self, scheme: &mut Front, x: i64) -> u32 {
        if let Some(&r) = self.done.get(&x) {
            return r;
        }
        let Some((name, a, b)) = self.made.get(&x).cloned() else { return 0 };
        let use_at = self.span(scheme, a, b);
        let r = fixpt_read::record_expansion(&name, use_at, None);
        self.done.insert(x, r);
        r
    }
}

/// Where key `k` is, and the expansion that made the part there; a place
/// that is no key, itself and 0 (`macro-source`).
/// Where the FX-26 expander's key `k` was written: its template's place (a
/// character); `k` itself if it is no key.
pub fn source_place(scheme: &mut Front, k: i64) -> i64 {
    source_of(scheme, k).0
}

fn source_of(scheme: &mut Front, k: i64) -> (i64, i64) {
    if k < SOURCE_BASE || !crate::entries::bound(scheme, "macro-source") {
        return (k, 0);
    }
    let arg = scheme.make(|_| Value::fixnum(k));
    let Ok(r) = crate::entries::call(scheme, "macro-source", &[arg]) else { return (k, 0) };
    scheme.view(|v| {
        let r = v.get(r);
        (r.product_field(1).and_then(|x| x.fixnum()).unwrap_or(k), r.product_field(2).and_then(|x| x.fixnum()).unwrap_or(0))
    })
}

/// The FX-26 expander's expansions (`expansions-made`): each one's macro's
/// name and its use's place, by its number.
fn expansions_made(scheme: &mut Front) -> HashMap<i64, (String, i64, i64)> {
    if !crate::entries::bound(scheme, "expansions-made") {
        return HashMap::default();
    }
    let Ok(list) = crate::entries::call(scheme, "expansions-made", &[]) else { return HashMap::default() };
    scheme.view(|v| {
        let int = |x: Option<Local<'_>>| x.and_then(|x| x.fixnum()).unwrap_or(0);
        v.get(list)
            .list()
            .unwrap_or_default()
            .into_iter()
            .map(|e| (int(e.product_field(1)), (e.product_field(2).and_then(|n| n.symbol_name()).unwrap_or_default(), int(e.product_field(3)), int(e.product_field(4)))))
            .collect()
    })
}

/// What a top-level `include` of a text gives (`includes-given!`): where it
/// starts (a byte), the names of its module's values, types and effects;
/// or why it is refused, and where.
pub struct IncludeGiven {
    pub at: u32,
    pub names: [Vec<String>; 3],
    pub why: String,
    pub why_at: u32,
    pub why_end: u32,
}

/// For the next text parsed by the front end written in FX-26: what each
/// top-level `include` of it gives, as the Rust checker, which has checked
/// it, knows (`compare::both_checkers`).
pub fn set_includes(given: Vec<IncludeGiven>) {
    INCLUDES.with(|i| *i.borrow_mut() = given);
}

/// For the next text parsed by the front end written in FX-26: the
/// standard bindings' names, which a file's macro may name, as the Rust
/// checker has them (`Checker::standard_names`).
pub fn set_standard_names(names: Vec<String>) {
    STANDARD_NAMES.with(|n| *n.borrow_mut() = names);
}

/// What `text`'s `load-module`s read, as [`supply_loaded`] hands it to the
/// parser written in FX-26: for a driver that hands it to a front end of
/// its own (`tests/bootstrap.rs`, whose front end reads the front end's
/// built-in module files).
pub fn loaded_files(scheme: &mut Front, file: FileId, text: &str) -> R<fixpt_scheme::Handle> {
    loaded_files_at(scheme, file, Loads::Text(text, 0)).map(|(list, _)| list)
}

fn loaded_files_at(scheme: &mut Front, file: FileId, from: Loads<'_>) -> R<(fixpt_scheme::Handle, Vec<(String, String)>)> {
    let base_dir = LOAD_BASE.with(|b| b.borrow().clone());
    let mut list = scheme.make(|_| Value::NULL);
    let mut read = 0;
    let mut seen = HashMap::default();
    let mut order = Vec::new();
    supply_loaded_in(scheme, file, from, base_dir, &mut read, &mut seen, &mut order, &mut list)?;
    Ok((list, order))
}

/// Where the loads a parse is given are found: a text, read here, its
/// positions counted from a base; or the forms the Rust checker read and
/// expanded, handed to the parser as they are, placed where they are.
#[derive(Clone, Copy)]
enum Loads<'a> {
    Text(&'a str, i64),
    Forms(&'a [Load]),
}

/// [`supply_loaded`] for the `load-module`s of `text`, a program or a file
/// read at `base` (its positions moved past the program's by it), whose
/// relative paths are from `dir`: each file read, then those it loads, in
/// the order the Rust checker begins them (`Checker::files_read`).
fn supply_loaded_in(
    scheme: &mut Front,
    file: FileId,
    from: Loads<'_>,
    dir: Option<std::path::PathBuf>,
    read: &mut u32,
    seen: &mut HashMap<String, Read>,
    order: &mut Vec<(String, String)>,
    list: &mut fixpt_scheme::Handle,
) -> R<()> {
    let fail = |m: String| FxError::at(Span::new(file, 0, 0), m);
    let mut loads = Vec::new();
    // Each load's place: in a text read here, its byte's; in forms handed
    // over, its span's, in whichever file the form is.
    let place: Box<dyn Fn(Span) -> i64> = match from {
        Loads::Text(text, base) => {
            let mut interner = Interner::new();
            let read = crate::heap_syn::aside(|| crate::heap_syn::read_syn_passing(text, &mut interner, |forms, interner| load_modules_in(forms, interner, &mut loads)));
            if read.is_err() {
                return Ok(());
            }
            let offsets = byte_offsets(text);
            Box::new(move |span| base + offsets.partition_point(|&o| o < span.start as usize) as i64)
        }
        Loads::Forms(given) => {
            loads.extend_from_slice(given);
            Box::new(|span| crate::heap_syn::at_of(span).start)
        }
    };
    for (start, path, input, resolved) in loads {
        let at = match (&resolved, &dir) {
            (Some(file), _) => std::path::PathBuf::from(file),
            (None, Some(d)) if std::path::Path::new(&path).is_relative() && crate::built_in_module(&path).is_none() => d.join(&path),
            _ => std::path::PathBuf::from(&path),
        };
        // Every load of a path is one (`TODO.md` §68): the file read once,
        // as the Rust checker reads it, and named by `key` for the parser. A
        // file of module parameters is read as a `load-input` file is
        // (`Checker::modules_made`): its key `input:` for a `load-module`
        // too, which the parser takes as it is.
        let redirected = !input && crate::parse::takes_modules_at(&at, &path);
        let input = input || redirected;
        let key = if redirected { format!("input:{}", at.display()) } else { at.display().to_string() };
        let string = |sc: &mut Front, t: &str| sc.make(|m| m.heap().string_from_chars(&t.chars().collect::<Vec<_>>()));
        let entry = |sc: &mut Front, list: &mut fixpt_scheme::Handle, r: &Read| -> R<()> {
            let fields = [
                sc.make(|_| Value::fixnum(37)),
                sc.make(|_| Value::fixnum(place(start))),
                sc.make(|_| Value::fixnum(r.base)),
                string(sc, &r.why),
                string(sc, &path),
                r.syns,
                string(sc, &r.text),
                string(sc, &key),
                sc.make(|_| Value::boolean(r.fasl)),
            ];
            let one = make_frozen(sc, &fields).map_err(|e| fail(e.to_string()))?;
            *list = cons(sc, one, *list).map_err(|e| fail(e.to_string()))?;
            Ok(())
        };
        let shared = if input && !redirected { format!("input:{key}") } else { key.clone() };
        if let Some(r) = seen.get(&shared) {
            entry(scheme, list, r)?;
            continue;
        }
        // Made by a form before, and loaded here, not defined (a
        // `%loaded` is its definition).
        if resolved.is_none() && SHARED_MADE.with(|m| m.borrow().contains(&shared)) {
            // Its text in the reading of the form that made it.
            order.push((shared.clone(), String::new()));
            let nil = scheme.make(|_| Value::NULL);
            entry(scheme, list, &Read { base: -1, why: String::new(), syns: nil, text: String::new(), fasl: false })?;
            continue;
        }
        // A module file built in (`fx26:…`) is its text, not a file's; one
        // the Rust checker read from its `.fasl`, the expression it read.
        let fasl = FASL_USED.with(|f| f.borrow().get(&shared).cloned());
        let contents = |at: &std::path::Path| match (fasl.as_deref(), crate::built_in_module(&path)) {
            (Some(t), _) | (None, Some(t)) => Ok(t.to_string()),
            (None, None) => crate::reads::read_file(at),
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
        let r = Read { base: file_base, why, syns, text: ftext, fasl: fasl.is_some() };
        entry(scheme, list, &r)?;
        order.push((shared.clone(), if r.why.is_empty() { r.text.clone() } else { r.why.clone() }));
        let ftext = r.text.clone();
        seen.insert(shared, r);
        // The files it loads, from its directory, at its positions.
        if file_base > 0 {
            supply_loaded_in(scheme, FileId(1000 + *read), Loads::Text(&ftext, file_base), at.parent().map(|d| d.to_path_buf()), read, seen, order, list)?;
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
    /// Whether `text` is a `.fasl`'s expression, not the file's.
    fasl: bool,
}

/// The byte offset of each character, and of the end.
fn byte_offsets(text: &str) -> Vec<usize> {
    let mut v: Vec<usize> = text.char_indices().map(|(i, _)| i).collect();
    v.push(text.len());
    v
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Where the loads' scan finds the scheduler loaded (`load_modules_in`).
    fn scheduler_loads(text: &str) -> Vec<u32> {
        let mut interner = Interner::new();
        let mut out = Vec::new();
        crate::heap_syn::aside(|| crate::heap_syn::read_syn_passing(text, &mut interner, |forms, interner| load_modules_in(forms, interner, &mut out))).expect("reads");
        out.into_iter().filter(|(_, p, _, _)| p == crate::check::PROCESSES).map(|(at, ..)| at.start).collect()
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

/// What `%make-frozen` makes, with no engine between: a frozen sum or
/// product of kind `fields[0]` (a fixnum), its fields the rest.
fn make_frozen(s: &mut Front, fields: &[Handle]) -> Result<Handle, String> {
    let kind = s.view(|v| v.get(fields[0]).fixnum()).ok_or("%make-frozen makes sums and products")?;
    if kind != fixpt_heap::layout::kind("sum") as i64 && kind != fixpt_heap::layout::kind("product") as i64 {
        return Err("%make-frozen makes sums and products".into());
    }
    Ok(s.make(|m| {
        let rest: Vec<Value> = fields[1..].iter().map(|h| m.get(*h)).collect();
        m.heap().make_frozen(kind as u8, &rest)
    }))
}

/// A pair of what `a` and `b` root, as `cons` makes it.
fn cons(s: &mut Front, a: Handle, b: Handle) -> Result<Handle, String> {
    Ok(s.make(|m| {
        let (x, y) = (m.get(a), m.get(b));
        m.heap().cons(x, y)
    }))
}
