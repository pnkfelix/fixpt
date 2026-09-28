//! Cellular code, shown: a word's cells as routines and their operands,
//! and every word it reaches, each once. For looking at what a compiler
//! made, from a REPL (`%disassemble`) or a test.

use crate::print::write_value;
use fixpt_heap::layout::kind;
use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, PRIMITIVES, ROUTINES, WORD_CELL0, WORD_ENTRY, WORD_NAME, WORD_TWIN, operands};
use fixpt_heap::{Heap, Value};
use std::fmt::Write as _;

/// `v`, a cellular word or closure, shown; or why it is neither.
pub fn disassemble(heap: &Heap, v: Value) -> String {
    disassemble_with(heap, v, None)
}

/// A native closure shown as what its machine code was compiled from:
/// its free values, then its code's register code, and that of every
/// procedure it makes closures of (the stack code beside it the native
/// compiler does not read). `None` if `v` is not one, or its code keeps no
/// word (a continuation's).
pub fn native_source(heap: &Heap, v: Value) -> Option<String> {
    use fixpt_heap::layout::cellular::{CLOSURE_FREE0, CLOSURE_WORD, CODE_SOURCE};
    if !(v.is_bloblet() && heap.bloblet_kind(v) == kind("native-closure")) {
        return None;
    }
    let code = heap.bloblet_slot(v, CLOSURE_WORD);
    let word = heap.bloblet_slot(code, CODE_SOURCE);
    if !heap.is_cellular_word(word) {
        return None;
    }
    let free = (heap.bloblet_head(v).fields + 1).saturating_sub(CLOSURE_FREE0);
    let mut out = format!("a native closure over {free} value(s), compiled from the register code below (`,disassemble-asm` shows its machine code):\n");
    for i in 0..free {
        let _ = writeln!(out, "  free {i}: {}", short(heap, heap.bloblet_slot(v, CLOSURE_FREE0 + i)));
    }
    let (mut todo, mut seen) = (vec![word], Vec::new());
    while let Some(w) = todo.pop() {
        if seen.contains(&w.raw()) || !heap.is_cellular_word(w) {
            continue;
        }
        seen.push(w.raw());
        let twin = heap.bloblet_slot(w, WORD_TWIN);
        let fields = heap.bloblet_head(twin).fields;
        if heap.is_register_word(twin) {
            let _ = writeln!(out, "\nprocedure {} ({} cells of register code):", name_of(heap, w), fields + 1 - WORD_CELL0);
            register_lines(heap, twin, &mut out, &mut todo);
        }
    }
    Some(out)
}

/// The same, with each word's machine code as `asm` shows it, after its
/// cells and after its register code's (`,disassemble-asm`).
pub fn disassemble_with(heap: &Heap, v: Value, asm: Option<crate::runtime::MachineCode>) -> String {
    let closure = kind("cellular-closure");
    let mut out = String::new();
    if let Some(k) = heap.continuation_of(v) {
        let mut todo = continuation(heap, k, &mut out);
        let mut seen = Vec::new();
        while let Some(w) = todo.pop() {
            if !seen.contains(&w.raw()) {
                seen.push(w.raw());
                word(heap, w, &mut out, &mut todo, asm);
            }
        }
        return out;
    }
    let start = if v.is_bloblet() && heap.bloblet_kind(v) == closure {
        let free = (heap.bloblet_head(v).fields + 1).saturating_sub(CLOSURE_FREE0);
        let _ = writeln!(out, "a closure over {free} value(s):");
        for i in 0..free {
            let _ = writeln!(out, "  free {i}: {}", short(heap, heap.bloblet_slot(v, CLOSURE_FREE0 + i)));
        }
        heap.bloblet_slot(v, CLOSURE_WORD)
    } else if heap.is_cellular_word(v) {
        v
    } else {
        return format!("not cellular code: {}\n", short(heap, v));
    };
    let (mut todo, mut seen) = (vec![start], Vec::new());
    while let Some(w) = todo.pop() {
        if seen.contains(&w.raw()) {
            continue;
        }
        seen.push(w.raw());
        word(heap, w, &mut out, &mut todo, asm);
    }
    out
}

/// A continuation: where it resumes, and the stacks it carries, oldest
/// first, as they will be when it is reinstated. Returns the words it
/// reaches, to show after.
fn continuation(heap: &Heap, k: Value, out: &mut String) -> Vec<Value> {
    use fixpt_heap::layout::cellular::{CONT_BASE, CONT_CLO, CONT_CUR, CONT_DS, CONT_FP, CONT_K, CONT_RS, CONT_WHOLE};
    let mut words = Vec::new();
    let whole = heap.bloblet_slot(k, CONT_WHOLE) == Value::TRUE;
    let at = |w: Value, k: Value| {
        let cell = k.as_fixnum() - WORD_CELL0 as i64;
        if heap.is_cellular_word(w) { format!("word {} at cell {cell}", name_of(heap, w)) } else { short(heap, w) }
    };
    let cur = heap.bloblet_slot(k, CONT_CUR);
    let _ = writeln!(
        out,
        "a {} continuation, resuming in {} (frame at {}, closure {}), captured above data stack depth {}:",
        if whole { "whole" } else { "composable" },
        at(cur, heap.bloblet_slot(k, CONT_K)),
        heap.bloblet_slot(k, CONT_FP).as_fixnum(),
        short(heap, heap.bloblet_slot(k, CONT_CLO)),
        heap.bloblet_slot(k, CONT_BASE).as_fixnum(),
    );
    if heap.is_cellular_word(cur) {
        words.push(cur);
    }
    let ds = heap.bloblet_slot(k, CONT_DS);
    let _ = writeln!(out, "  data stack, {} value(s), oldest first:", heap.obj_len(ds));
    for (i, x) in heap.obj_iter(ds).enumerate() {
        let _ = writeln!(out, "    {i:>4}: {}", short(heap, x));
    }
    let rs: Vec<Value> = heap.obj_iter(heap.bloblet_slot(k, CONT_RS)).collect();
    let _ = writeln!(out, "  return stack, {} entr(ies), oldest first:", rs.len() / 4);
    // The markers' first words, as `fixpt_engine::cellular` has them.
    let (prompt_mark, mark_mark) = (Value::DEFAULT, Value::UNSPECIFIED);
    for (i, e) in rs.chunks(4).enumerate() {
        let line = match e {
            [m, tag, handler, height] if *m == prompt_mark => {
                format!("prompt for {}, handler {}, data stack height {}", short(heap, *tag), short(heap, *handler), height.as_fixnum())
            }
            [m, key, v, _] if *m == mark_mark => format!("mark {} = {}", short(heap, *key), short(heap, *v)),
            [w, k, fp, clo] => {
                if heap.is_cellular_word(*w) {
                    words.push(*w);
                }
                format!("return to {} (frame at {}, closure {})", at(*w, *k), fp.as_fixnum(), short(heap, *clo))
            }
            _ => "a partial entry".to_string(),
        };
        let _ = writeln!(out, "    {i:>4}: {line}");
    }
    words
}

/// A value as it is written, cut short.
fn short(heap: &Heap, v: Value) -> String {
    let s = write_value(heap, v);
    if s.chars().count() > 60 { format!("{}…", s.chars().take(60).collect::<String>()) } else { s }
}

fn name_of(heap: &Heap, w: Value) -> String {
    heap.symbol_name(heap.bloblet_slot(w, WORD_NAME))
}

/// One word: its name, how it is entered, and a line per instruction.
fn word(heap: &Heap, w: Value, out: &mut String, todo: &mut Vec<Value>, asm: Option<crate::runtime::MachineCode>) {
    let closure = kind("cellular-closure");
    let fields = heap.bloblet_head(w).fields;
    let entry = heap.bloblet_slot(w, WORD_ENTRY).as_fixnum();
    let how = match entry {
        0 => "cellular".to_string(),
        n if n >= PRIMITIVES as i64 => format!("compiled to machine code, native slot {n}"),
        n => format!("the routine {}", ROUTINES.get(n as usize).map_or("?", |r| r.0)),
    };
    let _ = writeln!(out, "\nword {} ({} cells, {how}):", name_of(heap, w), fields + 1 - WORD_CELL0);
    let mut k = WORD_CELL0;
    while k <= fields {
        let cell = heap.bloblet_slot(w, k);
        let at = k - WORD_CELL0;
        if !cell.is_fixnum() {
            if heap.is_cellular_word(cell) {
                todo.push(cell);
                let _ = writeln!(out, "  {at:>4}: word {}", name_of(heap, cell));
            } else {
                let _ = writeln!(out, "  {at:>4}: {}", short(heap, cell));
            }
            k += 1;
            continue;
        }
        let n = cell.as_fixnum() as usize;
        let name = ROUTINES.get(n).map_or("?", |r| r.0);
        let ops: Vec<Value> = (1..=operands(name)).filter(|i| k + i <= fields).map(|i| heap.bloblet_slot(w, k + i)).collect();
        let shown: Vec<String> = match name {
            "branch" | "0branch" => vec![format!("→ {}", at as i64 + 2 + ops[0].as_fixnum())],
            "global" | "global!" => vec![global(heap, ops[0])],
            "prim" => {
                let p = ops[0].as_fixnum() as usize;
                let pname = crate::PRIMITIVES.get(p).map_or("?", |d| d.name);
                vec![pname.to_string(), ops[1].as_fixnum().to_string()]
            }
            "closure" => {
                todo.push(ops[0]);
                vec![format!("word {}", name_of(heap, ops[0])), format!("over {}", ops[1].as_fixnum())]
            }
            _ => ops
                .iter()
                .map(|v| {
                    if heap.is_cellular_word(*v) {
                        todo.push(*v);
                        format!("word {}", name_of(heap, *v))
                    } else if v.is_bloblet() && heap.bloblet_kind(*v) == closure {
                        todo.push(heap.bloblet_slot(*v, CLOSURE_WORD));
                        format!("closure of {}", name_of(heap, heap.bloblet_slot(*v, CLOSURE_WORD)))
                    } else {
                        short(heap, *v)
                    }
                })
                .collect(),
        };
        let _ = writeln!(out, "  {at:>4}: {name}{}{}", if shown.is_empty() { "" } else { " " }, shown.join(" "));
        k += 1 + ops.len();
    }
    if let Some(text) = asm.and_then(|f| f(heap, w)) {
        machine_code(out, &text);
    }
    let twin = heap.bloblet_slot(w, WORD_TWIN);
    if heap.is_register_word(twin) {
        register_word(heap, twin, out, todo);
        if let Some(text) = asm.and_then(|f| f(heap, twin)) {
            machine_code(out, &format!("its register code's {text}"));
        }
    }
}

/// Machine code as a machine shows it, under the word it belongs to.
fn machine_code(out: &mut String, text: &str) {
    for line in text.lines() {
        let _ = writeln!(out, "  {line}");
    }
}

/// A word's register code (PLAN.md 13h′): a line per instruction.
fn register_word(heap: &Heap, w: Value, out: &mut String, todo: &mut Vec<Value>) {
    let fields = heap.bloblet_head(w).fields;
    let entry = heap.bloblet_slot(w, WORD_ENTRY).as_fixnum();
    let how = if entry == 0 { "not compiled".to_string() } else { format!("native slot {entry}") };
    let _ = writeln!(out, "  its register code ({} cells, {how}):", fields + 1 - WORD_CELL0);
    register_lines(heap, w, out, todo);
}

/// A word's register code, a line per instruction.
fn register_lines(heap: &Heap, w: Value, out: &mut String, todo: &mut Vec<Value>) {
    use fixpt_heap::layout::regcode::OPS;
    let fields = heap.bloblet_head(w).fields;
    let mut k = WORD_CELL0;
    while k <= fields {
        let at = k - WORD_CELL0;
        let (name, n, _) = OPS[heap.bloblet_slot(w, k).as_fixnum() as usize];
        let ops: Vec<Value> = (1..=n).map(|i| heap.bloblet_slot(w, k + i)).collect();
        let routine = |v: Value| ROUTINES.get(v.as_fixnum() as usize).map_or("?", |r| r.0).to_string();
        let shown: Vec<String> = match name {
            "branch" | "branchf" => vec![format!("→ {}", at as i64 + 2 + ops[0].as_fixnum())],
            "global" | "setglbl" => vec![global(heap, ops[0])],
            "op1" | "cellular" => std::iter::once(routine(ops[0])).chain(ops[1..].iter().map(|v| short(heap, *v))).collect(),
            "op2" | "op2imm" => vec![routine(ops[0]), short(heap, ops[1])],
            "prim" => {
                let pname = crate::PRIMITIVES.get(ops[0].as_fixnum() as usize).map_or("?", |d| d.name);
                vec![pname.to_string(), ops[1].as_fixnum().to_string()]
            }
            "lambda" => {
                todo.push(ops[0]);
                vec![format!("word {}", name_of(heap, ops[0])), format!("over {}", ops[1].as_fixnum())]
            }
            _ => ops.iter().map(|v| short(heap, *v)).collect(),
        };
        let _ = writeln!(out, "  {at:>6}: {name}{}{}", if shown.is_empty() { "" } else { " " }, shown.join(" "));
        k += 1 + n;
    }
}

/// A global's cell: its name, if it carries one (field 3).
fn global(heap: &Heap, g: Value) -> String {
    if g.is_bloblet() && heap.bloblet_head(g).fields >= 3 {
        let n = heap.bloblet_slot(g, 3);
        if n.is_bloblet() && heap.bloblet_kind(n) == kind("symbol") {
            return heap.symbol_name(n);
        }
    }
    "a global".to_string()
}
