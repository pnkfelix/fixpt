//! Threaded code, shown: a word's cells as routines and their operands,
//! and every word it reaches, each once. For looking at what a compiler
//! made, from a REPL (`%disassemble`) or a test.

use crate::print::write_value;
use fixpt_heap::layout::kind;
use fixpt_heap::layout::threaded::{CLOSURE_FREE0, CLOSURE_WORD, PRIMITIVES, ROUTINES, WORD_CELL0, WORD_ENTRY, WORD_NAME, operands};
use fixpt_heap::{Heap, Value};
use std::fmt::Write as _;

/// `v`, a threaded word or closure, shown; or why it is neither.
pub fn disassemble(heap: &Heap, v: Value) -> String {
    let closure = kind("threaded-closure");
    let mut out = String::new();
    let start = if v.is_bloblet() && heap.bloblet_kind(v) == closure {
        let free = (heap.bloblet_head(v).fields + 1).saturating_sub(CLOSURE_FREE0);
        let _ = writeln!(out, "a closure over {free} value(s):");
        for i in 0..free {
            let _ = writeln!(out, "  free {i}: {}", short(heap, heap.bloblet_slot(v, CLOSURE_FREE0 + i)));
        }
        heap.bloblet_slot(v, CLOSURE_WORD)
    } else if heap.is_threaded_word(v) {
        v
    } else {
        return format!("not threaded code: {}\n", short(heap, v));
    };
    let (mut todo, mut seen) = (vec![start], Vec::new());
    while let Some(w) = todo.pop() {
        if seen.contains(&w.raw()) {
            continue;
        }
        seen.push(w.raw());
        word(heap, w, &mut out, &mut todo);
    }
    out
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
fn word(heap: &Heap, w: Value, out: &mut String, todo: &mut Vec<Value>) {
    let closure = kind("threaded-closure");
    let fields = heap.bloblet_head(w).fields;
    let entry = heap.bloblet_slot(w, WORD_ENTRY).as_fixnum();
    let how = match entry {
        0 => "threaded".to_string(),
        n if n >= PRIMITIVES as i64 => format!("compiled to machine code, native slot {n}"),
        n => format!("the routine {}", ROUTINES.get(n as usize).map_or("?", |r| r.0)),
    };
    let _ = writeln!(out, "\nword {} ({} cells, {how}):", name_of(heap, w), fields + 1 - WORD_CELL0);
    let mut k = WORD_CELL0;
    while k <= fields {
        let cell = heap.bloblet_slot(w, k);
        let at = k - WORD_CELL0;
        if !cell.is_fixnum() {
            if heap.is_threaded_word(cell) {
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
                    if heap.is_threaded_word(*v) {
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
