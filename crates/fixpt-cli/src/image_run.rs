//! Heap images as programs: dumping one, running one, and shipping one.
//!
//! The model is Larceny's, with the part Larceny never had. A heap image is the
//! program — not a serialised AST that something else interprets, but the live
//! object graph, closures and code objects included, written out and read back.
//! Because the Core IR lives in the heap, "the program" and "the heap" are the
//! same thing, so there is no separate code format to keep in step.
//!
//! Three ways to ship it, which is what the whole arrangement is for:
//!
//! * **`dump-heap`** — an image beside a runtime. The `fixpt` binary stays one
//!   copy on disk however many images you have.
//! * **`build`** — the image appended to a copy of the runtime, with a trailer
//!   saying where it starts. One file, no install step, nothing to find at run
//!   time.
//! * **`run-image`** — either of the above, run explicitly.
//!
//! An image says which engine made it, so none of these take an `--engine`:
//! compiled code has a constants vector where interpreted code has `#f`, and
//! that is enough to pick the machine that can run it.

use fixpt_core::lower::{CODE_ARITY, CODE_HAS_REST};
use fixpt_engine::{Backend, Interp, Prepared, Vm};
use fixpt_heap::{Heap, ObjType, Value, image};
use fixpt_runtime::{Runtime, write_value};

/// Read a file that is either a bare image or an executable with one appended.
pub fn read_image(path: &str) -> Result<Heap, String> {
    let bytes = std::fs::read(path).map_err(|e| format!("cannot read {path}: {e}"))?;
    let img = image::extract_embedded(&bytes).unwrap_or(&bytes);
    image::load(img).map_err(|e| format!("{path}: {e}"))
}

/// Which engine can run `proc`.
///
/// Self-describing rather than recorded in a header: a `Code` object built by
/// the compiler carries its constants in a vector, and one built by the lowerer
/// has `#f` there because its constants sit inline among its nodes. So the
/// question is answered by the code itself, and an image cannot claim to be
/// something it is not.
pub fn backend_of(heap: &Heap, proc: Value) -> Option<Backend> {
    if !heap.is_a(proc, ObjType::Closure) {
        return None;
    }
    let code = heap.obj_ref(proc, 0);
    if !heap.is_a(code, ObjType::Code) {
        return None;
    }
    Some(if !fixpt_core::lower::is_compiled(heap, code) {
        Backend::Ast
    } else {
        Backend::Bytecode
    })
}

/// Run an image's entry point.
///
/// `main` is called with the remaining command-line arguments as a list of
/// strings if it takes any, and with none if it does not — so the common case
/// of a program that ignores its arguments needs no ceremony.
pub fn run_entry(heap: Heap, entry: &str, argv: &[String]) -> i32 {
    let mut rt = Runtime::from_heap(heap);
    let Some(sym) = rt.heap.intern_existing(entry) else {
        eprintln!("fixpt: this image defines no `{entry}`");
        return 1;
    };
    let slot = rt.heap.symbol_global_slot(sym);
    let proc = rt.heap.global(slot);
    if proc.is_unbound() {
        eprintln!("fixpt: this image defines no `{entry}`");
        return 1;
    }
    let Some(backend) = backend_of(&rt.heap, proc) else {
        eprintln!("fixpt: `{entry}` is not a procedure");
        return 1;
    };

    let args: Vec<Value> = if wants_arguments(&rt.heap, proc) {
        let strings: Vec<Value> = argv.iter().map(|a| rt.heap.make_string(a)).collect();
        vec![rt.heap.list_from(&strings)]
    } else {
        Vec::new()
    };

    let mut prepared = Prepared::resumed_with(backend);
    let outcome = match backend {
        Backend::Ast => Interp::new().call(&mut rt, &mut prepared, proc, &args),
        Backend::Bytecode => Vm::new().call(&mut rt, &mut prepared, proc, &args),
    };
    match outcome {
        Ok(v) => {
            // An explicit exit code if the program returns one, which is the
            // only thing a shell can read back.
            if v.is_fixnum() {
                v.as_fixnum() as i32
            } else {
                0
            }
        }
        Err(t) => {
            eprintln!("fixpt: {}", describe(&rt, t.obj));
            1
        }
    }
}

fn wants_arguments(heap: &Heap, proc: Value) -> bool {
    let code = heap.obj_ref(proc, 0);
    let arity = heap.bloblet_slot(code, CODE_ARITY).as_fixnum();
    arity > 0 || heap.bloblet_slot(code, CODE_HAS_REST).is_true()
}

fn describe(rt: &Runtime, obj: Value) -> String {
    if rt.is_error_object(obj) {
        let msg = fixpt_runtime::display_value(&rt.heap, rt.heap.obj_ref(obj, 1));
        let irritants = rt
            .heap
            .list_to_vec(rt.heap.obj_ref(obj, 2))
            .unwrap_or_default();
        if irritants.is_empty() {
            return msg;
        }
        let rendered: Vec<String> = irritants
            .iter()
            .map(|v| write_value(&rt.heap, *v))
            .collect();
        return format!("{msg}: {}", rendered.join(" "));
    }
    format!("uncaught: {}", write_value(&rt.heap, obj))
}

/// Append an image to a copy of this executable, producing a standalone one.
///
/// The runtime is copied rather than referenced: the result has to keep working
/// when the `fixpt` that produced it is gone, which is exactly the property
/// that makes a single binary worth having.
pub fn embed(image_bytes: &[u8], out: &str) -> Result<(), String> {
    let exe = std::env::current_exe().map_err(|e| format!("cannot find myself: {e}"))?;
    let runtime = std::fs::read(&exe).map_err(|e| format!("cannot read {}: {e}", exe.display()))?;
    if image::extract_embedded(&runtime).is_some() {
        return Err("this executable already carries an image; build from a plain `fixpt`".into());
    }
    let combined = image::embed_into(&runtime, image_bytes);
    std::fs::write(out, &combined).map_err(|e| format!("cannot write {out}: {e}"))?;
    make_executable(out)
}

#[cfg(unix)]
fn make_executable(path: &str) -> Result<(), String> {
    use std::os::unix::fs::PermissionsExt as _;
    let mut perms = std::fs::metadata(path)
        .map_err(|e| format!("cannot stat {path}: {e}"))?
        .permissions();
    perms.set_mode(perms.mode() | 0o111);
    std::fs::set_permissions(path, perms).map_err(|e| format!("cannot chmod {path}: {e}"))
}

#[cfg(not(unix))]
fn make_executable(_path: &str) -> Result<(), String> {
    Ok(())
}

/// If *this* binary carries an image, it is that program rather than the
/// driver. Checked before any argument parsing, so an embedded program owns its
/// whole command line.
pub fn embedded_in_self() -> Option<Heap> {
    let exe = std::env::current_exe().ok()?;
    let bytes = std::fs::read(exe).ok()?;
    let img = image::extract_embedded(&bytes)?;
    image::load(img).ok()
}
