//! FX-26: the tooling's own language. See `docs/fx26.md`.
//!
//! Step 1 of that plan: the kernel — KFX, the kernel of FX-87 that Jouvelot &
//! Gifford state their rules over, with the changes the design document lists
//! — and **control effects**. `(goto r)` is the effect of an expression that
//! may not return to its continuation; `(comefrom r)` of one that may keep its
//! continuation for later (PLDI '89, §3). `cwcc` carries them in its type, and
//! masking removes them under the paper's conditions (§5).
//!
//! Checking is bidirectional (`infer`): an expression is checked against a
//! type when one is expected, which supplies `lambda` parameter types and
//! solves the binders of a polymorphic operator, so that most `proj`s and
//! `plambda`s need not be written. Written out, they mean the same thing.
//!
//! This crate depends on neither FX-87 nor FX-91. It borrows FX-87's
//! algorithms — regions, subtyping, masking — by reading them; each place that
//! does says where from.

pub mod ast;

/// The eager reader, written in FX-26: see the file's own header. A module
/// file of the reader's regions, built in ([`FRONT_END_MODULES`]).
/// The parser's types, of the reader's regions and its own: a module file
/// of no state (`TODO.md` §68).
pub const PARSER_TYPES: &str = include_str!("parser-types.fx");

/// The types of `check-types.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_TYPES_TYPES: &str = include_str!("check-types-types.fx");

/// The types of `check-env.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_ENV_TYPES: &str = include_str!("check-env-types.fx");

/// The types of `check-print.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_PRINT_TYPES: &str = include_str!("check-print-types.fx");

/// The types of `check-unions.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_UNIONS_TYPES: &str = include_str!("check-unions-types.fx");

/// The types of `check-holds.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_HOLDS_TYPES: &str = include_str!("check-holds-types.fx");

/// The types of `check-read.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_READ_TYPES: &str = include_str!("check-read-types.fx");

/// The types of `check-syntax.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_SYNTAX_TYPES: &str = include_str!("check-syntax-types.fx");

/// The types of `check-subst.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_SUBST_TYPES: &str = include_str!("check-subst-types.fx");

/// The types of `check-generative.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_GENERATIVE_TYPES: &str = include_str!("check-generative-types.fx");

/// The types of `check-resolve.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_RESOLVE_TYPES: &str = include_str!("check-resolve-types.fx");

/// The types of `arm64.fx`: a module file of no state (`TODO.md` §68).
pub const ARM64_TYPES: &str = include_str!("arm64-types.fx");

/// The types of `native.fx`: a module file of no state (`TODO.md` §68).
pub const NATIVE_TYPES: &str = include_str!("native-types.fx");

/// The signature of `layout.fx` as its clients use it (`TODO.md` §68).
pub const LAYOUT_TYPES: &str = include_str!("layout-types.fx");

/// The signature of `native-layout.fx` as its clients use it (`TODO.md`
/// §68).
pub const NATIVE_LAYOUT_TYPES: &str = include_str!("native-layout-types.fx");

/// The types of `compile.fx`: a module file of no state (`TODO.md` §68).
pub const COMPILE_TYPES: &str = include_str!("compile-types.fx");

/// The types of `compile-lift.fx`: a module file of no state (`TODO.md` §68).
pub const COMPILE_LIFT_TYPES: &str = include_str!("compile-lift-types.fx");

/// The types of `compile-exps.fx`: a module file of no state (`TODO.md` §68).
pub const COMPILE_EXPS_TYPES: &str = include_str!("compile-exps-types.fx");

/// The types of `compile-plan.fx`: a module file of no state (`TODO.md` §68).
pub const COMPILE_PLAN_TYPES: &str = include_str!("compile-plan-types.fx");

/// The types of `regcode.fx`: a module file of no state (`TODO.md` §68).
pub const REGCODE_TYPES: &str = include_str!("regcode-types.fx");

/// The types of `regcode-exps.fx`: a module file of no state (`TODO.md` §68).
pub const REGCODE_EXPS_TYPES: &str = include_str!("regcode-exps-types.fx");

/// The types of `regcode-helpers.fx`: a module file of no state (`TODO.md` §68).
pub const REGCODE_HELPERS_TYPES: &str = include_str!("regcode-helpers-types.fx");

/// The types of `regcode-modules.fx`: a module file of no state (`TODO.md` §68).
pub const REGCODE_MODULES_TYPES: &str = include_str!("regcode-modules-types.fx");

/// The types of `regcode-entry.fx`: a module file of no state (`TODO.md` §68).
pub const REGCODE_ENTRY_TYPES: &str = include_str!("regcode-entry-types.fx");

/// The types of `compile-programs.fx`: a module file of no state (`TODO.md` §68).
pub const COMPILE_PROGRAMS_TYPES: &str = include_str!("compile-programs-types.fx");

/// The signatures of `compile-twins.fx` and `compile-inline.fx` as their
/// clients use them (`TODO.md` §68).
pub const COMPILE_TWINS_TYPES: &str = include_str!("compile-twins-types.fx");
pub const COMPILE_INLINE_TYPES: &str = include_str!("compile-inline-types.fx");

/// The compiler's loop over a program's forms: a `load-input` file, which
/// the conductor applies to the modules it uses (`TODO.md` §68).
pub const COMPILE_PROGRAMS: &str = include_str!("compile-programs.fx");

/// `compile-inline.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const COMPILE_INLINE: &str = include_str!("compile-inline.fx");

/// `compile-twins.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const COMPILE_TWINS: &str = include_str!("compile-twins.fx");

/// `regcode-entry.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const REGCODE_ENTRY: &str = include_str!("regcode-entry.fx");

/// `regcode-core-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const REGCODE_CORE_TYPES: &str = include_str!("regcode-core-types.fx");

/// `regcode-core.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const REGCODE_CORE: &str = include_str!("regcode-core.fx");

/// `regcode-modules.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const REGCODE_MODULES: &str = include_str!("regcode-modules.fx");

/// `regcode-helpers.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const REGCODE_HELPERS: &str = include_str!("regcode-helpers.fx");

/// `regcode-places-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const REGCODE_PLACES_TYPES: &str = include_str!("regcode-places-types.fx");

/// `regcode-places.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const REGCODE_PLACES: &str = include_str!("regcode-places.fx");

/// `regcode-exps.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const REGCODE_EXPS: &str = include_str!("regcode-exps.fx");

/// `standard-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const STANDARD_TYPES: &str = include_str!("standard-types.fx");

/// `compile-plan.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const COMPILE_PLAN: &str = include_str!("compile-plan.fx");

/// `check-program-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_PROGRAM_TYPES: &str = include_str!("check-program-types.fx");

/// `compile-state-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const COMPILE_STATE_TYPES: &str = include_str!("compile-state-types.fx");

/// `compile-exps.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const COMPILE_EXPS: &str = include_str!("compile-exps.fx");

/// `compile-state.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const COMPILE_STATE: &str = include_str!("compile-state.fx");

/// `compile-lift.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const COMPILE_LIFT: &str = include_str!("compile-lift.fx");

/// Hash tables' types: a module file of no state (`TODO.md` §68).
pub const TABLE_TYPES: &str = include_str!("table-types.fx");

/// The eager reader's types, of its regions: a module file of no state,
/// which the reader and any of its clients load (`TODO.md` §68).
pub const EAGER_READER_TYPES: &str = include_str!("eager-reader-types.fx");

pub const EAGER_READER: &str = include_str!("eager-reader.fx");

/// The parser written in FX-26, which needs the reader's types: a module
/// file of the reader's regions and its own, loading the reader at them.
pub const PARSER: &str = include_str!("parser.fx");

/// The parser's top-level forms, and a program of them.
pub const PARSER_TOP: &str = include_str!("parser-top.fx");

/// The parser's expressions, and its `load-module`
/// (`docs/research/first-class-modules.md`, M7): the files a program names,
/// as the driver read them. After [`PARSER`], before [`PARSER_TOP`].
pub const PARSER_EXPS: &str = include_str!("parser-exps.fx");

/// The evaluator written in FX-26, which runs the parser's trees: a
/// metacircular evaluator (rewritten 2026-10-08). Its values, a union of the
/// program's own where FX-26 has their shape;
/// its primitives, in a table by symbol; and the evaluator proper, with its
/// entry points.
pub const EVAL_VALUES: &str = include_str!("eval-values.fx");
pub const EVAL_PRIMS: &str = include_str!("eval-prims.fx");
pub const EVAL_CORE: &str = include_str!("eval-core.fx");

/// The evaluator's types and the signatures of its modules: a module file of
/// no state (`TODO.md` §68).
pub const EVAL_TYPES: &str = include_str!("eval-types.fx");

/// The conductor: the front end's modules made and linked (`TODO.md` §68).
/// Last of [`FRONT_END_FILES`].
pub const CONDUCTOR: &str = include_str!("conductor.fx");

/// The compiler from FX-26 to cellular words, written in FX-26.
pub const COMPILER: &str = include_str!("compile.fx");

/// Its other parts, in order: lambda lifting and the standard operations;
/// expressions; the middle phase's plan of a form. Then the register
/// compiler ([`REGCODE`]), and after it [`COMPILER_DRIVER`].
pub const COMPILER_PARTS: [(&str, &str); 0] = [
];

/// The compiler's last parts written as top-level files, after the register
/// compiler, which they call (`docs/research/compiler-middle-phase.md`,
/// step 4): none now. The twin phase, inlining and programs are
/// `load-input` files the conductor applies (`TODO.md` §68).
pub const COMPILER_DRIVER: [(&str, &str); 0] = [
];

/// The register compiler written in FX-26 (PLAN.md 13h′ (e)): register code
/// for each lambda, as its word's twin, when `c-registers` is set.
pub const REGCODE: &str = include_str!("regcode.fx");

/// Register code's other parts, in order: expressions; the helpers of the
/// expressions' compiler proper; modules' helpers; it, one recursive group
/// (modules and a leaf's tail calls in it); and the entry.
pub const REGCODE_PARTS: [(&str, &str); 0] = [
];

/// The standard operations the compiler written in FX-26 runs as runtime
/// primitives, generated from the lowering's table.
pub const STANDARD_OPS: &str = include_str!("standard.fx");

/// The arm64 encoder written in FX-26, the Rust one its oracle: a
/// `load-input` file, its module of no state, which the conductor loads.
pub const ARM64: &str = include_str!("arm64.fx");

/// What the compiler to machine code written in FX-26 knows of the
/// hand-encoded machine, generated from it: a module file, which the
/// conductor loads.
pub const NATIVE_LAYOUT: &str = include_str!("native-layout.fx");

/// Words compiled to machine code, in FX-26: the hand-encoded machine's
/// `assemble_word`, over [`ARM64`]. A `load-input` file, applied by the
/// conductor.
pub const NATIVE: &str = include_str!("native.fx");

/// The checker written in FX-26, over the parser's trees, in files of its
/// parts, in order: types, effects, the environment, printing, unions, reading
/// descriptions, resolving them, errors, modules' descriptions, subtyping,
/// instantiation, termination and what tests say of sizes, the rules,
/// modules' rules, and programs.
pub const CHECKER_FILES: [(&str, &str); 34] = [
    ("check-types.fx", include_str!("check-types.fx")),
    ("check-effects.fx", include_str!("check-effects.fx")),
    ("check-env.fx", include_str!("check-env.fx")),
    ("check-print.fx", include_str!("check-print.fx")),
    ("check-unions.fx", include_str!("check-unions.fx")),
    ("check-holds.fx", include_str!("check-holds.fx")),
    ("check-read.fx", include_str!("check-read.fx")),
    ("check-syntax.fx", include_str!("check-syntax.fx")),
    ("check-subst.fx", include_str!("check-subst.fx")),
    ("check-proving.fx", include_str!("check-proving.fx")),
    ("check-read-descs.fx", include_str!("check-read-descs.fx")),
    ("check-generative.fx", include_str!("check-generative.fx")),
    ("check-resolve.fx", include_str!("check-resolve.fx")),
    ("check-mask.fx", include_str!("check-mask.fx")),
    ("check-kinds.fx", include_str!("check-kinds.fx")),
    ("check-errors.fx", include_str!("check-errors.fx")),
    ("check-modules.fx", include_str!("check-modules.fx")),
    ("check-subtype.fx", include_str!("check-subtype.fx")),
    ("check-expect.fx", include_str!("check-expect.fx")),
    ("check-calls.fx", include_str!("check-calls.fx")),
    ("check-dependent.fx", include_str!("check-dependent.fx")),
    ("check-data.fx", include_str!("check-data.fx")),
    ("check-bounds.fx", include_str!("check-bounds.fx")),
    ("check-infer.fx", include_str!("check-infer.fx")),
    ("check-close.fx", include_str!("check-close.fx")),
    ("check-terminate.fx", include_str!("check-terminate.fx")),
    ("check-test-facts.fx", include_str!("check-test-facts.fx")),
    ("check-letrec.fx", include_str!("check-letrec.fx")),
    ("check-facts.fx", include_str!("check-facts.fx")),
    ("check-synth.fx", include_str!("check-synth.fx")),
    ("check-modorder.fx", include_str!("check-modorder.fx")),
    ("check-module-rules.fx", include_str!("check-module-rules.fx")),
    ("check-rules.fx", include_str!("check-rules.fx")),
    ("check-program.fx", include_str!("check-program.fx")),
];

/// The reader, the parser, the tables, the checker, the evaluator and the
/// compiler written in FX-26, with the layout they share, as one program:
/// each needs the types of the ones before.
pub fn front_end() -> String {
    FRONT_END_FILES.iter().map(|(_, t)| *t).collect::<Vec<_>>().join("\n")
}

/// The reader and the parser made at the front end's regions, and what
/// the rest of the front end uses of them, re-exported. The first of
/// [`FRONT_END_FILES`].
pub const READER: &str = include_str!("reader.fx");

/// The module files built in, each loaded by the one after
/// (`(load-module "fx26:name")`, [`built_in_module`]), the last by
/// [`READER`]: the reader and the parser, of the reader's regions.
pub const FRONT_END_MODULES: [(&str, &str); 59] = [
    ("eager-reader-types.fx", EAGER_READER_TYPES),
    ("table-types.fx", TABLE_TYPES),
    ("compile-programs-types.fx", COMPILE_PROGRAMS_TYPES),
    ("regcode-entry-types.fx", REGCODE_ENTRY_TYPES),
    ("regcode-modules-types.fx", REGCODE_MODULES_TYPES),
    ("regcode-helpers-types.fx", REGCODE_HELPERS_TYPES),
    ("regcode-exps-types.fx", REGCODE_EXPS_TYPES),
    ("regcode-types.fx", REGCODE_TYPES),
    ("compile-plan-types.fx", COMPILE_PLAN_TYPES),
    ("compile-exps-types.fx", COMPILE_EXPS_TYPES),
    ("compile-lift-types.fx", COMPILE_LIFT_TYPES),
    ("compile-types.fx", COMPILE_TYPES),
    ("native-types.fx", NATIVE_TYPES),
    ("arm64-types.fx", ARM64_TYPES),
    ("layout-types.fx", LAYOUT_TYPES),
    ("native-layout-types.fx", NATIVE_LAYOUT_TYPES),
    ("check-resolve-types.fx", CHECK_RESOLVE_TYPES),
    ("check-generative-types.fx", CHECK_GENERATIVE_TYPES),
    ("check-subst-types.fx", CHECK_SUBST_TYPES),
    ("check-syntax-types.fx", CHECK_SYNTAX_TYPES),
    ("check-read-types.fx", CHECK_READ_TYPES),
    ("check-holds-types.fx", CHECK_HOLDS_TYPES),
    ("check-unions-types.fx", CHECK_UNIONS_TYPES),
    ("check-print-types.fx", CHECK_PRINT_TYPES),
    ("check-env-types.fx", CHECK_ENV_TYPES),
    ("check-types-types.fx", CHECK_TYPES_TYPES),
    ("eager-reader.fx", EAGER_READER),
    ("parser-types.fx", PARSER_TYPES),
    ("parser.fx", PARSER),
    ("parser-exps.fx", PARSER_EXPS),
    ("parser-top.fx", PARSER_TOP),
    ("eval-types.fx", EVAL_TYPES),
    ("eval-values.fx", EVAL_VALUES),
    ("eval-prims.fx", EVAL_PRIMS),
    ("eval-core.fx", EVAL_CORE),
    ("native-layout.fx", NATIVE_LAYOUT),
    ("arm64.fx", ARM64),
    ("native.fx", NATIVE),
    ("compile-twins-types.fx", COMPILE_TWINS_TYPES),
    ("compile-inline-types.fx", COMPILE_INLINE_TYPES),
    ("compile-programs.fx", COMPILE_PROGRAMS),
    ("compile-inline.fx", COMPILE_INLINE),
    ("compile-twins.fx", COMPILE_TWINS),
    ("regcode-core-types.fx", REGCODE_CORE_TYPES),
    ("regcode-entry.fx", REGCODE_ENTRY),
    ("regcode-core.fx", REGCODE_CORE),
    ("regcode-modules.fx", REGCODE_MODULES),
    ("regcode-helpers.fx", REGCODE_HELPERS),
    ("regcode-places-types.fx", REGCODE_PLACES_TYPES),
    ("regcode-places.fx", REGCODE_PLACES),
    ("regcode-exps.fx", REGCODE_EXPS),
    ("standard-types.fx", STANDARD_TYPES),
    ("regcode.fx", REGCODE),
    ("check-program-types.fx", CHECK_PROGRAM_TYPES),
    ("compile-plan.fx", COMPILE_PLAN),
    ("compile-state-types.fx", COMPILE_STATE_TYPES),
    ("compile-exps.fx", COMPILE_EXPS),
    ("compile-state.fx", COMPILE_STATE),
    ("compile-lift.fx", COMPILE_LIFT),
];

/// A `load-module` path naming a module file built in, in
/// [`FRONT_END_MODULES`]: this, then its name.
pub const BUILT_IN_PREFIX: &str = "fx26:";

/// The text of the module file built in that `path` names
/// (`fx26:parser.fx`), if it names one.
pub fn built_in_module(path: &str) -> Option<&'static str> {
    let name = path.strip_prefix(BUILT_IN_PREFIX)?;
    FRONT_END_MODULES.iter().find(|(n, _)| *n == name).map(|(_, t)| *t)
}

/// The front end's files, by name, in the order [`front_end`] joins them;
/// [`bootstrap_program`] puts `bootstrap.fx` after them. The module files
/// built in, [`FRONT_END_MODULES`], are loaded by the first.
pub const FRONT_END_FILES: [(&str, &str); 40] = [
    ("reader.fx", READER),
    ("table.fx", TABLE),
    CHECKER_FILES[0],
    CHECKER_FILES[1],
    CHECKER_FILES[2],
    CHECKER_FILES[3],
    CHECKER_FILES[4],
    CHECKER_FILES[5],
    CHECKER_FILES[6],
    CHECKER_FILES[7],
    CHECKER_FILES[8],
    CHECKER_FILES[9],
    CHECKER_FILES[10],
    CHECKER_FILES[11],
    CHECKER_FILES[12],
    CHECKER_FILES[13],
    CHECKER_FILES[14],
    CHECKER_FILES[15],
    CHECKER_FILES[16],
    CHECKER_FILES[17],
    CHECKER_FILES[18],
    CHECKER_FILES[19],
    CHECKER_FILES[20],
    CHECKER_FILES[21],
    CHECKER_FILES[22],
    CHECKER_FILES[23],
    CHECKER_FILES[24],
    CHECKER_FILES[25],
    CHECKER_FILES[26],
    CHECKER_FILES[27],
    CHECKER_FILES[28],
    CHECKER_FILES[29],
    CHECKER_FILES[30],
    CHECKER_FILES[31],
    CHECKER_FILES[32],
    CHECKER_FILES[33],
    ("layout.fx", LAYOUT),
    ("standard.fx", STANDARD_OPS),
    ("compile.fx", COMPILER),
    ("conductor.fx", CONDUCTOR),
];

/// Where byte `at` of [`front_end`] (or of [`bootstrap_program`]) is, as
/// `file.fx:line:col`: for an error in the front end itself, which is
/// read as one text.
pub fn front_end_location(at: usize) -> String {
    let mut start = 0;
    for (name, text) in FRONT_END_FILES.iter().copied().chain([("bootstrap.fx", BOOTSTRAP)]) {
        if at <= start + text.len() {
            let before = &text[..at - start];
            let line = before.matches('\n').count() + 1;
            let col = before.rsplit('\n').next().map_or(0, |l| l.chars().count()) + 1;
            return format!("{name}:{line}:{col}");
        }
        start += text.len() + 1;
    }
    format!("byte {at}, past the front end")
}

/// The file an error in the front end itself is in: no file of the
/// user's, so that a driver shows its message, which says where in the
/// front end (`front_end_location`), and not a place in the program it was
/// given (`TODO.md` §67).
pub const FRONT_END_FILE: fixpt_read::FileId = fixpt_read::FileId(u32::MAX);

/// `e`, found checking the front end, its span in [`front_end`]'s text: in
/// [`FRONT_END_FILE`], its message placed in the front end's own files.
pub fn front_end_error(e: FxError) -> FxError {
    let at = front_end_location(e.span.start as usize);
    front_end_failure(format!("the front end, {at}: {}", e.message))
}

/// A failure of the front end's with no place in it (loading it, its
/// licence), in [`FRONT_END_FILE`].
pub fn front_end_failure(message: String) -> FxError {
    FxError::at(fixpt_read::Span::new(FRONT_END_FILE, 0, 0), message)
}

/// A driver for the front end, in FX-26: a text read, parsed, checked and
/// compiled by the front end. See [`bootstrap_program`].
pub const BOOTSTRAP: &str = include_str!("bootstrap.fx");

/// Where the front end's files are in the source tree this was built from.
pub const SOURCE_DIR: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/src");

/// The front end with its driver after it, as the last expression: compiled
/// to a word and run, it gives the driver.
pub fn bootstrap_program() -> String {
    format!("{}\n{BOOTSTRAP}", front_end())
}

/// The object layout, generated from `fixpt_heap::layout`: tags, header
/// fields and kinds, as FX-26 definitions.
pub const LAYOUT: &str = include_str!("layout.fx");

/// Hash tables, written in FX-26: prepend to a program that uses them.
pub const TABLE: &str = include_str!("table.fx");

pub mod check;
pub mod compare;
pub mod infer;
mod kinds;
pub mod licence;
pub mod lemma;
pub mod lower;
mod sizes;
mod modules;
mod modorder;
pub mod parse;
pub mod session;
pub mod sexp;
pub mod syn;
mod terminate;
pub mod cellular;
pub mod standard;
pub mod top;
pub mod unparse;

pub use check::{Checker, Checked};
pub use top::Top;
pub use error::{FxError, R};

pub mod error {
    use fixpt_read::Span;

    #[derive(Clone, Debug)]
    pub struct FxError {
        pub span: Span,
        pub message: String,
    }

    impl FxError {
        pub fn at(span: Span, message: impl Into<String>) -> FxError {
            FxError { span, message: message.into() }
        }
    }

    impl std::fmt::Display for FxError {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str(&self.message)
        }
    }

    pub type R<T> = Result<T, FxError>;
}
