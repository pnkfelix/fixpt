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

pub mod typed_cells;
pub mod logic;
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

/// The types of `convention.fx`: a module file of no state (`TODO.md` §97).
pub const CONVENTION_TYPES: &str = include_str!("convention-types.fx");

/// The types of `x86_64.fx`: a module file of no state (`TODO.md` §68).
pub const X86_64_TYPES: &str = include_str!("x86_64-types.fx");

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

/// The types of `check-modules.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_MODULES_TYPES: &str = include_str!("check-modules-types.fx");

/// The types of `check-subtype.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_SUBTYPE_TYPES: &str = include_str!("check-subtype-types.fx");

/// The types of `check-calls.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_CALLS_TYPES: &str = include_str!("check-calls-types.fx");

/// The types of `check-dependent.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_DEPENDENT_TYPES: &str = include_str!("check-dependent-types.fx");

/// The types of `check-bounds.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_BOUNDS_TYPES: &str = include_str!("check-bounds-types.fx");

/// The types of `check-infer.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_INFER_TYPES: &str = include_str!("check-infer-types.fx");

/// The types of `check-terminate.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_TERMINATE_TYPES: &str = include_str!("check-terminate-types.fx");

/// The types of `check-test-facts.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_TEST_FACTS_TYPES: &str = include_str!("check-test-facts-types.fx");

/// The types of `check-letrec.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_LETREC_TYPES: &str = include_str!("check-letrec-types.fx");

/// The types of `check-synth.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_SYNTH_TYPES: &str = include_str!("check-synth-types.fx");

/// The types of `check-modorder.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_MODORDER_TYPES: &str = include_str!("check-modorder-types.fx");

/// The types of `check-module-rules.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_MODULE_RULES_TYPES: &str = include_str!("check-module-rules-types.fx");
/// The types of `check-processes.fx`: a module file of no state (`TODO.md` §68).
pub const CHECK_PROCESSES_TYPES: &str = include_str!("check-processes-types.fx");

/// `check-proofs-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_PROOFS_TYPES: &str = include_str!("check-proofs-types.fx");

/// `check-program.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_PROGRAM: &str = include_str!("check-program.fx");

/// `check-effects-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_EFFECTS_TYPES: &str = include_str!("check-effects-types.fx");

/// `check-errors-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_ERRORS_TYPES: &str = include_str!("check-errors-types.fx");

/// `check-expect-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_EXPECT_TYPES: &str = include_str!("check-expect-types.fx");

/// `check-read-descs-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_READ_DESCS_TYPES: &str = include_str!("check-read-descs-types.fx");

/// `check-rules-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_RULES_TYPES: &str = include_str!("check-rules-types.fx");

/// `reader-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const READER_TYPES: &str = include_str!("reader-types.fx");

/// `check-proofs.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_PROOFS: &str = include_str!("check-proofs.fx");

/// `check-rules.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_RULES: &str = include_str!("check-rules.fx");

/// `check-close-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_CLOSE_TYPES: &str = include_str!("check-close-types.fx");

/// `check-data-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_DATA_TYPES: &str = include_str!("check-data-types.fx");

/// `check-mask-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_MASK_TYPES: &str = include_str!("check-mask-types.fx");

/// `check-proving-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_PROVING_TYPES: &str = include_str!("check-proving-types.fx");

/// `check-logic-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_LOGIC_TYPES: &str = include_str!("check-logic-types.fx");

/// `check-specs-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_SPECS_TYPES: &str = include_str!("check-specs-types.fx");
/// `check-read-made-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_READ_MADE_TYPES: &str = include_str!("check-read-made-types.fx");

/// `check-module-rules.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_MODULE_RULES: &str = include_str!("check-module-rules.fx");
/// The checker's rules for processes and `par`: a `load-input` file, which
/// the conductor applies (`TODO.md` §68).
pub const CHECK_PROCESSES: &str = include_str!("check-processes.fx");

/// `check-modorder.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_MODORDER: &str = include_str!("check-modorder.fx");

/// `check-synth.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_SYNTH: &str = include_str!("check-synth.fx");

/// `check-blobrefs-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_BLOBREFS_TYPES: &str = include_str!("check-blobrefs-types.fx");

/// `check-blobrefs.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_BLOBREFS: &str = include_str!("check-blobrefs.fx");

/// `check-facts-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_FACTS_TYPES: &str = include_str!("check-facts-types.fx");

/// `check-facts.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_FACTS: &str = include_str!("check-facts.fx");

/// `check-letrec.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_LETREC: &str = include_str!("check-letrec.fx");

/// `check-test-facts.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_TEST_FACTS: &str = include_str!("check-test-facts.fx");

/// `check-sc-graphs-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_SC_GRAPHS_TYPES: &str = include_str!("check-sc-graphs-types.fx");

/// `check-terminate.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_TERMINATE: &str = include_str!("check-terminate.fx");

/// `check-sc-graphs.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_SC_GRAPHS: &str = include_str!("check-sc-graphs.fx");

/// `check-close.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_CLOSE: &str = include_str!("check-close.fx");

/// `check-binders-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_BINDERS_TYPES: &str = include_str!("check-binders-types.fx");

/// `check-infer.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_INFER: &str = include_str!("check-infer.fx");

/// `check-kinds-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_KINDS_TYPES: &str = include_str!("check-kinds-types.fx");

/// `check-binders.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_BINDERS: &str = include_str!("check-binders.fx");

/// `check-bounds.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_BOUNDS: &str = include_str!("check-bounds.fx");

/// `check-data.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_DATA: &str = include_str!("check-data.fx");

/// `check-dependent.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_DEPENDENT: &str = include_str!("check-dependent.fx");

/// `check-calls.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_CALLS: &str = include_str!("check-calls.fx");

/// `check-expect.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_EXPECT: &str = include_str!("check-expect.fx");

/// `check-sub-env-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_SUB_ENV_TYPES: &str = include_str!("check-sub-env-types.fx");

/// `check-subtype.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_SUBTYPE: &str = include_str!("check-subtype.fx");

/// `check-sub-env.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_SUB_ENV: &str = include_str!("check-sub-env.fx");

/// `check-modules-read-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_MODULES_READ_TYPES: &str = include_str!("check-modules-read-types.fx");

/// `check-modules.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_MODULES: &str = include_str!("check-modules.fx");

/// `check-modules-read.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_MODULES_READ: &str = include_str!("check-modules-read.fx");

/// `check-errors.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_ERRORS: &str = include_str!("check-errors.fx");

/// `check-kinds.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_KINDS: &str = include_str!("check-kinds.fx");

/// `check-mask.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_MASK: &str = include_str!("check-mask.fx");

/// `check-resolve.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_RESOLVE: &str = include_str!("check-resolve.fx");

/// `check-generative.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_GENERATIVE: &str = include_str!("check-generative.fx");

/// `check-read-helpers-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_READ_HELPERS_TYPES: &str = include_str!("check-read-helpers-types.fx");

/// `check-read-descs.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_READ_DESCS: &str = include_str!("check-read-descs.fx");

/// `check-read-helpers.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_READ_HELPERS: &str = include_str!("check-read-helpers.fx");

/// `check-proving.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_PROVING: &str = include_str!("check-proving.fx");

/// `check-logic.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_LOGIC: &str = include_str!("check-logic.fx");

/// `check-specs.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_SPECS: &str = include_str!("check-specs.fx");
/// `check-read-made.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_READ_MADE: &str = include_str!("check-read-made.fx");

/// `check-subst.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_SUBST: &str = include_str!("check-subst.fx");

/// `check-syntax.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_SYNTAX: &str = include_str!("check-syntax.fx");

/// `check-read.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_READ: &str = include_str!("check-read.fx");

/// `check-holds.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_HOLDS: &str = include_str!("check-holds.fx");

/// `check-unions.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_UNIONS: &str = include_str!("check-unions.fx");

/// `check-print-parts-types.fx`: types and signatures, a module file of no state (`TODO.md` §68).
pub const CHECK_PRINT_PARTS_TYPES: &str = include_str!("check-print-parts-types.fx");

/// `check-print.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_PRINT: &str = include_str!("check-print.fx");

/// `check-print-parts.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_PRINT_PARTS: &str = include_str!("check-print-parts.fx");

/// `check-env.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_ENV: &str = include_str!("check-env.fx");

/// `check-effects.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_EFFECTS: &str = include_str!("check-effects.fx");

/// `check-types.fx`: a `load-input` file, which the conductor applies (`TODO.md` §68).
pub const CHECK_TYPES: &str = include_str!("check-types.fx");

/// Hash tables' types: a module file of no state (`TODO.md` §68).
pub const TABLE_TYPES: &str = include_str!("table-types.fx");

/// The eager reader's types, of its regions: a module file of no state,
/// which the reader and any of its clients load (`TODO.md` §68).
pub const EAGER_READER_TYPES: &str = include_str!("eager-reader-types.fx");

/// The eager reader's states, which hold its continuations: a module file
/// of no state, which only the reader loads, so that the types its clients
/// load mention no continuation.
pub const EAGER_READER_STATES: &str = include_str!("eager-reader-states.fx");

/// `syn->datum`, apart from the reader: a module file of no state, which the
/// reader and the parser load, so that the parser loads no reader.
pub const SYN: &str = include_str!("syn.fx");

pub const EAGER_READER: &str = include_str!("eager-reader.fx");

/// The parser written in FX-26, which needs the reader's types: a module
/// file of the reader's regions and its own, loading the reader at them.
pub const PARSER: &str = include_str!("parser.fx");
/// The forms of processes and `par`, as syntax for the parser to parse.
pub const PARSER_FORMS: &str = include_str!("parser-forms.fx");

/// The parser's top-level forms, and a program of them.
pub const PARSER_TOP: &str = include_str!("parser-top.fx");

/// Each expression's identity, numbered after the parse (`ids.rs` the
/// Rust front end's alike). After [`PARSER_EXPS`], before [`PARSER_TOP`].
pub const PARSER_IDS: &str = include_str!("parser-ids.fx");

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

/// A native convention's declaration read as data a generator reads
/// (`TODO.md` §97): a `load-input` file, its module of no state.
pub const CONVENTION: &str = include_str!("convention.fx");

/// The types of `native-x64.fx`, and the signature of what it is given of
/// the x86_64 machine: a module file of no state (`TODO.md` §68).
pub const NATIVE_X64_TYPES: &str = include_str!("native-x64-types.fx");

/// Words compiled to x86_64 machine code, in FX-26: the x86_64 machine's
/// `assemble_word`, over [`X86_64`], as [`NATIVE`] is for arm64.
pub const NATIVE_X64: &str = include_str!("native-x64.fx");

/// The x86_64 encoder written in FX-26, the Rust one its oracle, as
/// [`ARM64`] is for arm64.
pub const X86_64: &str = include_str!("x86_64.fx");

/// What the compiler to x86_64 written in FX-26 knows of the x86_64
/// machine, generated from it, as [`NATIVE_LAYOUT`] is for arm64.
pub const NATIVE_X64_LAYOUT: &str = include_str!("native-x64-layout.fx");

/// Register code compiled to x86_64 machine code, in FX-26: the x86_64
/// machine's `assemble_register_word`, over [`NATIVE_X64`]'s assembler.
pub const NATIVE_X64_REGS: &str = include_str!("native-x64-regs.fx");

/// Its fast paths and what it does inline, and the helpers they share.
pub const NATIVE_X64_REGS_OPS: &str = include_str!("native-x64-regs-ops.fx");

/// What [`NATIVE_X64_REGS`] knows of the x86_64 machine's register code
/// beyond [`NATIVE_X64_LAYOUT`], generated from it.
pub const NATIVE_X64_REGS_LAYOUT: &str = include_str!("native-x64-regs-layout.fx");

/// The native convention's procedures compiled to x86_64, in FX-26:
/// `fixpt-native/src/direct/x64.rs`'s `procedure_x64`, in the files below,
/// as [`NATIVE_X64_REGS`] is for register code. Their types, and the
/// signatures of their modules as each other use them.
pub const NATIVE_DIRECT_X64_TYPES: &str = include_str!("native-direct-x64-types.fx");

/// What they know of the native convention on x86_64, generated from it,
/// and its signature, generated beside it.
pub const NATIVE_DIRECT_X64_LAYOUT: &str = include_str!("native-direct-x64-layout.fx");
pub const NATIVE_DIRECT_X64_LAYOUT_TYPES: &str = include_str!("native-direct-x64-layout-types.fx");

/// Their assembler, and the machine sequences they share.
pub const NATIVE_DIRECT_X64_ASM: &str = include_str!("native-direct-x64-asm.fx");

/// Where native code keeps raw values (`fixpt-native/src/direct/reps.rs`),
/// in FX-26: the analysis, of no machine's.
pub const NATIVE_REPS: &str = include_str!("native-reps.fx");

/// Its webs: a frame slot's writes and reads, joined where a write reaches
/// a read, by basic block.
pub const NATIVE_REPS_WEBS: &str = include_str!("native-reps-webs.fx");

/// Raw values, and the operations on them native code does in line.
pub const NATIVE_DIRECT_X64_RAW: &str = include_str!("native-direct-x64-raw.fx");

/// Flat arrays, suffix refs, bytevectors and shapes, in line.
pub const NATIVE_DIRECT_X64_FLAT: &str = include_str!("native-direct-x64-flat.fx");

/// The procedure being compiled: what Rust gave of it, its analysis, its
/// fields and the version being made.
pub const NATIVE_DIRECT_X64_PROC: &str = include_str!("native-direct-x64-proc.fx");

/// Its instructions: moves, frames, globals, `int` operations, calls and
/// branches; and primitives, control and call-outs.
pub const NATIVE_DIRECT_X64_OPS: &str = include_str!("native-direct-x64-ops.fx");
pub const NATIVE_DIRECT_X64_PRIMS: &str = include_str!("native-direct-x64-prims.fx");

/// The loop over the instructions, what is placed after them, and the
/// entry Rust calls.
pub const NATIVE_DIRECT_X64: &str = include_str!("native-direct-x64.fx");

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
pub const CHECKER_FILES: [(&str, &str); 0] = [
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
pub const FRONT_END_MODULES: [(&str, &str); 171] = [
    ("eager-reader-types.fx", EAGER_READER_TYPES),
    ("eager-reader-states.fx", EAGER_READER_STATES),
    ("syn.fx", SYN),
    ("table-types.fx", TABLE_TYPES),
    ("table.fx", TABLE),
    ("check-module-rules-types.fx", CHECK_MODULE_RULES_TYPES),
    ("check-processes-types.fx", CHECK_PROCESSES_TYPES),
    ("check-modorder-types.fx", CHECK_MODORDER_TYPES),
    ("check-synth-types.fx", CHECK_SYNTH_TYPES),
    ("check-letrec-types.fx", CHECK_LETREC_TYPES),
    ("check-test-facts-types.fx", CHECK_TEST_FACTS_TYPES),
    ("check-terminate-types.fx", CHECK_TERMINATE_TYPES),
    ("check-infer-types.fx", CHECK_INFER_TYPES),
    ("check-bounds-types.fx", CHECK_BOUNDS_TYPES),
    ("check-dependent-types.fx", CHECK_DEPENDENT_TYPES),
    ("check-calls-types.fx", CHECK_CALLS_TYPES),
    ("check-subtype-types.fx", CHECK_SUBTYPE_TYPES),
    ("check-modules-types.fx", CHECK_MODULES_TYPES),
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
    ("convention-types.fx", CONVENTION_TYPES),
    ("x86_64-types.fx", X86_64_TYPES),
    ("native-x64-types.fx", NATIVE_X64_TYPES),
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
    ("parser-forms.fx", PARSER_FORMS),
    ("parser-exps.fx", PARSER_EXPS),
    ("parser-ids.fx", PARSER_IDS),
    ("parser-top.fx", PARSER_TOP),
    ("eval-types.fx", EVAL_TYPES),
    ("eval-values.fx", EVAL_VALUES),
    ("eval-prims.fx", EVAL_PRIMS),
    ("eval-core.fx", EVAL_CORE),
    ("native-layout.fx", NATIVE_LAYOUT),
    ("arm64.fx", ARM64),
    ("convention.fx", CONVENTION),
    ("x86_64.fx", X86_64),
    ("native-x64-layout.fx", NATIVE_X64_LAYOUT),
    ("native-x64.fx", NATIVE_X64),
    ("native-x64-regs-layout.fx", NATIVE_X64_REGS_LAYOUT),
    ("native-direct-x64-types.fx", NATIVE_DIRECT_X64_TYPES),
    ("native-direct-x64-layout.fx", NATIVE_DIRECT_X64_LAYOUT),
    ("native-direct-x64-layout-types.fx", NATIVE_DIRECT_X64_LAYOUT_TYPES),
    ("native-direct-x64-asm.fx", NATIVE_DIRECT_X64_ASM),
    ("native-reps-webs.fx", NATIVE_REPS_WEBS),
    ("native-reps.fx", NATIVE_REPS),
    ("native-direct-x64-raw.fx", NATIVE_DIRECT_X64_RAW),
    ("native-direct-x64-flat.fx", NATIVE_DIRECT_X64_FLAT),
    ("native-direct-x64-proc.fx", NATIVE_DIRECT_X64_PROC),
    ("native-direct-x64-ops.fx", NATIVE_DIRECT_X64_OPS),
    ("native-direct-x64-prims.fx", NATIVE_DIRECT_X64_PRIMS),
    ("native-direct-x64.fx", NATIVE_DIRECT_X64),
    ("native-x64-regs-ops.fx", NATIVE_X64_REGS_OPS),
    ("native-x64-regs.fx", NATIVE_X64_REGS),
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
    ("compile.fx", COMPILER),
    ("standard.fx", STANDARD_OPS),
    ("layout.fx", LAYOUT),
    ("check-proofs-types.fx", CHECK_PROOFS_TYPES),
    ("reader-types.fx", READER_TYPES),
    ("check-rules-types.fx", CHECK_RULES_TYPES),
    ("check-read-descs-types.fx", CHECK_READ_DESCS_TYPES),
    ("check-expect-types.fx", CHECK_EXPECT_TYPES),
    ("check-errors-types.fx", CHECK_ERRORS_TYPES),
    ("check-effects-types.fx", CHECK_EFFECTS_TYPES),
    ("check-program.fx", CHECK_PROGRAM),
    ("check-proofs.fx", CHECK_PROOFS),
    ("check-proving-types.fx", CHECK_PROVING_TYPES),
    ("check-logic-types.fx", CHECK_LOGIC_TYPES),
    ("check-specs-types.fx", CHECK_SPECS_TYPES),
    ("check-read-made-types.fx", CHECK_READ_MADE_TYPES),
    ("check-mask-types.fx", CHECK_MASK_TYPES),
    ("check-data-types.fx", CHECK_DATA_TYPES),
    ("check-close-types.fx", CHECK_CLOSE_TYPES),
    ("check-rules.fx", CHECK_RULES),
    ("check-module-rules.fx", CHECK_MODULE_RULES),
    ("check-processes.fx", CHECK_PROCESSES),
    ("check-modorder.fx", CHECK_MODORDER),
    ("check-facts-types.fx", CHECK_FACTS_TYPES),
    ("check-blobrefs-types.fx", CHECK_BLOBREFS_TYPES),
    ("check-synth.fx", CHECK_SYNTH),
    ("check-facts.fx", CHECK_FACTS),
    ("check-blobrefs.fx", CHECK_BLOBREFS),
    ("check-letrec.fx", CHECK_LETREC),
    ("check-test-facts.fx", CHECK_TEST_FACTS),
    ("check-sc-graphs-types.fx", CHECK_SC_GRAPHS_TYPES),
    ("check-terminate.fx", CHECK_TERMINATE),
    ("check-sc-graphs.fx", CHECK_SC_GRAPHS),
    ("check-close.fx", CHECK_CLOSE),
    ("check-binders-types.fx", CHECK_BINDERS_TYPES),
    ("check-kinds-types.fx", CHECK_KINDS_TYPES),
    ("check-infer.fx", CHECK_INFER),
    ("check-binders.fx", CHECK_BINDERS),
    ("check-bounds.fx", CHECK_BOUNDS),
    ("check-data.fx", CHECK_DATA),
    ("check-dependent.fx", CHECK_DEPENDENT),
    ("check-calls.fx", CHECK_CALLS),
    ("check-expect.fx", CHECK_EXPECT),
    ("check-sub-env-types.fx", CHECK_SUB_ENV_TYPES),
    ("check-subtype.fx", CHECK_SUBTYPE),
    ("check-sub-env.fx", CHECK_SUB_ENV),
    ("check-modules-read-types.fx", CHECK_MODULES_READ_TYPES),
    ("check-modules.fx", CHECK_MODULES),
    ("check-modules-read.fx", CHECK_MODULES_READ),
    ("check-errors.fx", CHECK_ERRORS),
    ("check-kinds.fx", CHECK_KINDS),
    ("check-mask.fx", CHECK_MASK),
    ("check-resolve.fx", CHECK_RESOLVE),
    ("check-generative.fx", CHECK_GENERATIVE),
    ("check-read-helpers-types.fx", CHECK_READ_HELPERS_TYPES),
    ("check-read-descs.fx", CHECK_READ_DESCS),
    ("check-read-helpers.fx", CHECK_READ_HELPERS),
    ("check-proving.fx", CHECK_PROVING),
    ("check-logic.fx", CHECK_LOGIC),
    ("check-specs.fx", CHECK_SPECS),
    ("check-read-made.fx", CHECK_READ_MADE),
    ("check-subst.fx", CHECK_SUBST),
    ("check-syntax.fx", CHECK_SYNTAX),
    ("check-read.fx", CHECK_READ),
    ("check-holds.fx", CHECK_HOLDS),
    ("check-unions.fx", CHECK_UNIONS),
    ("check-print-parts-types.fx", CHECK_PRINT_PARTS_TYPES),
    ("check-print.fx", CHECK_PRINT),
    ("check-print-parts.fx", CHECK_PRINT_PARTS),
    ("check-env.fx", CHECK_ENV),
    ("check-effects.fx", CHECK_EFFECTS),
    ("check-types.fx", CHECK_TYPES),
];

/// A `load-module` path naming a module file built in, in
/// [`FRONT_END_MODULES`]: this, then its name.
pub const BUILT_IN_PREFIX: &str = "fx26:";

/// The text of the module file built in that `path` names
/// (`fx26:parser.fx`), if it names one: the front end's, or a standard
/// library's ([`STANDARD_MODULES`]).
pub fn built_in_module(path: &str) -> Option<&'static str> {
    let name = path.strip_prefix(BUILT_IN_PREFIX)?;
    FRONT_END_MODULES.iter().chain(STANDARD_MODULES.iter()).find(|(n, _)| *n == name).map(|(_, t)| *t)
}

/// Libraries written in FX-26 that a program loads by name, `(load-module
/// "fx26:conditions.fx")`: raising and handling conditions (`TODO.md` §89,
/// `docs/research/conditions.md`).
pub const STANDARD_MODULES: [(&str, &str); 2] =
    [("conditions.fx", include_str!("conditions.fx")), ("processes.fx", include_str!("processes.fx"))];

/// The front end's files, by name, in the order [`front_end`] joins them;
/// [`bootstrap_program`] puts `bootstrap.fx` after them. The module files
/// built in, [`FRONT_END_MODULES`], are loaded by the first.
pub const FRONT_END_FILES: [(&str, &str); 2] = [
    ("reader.fx", READER),
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
mod convention;
pub(crate) mod syscall;
pub mod ids;
pub mod infer;
mod kinds;
pub mod licence;
pub mod lemma;
pub mod lower;
mod sizes;
mod specs;
mod modules;
mod modorder;
mod processes;
pub mod parse;
pub mod session;
pub mod spec_tests;
pub mod sexp;
pub mod syn;
mod terminate;
pub mod cellular;
pub mod debts;
pub mod fasl;
pub mod typeat;
pub mod query;
pub mod standard;
pub mod top;
pub mod unparse;
pub mod verifying;
pub mod smt;
pub mod smt_theory;
pub mod sources;

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
