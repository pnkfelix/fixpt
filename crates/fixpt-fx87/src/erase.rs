//! Erasure — `erase-type`.
//!
//! Once a form has been checked, its types have done their work and are thrown
//! away: what runs is ordinary Scheme. `type-and-eval` is explicit about it —
//! `(fx-eval (erase-type node))` — and it is the same architecture FX-91 uses
//! and the reason both languages inherit this project's engines, heap images
//! and single-binary builds without any of that being written twice.
//!
//! Output is Scheme *text*, re-read by the Scheme session. The round trip is
//! deliberate, for the reason it is in FX-91: the FX-87 checker and the Scheme
//! session intern symbols separately, so handing syntax across directly would
//! quietly mix two symbol spaces. It also makes the generated code
//! inspectable, which is most of debugging a code generator.
//!
//! # What the types were hiding
//!
//! Erasure is where FX-87's data representations become visible, and they are
//! plainer than the types suggest:
//!
//! * a `oneof` is `(cons 'tag value)` — a tagged pair;
//! * a `recordof` is an association list, `(list (list 'field value) …)`;
//! * a `ref` is a box;
//! * `tagcase` is a `case` on the tag with the payload rebound.
//!
//! The type system is what makes those safe; nothing at run time checks them.

use crate::ast::{Arena, DoBinding, Exp, ExpId, TagClause};
use fixpt_read::{Interner, Sym};
use std::collections::HashSet;

pub struct Eraser<'a> {
    arena: &'a Arena,
    interner: &'a Interner,
    gensym: usize,
    /// Names bound by the standard environment, which live in the immutable
    /// region and therefore cannot be reassigned.
    standard: &'a HashSet<Sym>,
    /// Which expressions the checker proved to have no observable effect, and
    /// the effect it derived for each. `None` when erasing without a checker.
    purity: Option<&'a dyn Purity>,
    /// Names the program has rebound around the expression being erased.
    /// A standard name shadowed here is an ordinary variable.
    shadowed: Vec<Sym>,
}

/// The unit value. `#u` is not Scheme syntax, so the runtime binds a name.
pub const UNIT: &str = "%fx-unit";

/// What the checker proved about each expression, as the eraser needs it.
///
/// A trait rather than a concrete table so that `erase` stays usable without a
/// checker at all — the metadata is an enrichment, never a requirement.
pub trait Purity {
    fn is_pure(&self, exp: ExpId) -> bool;
    fn effect_text(&self, exp: ExpId) -> Option<String>;
}

pub fn erase(arena: &Arena, interner: &Interner, exp: ExpId) -> String {
    erase_with(arena, interner, exp, &HashSet::new(), None)
}

/// Erase, annotating what the checker proved.
///
/// `standard` names the bindings that came from the initial environment.
/// Because those live in the immutable region — and `(set! + -)` is therefore a
/// *type error*, not a program — an application of one can be compiled without
/// the indirection through a global. The claim rides along in the emitted
/// Scheme as an inert quoted constant, exactly as Twobit carries `R F G decls`
/// in a lambda's body, so the output remains a program any Scheme can run.
pub fn erase_with<'a>(
    arena: &'a Arena,
    interner: &'a Interner,
    exp: ExpId,
    standard: &'a HashSet<Sym>,
    purity: Option<&'a dyn Purity>,
) -> String {
    let mut e = Eraser {
        arena,
        interner,
        gensym: 0,
        standard,
        purity,
        shadowed: Vec::new(),
    };
    e.go(exp)
}

impl Eraser<'_> {
    fn name(&self, s: Sym) -> String {
        fixpt_read::escape_symbol(self.interner.name(s))
    }

    fn fresh(&mut self, tag: &str) -> String {
        self.gensym += 1;
        format!("%fx-{tag}-{}", self.gensym)
    }

    /// Is `name` still the standard binding here?
    fn is_standard(&self, name: Sym) -> bool {
        self.standard.contains(&name) && !self.shadowed.contains(&name)
    }

    /// Wrap `code` in the annotation the claim deserves.
    ///
    /// `(begin '(%fx-note …) code)` — an ordinary two-expression `begin`, so
    /// the annotation is evaluated for effect and discarded. A Scheme that has
    /// never heard of `%fx-note` runs this correctly and merely compiles it
    /// less well, which is what makes the encoding safe to adopt.
    fn note(&self, claims: &str, because: &str, code: String) -> String {
        format!("(begin '(%fx-note {claims} (basis checked) (because {because:?})) {code})")
    }

    fn seq(&mut self, ids: &[ExpId]) -> String {
        ids.iter().map(|i| self.go(*i)).collect::<Vec<_>>().join(" ")
    }

    fn go(&mut self, exp: ExpId) -> String {
        match self.arena.exp_at(exp).clone() {
            Exp::Int(n) => n.to_string(),
            Exp::Float(bits) => {
                let f = f64::from_bits(bits);
                // `1.0` type-checks as an `int`, but it is still the float the
                // reader produced, and erasure keeps the literal it was given.
                if f.fract() == 0.0 && f.is_finite() {
                    format!("{f:.1}")
                } else {
                    f.to_string()
                }
            }
            Exp::Char(c) => fixpt_read::write_syntax(
                &fixpt_read::Syntax {
                    span: self.arena.span(exp),
                    datum: fixpt_read::Datum::Char(c),
                },
                self.interner,
            ),
            Exp::Str(t) => format!("{t:?}"),
            Exp::Bool(b) => (if b { "#t" } else { "#f" }).to_string(),
            Exp::Unit => UNIT.to_string(),
            Exp::Symbol(s) => format!("'{}", self.name(s)),
            Exp::Quote(syntax) => {
                format!("'{}", fixpt_read::write_syntax(&syntax, self.interner))
            }
            Exp::Var(v) => self.name(v),
            // Annotations vanish, which is the whole point.
            Exp::The { body, .. } | Exp::PLambda { body, .. } | Exp::Proj { body, .. } => {
                self.go(body)
            }
            Exp::If { test, then, els } => {
                format!("(if {} {} {})", self.go(test), self.go(then), self.go(els))
            }
            Exp::Begin(items) => format!("(begin {})", self.seq(&items)),
            Exp::Lambda { params, body } => {
                let names: Vec<String> = params.iter().map(|p| self.name(p.name)).collect();
                let depth = self.shadowed.len();
                self.shadowed.extend(params.iter().map(|p| p.name));
                let b = self.go(body);
                self.shadowed.truncate(depth);
                format!("(lambda ({}) {})", names.join(" "), b)
            }
            Exp::VLambda { name, body, .. } => {
                // One rest parameter: the arguments arrive as a list, which is
                // exactly what the `vsubr` type said.
                let depth = self.shadowed.len();
                self.shadowed.push(name);
                let b = self.go(body);
                self.shadowed.truncate(depth);
                format!("(lambda {} {b})", self.name(name))
            }
            Exp::Let { bindings, body } => {
                let bs = self.bindings(&bindings);
                let depth = self.shadowed.len();
                self.shadowed.extend(bindings.iter().map(|b| b.name));
                let b = self.go(body);
                self.shadowed.truncate(depth);
                format!("(let ({bs}) {b})")
            }
            Exp::Letrec { bindings, body } => {
                let depth = self.shadowed.len();
                self.shadowed.extend(bindings.iter().map(|b| b.name));
                let bs = self.bindings(&bindings);
                let b = self.go(body);
                self.shadowed.truncate(depth);
                format!("(letrec ({bs}) {b})")
            }
            Exp::App { fun, args } => {
                let integrable = match self.arena.exp_at(fun) {
                    Exp::Var(v) if self.is_standard(*v) => Some(*v),
                    _ => None,
                };
                let f = self.go(fun);
                let call = if args.is_empty() {
                    format!("({f})")
                } else {
                    format!("({f} {})", self.seq(&args))
                };
                // Two independent claims, and either may be absent. The
                // effect is the checker's own derivation, carried verbatim as
                // the justification.
                let mut claims = String::new();
                if let Some(v) = integrable {
                    claims.push_str(&format!("(integrable {}) ", self.name(v)));
                }
                let pure = self.purity.is_some_and(|p| p.is_pure(exp));
                if pure {
                    claims.push_str("(pure) ");
                }
                if claims.is_empty() {
                    return call;
                }
                let because = match (integrable, self.purity.and_then(|p| p.effect_text(exp))) {
                    (Some(_), Some(e)) => format!(
                        "standard binding in @=, the immutable region; effect {e}"
                    ),
                    (Some(_), None) => {
                        "standard binding in @=, the immutable region, so `set!` on it \
                         is a type error".to_string()
                    }
                    (None, Some(e)) => format!("effect {e}"),
                    (None, None) => String::new(),
                };
                self.note(claims.trim_end(), &because, call)
            }
            // `set!` yields unit in FX-87, where Scheme's is unspecified.
            Exp::SetBang { name, value } => {
                format!("(begin (set! {} {}) {UNIT})", self.name(name), self.go(value))
            }

            // ------------------------------------------------ data forms
            Exp::Record { fields, .. } => {
                let parts: Vec<String> = fields
                    .iter()
                    .map(|(n, v)| format!("(list '{} {})", self.name(*n), self.go(*v)))
                    .collect();
                format!("(list {})", parts.join(" "))
            }
            Exp::Select { rec, field } => {
                format!("(cadr (assv '{} {}))", self.name(field), self.go(rec))
            }
            Exp::RecordSet { rec, field, value } => format!(
                "(begin (set-cdr! (assv '{} {}) (list {})) {UNIT})",
                self.name(field),
                self.go(rec),
                self.go(value)
            ),
            Exp::One { tag, value, .. } => {
                format!("(cons '{} {})", self.name(tag), self.go(value))
            }
            Exp::OneSet { target, tag, value } => {
                let g = self.fresh("one-set");
                format!(
                    "(begin (let (({g} {})) (set-car! {g} '{}) (set-cdr! {g} {})) {UNIT})",
                    self.go(target),
                    self.name(tag),
                    self.go(value)
                )
            }
            Exp::TagCase { var, scrutinee, clauses, .. } => {
                self.tagcase(var, scrutinee, &clauses)
            }
            Exp::Delay(body) => format!("(delay {})", self.go(body)),
            Exp::Do { bindings, test, result, body } => {
                self.do_loop(&bindings, test, result, body)
            }
        }
    }

    fn bindings(&mut self, bindings: &[crate::ast::Binding]) -> String {
        bindings
            .iter()
            .map(|b| format!("({} {})", self.name(b.name), self.go(b.value)))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// `(let ((g e)) (case (car g) ((tag) (let ((v (cdr g))) body)) …))`
    ///
    /// The `else` arm binds the *whole* tagged pair rather than its payload,
    /// because its type is the remaining `oneof` rather than one variant's.
    fn tagcase(&mut self, var: Sym, scrutinee: ExpId, clauses: &[TagClause]) -> String {
        let g = self.fresh("tagcase");
        let v = self.name(var);
        let arms: Vec<String> = clauses
            .iter()
            .map(|c| match c.tag {
                Some(tag) => format!(
                    "(({}) (let (({v} (cdr {g}))) {}))",
                    self.name(tag),
                    self.go(c.body)
                ),
                None => format!("(else (let (({v} {g})) {}))", self.go(c.body)),
            })
            .collect();
        format!("(let (({g} {})) (case (car {g}) {}))", self.go(scrutinee), arms.join(" "))
    }

    fn do_loop(
        &mut self,
        bindings: &[DoBinding],
        test: ExpId,
        result: ExpId,
        body: Option<ExpId>,
    ) -> String {
        let bs: Vec<String> = bindings
            .iter()
            .map(|b| {
                // A variable with no step keeps its value, which Scheme's `do`
                // spells by stepping it to itself.
                let step = match b.step {
                    Some(s) => self.go(s),
                    None => self.name(b.name),
                };
                format!("({} {} {})", self.name(b.name), self.go(b.init), step)
            })
            .collect();
        let tail = match body {
            Some(b) => format!(" {}", self.go(b)),
            None => String::new(),
        };
        format!(
            "(do ({}) ({} {}){tail})",
            bs.join(" "),
            self.go(test),
            self.go(result)
        )
    }
}
