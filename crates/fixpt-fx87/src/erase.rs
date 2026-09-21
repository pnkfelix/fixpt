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

pub struct Eraser<'a> {
    arena: &'a Arena,
    interner: &'a Interner,
    gensym: usize,
}

/// The unit value. `#u` is not Scheme syntax, so the runtime binds a name.
pub const UNIT: &str = "%fx-unit";

pub fn erase(arena: &Arena, interner: &Interner, exp: ExpId) -> String {
    let mut e = Eraser { arena, interner, gensym: 0 };
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
                format!("(lambda ({}) {})", names.join(" "), self.go(body))
            }
            Exp::VLambda { name, body, .. } => {
                // One rest parameter: the arguments arrive as a list, which is
                // exactly what the `vsubr` type said.
                format!("(lambda {} {})", self.name(name), self.go(body))
            }
            Exp::Let { bindings, body } => {
                let bs = self.bindings(&bindings);
                format!("(let ({bs}) {})", self.go(body))
            }
            Exp::Letrec { bindings, body } => {
                let bs = self.bindings(&bindings);
                format!("(letrec ({bs}) {})", self.go(body))
            }
            Exp::App { fun, args } => {
                let f = self.go(fun);
                if args.is_empty() {
                    format!("({f})")
                } else {
                    format!("({f} {})", self.seq(&args))
                }
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
