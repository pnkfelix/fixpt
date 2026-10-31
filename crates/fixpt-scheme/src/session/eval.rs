//! `eval`: data a running program made, expanded, compiled and run.
//!
//! The prelude's `eval` asks the session, `(%host 'eval datum)`, which
//! *pauses* the machine (the `%host` of procedural macros, `procmacro.rs`):
//! no primitive runs the expander, and the engine is never entered twice.
//! The session takes the datum as syntax, expands it as a top-level form of
//! its own and compiles it, and answers with the procedure that runs it,
//! or with a string saying why it could not; the prelude calls the one and
//! raises the other. Each place the session runs the engine answers so
//! ([`Session::answered`]).
//!
//! The expander has no engine of its own while the machine is paused, so a
//! procedural macro cannot run in code given to `eval`; `syntax-rules` can.

use super::Session;
use crate::expand::{Expander, ExpanderParts};
use fixpt_core::ir::{Builder, Program};
use fixpt_heap::{ObjType, Value};
use fixpt_read::{Datum, Span, Syntax};
use fixpt_runtime::Outcome;

impl Session {
    /// `outcome`, a run's, with each `eval` it asked answered, until it is
    /// done or asks something else.
    pub(super) fn answered(&mut self, mut outcome: Outcome<Value>) -> Outcome<Value> {
        loop {
            let datum = match &outcome {
                Err(t) if t.suspended => match self.eval_request(t.obj) {
                    Some(d) => d,
                    None => return outcome,
                },
                _ => return outcome,
            };
            let answer = match self.eval_procedure(datum) {
                Ok(f) => f,
                Err(why) => self.rt.heap.make_string(&why),
            };
            outcome = self.engine.answer_host(&mut self.rt, &mut self.prepared, answer);
        }
    }

    /// The datum of `request`, if it is `(eval datum)`.
    fn eval_request(&self, request: Value) -> Option<Value> {
        let heap = &self.rt.heap;
        let parts = heap.list_to_vec(request)?;
        let [op, datum] = parts[..] else { return None };
        (heap.is_a(op, ObjType::Symbol) && heap.symbol_name(op) == "eval").then_some(datum)
    }

    /// `datum` expanded as a top-level form and compiled: the procedure of
    /// no arguments that runs it; or why it could not be.
    fn eval_procedure(&mut self, datum: Value) -> Result<Value, String> {
        // Its text, for where an error is: the datum as written.
        let text = fixpt_runtime::write_value(&self.rt.heap, datum);
        let file = self.rt.sources.add("<eval>", text.as_str());
        let span = Span::new(file, 0, text.len() as u32);
        let mut pairs = 0;
        let form = self.datum_syntax(datum, span, &mut pairs)?;
        let parts = self.parts.take().expect("expander state is always returned");
        let program = std::mem::replace(&mut self.program, Program::empty());
        let mut expander = Expander::resume(&mut self.rt, ExpanderParts { builder: Builder::from_program(program), ..parts });
        let expanded = expander.expand_forms(std::slice::from_ref(&form));
        let (mut program, parts) = match expanded {
            Ok(body) => expander.into_parts(body),
            Err(e) => {
                let (program, parts) = expander.into_parts(fixpt_core::ir::NodeId(0));
                (self.program, self.parts) = (program, Some(parts));
                return Err(self.describe(e.span, &e.message));
            }
        };
        self.parts = Some(parts);
        // As a transformer's expression is (`Expander::eval_now`): what
        // this does not reach is analysed again before the next input runs.
        fixpt_core::analyze(&mut program);
        let f = self.prepared.thunk_for(&mut self.rt.heap, &self.rt.interner, &program);
        self.program = program;
        f.map_err(|e| e.to_string())
    }

    /// `v`, a datum, as syntax, every piece at `span`: lists, vectors,
    /// symbols, keywords, strings, characters, booleans, numbers and
    /// bytevectors. A list longer than the heap could hold is a cycle.
    fn datum_syntax(&mut self, v: Value, span: Span, pairs: &mut usize) -> Result<Syntax, String> {
        let datum = if v.is_pair() {
            let (mut items, mut cur) = (Vec::new(), v);
            while cur.is_pair() {
                *pairs += 1;
                if *pairs > self.rt.heap.capacity() {
                    return Err("eval: a cycle is not code".to_string());
                }
                let head = self.rt.heap.car(cur);
                items.push(self.datum_syntax(head, span, pairs)?);
                cur = self.rt.heap.cdr(cur);
            }
            let tail = if cur == Value::NULL { None } else { Some(Box::new(self.datum_syntax(cur, span, pairs)?)) };
            Datum::List { items, tail }
        } else if let Some(d) = self.atom_datum(v)? {
            d
        } else {
            let heap = &self.rt.heap;
            match heap.obj_type(v) {
                Some(ObjType::Vector) => {
                    let n = heap.obj_len(v);
                    let mut items = Vec::with_capacity(n);
                    for i in 0..n {
                        let x = self.rt.heap.obj_ref(v, i);
                        items.push(self.datum_syntax(x, span, pairs)?);
                    }
                    Datum::Vector(items)
                }
                _ => return Err(format!("eval: not code: {}", fixpt_runtime::write_value(heap, v))),
            }
        };
        Ok(Syntax::new(span, datum))
    }

    /// `v` as a datum of no parts, if it is one.
    fn atom_datum(&mut self, v: Value) -> Result<Option<Datum>, String> {
        let heap = &self.rt.heap;
        Ok(Some(if v == Value::NULL {
            Datum::Nil
        } else if v.is_char() {
            Datum::Char(v.as_char())
        } else if v == Value::TRUE || v == Value::FALSE {
            Datum::Bool(v == Value::TRUE)
        } else if heap.is_keyword(v) {
            let name = heap.symbol_name(heap.keyword_symbol(v));
            Datum::Keyword(self.rt.interner.intern(&name))
        } else if fixpt_runtime::N::load(heap, v).is_some() {
            let text = fixpt_runtime::write_value(heap, v);
            Datum::Number(fixpt_read::reader::parse_number(&text, 10, None).ok_or_else(|| format!("eval: not a number it reads: {text}"))?)
        } else {
            match heap.obj_type(v) {
                Some(ObjType::Symbol) => {
                    let name = heap.symbol_name(v);
                    Datum::Symbol(self.rt.interner.intern(&name))
                }
                Some(ObjType::String) => Datum::Str(heap.string_to_rust(v)),
                Some(ObjType::Bytevector) => Datum::Bytevector(heap.bytevector_to_vec(v)),
                _ => return Ok(None),
            }
        }))
    }
}
