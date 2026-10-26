//! The rules for processes and `par` (`docs/fx26.md`, "Processes and `par`";
//! kayak's request, `TODO.md` §92). The forms are derived (`parse.rs`):
//! each calls a procedure of the scheduler, `fx26:processes.fx`, through the
//! hidden global of its load, which `library_type` types. Two of them are
//! rules of their own, here, at the call:
//! - `spawn`'s body crosses into a process that shares no mutable data
//!   with the one that made it, so what it holds, and what it does beyond
//!   its own mailbox and place, must be *transmissible* (`untransmissible`,
//!   `crossing_atom`);
//! - `par`'s branches may run at once, so neither may do what the other's
//!   effect could see (`interference`): Lucassen's `cobegin` rule, by FX's
//!   table, with `init` against `await` dataflow.
//!
//! Nothing here assumes the processes take turns: the rules hold as well if
//! each runs on a thread of its own, with a heap of its own.

use crate::ast::{Atom, D, DVar, Effect, Exp, ExpId, Kind, Region, Ty, TyId};
use crate::check::{Checker, ADDR_INDEX, INBOX_INDEX, PROCESS_INDEX};
use crate::error::{FxError, R};
use fixpt_read::Syntax;
use std::collections::HashSet;

impl Checker {
    /// The forms of processes and `par`, each a call of a procedure of the
    /// scheduler's (`fx26:processes.fx`) through the hidden global of its
    /// load, made here if it is not yet:
    /// - `(spawn (box M r) body …)`: `((with lib spawn-process) (plambda
    ///   ((r place)) (lambda ((box (inbox M r)) (r (place r))) body … #u)))`;
    /// - `(send a v)`, `(receive box)`, `(self box)`, `(icell-get c)`,
    ///   `(icell-put! c v)`: `((with lib name) …)`;
    /// - `(par ((x1 e1) … (xn en)) body …)`: `par2` of the first branch and
    ///   the `par` of the rest, as thunks, its parts bound by `let`;
    /// - `(race e1 … en)`: `race2` of the first branch and the `race` of the
    ///   rest, as thunks;
    /// - `(attempt e h)`: `((with lib attempt1) (lambda () e) h)`.
    pub(crate) fn parse_process_form(&mut self, span: fixpt_read::Span, head: &str, items: &[Syntax]) -> R<ExpId> {
        let lib = self.parse_load(span, crate::check::PROCESSES, false)?;
        let Exp::Var(lib) = *self.arena.exp_at(lib) else { unreachable!("a load is its hidden global") };
        let sym = |c: &mut Self, s: &str| Syntax::symbol(span, c.interner.intern(s));
        let op = |c: &mut Self, name: &str| {
            let with = sym(c, "with");
            let name = sym(c, name);
            Syntax::list(span, vec![with, Syntax::symbol(span, lib), name])
        };
        let call = |c: &mut Self, name: &str, args: &[Syntax]| {
            let mut v = vec![op(c, name)];
            v.extend(args.iter().cloned());
            Syntax::list(span, v)
        };
        let usage = |shape: &str| FxError::at(span, format!("`{shape}`"));
        let expansion = match (head, items) {
            ("send", [_, a, v]) => call(self, "send", &[a.clone(), v.clone()]),
            ("send", _) => return Err(usage("(send address message)")),
            ("receive", [_, b]) => call(self, "receive", &[b.clone()]),
            ("receive", _) => return Err(usage("(receive mailbox)")),
            ("self", [_, b]) => call(self, "self", &[b.clone()]),
            ("self", _) => return Err(usage("(self mailbox)")),
            ("icell-get", [_, c]) => call(self, "icell-get", &[c.clone()]),
            ("icell-get", _) => return Err(usage("(icell-get i-cell)")),
            ("icell-put!", [_, c, v]) => call(self, "icell-put!", &[c.clone(), v.clone()]),
            ("icell-put!", _) => return Err(usage("(icell-put! i-cell value)")),
            ("spawn", [_, header, body @ ..]) if !body.is_empty() => {
                let proc = self.process_body(span, header, body)?;
                call(self, "spawn-process", &[proc])
            }
            ("spawn-monitored", [_, w, f, header, body @ ..]) if !body.is_empty() => {
                let proc = self.process_body(span, header, body)?;
                call(self, "spawn-monitored", &[w.clone(), f.clone(), proc])
            }
            ("spawn-monitored", _) => {
                return Err(usage("(spawn-monitored watcher on-failure (mailbox message-type place) body …)"));
            }
            ("spawn", _) => return Err(usage("(spawn (mailbox message-type place) body …)")),
            ("par", [_, bindings, body @ ..]) if !body.is_empty() => {
                let shape = "(par ((name expression) …) body …)";
                let Some(bs) = bindings.as_proper_list() else { return Err(usage(shape)) };
                let mut parts = Vec::new();
                for b in bs {
                    match b.as_proper_list() {
                        Some([x, e]) if x.as_symbol().is_some() => parts.push((x.clone(), e.clone(), b.span)),
                        _ => return Err(FxError::at(b.span, "a `par` binding is `(name expression)`")),
                    }
                }
                if parts.len() < 2 {
                    return Err(FxError::at(span, "`par` runs two branches or more: `(par ((name expression) …) body …)`"));
                }
                self.par_expansion(span, lib, &parts, body)
            }
            ("par", _) => return Err(usage("(par ((name expression) …) body …)")),
            ("race", [_, branches @ ..]) if branches.len() >= 2 => self.race_expansion(span, lib, branches),
            ("race", _) => return Err(usage("(race expression expression …)")),
            ("attempt", [_, body, on_failure]) => {
                let lambda = Syntax::symbol(body.span, self.interner.intern("lambda"));
                let thunk = Syntax::list(body.span, vec![lambda, Syntax::new(body.span, fixpt_read::Datum::Nil), body.clone()]);
                call(self, "attempt1", &[thunk, on_failure.clone()])
            }
            ("attempt", _) => return Err(usage("(attempt expression on-failure)")),
            ("pselect", [_, arms @ ..]) if !arms.is_empty() => self.select_expansion(span, lib, arms)?,
            ("pselect", _) => {
                return Err(usage(
                    "(pselect ((icell-get i-cell) name body …) ((receive mailbox) name body …) ((sleep-until time) name body …) ((read-byte) name body …) …)",
                ));
            }
            _ => unreachable!("a form of processes"),
        };
        self.parse_exp(&expansion)
    }

    /// A process's body, `(spawn (box M r) body …)`'s: `(plambda ((r
    /// place)) (lambda ((box (inbox M r)) (r (place r))) body … #u))`.
    fn process_body(&mut self, span: fixpt_read::Span, header: &Syntax, body: &[Syntax]) -> R<Syntax> {
        let sym = |c: &mut Self, s: &str| Syntax::symbol(span, c.interner.intern(s));
        let shape = "`(spawn (mailbox message-type place) body …)`";
        let Some([b, m, r]) = header.as_proper_list() else { return Err(FxError::at(span, shape)) };
        if b.as_symbol().is_none() || r.as_symbol().is_none() {
            return Err(FxError::at(span, shape));
        }
        let (place, inbox, lambda, plambda) = (sym(self, "place"), sym(self, "inbox"), sym(self, "lambda"), sym(self, "plambda"));
        let inbox_t = Syntax::list(span, vec![inbox, m.clone(), r.clone()]);
        let place_t = Syntax::list(span, vec![place.clone(), r.clone()]);
        let params = Syntax::list(span, vec![Syntax::list(span, vec![b.clone(), inbox_t]), Syntax::list(span, vec![r.clone(), place_t])]);
        let mut lam = vec![lambda, params];
        lam.extend(body.iter().cloned());
        lam.push(sym(self, "#u"));
        let binder = Syntax::list(span, vec![Syntax::list(span, vec![r.clone(), place])]);
        let lam = Syntax::list(span, lam);
        Ok(Syntax::list(span, vec![plambda, binder, lam]))
    }

    /// `(par ((x1 e1) … (xn en)) body …)`: `(let ((%par tree)) (let ((x1
    /// (extract %par 1)) (%par (extract %par 2))) … (let ((xn-1 (extract
    /// %par 1)) (xn (extract %par 2))) body …)))`, `tree` the branches as
    /// nested `par2`s, `(par2 (lambda () e1) (lambda () rest))`, so that
    /// each branch is checked against all the others. What is made for a
    /// binding (its thunk, its `extract`s) is at the binding; the rest at
    /// the form.
    fn par_expansion(&mut self, span: fixpt_read::Span, lib: fixpt_read::Sym, parts: &[(Syntax, Syntax, fixpt_read::Span)], body: &[Syntax]) -> Syntax {
        let sym = |c: &mut Self, sp: fixpt_read::Span, s: &str| Syntax::symbol(sp, c.interner.intern(s));
        let thunk = |c: &mut Self, sp: fixpt_read::Span, e: Syntax| {
            let lambda = sym(c, sp, "lambda");
            Syntax::list(sp, vec![lambda, Syntax::new(sp, fixpt_read::Datum::Nil), e])
        };
        let bindings: Vec<fixpt_read::Span> = parts.iter().map(|(_, _, b)| *b).collect();
        let n = parts.len();
        // The branches as nested `par2`s, from the last.
        let mut tree = thunk(self, bindings[n - 1], parts[n - 1].1.clone());
        for i in (0..n - 1).rev() {
            let b = bindings[i];
            let op = Syntax::list(span, vec![sym(self, span, "with"), Syntax::symbol(span, lib), sym(self, span, "par2")]);
            let first = thunk(self, b, parts[i].1.clone());
            tree = Syntax::list(span, vec![op, first, tree]);
            if i > 0 {
                tree = thunk(self, span, tree);
            }
        }
        let p = Syntax::symbol(span, self.interner.intern("%par"));
        let extract = |c: &mut Self, sp: fixpt_read::Span, k: i64| {
            let e = sym(c, sp, "extract");
            Syntax::list(sp, vec![e, p.clone(), Syntax::new(sp, fixpt_read::Datum::Number(fixpt_read::Num::Int(k)))])
        };
        // The innermost `let` first: the last two branches' values.
        let b = bindings[n - 2];
        let (x, y) = (parts[n - 2].0.clone(), parts[n - 1].0.clone());
        let (ex, ey) = (extract(self, b, 1), extract(self, b, 2));
        let mut inner = vec![sym(self, span, "let"), Syntax::list(span, vec![Syntax::list(span, vec![x, ex]), Syntax::list(span, vec![y, ey])])];
        inner.extend(body.iter().cloned());
        let mut out = Syntax::list(span, inner);
        for i in (0..n - 2).rev() {
            let b = bindings[i];
            let (ex, ep) = (extract(self, b, 1), extract(self, b, 2));
            let binds = Syntax::list(span, vec![Syntax::list(span, vec![parts[i].0.clone(), ex]), Syntax::list(span, vec![p.clone(), ep])]);
            out = Syntax::list(span, vec![sym(self, span, "let"), binds, out]);
        }
        let outer_bind = Syntax::list(span, vec![Syntax::list(span, vec![p.clone(), tree])]);
        Syntax::list(span, vec![sym(self, span, "let"), outer_bind, out])
    }

    /// `(race e1 … en)`: `((with lib race2) (lambda () e1) (lambda ()
    /// ((with lib race2) (lambda () e2) … (lambda () en))))`: a branch's
    /// thunk at its expression, the rest at the form.
    fn race_expansion(&mut self, span: fixpt_read::Span, lib: fixpt_read::Sym, es: &[Syntax]) -> Syntax {
        let sym = |c: &mut Self, sp: fixpt_read::Span, s: &str| Syntax::symbol(sp, c.interner.intern(s));
        let thunk = |c: &mut Self, sp: fixpt_read::Span, e: Syntax| {
            let lambda = sym(c, sp, "lambda");
            Syntax::list(sp, vec![lambda, Syntax::new(sp, fixpt_read::Datum::Nil), e])
        };
        let n = es.len();
        let mut tree = thunk(self, es[n - 1].span, es[n - 1].clone());
        for i in (0..n - 1).rev() {
            let e = &es[i];
            let op = Syntax::list(span, vec![sym(self, span, "with"), Syntax::symbol(span, lib), sym(self, span, "race2")]);
            let first = thunk(self, e.span, e.clone());
            tree = Syntax::list(span, vec![op, first, tree]);
            if i > 0 {
                tree = thunk(self, span, tree);
            }
        }
        tree
    }

    /// `(pselect (W0 x0 body0 …) … (Wn xn bodyn …))`, each `W` `(icell-get
    /// c)`, `(receive box)`, `(sleep-until t)` or `(read-byte)` (whose `c`
    /// is `#u`, at `W`, and which is called with none): `(let ((%sel-0 c0) …
    /// (%sel-n cn)) (let ((%sel (sync (or-event E0 (or-event E1 … En)))))
    /// (if (= %sel 0) (let ((x0 (icell-get %sel-0))) body0 …) … (let ((xn
    /// …)) bodyn …))))`, each `E` `(cell-event %sel-i)`, `(mailbox-event
    /// %sel-i)`, `(clock-event %sel-i)` or `(stdin-event %sel-i)`, through
    /// `lib`. An arm's event, test and `let` at the arm, its `W` at the
    /// `W`; the rest at the form.
    fn select_expansion(&mut self, span: fixpt_read::Span, lib: fixpt_read::Sym, arms: &[Syntax]) -> R<Syntax> {
        let sym = |c: &mut Self, sp: fixpt_read::Span, s: &str| Syntax::symbol(sp, c.interner.intern(s));
        let shape = "a `pselect` arm is `((icell-get i-cell) name body …)`, `((receive mailbox) name body …)`, \
                     `((sleep-until time) name body …)` or `((read-byte) name body …)`";
        let mut parts = Vec::new();
        for arm in arms {
            let Some([w, x, body @ ..]) = arm.as_proper_list() else { return Err(FxError::at(arm.span, shape)) };
            let ws = w.as_proper_list().unwrap_or_default();
            let head = ws.first().and_then(|h| h.as_symbol()).map(|h| self.interner.name(h));
            let event = match (head, ws.len()) {
                _ if x.as_symbol().is_none() || body.is_empty() => return Err(FxError::at(arm.span, shape)),
                (Some("icell-get"), 2) => "cell-event",
                (Some("receive"), 2) => "mailbox-event",
                (Some("sleep-until"), 2) => "clock-event",
                (Some("read-byte"), 1) => "stdin-event",
                _ => return Err(FxError::at(arm.span, shape)),
            };
            let operand = match ws.get(1) {
                Some(c) => c.clone(),
                None => sym(self, w.span, "#u"),
            };
            parts.push((arm.span, w.clone(), x.clone(), body.to_vec(), event, operand));
        }
        let lib_op = |c: &mut Self, sp: fixpt_read::Span, name: &str| {
            let with = sym(c, sp, "with");
            let name = sym(c, sp, name);
            Syntax::list(sp, vec![with, Syntax::symbol(sp, lib), name])
        };
        let n = parts.len();
        let names: Vec<Syntax> = (0..n).map(|i| sym(self, span, &format!("%sel-{i}"))).collect();
        // The events, joined from the last.
        let mut events = None;
        for (i, (arm, ..)) in parts.iter().enumerate().rev() {
            let e = Syntax::list(*arm, vec![lib_op(self, *arm, parts[i].4), names[i].clone()]);
            events = Some(match events {
                None => e,
                Some(rest) => Syntax::list(span, vec![lib_op(self, span, "or-event"), e, rest]),
            });
        }
        let sync = Syntax::list(span, vec![lib_op(self, span, "sync"), events.expect("an arm")]);
        let sel = sym(self, span, "%sel");
        // The arms, the last first.
        let mut out = None;
        for (i, (arm, w, x, body, ..)) in parts.iter().enumerate().rev() {
            let ws = w.as_proper_list().expect("an arm's wait");
            let mut get = vec![ws[0].clone()];
            if ws.len() == 2 {
                get.push(names[i].clone());
            }
            let get = Syntax::list(w.span, get);
            let mut l = vec![sym(self, *arm, "let"), Syntax::list(*arm, vec![Syntax::list(*arm, vec![x.clone(), get])])];
            l.extend(body.iter().cloned());
            let this = Syntax::list(*arm, l);
            out = Some(match out {
                None => this,
                Some(rest) => {
                    let k = Syntax::new(*arm, fixpt_read::Datum::Number(fixpt_read::Num::Int(i as i64)));
                    let test = Syntax::list(*arm, vec![sym(self, *arm, "="), sel.clone(), k]);
                    Syntax::list(span, vec![sym(self, span, "if"), test, this, rest])
                }
            });
        }
        let let_ = sym(self, span, "let");
        let inner = Syntax::list(span, vec![let_.clone(), Syntax::list(span, vec![Syntax::list(span, vec![sel, sync])]), out.expect("an arm")]);
        let binds = parts.iter().enumerate().map(|(i, p)| Syntax::list(span, vec![names[i].clone(), p.5.clone()]));
        Ok(Syntax::list(span, vec![let_, Syntax::list(span, binds.collect()), inner]))
    }

    /// The procedure of the scheduler's that `fun` names, if it names one:
    /// `(with %shared:fx26:processes.fx name)`.
    pub(crate) fn library_op(&self, fun: ExpId) -> Option<&str> {
        let Exp::With { module, body } = *self.arena.exp_at(fun) else { return None };
        self.library_type(module, body)?;
        match *self.arena.exp_at(body) {
            Exp::Var(n) => Some(self.interner.name(n)),
            _ => None,
        }
    }

    /// Why a value of type `t` may not cross into another process, or
    /// `None` if it may: if it is *transmissible*. Data frozen in the heap,
    /// numbers, characters, strings and symbols; products, sums and unions
    /// of transmissible parts; addresses and I-cells (shared: an I-cell is
    /// a capability, as an address is, and is never in a place that could
    /// end before a process holding it), and processes' bodies; procedures
    /// whose parameters and result are transmissible and whose latent
    /// effect does nothing but what a process may do anywhere
    /// (`crossing_atom`). Not a reference, array, pair or bloblet that can
    /// be written, or one frozen into a place; nor a mailbox, a tag, a
    /// continuation, a key, a place or a module; nor a type variable but of
    /// kind `data` in the heap.
    pub(crate) fn untransmissible(&self, t: TyId) -> Option<String> {
        self.untransmissible_in(t, &mut HashSet::new(), &mut Vec::new())
    }

    fn untransmissible_in(&self, t: TyId, seen: &mut HashSet<TyId>, bound: &mut Vec<DVar>) -> Option<String> {
        let t = self.arena.resolve(t);
        if !seen.insert(t) {
            return None;
        }
        let data_at = |c: &Self, r: Region, bound: &Vec<DVar>, what: &str| -> Option<String> {
            match r {
                Region::Frozen(None, _) => None,
                Region::Var(v) if bound.contains(&v) => None,
                _ => Some(format!("a {what} at {}, which can be written", c.show_region(r))),
            }
        };
        match self.arena.get(t).clone() {
            Ty::Base(_) | Ty::Nat(_) | Ty::Void | Ty::Nil | Ty::False => None,
            Ty::Var(v) if bound.contains(&v) || self.arena.dvar_kind_known(v) == Some(Kind::Sendable) => None,
            Ty::Var(v) if self.arena.is_data_var(v) && self.arena.bound(v).is_none_or(|p| p == Region::Heap) => None,
            Ty::Var(v) => Some(format!("a `{}`, which could be anything", self.interner.name(self.arena.dvar_name(v)))),
            Ty::Product(ps) | Ty::Sum(ps) => ps.iter().find_map(|(_, x)| self.untransmissible_in(*x, seen, bound)),
            Ty::Union(ms) => ms.iter().find_map(|x| self.untransmissible_in(*x, seen, bound)),
            Ty::Pair(a, b, r, _) => data_at(self, r, bound, "pair")
                .or_else(|| self.untransmissible_in(a, seen, bound))
                .or_else(|| self.untransmissible_in(b, seen, bound)),
            Ty::NList { elem, region, .. } => data_at(self, region, bound, "list").or_else(|| self.untransmissible_in(elem, seen, bound)),
            Ty::Array(a, _, r) => data_at(self, r, bound, "array").or_else(|| self.untransmissible_in(a, seen, bound)),
            Ty::Ref(a, r) => data_at(self, r, bound, "reference").or_else(|| self.untransmissible_in(a, seen, bound)),
            Ty::Bloblet { fields, frozen, region } => {
                let r = if frozen { None } else { data_at(self, region, bound, "bloblet") };
                r.or_else(|| fields.iter().find_map(|f| self.untransmissible_in(*f, seen, bound)))
            }
            Ty::ICell(a, _) => self.untransmissible_in(a, seen, bound),
            Ty::Named { which: ADDR_INDEX | PROCESS_INDEX, .. } => None,
            // A procedure's parameter, at a region it binds, the caller's.
            Ty::Named { which: INBOX_INDEX, args } if matches!(&args[..], [_, D::Region(Region::Var(v))] if bound.contains(v)) => None,
            Ty::Named { which: INBOX_INDEX, .. } => Some("a process's own mailbox, which only it may take from".to_string()),
            Ty::Subr { effect, params, result, .. } => self
                .crossing_effect(&effect, bound)
                .map(|a| format!("a procedure that has {}", self.show_effect(&Effect::atom(a))))
                .or_else(|| params.iter().chain([&result]).find_map(|p| self.untransmissible_in(*p, seen, bound))),
            Ty::Poly { binders, body } => {
                let depth = bound.len();
                bound.extend(binders.iter().map(|(v, _)| *v));
                let r = self.untransmissible_in(body, seen, bound);
                bound.truncate(depth);
                r
            }
            _ => Some(format!("a {}", self.show_ty(t))),
        }
    }

    /// The first atom of `e` that a procedure crossing into a process may
    /// not have, if any: one on a region that is not its own, but for
    /// sending, filling or awaiting an I-cell, reading globals' bindings or
    /// frozen data in the heap; any I/O, `spin` and `nondet`; and what is on
    /// a binder in `bound`, which its caller gives.
    fn crossing_effect(&self, e: &Effect, bound: &[DVar]) -> Option<Atom> {
        e.0.iter().copied().find(|a| {
            !(match *a {
                Atom::Var(v) => bound.contains(&v),
                _ => self.crossing_atom(*a) || a.region().is_some_and(|r| matches!(r, Region::Var(v) if bound.contains(&v))),
            })
        })
    }

    /// Whether atom `a` is one a process may have that is seen outside it:
    /// sending, filling or awaiting an I-cell, I/O, `spin`, `nondet`;
    /// reading globals' bindings or frozen data in the heap; allocating at a
    /// region that is no place (a constant, or the heap), which is the
    /// heap's memory. Not allocating at a region that could be a place: a
    /// process outliving the place would allocate in memory given back.
    /// What a process's body of latent effect `effect` does beyond its own
    /// place `own`, which is the process's alone: the rest, with `nondet`
    /// if it does I/O, which may interleave with another's (the process
    /// type's effect, `(process M e)`; `spawn`'s, and the cells' verifier's
    /// of a body passed to the scheduler).
    pub(crate) fn process_effect(&self, own: Region, effect: &Effect) -> Effect {
        let mut seen = Effect(effect.0.iter().copied().filter(|a| a.region() != Some(own)).collect());
        if seen.0.iter().any(|a| matches!(a, Atom::Io(_))) {
            seen.0.insert(Atom::Nondet);
        }
        seen
    }

    pub(crate) fn crossing_atom(&self, a: Atom) -> bool {
        match a {
            Atom::Send(_) | Atom::Init(_) | Atom::Await(_) | Atom::Io(_) | Atom::Spin | Atom::Nondet => true,
            Atom::Read(r) => r.is_globals() || matches!(r, Region::Frozen(None, _)),
            Atom::Alloc(r) => matches!(r, Region::Const(_) | Region::Heap),
            _ => false,
        }
    }

    /// `((with … spawn-process) body)`, as `spawn` makes it: `body` is
    /// `(plambda ((r place)) (lambda ((box (inbox M r)) (r (place r))) …))`,
    /// a process's body, which runs with a mailbox of its own and a place
    /// of its own, `r`, bound for it alone. What it is given (its free
    /// variables, globals too) and the messages it takes must be
    /// transmissible; what it does to anything but `r` must be what a
    /// process may do (`crossing_atom`), and is the spawn's effect, with
    /// `nondet` if it does I/O, which may interleave with another's. Its
    /// value is the process's address, `(addr M A)`, at the region the
    /// address is expected at, else at a region of its own; making it
    /// allocates there.
    /// `((with … spawn-monitored) w f body)`, as `spawn-monitored` makes
    /// it: `spawn`'s rule for the body; `w`, the watcher's address, `(addr
    /// W R)`; `f`, a `(subr pure (string) W)`, which makes the watcher's
    /// message of a failure's; and the form's effect `spawn`'s, its
    /// arguments', and `(send R)`, the failure's message.
    pub(crate) fn synth_spawn_monitored(&mut self, e: ExpId, fun: ExpId, w: ExpId, f: ExpId, body: ExpId, expected: Option<TyId>) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let (wt, we) = self.synth(w)?;
        let (msg, at) = match self.arena.get(self.arena.resolve(wt)).clone() {
            Ty::Named { which: ADDR_INDEX, args } => match &args[..] {
                [D::Type(m), D::Region(a)] => (*m, *a),
                _ => return Err(FxError::at(span, "a watcher is a process's address")),
            },
            _ => {
                return Err(FxError::at(span, format!("a watcher is a process's address, `(addr M R)`, and this is a {}", self.show_ty(wt))));
            }
        };
        let string = self.base[&self.interner.intern("string")];
        let want = self.arena.ty(Ty::Subr { effect: Effect::pure(), params: vec![string], result: msg, conv: self.conv_default, spec: None });
        let (ft, fe) = self.synth(f)?;
        if !self.subtype(ft, want) {
            return Err(FxError::at(
                span,
                format!("a monitor's `on-failure` makes the watcher's message of a failure's, a {}, and this is a {}", self.show_ty(want), self.show_ty(ft)),
            ));
        }
        let (t, eff) = self.synth_spawn(e, fun, body, expected)?;
        if let Some(mut inst) = self.facts.insts.remove(&e) {
            inst.extend([D::Type(msg), D::Region(at)]);
            self.note_library_inst(e, inst);
        }
        Ok((t, eff.union(&we).union(&fe).union(&Effect::atom(Atom::Send(at)))))
    }

    pub(crate) fn synth_spawn(&mut self, e: ExpId, fun: ExpId, body: ExpId, expected: Option<TyId>) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let usage = "a process's body is `(spawn (mailbox message-type place) body …)`";
        let Exp::PLambda { binders, body: lam } = self.arena.exp_at(body).clone() else {
            return Err(FxError::at(span, usage));
        };
        let [(r, Kind::Place)] = binders[..] else { return Err(FxError::at(span, usage)) };
        if !matches!(self.arena.exp_at(lam), Exp::Lambda { params, .. } if params.len() == 2) {
            return Err(FxError::at(span, usage));
        }
        let (t, _) = self.synth(body)?;
        let Ty::Poly { body: inner, .. } = self.arena.get(self.arena.resolve(t)).clone() else { unreachable!("a plambda's type") };
        let Ty::Subr { effect, params, .. } = self.arena.get(self.arena.resolve(inner)).clone() else { unreachable!("a lambda's type") };
        // What crosses: each free variable's value, globals' included; not
        // the standard bindings, nor the hidden globals of loads, which are
        // the runtime's.
        for v in self.free_vars(body) {
            if self.is_standard(v) || self.shared_globals.contains(&v) {
                continue;
            }
            let Some(t) = self.lookup(v) else { continue };
            if let Some(why) = self.untransmissible(t) {
                return Err(FxError::at(
                    span,
                    format!("a process may share nothing that can be written, and its body holds `{}`: {why}", self.interner.name(v)),
                ));
            }
        }
        let msg = match self.arena.get(self.arena.resolve(params[0])).clone() {
            Ty::Named { which: INBOX_INDEX, args } => match &args[..] {
                [D::Type(m), D::Region(Region::Var(q))] if *q == r => *m,
                _ => return Err(FxError::at(span, usage)),
            },
            _ => return Err(FxError::at(span, usage)),
        };
        if let Some(why) = self.untransmissible(msg) {
            return Err(FxError::at(span, format!("a process's messages are copied to it, so they must be transmissible, and a {} is not: {why}", self.show_ty(msg))));
        }
        let mut seen = self.process_effect(Region::Var(r), &effect);
        if let Some(a) = seen.0.iter().copied().find(|a| !self.crossing_atom(*a)) {
            return Err(FxError::at(
                span,
                format!(
                    "a process may share nothing that can be written, and its body has {}, on a region outside it",
                    self.show_effect(&Effect::atom(a))
                ),
            ));
        }
        // The address's region: as expected, or one of its own.
        let wanted = expected.and_then(|x| match self.arena.get(self.arena.resolve(x)).clone() {
            Ty::Named { which: ADDR_INDEX, args } => match &args[..] {
                [D::Type(m), D::Region(a)] => Some((*m, *a)),
                _ => None,
            },
            _ => None,
        });
        let at = wanted.filter(|(m, _)| self.subtype(msg, *m) && self.subtype(*m, msg)).map(|(_, a)| a);
        let at = match at {
            Some(a) => a,
            None => self.fresh_region_named("@process"),
        };
        if let Exp::With { module, body } = *self.arena.exp_at(fun) {
            self.with_as(fun, module, body, None)?;
        }
        let addr = self.arena.ty(Ty::Named { which: ADDR_INDEX, args: vec![D::Type(msg), D::Region(at)] });
        // The scheduler's `spawn-process` at what this rule found, for the
        // cells' verifier (`Facts::insts`).
        self.note_library_inst(e, vec![D::Type(msg), D::Region(at), D::Effect(seen.clone())]);
        seen.0.insert(Atom::Alloc(at));
        Ok((addr, seen))
    }

    /// `((with … par2) (lambda () e1) (lambda () e2))`, as `par` makes it:
    /// both run, perhaps at once, so neither may write what the other
    /// reads or writes, by the table of `interference`, nor transfer
    /// control out of its branch; its value is both theirs, `(productof (1
    /// T1) (2 T2))`, and its effect both theirs. Its answer is the same
    /// however the two are interleaved.
    pub(crate) fn synth_par(&mut self, e: ExpId, fun: ExpId, args: &[ExpId]) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let [f, g] = args else { return Err(FxError::at(span, "`(par ((name expression) …) body …)`")) };
        let (ft, fe) = self.synth(*f)?;
        let (gt, ge) = self.synth(*g)?;
        let thunk = |c: &Self, t: TyId| match c.arena.get(c.arena.resolve(t)).clone() {
            Ty::Subr { effect, params, result, .. } if params.is_empty() => Some((effect, result)),
            _ => None,
        };
        let (Some((e1, a)), Some((e2, b))) = (thunk(self, ft), thunk(self, gt)) else {
            return Err(FxError::at(span, "`(par ((name expression) …) body …)`"));
        };
        for (branch, eff) in [(*f, &e1), (*g, &e2)] {
            if let Some(a) = eff.0.iter().find(|a| matches!(a, Atom::Goto(_) | Atom::Comefrom(_))) {
                return Err(FxError::at(
                    self.arena.span_of(branch),
                    format!("a `par` branch must end where it began, and this one has {}", self.show_effect(&Effect::atom(*a))),
                ));
            }
        }
        if let Some((x, y)) = self.interference(&e1, &e2) {
            return Err(FxError::at(
                span,
                format!(
                    "`par`'s branches interfere: one has {} and another {}, so the answer could depend on which runs first",
                    self.show_effect(&Effect::atom(x)),
                    self.show_effect(&Effect::atom(y))
                ),
            ));
        }
        if let Exp::With { module, body } = *self.arena.exp_at(fun) {
            self.with_as(fun, module, body, None)?;
        }
        let one = self.interner.intern("1");
        let two = self.interner.intern("2");
        let t = self.arena.ty(Ty::Product(vec![(one, a), (two, b)]));
        self.note_library_inst(e, vec![D::Type(a), D::Type(b), D::Effect(e1.clone()), D::Effect(e2.clone())]);
        Ok((t, fe.union(&ge).union(&e1).union(&e2)))
    }

    /// What the scheduler's procedure called at `e` is instantiated at, by
    /// the rule that checked the call rather than by instantiation: for the
    /// cells' verifier, as an ordinary call's is (`Facts::insts`).
    fn note_library_inst(&mut self, e: ExpId, inst: Vec<D>) {
        if self.record_types {
            self.facts.insts.insert(e, inst);
        }
    }

    /// `((with … race2) (lambda () e1) (lambda () e2))`, as `race` makes
    /// it: both run, perhaps at once, and the first to finish gives the
    /// value; the other may be stopped at once, at its next wait, or never.
    /// So that no program can tell which, each branch must be
    /// *cancellable*: it may read, allocate, await, receive and spin, but
    /// not write, fill an I-cell, send, do I/O, or transfer control out of
    /// itself, nor have an effect not known (a variable's); and the two
    /// must not interfere (two receives). Its value is a branch's, both of
    /// one type, and its effect both theirs and `nondet`: which finishes
    /// first is the schedule's.
    pub(crate) fn synth_race(&mut self, e: ExpId, fun: ExpId, args: &[ExpId]) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let usage = "`(race expression expression …)`";
        let [f, g] = args else { return Err(FxError::at(span, usage)) };
        let (ft, fe) = self.synth(*f)?;
        let (gt, ge) = self.synth(*g)?;
        let thunk = |c: &Self, t: TyId| match c.arena.get(c.arena.resolve(t)).clone() {
            Ty::Subr { effect, params, result, .. } if params.is_empty() => Some((effect, result)),
            _ => None,
        };
        let (Some((e1, a)), Some((e2, b))) = (thunk(self, ft), thunk(self, gt)) else {
            return Err(FxError::at(span, usage));
        };
        for (branch, eff) in [(*f, &e1), (*g, &e2)] {
            self.cancellable(branch, eff, "a `race` branch may be stopped half way")?;
        }
        if let Some((x, y)) = self.interference(&e1, &e2) {
            return Err(FxError::at(
                span,
                format!(
                    "`race`'s branches interfere: one has {} and another {}",
                    self.show_effect(&Effect::atom(x)),
                    self.show_effect(&Effect::atom(y))
                ),
            ));
        }
        let t = if self.subtype(b, a) {
            a
        } else if self.subtype(a, b) {
            b
        } else {
            return Err(FxError::at(
                span,
                format!("`race`'s branches give values of two types, {} and {}", self.show_ty(a), self.show_ty(b)),
            ));
        };
        if let Exp::With { module, body } = *self.arena.exp_at(fun) {
            self.with_as(fun, module, body, None)?;
        }
        self.note_library_inst(e, vec![D::Type(t), D::Effect(e1.clone()), D::Effect(e2.clone())]);
        Ok((t, fe.union(&ge).union(&e1).union(&e2).union(&Effect::atom(Atom::Nondet))))
    }

    /// Refused unless `eff`, of the thunk `branch`, is cancellable: it may
    /// read, allocate, await, receive and spin, but not write, fill an
    /// I-cell, send, do I/O, or transfer control out of itself, nor have
    /// an effect not known. `why` begins the refusal.
    fn cancellable(&self, branch: ExpId, eff: &Effect, why: &str) -> R<()> {
        let uncancellable = |a: &Atom| {
            matches!(a, Atom::Write(_) | Atom::Init(_) | Atom::Send(_) | Atom::Io(_) | Atom::Goto(_) | Atom::Comefrom(_) | Atom::Var(_) | Atom::App(_))
        };
        match eff.0.iter().find(|a| uncancellable(a)) {
            Some(a) => Err(FxError::at(
                self.arena.span_of(branch),
                format!("{why}, so it must do nothing another could see, and this one has {}", self.show_effect(&Effect::atom(*a))),
            )),
            None => Ok(()),
        }
    }

    /// `((with … attempt1) (lambda () e) h)`, as `attempt` makes it
    /// (Heist's, `FIXPT-CHANGES.md` F1): `e`'s value, or, should it fail
    /// (`error`, a trap), `h` of the failure's message. `e` must be
    /// cancellable, as a `race` branch must, so that a failure half way
    /// leaves nothing another could see; `h` is a `(subr eh (string) b)`,
    /// run after. Its value is the wider of `e`'s and `h`'s, and its effect
    /// both theirs and `nondet`: what a failure says is the machine's.
    pub(crate) fn synth_attempt(&mut self, e: ExpId, fun: ExpId, args: &[ExpId]) -> R<(TyId, Effect)> {
        let span = self.arena.span_of(e);
        let usage = "`(attempt expression on-failure)`";
        let [f, h] = args else { return Err(FxError::at(span, usage)) };
        let (ft, fe) = self.synth(*f)?;
        let (ht, he) = self.synth(*h)?;
        let Ty::Subr { effect: e1, params, result: a, .. } = self.arena.get(self.arena.resolve(ft)).clone() else {
            return Err(FxError::at(span, usage));
        };
        if !params.is_empty() {
            return Err(FxError::at(span, usage));
        }
        let string = self.base[&self.interner.intern("string")];
        let (e2, b) = match self.arena.get(self.arena.resolve(ht)).clone() {
            Ty::Subr { effect, params, result, .. } if params.len() == 1 && self.subtype(string, params[0]) => {
                (effect, result)
            }
            _ => {
                return Err(FxError::at(
                    self.arena.span_of(*h),
                    format!("`attempt`'s on-failure takes the failure's message, a string, but is {}", self.show_ty(ht)),
                ));
            }
        };
        self.cancellable(*f, &e1, "an `attempt`'s body may be stopped half way")?;
        let t = if self.subtype(b, a) {
            a
        } else if self.subtype(a, b) {
            b
        } else {
            return Err(FxError::at(
                span,
                format!("`attempt`'s body gives {} and its on-failure {}", self.show_ty(a), self.show_ty(b)),
            ));
        };
        if let Exp::With { module, body } = *self.arena.exp_at(fun) {
            self.with_as(fun, module, body, None)?;
        }
        self.note_library_inst(e, vec![D::Type(t), D::Effect(e1.clone()), D::Effect(e2.clone())]);
        Ok((t, fe.union(&he).union(&e1).union(&e2).union(&Effect::atom(Atom::Nondet))))
    }

    /// The first pair of atoms, one of each effect, that interfere: on
    /// regions that may be one (`regions_distinct` says when they are
    /// not), a write against a read, a write, a fill or an await; a fill
    /// against a write (against a read or an await it is dataflow: the
    /// await waits for it); two sends to one mailbox's region (which
    /// arrives first is a choice), a receive against a send or a receive;
    /// any two I/O effects (none commutes with another). An effect
    /// variable, or an application of one, may be any of them: against
    /// anything but allocation, `spin` and `nondet`. Lucassen and Gifford's
    /// `cobegin` (FX-87), Lucassen's thesis, chapter 6.
    pub(crate) fn interference(&self, x: &Effect, y: &Effect) -> Option<(Atom, Atom)> {
        for a in &x.0 {
            for b in &y.0 {
                if self.interferes(*a, *b) || self.interferes(*b, *a) {
                    return Some((*a, *b));
                }
            }
        }
        None
    }

    fn interferes(&self, a: Atom, b: Atom) -> bool {
        let unknown = |a: Atom| matches!(a, Atom::Var(_) | Atom::App(_));
        let harmless = |a: Atom| matches!(a, Atom::Alloc(_) | Atom::Spin | Atom::Nondet);
        if unknown(a) {
            return !harmless(b);
        }
        let one = |p: Region, q: Region| !self.regions_distinct(p, q);
        match (a, b) {
            (Atom::Write(p), Atom::Read(q) | Atom::Write(q) | Atom::Init(q) | Atom::Await(q)) => one(p, q),
            (Atom::Init(p), Atom::Write(q)) => one(p, q),
            (Atom::Send(p), Atom::Send(q)) => one(p, q),
            (Atom::Receive(p), Atom::Send(q) | Atom::Receive(q)) => one(p, q),
            (Atom::Io(_), Atom::Io(_)) => true,
            _ => false,
        }
    }
}
