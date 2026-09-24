//! Special-form expansion.
//!
//! Most handlers rewrite to simpler *syntax* and re-enter [`Expander::expr`],
//! rather than emitting IR. `cond`, `case`, `do`, `when`, `let*` and `guard`
//! are each a few lines that read like their definition in the report, which is
//! the point: the derived forms are correct by visibly matching the standard's
//! own rewriting, not by a second implementation that has to be re-argued.

use crate::env::{Binding, Special};
use crate::expand::{fixnum, form, nil, sym, ExpandError, Expander};
use fixpt_core::ir::{LambdaInfo, Node, NodeId};
use fixpt_core::VarId;
use fixpt_heap::Value;
use fixpt_read::{Datum, Span, Sym, Syntax};

type R<T> = Result<T, ExpandError>;

impl Expander<'_> {
    pub(crate) fn special(
        &mut self,
        s: &Syntax,
        sp: Special,
        items: &[Syntax],
        name: Option<Sym>,
    ) -> R<NodeId> {
        let span = s.span;
        let args = &items[1..];
        match sp {
            Special::Quote => {
                self.need(span, args, 1, "quote")?;
                let v = self.datum_to_value(&args[0]);
                self.constant(span, v)
            }
            Special::Quasiquote => {
                self.need(span, args, 1, "quasiquote")?;
                let expanded = self.quasiquote(&args[0], 1)?;
                self.expr(&expanded)
            }
            Special::Unquote | Special::UnquoteSplicing => {
                Err(ExpandError::at(span, "unquote outside of a quasiquote"))
            }
            Special::Else | Special::Arrow => {
                Err(ExpandError::at(span, "`else` and `=>` are only valid in `cond` and `case`"))
            }
            Special::If => {
                if args.len() != 2 && args.len() != 3 {
                    return Err(ExpandError::at(span, "`if` takes a test and one or two branches"));
                }
                let test = self.expr(&args[0])?;
                let then = self.expr(&args[1])?;
                let els = match args.get(2) {
                    Some(e) => self.expr(e)?,
                    None => self.constant(span, Value::UNSPECIFIED)?,
                };
                Ok(self.b.node(span, Node::If(test, then, els)))
            }
            Special::Lambda => {
                if args.is_empty() {
                    return Err(ExpandError::at(span, "`lambda` needs a formal list"));
                }
                self.lambda(span, &args[0], &args[1..], name)
            }
            Special::Define => Err(ExpandError::at(
                span,
                "`define` is only allowed at the top level or at the start of a body",
            )),
            Special::Set => {
                self.need(span, args, 2, "set!")?;
                let target = args[0]
                    .as_symbol()
                    .ok_or_else(|| ExpandError::at(args[0].span, "`set!` needs a variable"))?;
                let value = self.expr(&args[1])?;
                match self.resolve(target) {
                    Some(Binding::Local(v)) => Ok(self.b.node(span, Node::Set(v, value))),
                    Some(Binding::Special(_)) => {
                        Err(ExpandError::at(args[0].span, "cannot `set!` a syntactic keyword"))
                    }
                    _ => {
                        let g = self.global(target);
                        Ok(self.b.node(span, Node::GlobalSet(g, value)))
                    }
                }
            }
            Special::Begin => {
                // A `begin` whose first element is an inert annotation is not a
                // sequence: it is one expression carrying what a front end
                // proved about it. See `Expander::read_note`.
                if let Some(facts) = self.read_note(args)
                    && args.len() == 2
                {
                    let node = self.expr(&args[1])?;
                    self.b.set_facts(node, facts);
                    return Ok(node);
                }
                let mut nodes = Vec::with_capacity(args.len());
                for a in args {
                    nodes.push(self.expr(a)?);
                }
                Ok(self.seq(span, nodes))
            }
            Special::Let => self.expand_let(span, args),
            Special::LetStar => self.expand_let_star(span, args),
            Special::Letrec | Special::LetrecStar => self.expand_letrec(span, args),
            Special::LetValues | Special::LetStarValues => self.expand_let_values(span, args),
            Special::DefineValues => Err(ExpandError::at(
                span,
                "`define-values` is only allowed at the top level or at the start of a body",
            )),
            Special::DefineRecordType => Err(ExpandError::at(
                span,
                "`define-record-type` is only allowed at the top level or at the start of a body",
            )),
            Special::Do => self.expand_do(span, args),
            Special::Cond => self.expand_cond(span, args),
            Special::Case => self.expand_case(span, args),
            Special::And => self.expand_and(span, args),
            Special::Or => self.expand_or(span, args),
            Special::When => self.expand_when(span, args, true),
            Special::Unless => self.expand_when(span, args, false),
            Special::Delay => self.expand_delay(span, args, false),
            Special::DelayForce => self.expand_delay(span, args, true),
            Special::Guard => self.expand_guard(span, args),
            Special::WithMark => self.expand_with_mark(span, args),
            Special::DefineSyntax => Err(ExpandError::at(
                span,
                "`define-syntax` is only allowed at the top level or at the start of a body",
            )),
            Special::BeginForSyntax => Err(ExpandError::at(
                span,
                "`begin-for-syntax` is only allowed at the top level",
            )),
            Special::SyntaxRules => Err(ExpandError::at(
                span,
                "`syntax-rules` is only valid as the transformer of a macro definition",
            )),
            Special::LetSyntax => self.expand_let_syntax(span, args, false),
            Special::LetrecSyntax => self.expand_let_syntax(span, args, true),
        }
    }

    fn need(&self, span: Span, args: &[Syntax], n: usize, what: &str) -> R<()> {
        if args.len() == n {
            Ok(())
        } else {
            Err(ExpandError::at(
                span,
                format!("`{what}` takes {n} argument{}, got {}", if n == 1 { "" } else { "s" }, args.len()),
            ))
        }
    }

    // ------------------------------------------------------------- lambda
    fn lambda(
        &mut self,
        span: Span,
        formals: &Syntax,
        body: &[Syntax],
        name: Option<Sym>,
    ) -> R<NodeId> {
        let (names, rest_name) = self.formals(formals)?;
        self.env.push();
        let params: Vec<VarId> = names
            .iter()
            .map(|n| {
                let v = self.b.var(*n, span);
                self.env.bind(*n, Binding::Local(v));
                v
            })
            .collect();
        let rest = rest_name.map(|n| {
            let v = self.b.var(n, span);
            self.env.bind(n, Binding::Local(v));
            v
        });
        let placeholder = self.constant(span, Value::UNSPECIFIED)?;
        let id = self.b.lambda(LambdaInfo {
            name,
            params,
            rest,
            body: placeholder,
            span,
            free: Vec::new(),
        });
        let b = self.body(span, body)?;
        self.b.set_lambda_body(id, b);
        self.env.pop();
        Ok(self.b.node(span, Node::Lambda(id)))
    }

    /// `(a b c)`, `(a b . rest)`, or a bare `rest`.
    fn formals(&mut self, s: &Syntax) -> R<(Vec<Sym>, Option<Sym>)> {
        match &s.datum {
            Datum::Symbol(rest) => Ok((Vec::new(), Some(*rest))),
            Datum::Nil => Ok((Vec::new(), None)),
            Datum::List { items, tail } => {
                let mut names = Vec::with_capacity(items.len());
                for item in items {
                    let n = item
                        .as_symbol()
                        .ok_or_else(|| ExpandError::at(item.span, "a formal must be a symbol"))?;
                    if names.contains(&n) {
                        let text = self.rt.interner.name(n);
                        return Err(ExpandError::at(item.span, format!("duplicate formal `{text}`")));
                    }
                    names.push(n);
                }
                let rest = match tail {
                    None => None,
                    Some(t) => Some(
                        t.as_symbol()
                            .ok_or_else(|| ExpandError::at(t.span, "a rest formal must be a symbol"))?,
                    ),
                };
                Ok((names, rest))
            }
            _ => Err(ExpandError::at(s.span, "a formal list must be a list of symbols")),
        }
    }

    // ---------------------------------------------------------------- let
    fn bindings(&self, s: &Syntax, what: &str) -> R<Vec<(Syntax, Syntax)>> {
        let items = s
            .as_proper_list()
            .ok_or_else(|| ExpandError::at(s.span, format!("`{what}` needs a binding list")))?;
        let mut out = Vec::with_capacity(items.len());
        for b in items {
            let parts = b.as_proper_list().ok_or_else(|| {
                ExpandError::at(b.span, format!("a `{what}` binding must be `(name value)`"))
            })?;
            match parts.len() {
                1 => out.push((parts[0].clone(), Syntax::new(b.span, Datum::Bool(false)))),
                2 => out.push((parts[0].clone(), parts[1].clone())),
                _ => {
                    return Err(ExpandError::at(
                        b.span,
                        format!("a `{what}` binding must be `(name value)`"),
                    ));
                }
            }
        }
        Ok(out)
    }

    fn expand_let(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        if args.is_empty() {
            return Err(ExpandError::at(span, "`let` needs bindings and a body"));
        }
        // Named let: `(let loop ((v init)…) body…)`.
        if let Some(loop_name) = args[0].as_symbol() {
            if args.len() < 2 {
                return Err(ExpandError::at(span, "named `let` needs bindings and a body"));
            }
            let binds = self.bindings(&args[1], "let")?;
            let vars: Vec<Syntax> = binds.iter().map(|(n, _)| n.clone()).collect();
            let inits: Vec<Syntax> = binds.iter().map(|(_, v)| v.clone()).collect();
            // `((letrec* ((loop (lambda (v…) body…))) loop) init…)`
            let lam = {
                let mut l = vec![sym(span, self.syms.lambda), Syntax::list(span, vars)];
                l.extend_from_slice(&args[2..]);
                Syntax::list(span, l)
            };
            let binding = Syntax::list(span, vec![args[0].clone(), lam]);
            let rec = form(
                span,
                self.syms.letrec_star,
                vec![Syntax::list(span, vec![binding]), sym(span, loop_name)],
            );
            let mut call = vec![rec];
            call.extend(inits);
            return self.expr(&Syntax::list(span, call));
        }

        let binds = self.bindings(&args[0], "let")?;
        let mut inits = Vec::with_capacity(binds.len());
        for (_, v) in &binds {
            inits.push(self.expr(v)?);
        }
        self.env.push();
        let mut vars = Vec::with_capacity(binds.len());
        for (n, _) in &binds {
            let sym = n
                .as_symbol()
                .ok_or_else(|| ExpandError::at(n.span, "a `let` binding needs a name"))?;
            let v = self.b.var(sym, n.span);
            self.env.bind(sym, Binding::Local(v));
            vars.push(v);
        }
        let body = self.body(span, &args[1..])?;
        self.env.pop();
        Ok(self.b.node(
            span,
            Node::Let { vars: vars.into_boxed_slice(), inits: inits.into_boxed_slice(), body },
        ))
    }

    fn expand_let_star(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        if args.is_empty() {
            return Err(ExpandError::at(span, "`let*` needs bindings and a body"));
        }
        let binds = self.bindings(&args[0], "let*")?;
        if binds.len() <= 1 {
            let mut form = vec![sym(span, self.syms.let_), args[0].clone()];
            form.extend_from_slice(&args[1..]);
            return self.expr(&Syntax::list(span, form));
        }
        // `(let (b0) (let* (b1…) body…))`
        let first = Syntax::list(span, vec![binds[0].0.clone(), binds[0].1.clone()]);
        let rest: Vec<Syntax> = binds[1..]
            .iter()
            .map(|(n, v)| Syntax::list(span, vec![n.clone(), v.clone()]))
            .collect();
        let mut inner = vec![sym(span, self.syms.let_star), Syntax::list(span, rest)];
        inner.extend_from_slice(&args[1..]);
        let form = form(
            span,
            self.syms.let_,
            vec![Syntax::list(span, vec![first]), Syntax::list(span, inner)],
        );
        self.expr(&form)
    }

    fn expand_letrec(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        if args.is_empty() {
            return Err(ExpandError::at(span, "`letrec` needs bindings and a body"));
        }
        let binds = self.bindings(&args[0], "letrec")?;
        self.env.push();
        let mut vars = Vec::with_capacity(binds.len());
        for (n, _) in &binds {
            let sym = n
                .as_symbol()
                .ok_or_else(|| ExpandError::at(n.span, "a `letrec` binding needs a name"))?;
            let v = self.b.var(sym, n.span);
            self.env.bind(sym, Binding::Local(v));
            vars.push(v);
        }
        let mut inits = Vec::with_capacity(binds.len());
        for (i, (n, v)) in binds.iter().enumerate() {
            let _ = i;
            inits.push(self.named_expr(v, n.as_symbol())?);
        }
        let body = self.body(span, &args[1..])?;
        self.env.pop();
        Ok(self.b.node(
            span,
            Node::Fix { vars: vars.into_boxed_slice(), inits: inits.into_boxed_slice(), body },
        ))
    }

    /// `(let-values (((a b) e)…) body…)` becomes nested `call-with-values`.
    fn expand_let_values(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        if args.is_empty() {
            return Err(ExpandError::at(span, "`let-values` needs bindings and a body"));
        }
        let items = args[0]
            .as_proper_list()
            .ok_or_else(|| ExpandError::at(args[0].span, "`let-values` needs a binding list"))?;
        if items.is_empty() {
            let mut form = vec![sym(span, self.syms.let_), nil(span)];
            form.extend_from_slice(&args[1..]);
            return self.expr(&Syntax::list(span, form));
        }
        let parts = items[0]
            .as_proper_list()
            .ok_or_else(|| ExpandError::at(items[0].span, "expected `(formals expression)`"))?;
        if parts.len() != 2 {
            return Err(ExpandError::at(items[0].span, "expected `(formals expression)`"));
        }
        let producer = form(
            span,
            self.syms.lambda,
            vec![nil(span), parts[1].clone()],
        );
        let inner_bindings = Syntax::list(span, items[1..].to_vec());
        let mut consumer_body = vec![sym(span, self.syms.let_values), inner_bindings];
        consumer_body.extend_from_slice(&args[1..]);
        let consumer = form(
            span,
            self.syms.lambda,
            vec![parts[0].clone(), Syntax::list(span, consumer_body)],
        );
        let form = form(span, self.syms.call_with_values, vec![producer, consumer]);
        self.expr(&form)
    }

    // ---------------------------------------------------------- conditionals
    fn expand_cond(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        if args.is_empty() {
            return self.constant(span, Value::UNSPECIFIED);
        }
        let clause = args[0]
            .as_proper_list()
            .ok_or_else(|| ExpandError::at(args[0].span, "a `cond` clause must be a list"))?;
        if clause.is_empty() {
            return Err(ExpandError::at(args[0].span, "an empty `cond` clause"));
        }
        let is_else = clause[0]
            .as_symbol()
            .is_some_and(|s| self.resolve(s) == Some(Binding::Special(Special::Else)));
        if is_else {
            if args.len() > 1 {
                return Err(ExpandError::at(args[1].span, "`else` must be the last `cond` clause"));
            }
            let mut form = vec![sym(span, self.syms.begin)];
            form.extend_from_slice(&clause[1..]);
            return self.expr(&Syntax::list(span, form));
        }
        let rest = {
            let mut f = vec![sym(span, self.syms.cond)];
            f.extend_from_slice(&args[1..]);
            Syntax::list(span, f)
        };
        // `(test => receiver)`: bind the test value so the receiver sees it.
        let is_arrow = clause.len() == 3
            && clause[1]
                .as_symbol()
                .is_some_and(|s| self.resolve(s) == Some(Binding::Special(Special::Arrow)));
        if is_arrow {
            let t = self.gensym(span, "cond");
            let binding = Syntax::list(span, vec![t.clone(), clause[0].clone()]);
            let call = Syntax::list(span, vec![clause[2].clone(), t.clone()]);
            let if_form = form(span, self.syms.if_, vec![t, call, rest]);
            let form = form(
                span,
                self.syms.let_,
                vec![Syntax::list(span, vec![binding]), if_form],
            );
            return self.expr(&form);
        }
        if clause.len() == 1 {
            // `(test)` yields the test's value when it is true.
            let t = self.gensym(span, "cond");
            let binding = Syntax::list(span, vec![t.clone(), clause[0].clone()]);
            let if_form = form(span, self.syms.if_, vec![t.clone(), t, rest]);
            let form = form(
                span,
                self.syms.let_,
                vec![Syntax::list(span, vec![binding]), if_form],
            );
            return self.expr(&form);
        }
        let body = {
            let mut f = vec![sym(span, self.syms.begin)];
            f.extend_from_slice(&clause[1..]);
            Syntax::list(span, f)
        };
        let form = form(span, self.syms.if_, vec![clause[0].clone(), body, rest]);
        self.expr(&form)
    }

    fn expand_case(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        if args.is_empty() {
            return Err(ExpandError::at(span, "`case` needs a key"));
        }
        let key = self.gensym(span, "case");
        let mut clauses = Vec::new();
        for clause in &args[1..] {
            let parts = clause
                .as_proper_list()
                .ok_or_else(|| ExpandError::at(clause.span, "a `case` clause must be a list"))?;
            if parts.is_empty() {
                return Err(ExpandError::at(clause.span, "an empty `case` clause"));
            }
            let is_else = parts[0]
                .as_symbol()
                .is_some_and(|s| self.resolve(s) == Some(Binding::Special(Special::Else)));
            let test = if is_else {
                sym(span, self.syms.else_)
            } else {
                let data = form(span, self.syms.quote, vec![parts[0].clone()]);
                form(span, self.syms.memv, vec![key.clone(), data])
            };
            // `=>` in a case clause receives the key, per R7RS.
            let is_arrow = parts.len() == 3
                && parts[1]
                    .as_symbol()
                    .is_some_and(|s| self.resolve(s) == Some(Binding::Special(Special::Arrow)));
            let mut out = vec![test];
            if is_arrow {
                out.push(Syntax::list(span, vec![parts[2].clone(), key.clone()]));
            } else {
                out.extend_from_slice(&parts[1..]);
            }
            clauses.push(Syntax::list(span, out));
        }
        let cond = {
            let mut f = vec![sym(span, self.syms.cond)];
            f.append(&mut clauses);
            Syntax::list(span, f)
        };
        let binding = Syntax::list(span, vec![key, args[0].clone()]);
        let form =
            form(span, self.syms.let_, vec![Syntax::list(span, vec![binding]), cond]);
        self.expr(&form)
    }

    fn expand_and(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        match args.len() {
            0 => self.constant(span, Value::TRUE),
            1 => self.expr(&args[0]),
            _ => {
                let rest = {
                    let mut f = vec![sym(span, self.syms.and)];
                    f.extend_from_slice(&args[1..]);
                    Syntax::list(span, f)
                };
                let falsy = Syntax::new(span, Datum::Bool(false));
                let form = form(span, self.syms.if_, vec![args[0].clone(), rest, falsy]);
                self.expr(&form)
            }
        }
    }

    fn expand_or(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        match args.len() {
            0 => self.constant(span, Value::FALSE),
            1 => self.expr(&args[0]),
            _ => {
                // The value of the first true operand is the result, so it must
                // be bound rather than re-evaluated.
                let t = self.gensym(span, "or");
                let rest = {
                    let mut f = vec![sym(span, self.syms.or)];
                    f.extend_from_slice(&args[1..]);
                    Syntax::list(span, f)
                };
                let binding = Syntax::list(span, vec![t.clone(), args[0].clone()]);
                let if_form = form(span, self.syms.if_, vec![t.clone(), t, rest]);
                let form = form(
                    span,
                    self.syms.let_,
                    vec![Syntax::list(span, vec![binding]), if_form],
                );
                self.expr(&form)
            }
        }
    }

    fn expand_when(&mut self, span: Span, args: &[Syntax], positive: bool) -> R<NodeId> {
        if args.is_empty() {
            return Err(ExpandError::at(span, "`when`/`unless` needs a test"));
        }
        let body = {
            let mut f = vec![sym(span, self.syms.begin)];
            f.extend_from_slice(&args[1..]);
            Syntax::list(span, f)
        };
        let unspecified = Syntax::list(span, vec![sym(span, self.syms.begin)]);
        let branches =
            if positive { vec![body, unspecified] } else { vec![unspecified, body] };
        let mut form_args = vec![args[0].clone()];
        form_args.extend(branches);
        let form = form(span, self.syms.if_, form_args);
        self.expr(&form)
    }

    fn expand_do(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        if args.len() < 2 {
            return Err(ExpandError::at(span, "`do` needs bindings and a test clause"));
        }
        let specs = args[0]
            .as_proper_list()
            .ok_or_else(|| ExpandError::at(args[0].span, "`do` needs a binding list"))?;
        let mut names = Vec::new();
        let mut inits = Vec::new();
        let mut steps = Vec::new();
        for spec in specs {
            let parts = spec.as_proper_list().ok_or_else(|| {
                ExpandError::at(spec.span, "a `do` binding is `(name init [step])`")
            })?;
            if parts.len() < 2 || parts.len() > 3 {
                return Err(ExpandError::at(spec.span, "a `do` binding is `(name init [step])`"));
            }
            names.push(parts[0].clone());
            inits.push(parts[1].clone());
            // An omitted step means the variable is unchanged.
            steps.push(parts.get(2).cloned().unwrap_or_else(|| parts[0].clone()));
        }
        let test_clause = args[1]
            .as_proper_list()
            .ok_or_else(|| ExpandError::at(args[1].span, "`do` needs a test clause"))?;
        if test_clause.is_empty() {
            return Err(ExpandError::at(args[1].span, "`do`'s test clause needs a test"));
        }
        let result = {
            let mut f = vec![sym(span, self.syms.begin)];
            f.extend_from_slice(&test_clause[1..]);
            Syntax::list(span, f)
        };
        let loop_name = self.gensym(span, "do");
        let recur = {
            let mut f = vec![loop_name.clone()];
            f.extend(steps);
            Syntax::list(span, f)
        };
        let body = {
            let mut f = vec![sym(span, self.syms.begin)];
            f.extend_from_slice(&args[2..]);
            f.push(recur);
            Syntax::list(span, f)
        };
        let if_form =
            form(span, self.syms.if_, vec![test_clause[0].clone(), result, body]);
        let lam = form(span, self.syms.lambda, vec![Syntax::list(span, names), if_form]);
        let binding = Syntax::list(span, vec![loop_name.clone(), lam]);
        let call = {
            let mut f = vec![loop_name];
            f.extend(inits);
            Syntax::list(span, f)
        };
        let form = form(
            span,
            self.syms.letrec_star,
            vec![Syntax::list(span, vec![binding]), call],
        );
        self.expr(&form)
    }

    // ------------------------------------------------------------- promises
    fn expand_delay(&mut self, span: Span, args: &[Syntax], lazy: bool) -> R<NodeId> {
        self.need(span, args, 1, if lazy { "delay-force" } else { "delay" })?;
        let thunk = form(
            span,
            self.syms.lambda,
            vec![nil(span), args[0].clone()],
        );
        let maker = if lazy { self.syms.make_promise_lazy } else { self.syms.make_promise_thunk };
        let form = form(span, maker, vec![thunk]);
        self.expr(&form)
    }

    /// `(let-syntax ((name spec) …) body…)` and `letrec-syntax`.
    ///
    /// The only difference is where the transformers' free identifiers are
    /// looked up: outside the new scope for `let-syntax`, inside it — so the
    /// macros can refer to one another — for `letrec-syntax`.
    fn expand_let_syntax(&mut self, span: Span, args: &[Syntax], rec: bool) -> R<NodeId> {
        let what = if rec { "letrec-syntax" } else { "let-syntax" };
        let Some((bindings, body)) = args.split_first() else {
            return Err(ExpandError::at(span, format!("`{what}` needs bindings and a body")));
        };
        let pairs = bindings
            .as_proper_list()
            .or(matches!(bindings.datum, Datum::Nil).then_some(&[][..]))
            .ok_or_else(|| ExpandError::at(bindings.span, format!("`{what}` needs a list of bindings")))?
            .to_vec();
        let outer = self.env.depth() as u32;
        self.env.push();
        let scope = if rec { outer + 1 } else { outer };
        let result = (|| {
            for pair in &pairs {
                let (name, spec) = match pair.as_proper_list() {
                    Some([n, spec]) if n.as_symbol().is_some() => (n.as_symbol().expect("checked"), spec.clone()),
                    _ => return Err(ExpandError::at(pair.span, format!("a `{what}` binding is `(name transformer)`"))),
                };
                let id = self.make_macro(name, &spec, scope)?;
                self.env.bind(name, Binding::Macro(id));
            }
            self.body(span, body)
        })();
        self.env.pop();
        result
    }

    /// `(with-continuation-mark key val body)` → `(%wcm key val (lambda () body))`.
    ///
    /// Syntax rather than a procedure because `body` is in tail position with
    /// respect to the whole form: `%wcm` attaches the mark to the continuation
    /// of its own call and then *tail-calls* the thunk, so a
    /// `with-continuation-mark` in tail position marks the same frame each
    /// time round a loop and replaces the mark instead of stacking it.
    fn expand_with_mark(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        self.need(span, args, 3, "with-continuation-mark")?;
        let thunk = form(span, self.syms.lambda, vec![nil(span), args[2].clone()]);
        let call = form(span, self.syms.wcm, vec![args[0].clone(), args[1].clone(), thunk]);
        self.expr(&call)
    }

    // ---------------------------------------------------------------- guard
    /// The R7RS 4.2.7 reference expansion, written out. It is intricate, but
    /// implementing `guard` any other way would mean re-deriving the
    /// interaction between the handler stack and the escaping continuation,
    /// which is exactly what the standard already did.
    fn expand_guard(&mut self, span: Span, args: &[Syntax]) -> R<NodeId> {
        if args.is_empty() {
            return Err(ExpandError::at(span, "`guard` needs `(variable clause…)`"));
        }
        let spec = args[0]
            .as_proper_list()
            .ok_or_else(|| ExpandError::at(args[0].span, "`guard` needs `(variable clause…)`"))?;
        if spec.is_empty() {
            return Err(ExpandError::at(args[0].span, "`guard` needs a condition variable"));
        }
        let var = spec[0].clone();
        let clauses = &spec[1..];
        let guard_k = self.gensym(span, "guard-k");
        let handler_k = self.gensym(span, "handler-k");
        let condition = self.gensym(span, "condition");
        let rest_args = self.gensym(span, "args");

        let has_else = clauses.iter().any(|c| {
            c.as_proper_list()
                .and_then(|p| p.first())
                .and_then(|h| h.as_symbol())
                .is_some_and(|s| self.resolve(s) == Some(Binding::Special(Special::Else)))
        });

        // (handler-k (lambda () (raise-continuable condition)))
        let reraise = {
            let rc = form(span, self.syms.raise_continuable, vec![condition.clone()]);
            let th =
                form(span, self.syms.lambda, vec![nil(span), rc]);
            Syntax::list(span, vec![handler_k.clone(), th])
        };
        let cond_form = {
            let mut f = vec![sym(span, self.syms.cond)];
            f.extend_from_slice(clauses);
            if !has_else {
                f.push(Syntax::list(span, vec![sym(span, self.syms.else_), reraise]));
            }
            Syntax::list(span, f)
        };
        let bind_var = form(
            span,
            self.syms.let_,
            vec![
                Syntax::list(span, vec![Syntax::list(span, vec![var, condition.clone()])]),
                cond_form,
            ],
        );
        let guard_thunk =
            form(span, self.syms.lambda, vec![nil(span), bind_var]);
        let escape = Syntax::list(span, vec![guard_k.clone(), guard_thunk]);
        let handler_cc = form(
            span,
            self.syms.call_cc,
            vec![form(
                span,
                self.syms.lambda,
                vec![Syntax::list(span, vec![handler_k]), escape],
            )],
        );
        let handler = form(
            span,
            self.syms.lambda,
            vec![Syntax::list(span, vec![condition]), Syntax::list(span, vec![handler_cc])],
        );

        // (lambda () (call-with-values (lambda () body…)
        //              (lambda args (guard-k (lambda () (apply values args))))))
        let producer = {
            let mut f = vec![sym(span, self.syms.lambda), nil(span)];
            f.extend_from_slice(&args[1..]);
            Syntax::list(span, f)
        };
        let apply_values = Syntax::list(
            span,
            vec![
                sym(span, self.syms.apply),
                sym(span, self.syms.values),
                rest_args.clone(),
            ],
        );
        let result_thunk = form(
            span,
            self.syms.lambda,
            vec![nil(span), apply_values],
        );
        let consumer = form(
            span,
            self.syms.lambda,
            vec![rest_args, Syntax::list(span, vec![guard_k.clone(), result_thunk])],
        );
        let cwv = form(span, self.syms.call_with_values, vec![producer, consumer]);
        let thunk =
            form(span, self.syms.lambda, vec![nil(span), cwv]);
        let weh = form(span, self.syms.with_exception_handler, vec![handler, thunk]);
        let outer = form(
            span,
            self.syms.call_cc,
            vec![form(
                span,
                self.syms.lambda,
                vec![Syntax::list(span, vec![guard_k]), weh],
            )],
        );
        self.expr(&Syntax::list(span, vec![outer]))
    }

    // ---------------------------------------------------- define-record-type
    /// Produces the `define`s the record type stands for; the caller splices
    /// them into whatever definition context it is in.
    pub(crate) fn record_type_defines(&mut self, span: Span, args: &[Syntax]) -> R<Vec<Syntax>> {
        if args.len() < 3 {
            return Err(ExpandError::at(
                span,
                "`define-record-type` needs a name, a constructor, a predicate and fields",
            ));
        }
        let type_name = args[0]
            .as_symbol()
            .ok_or_else(|| ExpandError::at(args[0].span, "a record type name must be a symbol"))?;
        let ctor = args[1]
            .as_proper_list()
            .ok_or_else(|| ExpandError::at(args[1].span, "expected `(make-x field…)`"))?;
        if ctor.is_empty() {
            return Err(ExpandError::at(args[1].span, "expected `(make-x field…)`"));
        }
        let pred = args[2].clone();
        let field_specs = &args[3..];

        let mut field_names = Vec::new();
        for spec in field_specs {
            let parts = spec.as_proper_list().ok_or_else(|| {
                ExpandError::at(spec.span, "expected `(field accessor [modifier])`")
            })?;
            if parts.is_empty() {
                return Err(ExpandError::at(spec.span, "expected `(field accessor [modifier])`"));
            }
            field_names.push(parts[0].clone());
        }

        let mut forms: Vec<Syntax> = Vec::new();
        // (define <type> (%make-record-type '<type> '(field…)))
        let quoted_name = form(span, self.syms.quote, vec![args[0].clone()]);
        let quoted_fields =
            form(span, self.syms.quote, vec![Syntax::list(span, field_names.clone())]);
        forms.push(form(
            span,
            self.syms.define,
            vec![
                sym(span, type_name),
                form(span, self.syms.make_record_type, vec![quoted_name, quoted_fields]),
            ],
        ));

        // (define (make-x a b) (%record <type> f0 f1 …)) with each field taken
        // from the constructor argument of the same name, or #f when the
        // constructor does not mention it.
        let ctor_args: Vec<Syntax> = ctor[1..].to_vec();
        let mut record_args = vec![sym(span, type_name)];
        for f in &field_names {
            let named = ctor_args.iter().find(|a| a.as_symbol() == f.as_symbol());
            record_args
                .push(named.cloned().unwrap_or_else(|| Syntax::new(span, Datum::Bool(false))));
        }
        let ctor_head = {
            let mut h = vec![ctor[0].clone()];
            h.extend(ctor_args.clone());
            Syntax::list(span, h)
        };
        forms.push(form(
            span,
            self.syms.define,
            vec![ctor_head, form(span, self.syms.record, record_args)],
        ));

        // (define (pred x) (%record-of-type? x <type>))
        let x = self.gensym(span, "obj");
        forms.push(form(
            span,
            self.syms.define,
            vec![
                Syntax::list(span, vec![pred, x.clone()]),
                form(
                    span,
                    self.syms.record_of_type,
                    vec![x.clone(), sym(span, type_name)],
                ),
            ],
        ));

        for (i, spec) in field_specs.iter().enumerate() {
            let parts = spec.as_proper_list().expect("checked above");
            if let Some(accessor) = parts.get(1) {
                let idx = fixnum(span, i as i64);
                forms.push(form(
                    span,
                    self.syms.define,
                    vec![
                        Syntax::list(span, vec![accessor.clone(), x.clone()]),
                        form(
                            span,
                            self.syms.record_ref,
                            vec![x.clone(), sym(span, type_name), idx],
                        ),
                    ],
                ));
            }
            if let Some(modifier) = parts.get(2) {
                let idx = fixnum(span, i as i64);
                let v = self.gensym(span, "val");
                forms.push(form(
                    span,
                    self.syms.define,
                    vec![
                        Syntax::list(span, vec![modifier.clone(), x.clone(), v.clone()]),
                        form(
                            span,
                            self.syms.record_set,
                            vec![x.clone(), sym(span, type_name), idx, v],
                        ),
                    ],
                ));
            }
        }

        Ok(forms)
    }
}
